module

public import AmbidextrousSofa.Analysis.EndpointPolygons
public import AmbidextrousSofa.Analysis.FiniteScore

@[expose] public section

/-!
# Inward endpoint pressures from actual selected caps

The roof is extended continuously by clamping onto its original projection.
This extension is used only to differentiate the fixed comparison graph;
on every retained section it is the actual old roof. Inclusion decreases
the actual finite barrier, while the support-distance estimate controls
the actual quadratic penalty. This supplies the inward pressure inequality
without requiring a positive endpoint face.

The penalty normals may have a separate index type from the wall normals,
so both horizontal axis supports can be included. Its error coefficient
uses the dual one-norm appropriate to the product metric on `Plane`.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- Continuous extension by the attained endpoint values, used for local
endpoint differentiation only. -/
def extendedCapRoof (U : Set Plane) (x : ℝ) : ℝ :=
  capRoof U (max (horizontalLeft U) (min (horizontalRight U) x))

theorem IsDownwardCap.extendedCapRoof_eq {U : Set Plane} (hU : IsDownwardCap U)
    {x : ℝ} (hx : x ∈ Icc (horizontalLeft U) (horizontalRight U)) :
    extendedCapRoof U x = capRoof U x := by
  rw [extendedCapRoof, min_eq_right hx.2, max_eq_right hx.1]

theorem IsDownwardCap.continuous_extendedCapRoof {U : Set Plane} (hU : IsDownwardCap U) :
    Continuous (extendedCapRoof U) := by
  apply hU.continuousOn_capRoof_Icc.comp_continuous (by fun_prop)
  intro x
  exact ⟨le_max_left _ _, max_le
    (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact) (min_le_left _ _)⟩

def rightEndpointPressure (roof niche : ℝ → ℝ) (l r : ℝ) : ℝ :=
  (3 * (roof (r - (r - l) / 4) + niche (r - (r - l) / 4)) -
    (roof (l + (r - l) / 4) + niche (l + (r - l) / 4))) / 4

def leftEndpointPressure (roof niche : ℝ → ℝ) (l r : ℝ) : ℝ :=
  (3 * (roof (l + (r - l) / 4) + niche (l + (r - l) / 4)) -
    (roof (r - (r - l) / 4) + niche (r - (r - l) / 4))) / 4

theorem rightEndpointPressure_congr_roof {roof roof' niche : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r) (hroof : EqOn roof roof' (Icc l r)) :
    rightEndpointPressure roof niche l r = rightEndpointPressure roof' niche l r := by
  have hleft : l + (r - l) / 4 ∈ Icc l r := ⟨by linarith, by linarith⟩
  have hright : r - (r - l) / 4 ∈ Icc l r := ⟨by linarith, by linarith⟩
  rw [rightEndpointPressure, rightEndpointPressure, hroof hleft, hroof hright]

theorem leftEndpointPressure_congr_roof {roof roof' niche : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r) (hroof : EqOn roof roof' (Icc l r)) :
    leftEndpointPressure roof niche l r = leftEndpointPressure roof' niche l r := by
  have hleft : l + (r - l) / 4 ∈ Icc l r := ⟨by linarith, by linarith⟩
  have hright : r - (r - l) / 4 ∈ Icc l r := ⟨by linarith, by linarith⟩
  rw [leftEndpointPressure, leftEndpointPressure, hroof hleft, hroof hright]

theorem hasDerivAt_intervalSpatialScore_inward_right {roof niche : ℝ → ℝ}
    (hroof : Continuous roof) (hniche : Continuous niche) (l r : ℝ) :
    HasDerivAt (fun ε : ℝ => intervalSpatialScore roof niche l (r - ε))
      (rightEndpointPressure roof niche l r - roof r) 0 := by
  convert hasDerivAt_intervalSpatialScore_endpoints hroof hniche l r 0 (-1) using 1
  · funext ε
    simp only [mul_zero, add_zero, mul_neg_one, sub_eq_add_neg]
  · unfold rightEndpointPressure
    ring

theorem hasDerivAt_intervalSpatialScore_inward_left {roof niche : ℝ → ℝ}
    (hroof : Continuous roof) (hniche : Continuous niche) (l r : ℝ) :
    HasDerivAt (fun ε : ℝ => intervalSpatialScore roof niche (l + ε) r)
      (leftEndpointPressure roof niche l r - roof l) 0 := by
  convert hasDerivAt_intervalSpatialScore_endpoints hroof hniche l r 1 0 using 1
  · funext ε
    simp only [mul_zero, add_zero, mul_one]
  · unfold leftEndpointPressure
    ring

theorem rightEndpointPressure_le_of_inward_comparison {roof niche : ℝ → ℝ}
    (hroof : Continuous roof) (hniche : Continuous niche) (l r K : ℝ)
    (hcomparison : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      intervalSpatialScore roof niche l (r - ε) ≤ intervalSpatialScore roof niche l r + ε * K) :
    rightEndpointPressure roof niche l r ≤ roof r + K := by
  have hlinear : HasDerivAt (fun ε : ℝ => ε * K) K 0 := by
    simpa only [one_mul] using (hasDerivAt_id' (0 : ℝ)).mul_const K
  have hderiv := (hasDerivAt_intervalSpatialScore_inward_right hroof hniche l r).sub hlinear
  have hmax : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      intervalSpatialScore roof niche l (r - ε) - ε * K ≤
        intervalSpatialScore roof niche l (r - 0) - 0 * K := by
    filter_upwards [hcomparison] with ε hε
    simp only [sub_zero, zero_mul]
    linarith
  have hsign := hasDerivAt_nonpos_of_right_max hderiv hmax
  linarith

theorem leftEndpointPressure_le_of_inward_comparison {roof niche : ℝ → ℝ}
    (hroof : Continuous roof) (hniche : Continuous niche) (l r K : ℝ)
    (hcomparison : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      intervalSpatialScore roof niche (l + ε) r ≤ intervalSpatialScore roof niche l r + ε * K) :
    leftEndpointPressure roof niche l r ≤ roof l + K := by
  have hlinear : HasDerivAt (fun ε : ℝ => ε * K) K 0 := by
    simpa only [one_mul] using (hasDerivAt_id' (0 : ℝ)).mul_const K
  have hderiv := (hasDerivAt_intervalSpatialScore_inward_left hroof hniche l r).sub hlinear
  have hmax : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      intervalSpatialScore roof niche (l + ε) r - ε * K ≤
        intervalSpatialScore roof niche (l + 0) r - 0 * K := by
    filter_upwards [hcomparison] with ε hε
    simp only [add_zero, zero_mul]
    linarith
  have hsign := hasDerivAt_nonpos_of_right_max hderiv hmax
  linarith

/-- The two outer integrals agree; only the sign of the middle integral
changes. Both niches are actual integrable functions on the same window. -/
theorem intervalSpatialScore_le_of_roof_eq_of_niche_le
    {roof roof' niche niche' : ℝ → ℝ} {l r : ℝ} (hlr : l ≤ r)
    (hroof : EqOn roof roof' (Icc l r))
    (hniche : Continuous niche) (hniche' : Continuous niche') (hle : ∀ x, niche' x ≤ niche x) :
    intervalSpatialScore roof niche l r ≤ intervalSpatialScore roof' niche' l r := by
  rw [FinitePolygon.intervalSpatialScore_congr_roof hlr hroof]
  have hm : l + (r - l) / 4 ≤ r - (r - l) / 4 := by linarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) hm
    (hniche'.intervalIntegrable _ _) (hniche.intervalIntegrable _ _) (fun x _ => hle x)
  unfold intervalSpatialScore
  linarith

theorem abs_sq_sub_sq_le_of_abs_le {s t z B : ℝ}
    (hs : |s| ≤ B) (ht : |t| ≤ B) (hz : |z| ≤ B) :
    |(s - z) ^ 2 - (t - z) ^ 2| ≤ 4 * B * |s - t| := by
  have hbound : |s + t - 2 * z| ≤ 4 * B := by
    calc
      |s + t - 2 * z| ≤ |s + t| + |2 * z| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (s + t) (-(2 * z))
      _ = |s + t| + 2 * |z| := by rw [abs_mul]; norm_num
      _ ≤ |s| + |t| + 2 * |z| := by linarith [abs_add_le s t]
      _ ≤ 4 * B := by linarith
  rw [show (s - z) ^ 2 - (t - z) ^ 2 = (s - t) * (s + t - 2 * z) by ring, abs_mul]
  calc
    |s - t| * |s + t - 2 * z| ≤ |s - t| * (4 * B) :=
      mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
    _ = 4 * B * |s - t| := by ring

theorem abs_support_le_of_pointwise_bound {U : Set Plane} (hU : IsDownwardCap U)
    (v : Plane) {B : ℝ} (hB : ∀ p ∈ U, |coordDot p v| ≤ B) : |support U v| ≤ B := by
  obtain ⟨p, hp, hsupport⟩ := exists_coordDot_eq_support hU.isCompact hU.nonempty v
  rw [← hsupport]
  exact hB p hp

namespace FinitePolygon

variable {ι κ : Type*}

theorem supportWall_mono {U V : Set Plane} (hUV : U ⊆ V) (hne : U.Nonempty)
    (hV : IsCompact V) {n : Plane} (hn : 0 ≤ n.2) (x : ℝ) :
    supportWall U n x ≤ supportWall V n x := by
  unfold supportWall
  exact div_le_div_of_nonneg_right
    (sub_le_sub_right (sub_le_sub_right (support_mono hUV hne hV n) 1) _) hn

theorem finiteNiche_mono {U V : Set Plane} (hUV : U ⊆ V) (hne : U.Nonempty)
    (hV : IsCompact V) (normal : ι → Plane) (hnormal : ∀ i, 0 ≤ (normal i).2)
    (corners : List (ι × ι)) (x : ℝ) :
    finiteNiche U normal corners x ≤ finiteNiche V normal corners x := by
  induction corners with
  | nil => exact le_rfl
  | cons ij rest ih =>
    exact max_le_max (min_le_min (supportWall_mono hUV hne hV (hnormal ij.1) x)
      (supportWall_mono hUV hne hV (hnormal ij.2) x)) ih

theorem finiteBarrier_mono {U V : Set Plane} (hUV : U ⊆ V) (hne : U.Nonempty)
    (hV : IsCompact V) (normal : ι → Plane) (hnormal : ∀ i, 0 ≤ (normal i).2)
    (corners : List (ι × ι)) (terminal : Option ι) (x : ℝ) :
    finiteBarrier U normal corners terminal x ≤ finiteBarrier V normal corners terminal x := by
  cases terminal with
  | none => exact finiteNiche_mono hUV hne hV normal hnormal corners x
  | some i =>
    exact max_le_max (finiteNiche_mono hUV hne hV normal hnormal corners x)
      (supportWall_mono hUV hne hV (hnormal i) x)

/-- Exact coefficient for a product-metric support perturbation of the
displayed finite quadratic penalty. The weights already include any
selection parameter. -/
def supportPenaltyLipschitz [Fintype κ] (B : ℝ) (normal : κ → Plane) (weight : κ → ℝ) : ℝ :=
  4 * B * ∑ i, weight i * (|(normal i).1| + |(normal i).2|)

/-- The penalty is estimated at the new actual supports, including any
support whose displayed halfplane became redundant. -/
theorem abs_sampledPenalty_sub_le_of_support_control [Fintype κ]
    {U V : Set Plane} (hU : IsDownwardCap U) (hV : IsDownwardCap V) (hVU : V ⊆ U)
    (normal : κ → Plane) (weight target : κ → ℝ) {B ε : ℝ} (hB : 0 ≤ B)
    (hweight : ∀ i, 0 ≤ weight i)
    (hpoints : ∀ p ∈ U, ∀ i, |coordDot p (normal i)| ≤ B)
    (htarget : ∀ i, |target i| ≤ B)
    (hchange : ∀ i, |support V (normal i) - support U (normal i)| ≤
      ε * (|(normal i).1| + |(normal i).2|)) :
    |sampledPenalty V normal weight target - sampledPenalty U normal weight target| ≤
      ε * supportPenaltyLipschitz B normal weight := by
  have hi : ∀ i,
      |weight i * (support V (normal i) - target i) ^ 2 -
        weight i * (support U (normal i) - target i) ^ 2| ≤
      ε * (4 * B * (weight i * (|(normal i).1| + |(normal i).2|))) := by
    intro i
    have hVbound := abs_support_le_of_pointwise_bound hV (normal i)
      (fun p hp => hpoints p (hVU hp) i)
    have hUbound := abs_support_le_of_pointwise_bound hU (normal i)
      (fun p hp => hpoints p hp i)
    have hsquare := abs_sq_sub_sq_le_of_abs_le hVbound hUbound (htarget i)
    rw [← mul_sub, abs_mul, abs_of_nonneg (hweight i)]
    calc
      weight i * |(support V (normal i) - target i) ^ 2 -
          (support U (normal i) - target i) ^ 2| ≤
        weight i * (4 * B * |support V (normal i) - support U (normal i)|) :=
          mul_le_mul_of_nonneg_left hsquare (hweight i)
      _ ≤ weight i * (4 * B * (ε * (|(normal i).1| + |(normal i).2|))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hchange i) (mul_nonneg (by norm_num) hB)) (hweight i)
      _ = ε * (4 * B * (weight i * (|(normal i).1| + |(normal i).2|))) := by ring
  unfold sampledPenalty heightPenalty supportPenaltyLipschitz
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i, (weight i * (support V (normal i) - target i) ^ 2 -
        weight i * (support U (normal i) - target i) ^ 2)| ≤
      ∑ i, |weight i * (support V (normal i) - target i) ^ 2 -
        weight i * (support U (normal i) - target i) ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ε * (4 * B * (weight i * (|(normal i).1| + |(normal i).2|))) :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = ε * (4 * B * ∑ i, weight i * (|(normal i).1| + |(normal i).2|)) := by
      simp only [Finset.mul_sum]

theorem rightTrim_frozen_barrier_comparison {U : Set Plane} (hU : IsDownwardCap U)
    (normal : ι → Plane) (hnormal : ∀ i, 0 ≤ (normal i).2)
    (corners : List (ι × ι)) (terminal : Option ι)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    intervalSpatialScore (extendedCapRoof U) (finiteBarrier U normal corners terminal)
      (horizontalLeft U) (horizontalRight U - ε) ≤
      finiteSpatialScore (rightTrim U ε) normal corners terminal := by
  have hT := hU.rightTrim hε0 hεW
  unfold finiteSpatialScore
  rw [horizontalLeft_rightTrim hU hε0 hεW, horizontalRight_rightTrim hU hε0 hεW]
  refine intervalSpatialScore_le_of_roof_eq_of_niche_le
    (by unfold capWidth at hεW; linarith) ?_
    (continuous_finiteBarrier U normal corners terminal)
    (continuous_finiteBarrier (rightTrim U ε) normal corners terminal) ?_
  · intro x hx
    rw [capRoof_rightTrim hU hε0 hεW hx]
    apply hU.extendedCapRoof_eq
    exact ⟨hx.1, hx.2.trans (sub_le_self _ hε0)⟩
  · exact finiteBarrier_mono (rightTrim_subset U ε) hT.nonempty hU.isCompact
      normal hnormal corners terminal

theorem leftTrim_frozen_barrier_comparison {U : Set Plane} (hU : IsDownwardCap U)
    (normal : ι → Plane) (hnormal : ∀ i, 0 ≤ (normal i).2)
    (corners : List (ι × ι)) (terminal : Option ι)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    intervalSpatialScore (extendedCapRoof U) (finiteBarrier U normal corners terminal)
      (horizontalLeft U + ε) (horizontalRight U) ≤
      finiteSpatialScore (leftTrim U ε) normal corners terminal := by
  have hT := hU.leftTrim hε0 hεW
  unfold finiteSpatialScore
  rw [horizontalLeft_leftTrim hU hε0 hεW, horizontalRight_leftTrim hU hε0 hεW]
  refine intervalSpatialScore_le_of_roof_eq_of_niche_le
    (by unfold capWidth at hεW; linarith) ?_
    (continuous_finiteBarrier U normal corners terminal)
    (continuous_finiteBarrier (leftTrim U ε) normal corners terminal) ?_
  · intro x hx
    rw [capRoof_leftTrim hU hε0 hεW hx]
    apply hU.extendedCapRoof_eq
    exact ⟨(le_add_of_nonneg_right hε0).trans hx.1, hx.2⟩
  · exact finiteBarrier_mono (leftTrim_subset U ε) hT.nonempty hU.isCompact
      normal hnormal corners terminal

/-- Selected inward right pressure. The comparison domain may be a fixed
box: only competitors contained in the selected cap are used here. -/
theorem selected_right_inward_pressure [Fintype κ] {U : Set Plane} (hU : IsDownwardCap U)
    (hW : 1 ≤ capWidth U) (normal : ι → Plane) (hnormal : ∀ i, 0 ≤ (normal i).2)
    (corners : List (ι × ι)) (terminal : Option ι)
    (penaltyNormal : κ → Plane) (weight target : κ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hweight : ∀ i, 0 ≤ weight i)
    (hpoints : ∀ p ∈ U, ∀ i, |coordDot p (penaltyNormal i)| ≤ B)
    (htarget : ∀ i, |target i| ≤ B)
    (hmax : ∀ V : Set Plane, IsDownwardCap V → V ⊆ U →
      finiteSpatialScore V normal corners terminal - sampledPenalty V penaltyNormal weight target ≤
        finiteSpatialScore U normal corners terminal - sampledPenalty U penaltyNormal weight target) :
    rightEndpointPressure (capRoof U) (finiteBarrier U normal corners terminal)
      (horizontalLeft U) (horizontalRight U) ≤
      capRoof U (horizontalRight U) + supportPenaltyLipschitz B penaltyNormal weight := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hW0 : 0 < capWidth U := zero_lt_one.trans_le hW
  have hroof : EqOn (extendedCapRoof U) (capRoof U)
      (Icc (horizontalLeft U) (horizontalRight U)) := fun _ hx => hU.extendedCapRoof_eq hx
  have hscore : intervalSpatialScore (extendedCapRoof U) (finiteBarrier U normal corners terminal)
      (horizontalLeft U) (horizontalRight U) = finiteSpatialScore U normal corners terminal :=
    intervalSpatialScore_congr_roof hlr hroof
  have hcomparison : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      intervalSpatialScore (extendedCapRoof U) (finiteBarrier U normal corners terminal)
        (horizontalLeft U) (horizontalRight U - ε) ≤
      intervalSpatialScore (extendedCapRoof U) (finiteBarrier U normal corners terminal)
        (horizontalLeft U) (horizontalRight U) + ε * supportPenaltyLipschitz B penaltyNormal weight := by
    have hsmall : Iio (capWidth U) ∈ 𝓝[>] (0 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hW0)
    filter_upwards [hsmall, self_mem_nhdsWithin] with ε hεW hεpos
    have hε0 : 0 ≤ ε := (show 0 < ε from hεpos).le
    have hT := hU.rightTrim hε0 hεW.le
    have hfreeze := rightTrim_frozen_barrier_comparison hU normal hnormal corners terminal hε0 hεW.le
    have hselected := hmax (rightTrim U ε) hT (rightTrim_subset U ε)
    have hpenalty := (le_abs_self _).trans
      (abs_sampledPenalty_sub_le_of_support_control hU hT (rightTrim_subset U ε)
        penaltyNormal weight target hB hweight hpoints htarget
        (fun i => abs_support_rightTrim_sub_le hU hW hε0 hεW.le (penaltyNormal i)))
    rw [hscore]
    linarith
  have hpressure := rightEndpointPressure_le_of_inward_comparison
    hU.continuous_extendedCapRoof (continuous_finiteBarrier U normal corners terminal)
    (horizontalLeft U) (horizontalRight U) (supportPenaltyLipschitz B penaltyNormal weight) hcomparison
  rw [rightEndpointPressure_congr_roof hlr hroof,
    hU.extendedCapRoof_eq ⟨hlr, le_rfl⟩] at hpressure
  exact hpressure

theorem selected_left_inward_pressure [Fintype κ] {U : Set Plane} (hU : IsDownwardCap U)
    (hW : 1 ≤ capWidth U) (normal : ι → Plane) (hnormal : ∀ i, 0 ≤ (normal i).2)
    (corners : List (ι × ι)) (terminal : Option ι)
    (penaltyNormal : κ → Plane) (weight target : κ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hweight : ∀ i, 0 ≤ weight i)
    (hpoints : ∀ p ∈ U, ∀ i, |coordDot p (penaltyNormal i)| ≤ B)
    (htarget : ∀ i, |target i| ≤ B)
    (hmax : ∀ V : Set Plane, IsDownwardCap V → V ⊆ U →
      finiteSpatialScore V normal corners terminal - sampledPenalty V penaltyNormal weight target ≤
        finiteSpatialScore U normal corners terminal - sampledPenalty U penaltyNormal weight target) :
    leftEndpointPressure (capRoof U) (finiteBarrier U normal corners terminal)
      (horizontalLeft U) (horizontalRight U) ≤
      capRoof U (horizontalLeft U) + supportPenaltyLipschitz B penaltyNormal weight := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hW0 : 0 < capWidth U := zero_lt_one.trans_le hW
  have hroof : EqOn (extendedCapRoof U) (capRoof U)
      (Icc (horizontalLeft U) (horizontalRight U)) := fun _ hx => hU.extendedCapRoof_eq hx
  have hscore : intervalSpatialScore (extendedCapRoof U) (finiteBarrier U normal corners terminal)
      (horizontalLeft U) (horizontalRight U) = finiteSpatialScore U normal corners terminal :=
    intervalSpatialScore_congr_roof hlr hroof
  have hcomparison : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      intervalSpatialScore (extendedCapRoof U) (finiteBarrier U normal corners terminal)
        (horizontalLeft U + ε) (horizontalRight U) ≤
      intervalSpatialScore (extendedCapRoof U) (finiteBarrier U normal corners terminal)
        (horizontalLeft U) (horizontalRight U) + ε * supportPenaltyLipschitz B penaltyNormal weight := by
    have hsmall : Iio (capWidth U) ∈ 𝓝[>] (0 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hW0)
    filter_upwards [hsmall, self_mem_nhdsWithin] with ε hεW hεpos
    have hε0 : 0 ≤ ε := (show 0 < ε from hεpos).le
    have hT := hU.leftTrim hε0 hεW.le
    have hfreeze := leftTrim_frozen_barrier_comparison hU normal hnormal corners terminal hε0 hεW.le
    have hselected := hmax (leftTrim U ε) hT (leftTrim_subset U ε)
    have hpenalty := (le_abs_self _).trans
      (abs_sampledPenalty_sub_le_of_support_control hU hT (leftTrim_subset U ε)
        penaltyNormal weight target hB hweight hpoints htarget
        (fun i => abs_support_leftTrim_sub_le hU hW hε0 hεW.le (penaltyNormal i)))
    rw [hscore]
    linarith
  have hpressure := leftEndpointPressure_le_of_inward_comparison
    hU.continuous_extendedCapRoof (continuous_finiteBarrier U normal corners terminal)
    (horizontalLeft U) (horizontalRight U) (supportPenaltyLipschitz B penaltyNormal weight) hcomparison
  rw [leftEndpointPressure_congr_roof hlr hroof,
    hU.extendedCapRoof_eq ⟨le_rfl, hlr⟩] at hpressure
  exact hpressure

end FinitePolygon

theorem IsDownwardCap.continuous_partialBarrier_pi_div_two {U : Set Plane}
    (hU : IsDownwardCap U) : Continuous (partialBarrier U (Real.pi / 2)) := by
  have heq : partialBarrier U (Real.pi / 2) =
      fun x => sweptNiche hU.toCompactCap.carrier (Real.pi / 2) x :=
    funext (fun x => hU.partialBarrier_pi_div_two x)
  rw [heq]
  have hcomp := continuous_capSweptNiche.comp
    (show Continuous (fun x : ℝ => (hU.toCompactCap, x)) from
      continuous_const.prodMk continuous_id)
  exact hcomp

end AmbidextrousSofa
