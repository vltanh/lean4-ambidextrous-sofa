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

theorem extendedCapRoof_eqOn (U : Set Plane) :
    EqOn (extendedCapRoof U) (capRoof U) (Icc (horizontalLeft U) (horizontalRight U)) :=
  fun _ hx => by rw [extendedCapRoof, min_eq_right hx.2, max_eq_right hx.1]

theorem IsDownwardCap.continuous_extendedCapRoof {U : Set Plane} (hU : IsDownwardCap U) :
    Continuous (extendedCapRoof U) :=
  hU.continuousOn_capRoof_Icc.comp_continuous (by fun_prop) fun _ => ⟨le_max_left _ _,
    max_le (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact) (min_le_left _ _)⟩

def rightEndpointPressure (roof niche : ℝ → ℝ) (l r : ℝ) : ℝ :=
  (3 * (roof (r - (r - l) / 4) + niche (r - (r - l) / 4)) -
    (roof (l + (r - l) / 4) + niche (l + (r - l) / 4))) / 4

def leftEndpointPressure (roof niche : ℝ → ℝ) (l r : ℝ) : ℝ :=
  (3 * (roof (l + (r - l) / 4) + niche (l + (r - l) / 4)) -
    (roof (r - (r - l) / 4) + niche (r - (r - l) / 4))) / 4

theorem rightEndpointPressure_congr_roof {roof roof' niche : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r) (hroof : EqOn roof roof' (Icc l r)) :
    rightEndpointPressure roof niche l r = rightEndpointPressure roof' niche l r := by
  unfold rightEndpointPressure
  rw [hroof ⟨_, _⟩, hroof ⟨_, _⟩] <;> linarith

theorem leftEndpointPressure_congr_roof {roof roof' niche : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r) (hroof : EqOn roof roof' (Icc l r)) :
    leftEndpointPressure roof niche l r = leftEndpointPressure roof' niche l r := by
  unfold leftEndpointPressure
  rw [hroof ⟨_, _⟩, hroof ⟨_, _⟩] <;> linarith

theorem rightEndpointPressure_le_of_inward_comparison {roof niche : ℝ → ℝ}
    (hroof : Continuous roof) (hniche : Continuous niche) (l r K : ℝ)
    (hcomparison : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      intervalSpatialScore roof niche l (r - ε) ≤ intervalSpatialScore roof niche l r + ε * K) :
    rightEndpointPressure roof niche l r ≤ roof r + K := by
  have := hasDerivAt_nonpos_of_right_max ((hasDerivAt_intervalSpatialScore_endpoints hroof
    hniche l r 0 (-1)).sub ((hasDerivAt_id' (0 : ℝ)).mul_const K)) (by
      filter_upwards [hcomparison] with ε hε
      simp only [Pi.sub_apply, mul_zero, zero_mul, add_zero, sub_zero, mul_neg_one,
        ← sub_eq_add_neg]
      linarith)
  unfold rightEndpointPressure
  linarith

theorem leftEndpointPressure_le_of_inward_comparison {roof niche : ℝ → ℝ}
    (hroof : Continuous roof) (hniche : Continuous niche) (l r K : ℝ)
    (hcomparison : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      intervalSpatialScore roof niche (l + ε) r ≤ intervalSpatialScore roof niche l r + ε * K) :
    leftEndpointPressure roof niche l r ≤ roof l + K := by
  have := hasDerivAt_nonpos_of_right_max ((hasDerivAt_intervalSpatialScore_endpoints hroof
    hniche l r 1 0).sub ((hasDerivAt_id' (0 : ℝ)).mul_const K)) (by
      filter_upwards [hcomparison] with ε hε
      simp only [Pi.sub_apply, mul_zero, zero_mul, add_zero, sub_zero, mul_one]
      linarith)
  unfold leftEndpointPressure
  linarith

/-- The two outer integrals agree; only the sign of the middle integral
changes. Both niches are actual integrable functions on the same window. -/
theorem intervalSpatialScore_le_of_roof_eq_of_niche_le
    {roof roof' niche niche' : ℝ → ℝ} {l r : ℝ} (hlr : l ≤ r)
    (hroof : EqOn roof roof' (Icc l r))
    (hniche : Continuous niche) (hniche' : Continuous niche') (hle : ∀ x, niche' x ≤ niche x) :
    intervalSpatialScore roof niche l r ≤ intervalSpatialScore roof' niche' l r := by
  rw [FinitePolygon.intervalSpatialScore_congr_roof hlr hroof]
  exact sub_le_sub_left (intervalIntegral.integral_mono (by linarith)
    (hniche'.intervalIntegrable _ _) (hniche.intervalIntegrable _ _) hle) _

theorem abs_sq_sub_sq_le_of_abs_le {s t z B : ℝ}
    (hs : |s| ≤ B) (ht : |t| ≤ B) (hz : |z| ≤ B) :
    |(s - z) ^ 2 - (t - z) ^ 2| ≤ 4 * B * |s - t| := by
  rw [show (s - z) ^ 2 - (t - z) ^ 2 = (s + t - 2 * z) * (s - t) by ring, abs_mul]
  refine mul_le_mul_of_nonneg_right (abs_le.mpr ⟨?_, ?_⟩) (abs_nonneg _) <;>
    linarith [abs_le.mp hs, abs_le.mp ht, abs_le.mp hz]

theorem abs_support_le_of_pointwise_bound {U : Set Plane} (hU : IsDownwardCap U)
    (v : Plane) {B : ℝ} (hB : ∀ p ∈ U, |coordDot p v| ≤ B) : |support U v| ≤ B := by
  obtain ⟨p, hp, hsupport⟩ := exists_coordDot_eq_support hU.isCompact hU.nonempty v
  exact hsupport ▸ hB p hp

namespace FinitePolygon

variable {ι κ : Type*}

theorem supportWall_mono {U V : Set Plane} (hUV : U ⊆ V) (hne : U.Nonempty)
    (hV : IsCompact V) {n : Plane} (hn : 0 ≤ n.2) (x : ℝ) :
    supportWall U n x ≤ supportWall V n x :=
  div_le_div_of_nonneg_right (by linarith [support_mono hUV hne hV n]) hn

theorem finiteBarrier_mono {U V : Set Plane} (hUV : U ⊆ V) (hne : U.Nonempty)
    (hV : IsCompact V) (normal : ι → Plane) (hnormal : ∀ i, 0 ≤ (normal i).2)
    (corners : List (ι × ι)) (terminal : Option ι) (x : ℝ) :
    finiteBarrier U normal corners terminal x ≤ finiteBarrier V normal corners terminal x := by
  have hniche : finiteNiche U normal corners x ≤ finiteNiche V normal corners x := by
    induction corners with
    | nil => exact le_rfl
    | cons ij rest ih =>
      exact max_le_max (min_le_min (supportWall_mono hUV hne hV (hnormal ij.1) x)
        (supportWall_mono hUV hne hV (hnormal ij.2) x)) ih
  cases terminal with
  | none => exact hniche
  | some i => exact max_le_max hniche (supportWall_mono hUV hne hV (hnormal i) x)

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
  unfold sampledPenalty heightPenalty supportPenaltyLipschitz
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (hweight i)]
  have hsquare := abs_sq_sub_sq_le_of_abs_le
    (abs_support_le_of_pointwise_bound hV (normal i) fun p hp => hpoints p (hVU hp) i)
    (abs_support_le_of_pointwise_bound hU (normal i) fun p hp => hpoints p hp i) (htarget i)
  exact (mul_le_mul_of_nonneg_left (hsquare.trans (mul_le_mul_of_nonneg_left (hchange i)
    (mul_nonneg (by norm_num) hB))) (hweight i)).trans_eq (by ring)

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
  have hroof := extendedCapRoof_eqOn U
  rw [← rightEndpointPressure_congr_roof hlr hroof, ← hroof ⟨hlr, le_rfl⟩]
  refine rightEndpointPressure_le_of_inward_comparison hU.continuous_extendedCapRoof
    (continuous_finiteBarrier U normal corners terminal) _ _ _ ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one.trans_le hW)] with ε ⟨hε0, hεW⟩
  have hT := hU.rightTrim hε0.le hεW.le
  have hfreeze : intervalSpatialScore (extendedCapRoof U) (finiteBarrier U normal corners terminal)
      (horizontalLeft U) (horizontalRight U - ε) ≤
      finiteSpatialScore (rightTrim U ε) normal corners terminal := by
    unfold finiteSpatialScore
    rw [horizontalLeft_rightTrim hU hε0.le hεW.le, horizontalRight_rightTrim hU hε0.le hεW.le]
    exact intervalSpatialScore_le_of_roof_eq_of_niche_le (by unfold capWidth at hεW; linarith)
      (fun x hx => by rw [capRoof_rightTrim hU hε0.le hεW.le hx,
        hroof ⟨hx.1, hx.2.trans (sub_le_self _ hε0.le)⟩])
      (continuous_finiteBarrier U normal corners terminal)
      (continuous_finiteBarrier (rightTrim U ε) normal corners terminal)
      (finiteBarrier_mono (rightTrim_subset U ε) hT.nonempty hU.isCompact normal hnormal
        corners terminal)
  have := hmax (rightTrim U ε) hT (rightTrim_subset U ε)
  have := (le_abs_self _).trans (abs_sampledPenalty_sub_le_of_support_control hU hT
    (rightTrim_subset U ε) penaltyNormal weight target hB hweight hpoints htarget
    fun i => abs_support_rightTrim_sub_le hU hW hε0.le hεW.le (penaltyNormal i))
  rw [intervalSpatialScore_congr_roof hlr hroof]
  unfold finiteSpatialScore at *
  linarith

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
  have hroof := extendedCapRoof_eqOn U
  rw [← leftEndpointPressure_congr_roof hlr hroof, ← hroof ⟨le_rfl, hlr⟩]
  refine leftEndpointPressure_le_of_inward_comparison hU.continuous_extendedCapRoof
    (continuous_finiteBarrier U normal corners terminal) _ _ _ ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one.trans_le hW)] with ε ⟨hε0, hεW⟩
  have hT := hU.leftTrim hε0.le hεW.le
  have hfreeze : intervalSpatialScore (extendedCapRoof U) (finiteBarrier U normal corners terminal)
      (horizontalLeft U + ε) (horizontalRight U) ≤
      finiteSpatialScore (leftTrim U ε) normal corners terminal := by
    unfold finiteSpatialScore
    rw [horizontalLeft_leftTrim hU hε0.le hεW.le, horizontalRight_leftTrim hU hε0.le hεW.le]
    exact intervalSpatialScore_le_of_roof_eq_of_niche_le (by unfold capWidth at hεW; linarith)
      (fun x hx => by rw [capRoof_leftTrim hU hε0.le hεW.le hx,
        hroof ⟨(le_add_of_nonneg_right hε0.le).trans hx.1, hx.2⟩])
      (continuous_finiteBarrier U normal corners terminal)
      (continuous_finiteBarrier (leftTrim U ε) normal corners terminal)
      (finiteBarrier_mono (leftTrim_subset U ε) hT.nonempty hU.isCompact normal hnormal
        corners terminal)
  have := hmax (leftTrim U ε) hT (leftTrim_subset U ε)
  have := (le_abs_self _).trans (abs_sampledPenalty_sub_le_of_support_control hU hT
    (leftTrim_subset U ε) penaltyNormal weight target hB hweight hpoints htarget
    fun i => abs_support_leftTrim_sub_le hU hW hε0.le hεW.le (penaltyNormal i))
  rw [intervalSpatialScore_congr_roof hlr hroof]
  unfold finiteSpatialScore at *
  linarith

end FinitePolygon

theorem IsDownwardCap.continuous_partialBarrier_pi_div_two {U : Set Plane}
    (hU : IsDownwardCap U) : Continuous (partialBarrier U (Real.pi / 2)) :=
  (continuous_capSweptNiche.comp (continuous_const.prodMk continuous_id :
    Continuous fun x : ℝ => (hU.toCompactCap, x))).congr
      fun x => (hU.partialBarrier_pi_div_two x).symm

end AmbidextrousSofa
