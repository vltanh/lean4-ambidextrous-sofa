module

public import AmbidextrousSofa.Analysis.ExposureMoments

@[expose] public section

/-!
# Source moments of literal horizontal erosions

The right and left moments use the actual finite selected-source masses.
Their velocities are the positive horizontal normal components appearing
in the exact set identities for horizontal erosion. The displayed eroded
halfplanes need not be attained: their barrier is an upper bound on the
actual eroded barrier, which gives the correct comparison direction.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem WallExpr.eval_mono {ι : Type*} (e : WallExpr ι) {v w : ι → ℝ}
    (h : ∀ i, v i ≤ w i) : e.eval v ≤ e.eval w := by
  induction e with
  | leaf i => exact h i
  | minimum e f he hf => exact min_le_min he hf
  | maximum e f he hf => exact max_le_max he hf

namespace FinitePolygon

variable {ι κ : Type*}

def heightVelocity (normal : ι → Plane) (z : ι → ℝ) : Option ι → ℝ
  | none => 0
  | some i => z i / (normal i).2

def rightErosionVelocity (normal : ι → Plane) : Option ι → ℝ :=
  heightVelocity normal (fun i => -max (normal i).1 0)

def leftErosionVelocity (normal : ι → Plane) : Option ι → ℝ :=
  heightVelocity normal (fun i => -max (-(normal i).1) 0)

theorem affineEnvelope_roof_height [Fintype ι] (normal : ι → Plane)
    (height z : ι → ℝ) (ε : ℝ) :
    (roofExpr (ι := ι)).affineEnvelope (wallSlope normal) (roofIntercept normal height)
        (heightVelocity normal z) ε =
      roofEnvelope normal (fun i => height i + ε * z i) := by
  funext x
  unfold WallExpr.affineEnvelope roofEnvelope
  congr 1
  ext (_ | i) <;> simp only [heightVelocity, roofIntercept, wallSlope] <;> ring

theorem affineEnvelope_barrier_height (normal : ι → Plane) (height z : ι → ℝ)
    (corners : List (ι × ι)) (terminal : Option ι) (ε : ℝ) :
    (barrierExpr corners terminal).affineEnvelope (wallSlope normal)
        (barrierIntercept normal height) (heightVelocity normal z) ε =
      fun x => (barrierExpr corners terminal).eval
        (fun i => wallSlope normal i * x +
          barrierIntercept normal (fun j => height j + ε * z j) i) := by
  funext x
  unfold WallExpr.affineEnvelope
  congr 1
  ext (_ | i) <;> simp only [heightVelocity, barrierIntercept, wallSlope] <;> ring

theorem affineEnvelope_roof_zero [Fintype ι] (normal : ι → Plane)
    (height : ι → ℝ) (w : Option ι → ℝ) :
    (roofExpr (ι := ι)).affineEnvelope (wallSlope normal) (roofIntercept normal height) w 0 =
      roofEnvelope normal height := by
  funext x
  simp only [WallExpr.affineEnvelope, roofEnvelope, zero_mul, add_zero]

theorem affineEnvelope_barrier_zero (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) (w : Option ι → ℝ) :
    (barrierExpr corners terminal).affineEnvelope (wallSlope normal)
        (barrierIntercept normal (fun i => support U (normal i))) w 0 =
      finiteBarrier U normal corners terminal := by
  funext x
  rw [finiteBarrier_eq_eval normal _ (fun _ => rfl)]
  simp only [WallExpr.affineEnvelope, zero_mul, add_zero]

theorem eqOn_roofEnvelope_of_circumscription [Fintype ι] {U : Set Plane}
    (hU : IsDownwardCap U) (normal : ι → Plane) (hnormal : ∀ i, 0 < (normal i).2)
    (hpoly : U = circumscription U normal) :
    EqOn (roofEnvelope normal (fun i => support U (normal i))) (capRoof U)
      (Icc (horizontalLeft U) (horizontalRight U)) := fun _ hx =>
  ((congrArg (capRoof · _) hpoly).trans
    (capRoof_upperPolygon _ _ normal _ hnormal (circumscription_baseline hU normal) hx)).symm

/-- A non-tight displayed polygon has the same roof as its actual body,
while its displayed inner walls can only overestimate the true barrier. -/
theorem displayedSpatialScore_le_actual [Fintype ι] {U : Set Plane}
    (hU : IsDownwardCap U) (normal : ι → Plane) (height : ι → ℝ)
    (hnormal : ∀ i, 0 < (normal i).2) {l r : ℝ}
    (hleft : horizontalLeft U = l) (hright : horizontalRight U = r)
    (hpoly : U = upperPolygon l r normal height)
    (corners : List (ι × ι)) (terminal : Option ι) :
    intervalSpatialScore (roofEnvelope normal height)
      (fun x => (barrierExpr corners terminal).eval
        (fun i => wallSlope normal i * x + barrierIntercept normal height i)) l r ≤
      finiteSpatialScore U normal corners terminal := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hproj := horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex
  rw [hleft, hright] at hlr hproj
  have hmem {p : Plane} (hp : p ∈ U) i : coordDot p (normal i) ≤ height i := by
    rw [hpoly] at hp; exact ((mem_upperPolygon_iff _ _ _ _ _).mp hp).2.2 i
  unfold finiteSpatialScore
  rw [hleft, hright]
  refine intervalSpatialScore_le_of_roof_eq_of_niche_le hlr (fun x hx => ?_)
    ((barrierExpr corners terminal).continuous_eval fun _ => by fun_prop)
    (continuous_finiteBarrier U normal corners terminal) fun x => ?_
  · rw [hpoly, capRoof_upperPolygon l r normal height hnormal
      (fun x hx => hmem (hU.baseline_mem_of_mem_projection (hproj ▸ hx))) hx]
  · rw [finiteBarrier_eq_eval normal _ (fun _ => rfl)]
    refine WallExpr.eval_mono _ fun i => ?_
    rcases i with _ | i
    · exact le_rfl
    · exact add_le_add_right (div_le_div_of_nonneg_right (sub_le_sub_right
        (support_le_of_forall hU.nonempty fun p hp => hmem hp i) 1) (hnormal i).le) _

def finiteRightMoment [Fintype ι] (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) : ℝ :=
  finiteSourceVariation (roofExpr (ι := ι)) (barrierExpr corners terminal)
    (wallSlope normal) (roofIntercept normal (fun i => support U (normal i)))
    (wallSlope normal) (barrierIntercept normal (fun i => support U (normal i)))
    (horizontalLeft U) (horizontalRight U)
    (rightErosionVelocity normal) (rightErosionVelocity normal)

def finiteLeftMoment [Fintype ι] (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) : ℝ :=
  finiteSourceVariation (roofExpr (ι := ι)) (barrierExpr corners terminal)
    (wallSlope normal) (roofIntercept normal (fun i => support U (normal i)))
    (wallSlope normal) (barrierIntercept normal (fun i => support U (normal i)))
    (horizontalLeft U) (horizontalRight U)
    (leftErosionVelocity normal) (leftErosionVelocity normal)

/-- Both erosion moments at once: a displayed polygon of `U` whose endpoints move with
velocities `lD`, `rD` and whose heights move with velocities `z` is dominated by an actual
contained competitor `E ε`, so at a selected maximum the derivative of its score is at most the
penalty Lipschitz constant. -/
theorem selected_erosion_moment [Fintype ι] [Fintype κ] {U : Set Plane}
    (hU : IsDownwardCap U) (hW : 1 ≤ capWidth U)
    (normal : ι → Plane) (hnormal : ∀ i, 0 < (normal i).2)
    (hslope : Function.Injective (wallSlope normal)) (hpoly : U = circumscription U normal)
    (corners : List (ι × ι)) (terminal : Option ι)
    (penaltyNormal : κ → Plane) (weight target : κ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hweight : ∀ i, 0 ≤ weight i)
    (hpoints : ∀ p ∈ U, ∀ i, |coordDot p (penaltyNormal i)| ≤ B)
    (htarget : ∀ i, |target i| ≤ B)
    (hmax : ∀ V : Set Plane, IsDownwardCap V → V ⊆ U →
      finiteSpatialScore V normal corners terminal - sampledPenalty V penaltyNormal weight target ≤
        finiteSpatialScore U normal corners terminal - sampledPenalty U penaltyNormal weight target)
    (E : ℝ → Set Plane) (lD rD : ℝ) (z : ι → ℝ)
    (hE : ∀ ε, 0 ≤ ε → ε ≤ capWidth U → IsDownwardCap (E ε) ∧ E ε ⊆ U ∧
      (∀ v, |support (E ε) v - support U v| ≤ ε * (|v.1| + |v.2|)) ∧
      horizontalLeft (E ε) = horizontalLeft U + ε * lD ∧
      horizontalRight (E ε) = horizontalRight U + ε * rD ∧
      E ε = upperPolygon (horizontalLeft U + ε * lD) (horizontalRight U + ε * rD) normal
        fun i => support U (normal i) + ε * z i) :
    finiteSourceVariation (roofExpr (ι := ι)) (barrierExpr corners terminal)
        (wallSlope normal) (roofIntercept normal (fun i => support U (normal i)))
        (wallSlope normal) (barrierIntercept normal (fun i => support U (normal i)))
        (horizontalLeft U) (horizontalRight U) (heightVelocity normal z)
        (heightVelocity normal z) +
      capRoof U (horizontalRight U) * rD - capRoof U (horizontalLeft U) * lD -
      rD * rightEndpointPressure (capRoof U) (finiteBarrier U normal corners terminal)
        (horizontalLeft U) (horizontalRight U) +
      lD * leftEndpointPressure (capRoof U) (finiteBarrier U normal corners terminal)
        (horizontalLeft U) (horizontalRight U) ≤
      supportPenaltyLipschitz B penaltyNormal weight := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hroof := eqOn_roofEnvelope_of_circumscription hU normal hnormal hpoly
  have hderiv := hasDerivAt_finite_intervalSpatialScore_moving (roofExpr (ι := ι))
    (barrierExpr corners terminal) _ (roofIntercept normal fun i => support U (normal i))
    (heightVelocity normal z) _ (barrierIntercept normal fun i => support U (normal i))
    (heightVelocity normal z) hslope hslope (horizontalLeft U) (horizontalRight U) lD rD
  refine sub_nonpos.mp (hasDerivAt_nonpos_of_right_max ((hderiv.congr_deriv ?_).sub
    (hasDerivAt_mul_const (supportPenaltyLipschitz B penaltyNormal weight))) ?_)
  · rw [affineEnvelope_roof_zero, affineEnvelope_barrier_zero,
      finiteSourceVariation_eq_integrals _ _ _ _ _ _ _ _ hlr, ← hroof ⟨hlr, le_rfl⟩,
      ← hroof ⟨le_rfl, hlr⟩, ← rightEndpointPressure_congr_roof hlr hroof,
      ← leftEndpointPressure_congr_roof hlr hroof, rightEndpointPressure, leftEndpointPressure]
    ring
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (zero_lt_one.trans_le hW)),
    self_mem_nhdsWithin] with ε hεW (hε : 0 < ε)
  obtain ⟨hcap, hsub, hsupport, hleft, hright, hset⟩ := hE ε hε.le hεW.le
  have hcomparison := displayedSpatialScore_le_actual hcap normal _ hnormal hleft hright hset
    corners terminal
  rw [← affineEnvelope_roof_height, ← affineEnvelope_barrier_height] at hcomparison
  have := (le_abs_self _).trans (abs_sampledPenalty_sub_le_of_support_control hU hcap hsub
    penaltyNormal weight target hB hweight hpoints htarget fun i => hsupport _)
  simp only [Pi.sub_apply, affineEnvelope_roof_zero, affineEnvelope_barrier_zero, zero_mul,
    add_zero, sub_zero]
  rw [intervalSpatialScore_congr_roof hlr hroof]
  unfold finiteSpatialScore at hcomparison hmax
  linarith [hmax _ hcap hsub]

/-- A selected polygon only uses contained competitors here, so the same
theorem applies inside the artificial compact box used for selection. -/
theorem selected_right_erosion_moment [Fintype ι] [Fintype κ] {U : Set Plane}
    (hU : IsDownwardCap U) (hW : 1 ≤ capWidth U)
    (normal : ι → Plane) (hnormal : ∀ i, 0 < (normal i).2)
    (hslope : Function.Injective (wallSlope normal)) (hpoly : U = circumscription U normal)
    (corners : List (ι × ι)) (terminal : Option ι)
    (penaltyNormal : κ → Plane) (weight target : κ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hweight : ∀ i, 0 ≤ weight i)
    (hpoints : ∀ p ∈ U, ∀ i, |coordDot p (penaltyNormal i)| ≤ B)
    (htarget : ∀ i, |target i| ≤ B)
    (hmax : ∀ V : Set Plane, IsDownwardCap V → V ⊆ U →
      finiteSpatialScore V normal corners terminal - sampledPenalty V penaltyNormal weight target ≤
        finiteSpatialScore U normal corners terminal - sampledPenalty U penaltyNormal weight target) :
    finiteRightMoment U normal corners terminal ≤
      capRoof U (horizontalRight U) -
        rightEndpointPressure (capRoof U) (finiteBarrier U normal corners terminal)
          (horizontalLeft U) (horizontalRight U) + supportPenaltyLipschitz B penaltyNormal weight := by
  have := selected_erosion_moment hU hW normal hnormal hslope hpoly corners terminal
    penaltyNormal weight target hB hweight hpoints htarget hmax (rightErosion U) 0 (-1)
    (fun i => -max (normal i).1 0) fun ε h0 hε => ⟨hU.rightErosion h0 hε,
      rightErosion_subset U ε, abs_support_rightErosion_sub_le hU hW h0 hε,
      by rw [horizontalLeft_rightErosion hU h0 hε]; ring,
      by rw [horizontalRight_rightErosion hU h0 hε]; ring, by
        simpa only [mul_zero, add_zero, mul_neg, mul_one, ← sub_eq_add_neg] using
          (congrArg (rightErosion · ε) hpoly).trans (rightErosion_upperPolygon normal _ h0)⟩
  rw [finiteRightMoment, rightErosionVelocity]
  linarith

theorem selected_left_erosion_moment [Fintype ι] [Fintype κ] {U : Set Plane}
    (hU : IsDownwardCap U) (hW : 1 ≤ capWidth U)
    (normal : ι → Plane) (hnormal : ∀ i, 0 < (normal i).2)
    (hslope : Function.Injective (wallSlope normal)) (hpoly : U = circumscription U normal)
    (corners : List (ι × ι)) (terminal : Option ι)
    (penaltyNormal : κ → Plane) (weight target : κ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hweight : ∀ i, 0 ≤ weight i)
    (hpoints : ∀ p ∈ U, ∀ i, |coordDot p (penaltyNormal i)| ≤ B)
    (htarget : ∀ i, |target i| ≤ B)
    (hmax : ∀ V : Set Plane, IsDownwardCap V → V ⊆ U →
      finiteSpatialScore V normal corners terminal - sampledPenalty V penaltyNormal weight target ≤
        finiteSpatialScore U normal corners terminal - sampledPenalty U penaltyNormal weight target) :
    finiteLeftMoment U normal corners terminal ≤
      capRoof U (horizontalLeft U) -
        leftEndpointPressure (capRoof U) (finiteBarrier U normal corners terminal)
          (horizontalLeft U) (horizontalRight U) + supportPenaltyLipschitz B penaltyNormal weight := by
  have := selected_erosion_moment hU hW normal hnormal hslope hpoly corners terminal
    penaltyNormal weight target hB hweight hpoints htarget hmax (leftErosion U) 1 0
    (fun i => -max (-(normal i).1) 0) fun ε h0 hε => ⟨hU.leftErosion h0 hε,
      leftErosion_subset U ε, abs_support_leftErosion_sub_le hU hW h0 hε,
      by rw [horizontalLeft_leftErosion hU h0 hε]; ring,
      by rw [horizontalRight_leftErosion hU h0 hε]; ring, by
        simpa only [mul_zero, add_zero, mul_neg, mul_one, ← sub_eq_add_neg] using
          (congrArg (leftErosion · ε) hpoly).trans (leftErosion_upperPolygon normal _ h0)⟩
  rw [finiteLeftMoment, leftErosionVelocity]
  linarith

/-- Central horizontal source length minus both charged exterior source
lengths, at the same supporting normal. -/
def finiteExposureDefect [Fintype ι] (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) (i : ι) : ℝ :=
  (barrierExpr corners terminal).sourceMass (wallSlope normal)
    (barrierIntercept normal (fun j => support U (normal j)))
    (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)
    (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) (some i) -
  (roofExpr (ι := ι)).sourceMass (wallSlope normal)
    (roofIntercept normal (fun j => support U (normal j)))
    (horizontalLeft U)
    (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) (some i) -
  (roofExpr (ι := ι)).sourceMass (wallSlope normal)
    (roofIntercept normal (fun j => support U (normal j)))
    (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)
    (horizontalRight U) (some i)

theorem finiteRightMoment_eq_sum [Fintype ι] (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) :
    finiteRightMoment U normal corners terminal =
      ∑ i, finiteExposureDefect U normal corners terminal i *
        (max (normal i).1 0 / (normal i).2) := by
  simp only [finiteRightMoment, finiteSourceVariation, Fintype.sum_option, rightErosionVelocity,
    heightVelocity, mul_zero, zero_add, ← Finset.sum_sub_distrib, finiteExposureDefect]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem finiteLeftMoment_eq_sum [Fintype ι] (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) :
    finiteLeftMoment U normal corners terminal =
      ∑ i, finiteExposureDefect U normal corners terminal i *
        (max (-(normal i).1) 0 / (normal i).2) := by
  simp only [finiteLeftMoment, finiteSourceVariation, Fintype.sum_option, leftErosionVelocity,
    heightVelocity, mul_zero, zero_add, ← Finset.sum_sub_distrib, finiteExposureDefect]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Translation is the difference of the two erosion velocities. Its
zero total score derivative identifies the signed moment balance with
actual endpoint heights and actual finite-barrier pressures. -/
theorem finite_erosion_moment_balance [Fintype ι] {U : Set Plane}
    (hU : IsDownwardCap U) (normal : ι → Plane) (hnormal : ∀ i, 0 < (normal i).2)
    (hslope : Function.Injective (wallSlope normal)) (hpoly : U = circumscription U normal)
    (corners : List (ι × ι)) (terminal : Option ι) :
    finiteRightMoment U normal corners terminal - finiteLeftMoment U normal corners terminal =
      (capRoof U (horizontalRight U) -
        rightEndpointPressure (capRoof U) (finiteBarrier U normal corners terminal)
          (horizontalLeft U) (horizontalRight U)) -
      (capRoof U (horizontalLeft U) -
        leftEndpointPressure (capRoof U) (finiteBarrier U normal corners terminal)
          (horizontalLeft U) (horizontalRight U)) := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hroof := eqOn_roofEnvelope_of_circumscription hU normal hnormal hpoly
  have h := finiteSourceVariation_translation (roofExpr (ι := ι)) (barrierExpr corners terminal)
    (wallSlope normal) (roofIntercept normal (fun i => support U (normal i)))
    (wallSlope normal) (barrierIntercept normal (fun i => support U (normal i))) hslope hslope hlr
  rw [affineEnvelope_roof_zero, affineEnvelope_barrier_zero,
    rightEndpointPressure_congr_roof hlr hroof, leftEndpointPressure_congr_roof hlr hroof,
    hroof ⟨le_rfl, hlr⟩, hroof ⟨hlr, le_rfl⟩, finiteSourceVariation_neg] at h
  have hvel : rightErosionVelocity normal = fun i => leftErosionVelocity normal i +
      wallSlope normal i := by
    ext (_ | i)
    · simp [rightErosionVelocity, leftErosionVelocity, heightVelocity, wallSlope]
    · simp only [rightErosionVelocity, leftErosionVelocity, heightVelocity, wallSlope, ← add_div]
      congr 1
      linarith [max_zero_sub_max_neg_zero_eq_self (normal i).1]
  rw [finiteRightMoment, hvel, finiteSourceVariation_add, finiteLeftMoment]
  linarith

end FinitePolygon

end AmbidextrousSofa
