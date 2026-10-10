import AmbidextrousSofa.Analysis.ExposureMoments

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

theorem finiteSourceVariation_sub {ι κ : Type*} [Fintype ι] [Fintype κ]
    (outer : WallExpr ι) (inner : WallExpr κ) (a b : ι → ℝ) (c d : κ → ℝ)
    (l r : ℝ) (w w' : ι → ℝ) (v v' : κ → ℝ) :
    finiteSourceVariation outer inner a b c d l r (fun i => w i - w' i)
        (fun j => v j - v' j) =
      finiteSourceVariation outer inner a b c d l r w v -
        finiteSourceVariation outer inner a b c d l r w' v' := by
  unfold finiteSourceVariation
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

theorem hasDerivAt_le_of_right_linear_bound {f : ℝ → ℝ} {d K : ℝ}
    (hf : HasDerivAt f d 0)
    (hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε ≤ f 0 + ε * K) : d ≤ K := by
  have hlinear : HasDerivAt (fun ε : ℝ => ε * K) K 0 := by
    simpa only [one_mul] using (hasDerivAt_id (0 : ℝ)).mul_const K
  have hmax : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε - ε * K ≤ f 0 - 0 * K := by
    filter_upwards [hbound] with ε hε
    simp only [zero_mul, sub_zero]
    linarith
  have h := hasDerivAt_nonpos_of_right_max (hf.sub hlinear) hmax
  linarith

theorem hasDerivAt_finiteSourceScore_inward_right
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (outer : WallExpr ι) (inner : WallExpr κ) (a b w : ι → ℝ) (c d v : κ → ℝ)
    (ha : Function.Injective a) (hc : Function.Injective c) {l r : ℝ} (hlr : l ≤ r) :
    HasDerivAt (fun ε => intervalSpatialScore
      (outer.affineEnvelope a b w ε) (inner.affineEnvelope c d v ε) l (r - ε))
      (finiteSourceVariation outer inner a b c d l r w v +
        rightEndpointPressure (outer.affineEnvelope a b w 0)
          (inner.affineEnvelope c d v 0) l r - outer.affineEnvelope a b w 0 r) 0 := by
  convert hasDerivAt_finite_intervalSpatialScore_moving
    outer inner a b w c d v ha hc l r 0 (-1) using 1
  · funext ε
    simp only [mul_zero, add_zero, mul_neg_one, sub_eq_add_neg]
  · rw [finiteSourceVariation_eq_integrals outer inner a b w c d v hlr]
    unfold rightEndpointPressure
    ring

theorem hasDerivAt_finiteSourceScore_inward_left
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (outer : WallExpr ι) (inner : WallExpr κ) (a b w : ι → ℝ) (c d v : κ → ℝ)
    (ha : Function.Injective a) (hc : Function.Injective c) {l r : ℝ} (hlr : l ≤ r) :
    HasDerivAt (fun ε => intervalSpatialScore
      (outer.affineEnvelope a b w ε) (inner.affineEnvelope c d v ε) (l + ε) r)
      (finiteSourceVariation outer inner a b c d l r w v +
        leftEndpointPressure (outer.affineEnvelope a b w 0)
          (inner.affineEnvelope c d v 0) l r - outer.affineEnvelope a b w 0 l) 0 := by
  convert hasDerivAt_finite_intervalSpatialScore_moving
    outer inner a b w c d v ha hc l r 1 0 using 1
  · funext ε
    simp only [mul_zero, add_zero, mul_one]
  · rw [finiteSourceVariation_eq_integrals outer inner a b w c d v hlr]
    unfold leftEndpointPressure
    ring

namespace FinitePolygon

variable {ι κ : Type*}

def heightVelocity (normal : ι → Plane) (z : ι → ℝ) : Option ι → ℝ
  | none => 0
  | some i => z i / (normal i).2

def rightErosionVelocity (normal : ι → Plane) : Option ι → ℝ :=
  heightVelocity normal (fun i => -max (normal i).1 0)

def leftErosionVelocity (normal : ι → Plane) : Option ι → ℝ :=
  heightVelocity normal (fun i => -max (-(normal i).1) 0)

theorem erosionVelocity_sub (normal : ι → Plane) :
    (fun i => rightErosionVelocity normal i - leftErosionVelocity normal i) =
      wallSlope normal := by
  funext i
  cases i with
  | none => simp [rightErosionVelocity, leftErosionVelocity, heightVelocity, wallSlope]
  | some i =>
    by_cases h : 0 ≤ (normal i).1
    · simp only [rightErosionVelocity, leftErosionVelocity, heightVelocity, wallSlope,
        max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
      ring
    · have hi := (lt_of_not_ge h).le
      simp only [rightErosionVelocity, leftErosionVelocity, heightVelocity, wallSlope,
        max_eq_right hi, max_eq_left (neg_nonneg.mpr hi)]
      ring

theorem affineEnvelope_roof_height [Fintype ι] (normal : ι → Plane)
    (height z : ι → ℝ) (ε : ℝ) :
    (roofExpr (ι := ι)).affineEnvelope (wallSlope normal) (roofIntercept normal height)
        (heightVelocity normal z) ε =
      roofEnvelope normal (fun i => height i + ε * z i) := by
  funext x
  unfold WallExpr.affineEnvelope roofEnvelope
  congr 1
  funext i
  cases i <;> simp only [heightVelocity, roofIntercept, wallSlope] <;> ring

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
  funext i
  cases i <;> simp only [heightVelocity, barrierIntercept, wallSlope] <;> ring

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
      (Icc (horizontalLeft U) (horizontalRight U)) := by
  intro x hx
  have h := capRoof_upperPolygon (horizontalLeft U) (horizontalRight U) normal
    (fun i => support U (normal i)) hnormal (circumscription_baseline hU normal) hx
  change capRoof (circumscription U normal) x = _ at h
  rw [← hpoly] at h
  exact h.symm

theorem finiteBarrier_le_displayed {U : Set Plane} (normal : ι → Plane)
    (height : ι → ℝ) (hnormal : ∀ i, 0 ≤ (normal i).2)
    (hheight : ∀ i, support U (normal i) ≤ height i)
    (corners : List (ι × ι)) (terminal : Option ι) (x : ℝ) :
    finiteBarrier U normal corners terminal x ≤
      (barrierExpr corners terminal).eval
        (fun i => wallSlope normal i * x + barrierIntercept normal height i) := by
  rw [finiteBarrier_eq_eval normal _ (fun _ => rfl)]
  apply WallExpr.eval_mono
  intro i
  cases i with
  | none => exact le_rfl
  | some i =>
    apply add_le_add_left
    exact div_le_div_of_nonneg_right (sub_le_sub_right (hheight i) 1) (hnormal i)

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
  have hlr : l ≤ r := by
    rw [← hleft, ← hright]
    exact horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hbase : ∀ x ∈ Icc l r, ∀ i, coordDot (x, 0) (normal i) ≤ height i := by
    intro x hx i
    have hxproj : x ∈ horizontalProjection U := by
      rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hleft, hright]
      exact hx
    have hp := hU.baseline_mem_of_mem_projection hxproj
    rw [hpoly] at hp
    exact ((mem_upperPolygon_iff _ _ _ _ _).mp hp).2.2 i
  have hheight : ∀ i, support U (normal i) ≤ height i := by
    intro i
    apply support_le_of_forall hU.nonempty
    intro p hp
    rw [hpoly] at hp
    exact ((mem_upperPolygon_iff _ _ _ _ _).mp hp).2.2 i
  unfold finiteSpatialScore
  rw [hleft, hright]
  apply intervalSpatialScore_le_of_roof_eq_of_niche_le hlr ?_
    ((barrierExpr corners terminal).continuous_eval (fun _ => by fun_prop))
    (continuous_finiteBarrier U normal corners terminal)
    (finiteBarrier_le_displayed normal height (fun i => (hnormal i).le) hheight corners terminal)
  intro x hx
  have h := capRoof_upperPolygon l r normal height hnormal hbase hx
  rw [← hpoly] at h
  exact h.symm

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

def rightErosionComparisonScore [Fintype ι] (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) (ε : ℝ) : ℝ :=
  intervalSpatialScore
    ((roofExpr (ι := ι)).affineEnvelope (wallSlope normal)
      (roofIntercept normal (fun i => support U (normal i))) (rightErosionVelocity normal) ε)
    ((barrierExpr corners terminal).affineEnvelope (wallSlope normal)
      (barrierIntercept normal (fun i => support U (normal i))) (rightErosionVelocity normal) ε)
    (horizontalLeft U) (horizontalRight U - ε)

def leftErosionComparisonScore [Fintype ι] (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) (ε : ℝ) : ℝ :=
  intervalSpatialScore
    ((roofExpr (ι := ι)).affineEnvelope (wallSlope normal)
      (roofIntercept normal (fun i => support U (normal i))) (leftErosionVelocity normal) ε)
    ((barrierExpr corners terminal).affineEnvelope (wallSlope normal)
      (barrierIntercept normal (fun i => support U (normal i))) (leftErosionVelocity normal) ε)
    (horizontalLeft U + ε) (horizontalRight U)

theorem rightErosionComparisonScore_zero [Fintype ι] {U : Set Plane}
    (hU : IsDownwardCap U) (normal : ι → Plane) (hnormal : ∀ i, 0 < (normal i).2)
    (hpoly : U = circumscription U normal) (corners : List (ι × ι)) (terminal : Option ι) :
    rightErosionComparisonScore U normal corners terminal 0 =
      finiteSpatialScore U normal corners terminal := by
  rw [rightErosionComparisonScore, affineEnvelope_roof_zero, affineEnvelope_barrier_zero, sub_zero]
  exact intervalSpatialScore_congr_roof
    (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact)
    (eqOn_roofEnvelope_of_circumscription hU normal hnormal hpoly)

theorem leftErosionComparisonScore_zero [Fintype ι] {U : Set Plane}
    (hU : IsDownwardCap U) (normal : ι → Plane) (hnormal : ∀ i, 0 < (normal i).2)
    (hpoly : U = circumscription U normal) (corners : List (ι × ι)) (terminal : Option ι) :
    leftErosionComparisonScore U normal corners terminal 0 =
      finiteSpatialScore U normal corners terminal := by
  rw [leftErosionComparisonScore, affineEnvelope_roof_zero, affineEnvelope_barrier_zero, add_zero]
  exact intervalSpatialScore_congr_roof
    (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact)
    (eqOn_roofEnvelope_of_circumscription hU normal hnormal hpoly)

theorem rightErosionComparisonScore_le [Fintype ι] {U : Set Plane}
    (hU : IsDownwardCap U) (normal : ι → Plane) (hnormal : ∀ i, 0 < (normal i).2)
    (hpoly : U = circumscription U normal) (corners : List (ι × ι)) (terminal : Option ι)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    rightErosionComparisonScore U normal corners terminal ε ≤
      finiteSpatialScore (rightErosion U ε) normal corners terminal := by
  have hset : rightErosion U ε = upperPolygon (horizontalLeft U) (horizontalRight U - ε)
      normal (fun i => support U (normal i) - ε * max (normal i).1 0) :=
    (congrArg (fun V : Set Plane => rightErosion V ε) hpoly).trans
      (rightErosion_upperPolygon normal (fun i => support U (normal i)) hε0)
  unfold rightErosionComparisonScore rightErosionVelocity
  rw [affineEnvelope_roof_height, affineEnvelope_barrier_height]
  simp only [mul_neg, ← sub_eq_add_neg]
  exact displayedSpatialScore_le_actual (hU.rightErosion hε0 hεW) normal _ hnormal
    (horizontalLeft_rightErosion hU hε0 hεW) (horizontalRight_rightErosion hU hε0 hεW)
    hset corners terminal

theorem leftErosionComparisonScore_le [Fintype ι] {U : Set Plane}
    (hU : IsDownwardCap U) (normal : ι → Plane) (hnormal : ∀ i, 0 < (normal i).2)
    (hpoly : U = circumscription U normal) (corners : List (ι × ι)) (terminal : Option ι)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    leftErosionComparisonScore U normal corners terminal ε ≤
      finiteSpatialScore (leftErosion U ε) normal corners terminal := by
  have hset : leftErosion U ε = upperPolygon (horizontalLeft U + ε) (horizontalRight U)
      normal (fun i => support U (normal i) - ε * max (-(normal i).1) 0) :=
    (congrArg (fun V : Set Plane => leftErosion V ε) hpoly).trans
      (leftErosion_upperPolygon normal (fun i => support U (normal i)) hε0)
  unfold leftErosionComparisonScore leftErosionVelocity
  rw [affineEnvelope_roof_height, affineEnvelope_barrier_height]
  simp only [mul_neg, ← sub_eq_add_neg]
  exact displayedSpatialScore_le_actual (hU.leftErosion hε0 hεW) normal _ hnormal
    (horizontalLeft_leftErosion hU hε0 hεW) (horizontalRight_leftErosion hU hε0 hεW)
    hset corners terminal

theorem hasDerivAt_rightErosionComparisonScore [Fintype ι] {U : Set Plane}
    (hU : IsDownwardCap U) (normal : ι → Plane) (hnormal : ∀ i, 0 < (normal i).2)
    (hslope : Function.Injective (wallSlope normal)) (hpoly : U = circumscription U normal)
    (corners : List (ι × ι)) (terminal : Option ι) :
    HasDerivAt (rightErosionComparisonScore U normal corners terminal)
      (finiteRightMoment U normal corners terminal +
        rightEndpointPressure (capRoof U) (finiteBarrier U normal corners terminal)
          (horizontalLeft U) (horizontalRight U) - capRoof U (horizontalRight U)) 0 := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hroof := eqOn_roofEnvelope_of_circumscription hU normal hnormal hpoly
  have h := hasDerivAt_finiteSourceScore_inward_right
    (roofExpr (ι := ι)) (barrierExpr corners terminal)
    (wallSlope normal) (roofIntercept normal (fun i => support U (normal i)))
    (rightErosionVelocity normal)
    (wallSlope normal) (barrierIntercept normal (fun i => support U (normal i)))
    (rightErosionVelocity normal) hslope hslope hlr
  rw [affineEnvelope_roof_zero, affineEnvelope_barrier_zero,
    rightEndpointPressure_congr_roof hlr hroof, hroof ⟨hlr, le_rfl⟩] at h
  exact h

theorem hasDerivAt_leftErosionComparisonScore [Fintype ι] {U : Set Plane}
    (hU : IsDownwardCap U) (normal : ι → Plane) (hnormal : ∀ i, 0 < (normal i).2)
    (hslope : Function.Injective (wallSlope normal)) (hpoly : U = circumscription U normal)
    (corners : List (ι × ι)) (terminal : Option ι) :
    HasDerivAt (leftErosionComparisonScore U normal corners terminal)
      (finiteLeftMoment U normal corners terminal +
        leftEndpointPressure (capRoof U) (finiteBarrier U normal corners terminal)
          (horizontalLeft U) (horizontalRight U) - capRoof U (horizontalLeft U)) 0 := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hroof := eqOn_roofEnvelope_of_circumscription hU normal hnormal hpoly
  have h := hasDerivAt_finiteSourceScore_inward_left
    (roofExpr (ι := ι)) (barrierExpr corners terminal)
    (wallSlope normal) (roofIntercept normal (fun i => support U (normal i)))
    (leftErosionVelocity normal)
    (wallSlope normal) (barrierIntercept normal (fun i => support U (normal i)))
    (leftErosionVelocity normal) hslope hslope hlr
  rw [affineEnvelope_roof_zero, affineEnvelope_barrier_zero,
    leftEndpointPressure_congr_roof hlr hroof, hroof ⟨le_rfl, hlr⟩] at h
  exact h

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
  have hderiv := hasDerivAt_rightErosionComparisonScore hU normal hnormal hslope hpoly corners terminal
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      rightErosionComparisonScore U normal corners terminal ε ≤
        rightErosionComparisonScore U normal corners terminal 0 +
          ε * supportPenaltyLipschitz B penaltyNormal weight := by
    have hsmall : Iio (capWidth U) ∈ 𝓝[>] (0 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (zero_lt_one.trans_le hW))
    filter_upwards [hsmall, self_mem_nhdsWithin] with ε hεW hεpos
    have hε0 : 0 ≤ ε := (show 0 < ε from hεpos).le
    have hE := hU.rightErosion hε0 hεW.le
    have hcomparison := rightErosionComparisonScore_le hU normal hnormal hpoly
      corners terminal hε0 hεW.le
    have hselected := hmax (rightErosion U ε) hE (rightErosion_subset U ε)
    have hpenalty := (le_abs_self _).trans
      (abs_sampledPenalty_sub_le_of_support_control hU hE (rightErosion_subset U ε)
        penaltyNormal weight target hB hweight hpoints htarget
        (fun i => abs_support_rightErosion_sub_le hU hW hε0 hεW.le (penaltyNormal i)))
    rw [rightErosionComparisonScore_zero hU normal hnormal hpoly corners terminal]
    linarith
  have h := hasDerivAt_le_of_right_linear_bound hderiv hbound
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
  have hderiv := hasDerivAt_leftErosionComparisonScore hU normal hnormal hslope hpoly corners terminal
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      leftErosionComparisonScore U normal corners terminal ε ≤
        leftErosionComparisonScore U normal corners terminal 0 +
          ε * supportPenaltyLipschitz B penaltyNormal weight := by
    have hsmall : Iio (capWidth U) ∈ 𝓝[>] (0 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (zero_lt_one.trans_le hW))
    filter_upwards [hsmall, self_mem_nhdsWithin] with ε hεW hεpos
    have hε0 : 0 ≤ ε := (show 0 < ε from hεpos).le
    have hE := hU.leftErosion hε0 hεW.le
    have hcomparison := leftErosionComparisonScore_le hU normal hnormal hpoly
      corners terminal hε0 hεW.le
    have hselected := hmax (leftErosion U ε) hE (leftErosion_subset U ε)
    have hpenalty := (le_abs_self _).trans
      (abs_sampledPenalty_sub_le_of_support_control hU hE (leftErosion_subset U ε)
        penaltyNormal weight target hB hweight hpoints htarget
        (fun i => abs_support_leftErosion_sub_le hU hW hε0 hεW.le (penaltyNormal i)))
    rw [leftErosionComparisonScore_zero hU normal hnormal hpoly corners terminal]
    linarith
  have h := hasDerivAt_le_of_right_linear_bound hderiv hbound
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
  unfold finiteRightMoment finiteSourceVariation
  simp only [Fintype.sum_option, rightErosionVelocity, heightVelocity,
    mul_zero, zero_add, add_zero]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold finiteExposureDefect
  ring

theorem finiteLeftMoment_eq_sum [Fintype ι] (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) :
    finiteLeftMoment U normal corners terminal =
      ∑ i, finiteExposureDefect U normal corners terminal i *
        (max (-(normal i).1) 0 / (normal i).2) := by
  unfold finiteLeftMoment finiteSourceVariation
  simp only [Fintype.sum_option, leftErosionVelocity, heightVelocity,
    mul_zero, zero_add, add_zero]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold finiteExposureDefect
  ring

theorem finiteRightMoment_nonneg_of_exposure [Fintype ι] (U : Set Plane)
    (normal : ι → Plane) (hnormal : ∀ i, 0 ≤ (normal i).2)
    (corners : List (ι × ι)) (terminal : Option ι)
    (hexposure : ∀ i, 0 ≤ finiteExposureDefect U normal corners terminal i) :
    0 ≤ finiteRightMoment U normal corners terminal := by
  rw [finiteRightMoment_eq_sum]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hexposure i)
    (div_nonneg (le_max_right _ _) (hnormal i)))

theorem finiteLeftMoment_nonneg_of_exposure [Fintype ι] (U : Set Plane)
    (normal : ι → Plane) (hnormal : ∀ i, 0 ≤ (normal i).2)
    (corners : List (ι × ι)) (terminal : Option ι)
    (hexposure : ∀ i, 0 ≤ finiteExposureDefect U normal corners terminal i) :
    0 ≤ finiteLeftMoment U normal corners terminal := by
  rw [finiteLeftMoment_eq_sum]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hexposure i)
    (div_nonneg (le_max_right _ _) (hnormal i)))

theorem finiteRightMoment_ge_of_exposure_error [Fintype ι] (U : Set Plane)
    (normal : ι → Plane) (hnormal : ∀ i, 0 ≤ (normal i).2)
    (corners : List (ι × ι)) (terminal : Option ι) (error : ι → ℝ)
    (hexposure : ∀ i, -error i ≤ finiteExposureDefect U normal corners terminal i) :
    -(∑ i, error i * (max (normal i).1 0 / (normal i).2)) ≤
      finiteRightMoment U normal corners terminal := by
  rw [finiteRightMoment_eq_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [neg_mul] using mul_le_mul_of_nonneg_right (hexposure i)
    (div_nonneg (le_max_right _ _) (hnormal i))

theorem finiteLeftMoment_ge_of_exposure_error [Fintype ι] (U : Set Plane)
    (normal : ι → Plane) (hnormal : ∀ i, 0 ≤ (normal i).2)
    (corners : List (ι × ι)) (terminal : Option ι) (error : ι → ℝ)
    (hexposure : ∀ i, -error i ≤ finiteExposureDefect U normal corners terminal i) :
    -(∑ i, error i * (max (-(normal i).1) 0 / (normal i).2)) ≤
      finiteLeftMoment U normal corners terminal := by
  rw [finiteLeftMoment_eq_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [neg_mul] using mul_le_mul_of_nonneg_right (hexposure i)
    (div_nonneg (le_max_right _ _) (hnormal i))

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
  have htranslation := finiteSourceVariation_translation
    (roofExpr (ι := ι)) (barrierExpr corners terminal)
    (wallSlope normal) (roofIntercept normal (fun i => support U (normal i)))
    (wallSlope normal) (barrierIntercept normal (fun i => support U (normal i)))
    hslope hslope hlr
  rw [affineEnvelope_roof_zero, affineEnvelope_barrier_zero,
    rightEndpointPressure_congr_roof hlr hroof,
    leftEndpointPressure_congr_roof hlr hroof,
    hroof ⟨le_rfl, hlr⟩, hroof ⟨hlr, le_rfl⟩] at htranslation
  have halgebra : finiteRightMoment U normal corners terminal -
      finiteLeftMoment U normal corners terminal =
      -finiteSourceVariation (roofExpr (ι := ι)) (barrierExpr corners terminal)
        (wallSlope normal) (roofIntercept normal (fun i => support U (normal i)))
        (wallSlope normal) (barrierIntercept normal (fun i => support U (normal i)))
        (horizontalLeft U) (horizontalRight U)
        (fun i => -(wallSlope normal i)) (fun i => -(wallSlope normal i)) := by
    unfold finiteRightMoment finiteLeftMoment
    rw [← finiteSourceVariation_sub, erosionVelocity_sub]
    simpa only [neg_neg] using
      finiteSourceVariation_neg (roofExpr (ι := ι)) (barrierExpr corners terminal)
        (wallSlope normal) (roofIntercept normal (fun i => support U (normal i)))
        (wallSlope normal) (barrierIntercept normal (fun i => support U (normal i)))
        (horizontalLeft U) (horizontalRight U)
        (fun i => -(wallSlope normal i)) (fun i => -(wallSlope normal i))
  rw [halgebra, htranslation]
  ring

end FinitePolygon

end AmbidextrousSofa
