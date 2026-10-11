module

public import AmbidextrousSofa.Analysis.SelectedPressureLimit

@[expose] public section

/-!
# Selected erosion moments and their vanishing errors

The finite source defect is an actual middle source length minus the two
charged exterior source lengths. Dividing by the vertical normal component
turns those lengths into the outward support derivatives. The selected
curvature inequality therefore bounds that quotient from below.

Horizontal erosion multiplies the quotient by a positive part of the
horizontal normal component. That multiplier is at most one: the total
moment error is bounded by the already summable support penalty errors,
without a singular factor near either horizontal axis. The finite and
limiting translation identities retain both endpoint pressures.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace AngularGrid

open FinitePolygon

theorem finiteExposureDefect_div_eq_integrals {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (j : SourceIndex grid) :
    finiteExposureDefect U (normal grid) (pairList grid) none j / (normal grid j).2 =
      (∫ x in (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)..
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4),
        innerDensity U grid j x) -
      (∫ x in (horizontalLeft U)..
        (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4),
        outerDensity U grid j x) -
      (∫ x in (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)..
        (horizontalRight U), outerDensity U grid j x) := by
  classical
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  unfold innerDensity outerDensity finiteExposureDefect WallExpr.sourceMass
  repeat rw [integral_sourceDensity_outward _ _ _ _ (by linarith)]
  ring

/-- Actual curvature and the retained middle facet give the outward
derivative bound even when the selected outer facet has zero length. -/
theorem IsSelectedPolygon.exposure_defect_div_ge {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hc : 0 ≤ coefficient)
    (j : SourceIndex (dyadic level)) :
    -selectionDefect target U level coefficient j ≤
      finiteExposureDefect U (normal (dyadic level)) (pairList (dyadic level)) none j /
        (normal (dyadic level) j).2 := by
  classical
  have hcurvature := hU.curvature_atom_le hc j
  have hfull : (∫ x in (horizontalLeft U)..(horizontalRight U), outerDensity U (dyadic level) j x) =
      (upperCurvature U {fullAngle (dyadic level) j}).toReal :=
    integral_outerSource_eq_curvature_atom hU.isCap _ (normal_snd_pos _) (wallSlopes_injective _)
      hU.polygon_eq j (normal_eq_unitNormal _ j)
  rw [finiteExposureDefect_div_eq_integrals hU.isCap]
  set l := horizontalLeft U
  set r := horizontalRight U
  have hint := intervalIntegrable_outerDensity U (dyadic level) j
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hint l (l + (r - l) / 4))
    (hint _ (r - (r - l) / 4))
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hint l (r - (r - l) / 4)) (hint _ r)
  linarith

theorem IsSelectedPolygon.rightMoment_ge_neg_selectionDefect {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hc : 0 ≤ coefficient) :
    -(∑ j, selectionDefect target U level coefficient j) ≤
      finiteRightMoment U (normal (dyadic level)) (pairList (dyadic level)) none := by
  classical
  rw [finiteRightMoment_eq_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have hm0 := le_max_right (normal (dyadic level) j).1 0
  have hm : max (normal (dyadic level) j).1 0 ≤ 1 :=
    max_le (by rw [normal_eq_unitNormal]; exact Real.cos_le_one _) zero_le_one
  rw [← mul_div_assoc, mul_div_right_comm]
  linarith [mul_le_mul_of_nonneg_right (hU.exposure_defect_div_ge hc j) hm0,
    mul_le_of_le_one_right (selectionDefect_nonneg target U level hc j) hm]

theorem IsSelectedPolygon.leftMoment_ge_neg_selectionDefect {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hc : 0 ≤ coefficient) :
    -(∑ j, selectionDefect target U level coefficient j) ≤
      finiteLeftMoment U (normal (dyadic level)) (pairList (dyadic level)) none := by
  classical
  rw [finiteLeftMoment_eq_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have hm0 := le_max_right (-(normal (dyadic level) j).1) 0
  have hm : max (-(normal (dyadic level) j).1) 0 ≤ 1 :=
    max_le (by rw [normal_eq_unitNormal]; exact neg_le.2 (Real.neg_one_le_cos _)) zero_le_one
  rw [← mul_div_assoc, mul_div_right_comm]
  linarith [mul_le_mul_of_nonneg_right (hU.exposure_defect_div_ge hc j) hm0,
    mul_le_of_le_one_right (selectionDefect_nonneg target U level hc j) hm]

theorem positivePart_sub_self (c : ℝ) : max c 0 - c = max (-c) 0 := by
  linarith [max_zero_sub_max_neg_zero_eq_self c]

section Limits

variable {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ} {level : ℕ → ℕ}
  {coefficient : ℕ → ℝ} (hTarget : IsDownwardCap target)
  (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
  (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
  (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
  (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
  (hwidth : 1 < capWidth target)
include hTarget hTargetBox hU hHausdorff hlevel hc hrate hwidth

theorem rightErosionUpperBound_tendsto (hslack : horizontalRight target < b) :
    Tendsto (fun n => capRoof (U n) (horizontalRight (U n)) -
      rightPressure (U n) (dyadic (level n)) + endpointSelectionError a b (coefficient n))
      atTop (𝓝 (max (-capRightEndpointPressure target) 0)) := by
  simpa only [add_zero, positivePart_sub_self] using
    ((selected_right_height_tendsto hTarget hTargetBox hU hHausdorff hlevel hc hrate hwidth
      hslack).sub (rightPressure_tendsto hHausdorff (fun n => (hU n).isCap) hTarget hlevel
        (fun n => (hU n).inBox) (sub_pos.1 (zero_lt_one.trans hwidth)))).add
      (endpointSelectionError_tendsto a b hrate)

theorem leftErosionUpperBound_tendsto (hslack : a < horizontalLeft target) :
    Tendsto (fun n => capRoof (U n) (horizontalLeft (U n)) -
      leftPressure (U n) (dyadic (level n)) + endpointSelectionError a b (coefficient n))
      atTop (𝓝 (max (-capLeftEndpointPressure target) 0)) := by
  simpa only [add_zero, positivePart_sub_self] using
    ((selected_left_height_tendsto hTarget hTargetBox hU hHausdorff hlevel hc hrate hwidth
      hslack).sub (leftPressure_tendsto hHausdorff (fun n => (hU n).isCap) hTarget hlevel
        (fun n => (hU n).inBox) (sub_pos.1 (zero_lt_one.trans hwidth)))).add
      (endpointSelectionError_tendsto a b hrate)

/-- At a nonnegative pressure, the actual right erosion moment tends to
zero. Its lower estimate is supplied by the literal selected sources. -/
theorem rightMoment_tendsto_zero_of_pressure_nonneg (hslack : horizontalRight target < b)
    (hpressure : 0 ≤ capRightEndpointPressure target) :
    Tendsto (fun n => finiteRightMoment (U n) (normal (dyadic (level n)))
      (pairList (dyadic (level n))) none) atTop (𝓝 0) := by
  have hupper := rightErosionUpperBound_tendsto hTarget hTargetBox hU hHausdorff hlevel hc hrate
    hwidth hslack
  rw [max_eq_right (neg_nonpos.2 hpressure)] at hupper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using (selectionDefect_sum_tendsto
    hTarget (fun n => (hU n).isCap) (level := level) hc hrate hHausdorff).neg) hupper
    (.of_forall fun n => (hU n).rightMoment_ge_neg_selectionDefect (hc n)) ?_
  filter_upwards [(hHausdorff.capWidth_tendsto (fun n => (hU n).isCap) hTarget).eventually
    (Ioi_mem_nhds hwidth)] with n hn
  exact (hU n).right_erosion_bound hTarget hTargetBox (hc n) hn.le

theorem leftMoment_tendsto_zero_of_pressure_nonneg (hslack : a < horizontalLeft target)
    (hpressure : 0 ≤ capLeftEndpointPressure target) :
    Tendsto (fun n => finiteLeftMoment (U n) (normal (dyadic (level n)))
      (pairList (dyadic (level n))) none) atTop (𝓝 0) := by
  have hupper := leftErosionUpperBound_tendsto hTarget hTargetBox hU hHausdorff hlevel hc hrate
    hwidth hslack
  rw [max_eq_right (neg_nonpos.2 hpressure)] at hupper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using (selectionDefect_sum_tendsto
    hTarget (fun n => (hU n).isCap) (level := level) hc hrate hHausdorff).neg) hupper
    (.of_forall fun n => (hU n).leftMoment_ge_neg_selectionDefect (hc n)) ?_
  filter_upwards [(hHausdorff.capWidth_tendsto (fun n => (hU n).isCap) hTarget).eventually
    (Ioi_mem_nhds hwidth)] with n hn
  exact (hU n).left_erosion_bound hTarget hTargetBox (hc n) hn.le

/-- The exact finite translation identity passes to the selected limit
without first postulating separate limits for either signed moment. -/
theorem erosionMoment_difference_tendsto (hleft : a < horizontalLeft target)
    (hright : horizontalRight target < b) :
    Tendsto (fun n =>
      finiteRightMoment (U n) (normal (dyadic (level n))) (pairList (dyadic (level n))) none -
      finiteLeftMoment (U n) (normal (dyadic (level n))) (pairList (dyadic (level n))) none)
      atTop (𝓝 (max (-capRightEndpointPressure target) 0 -
        max (-capLeftEndpointPressure target) 0)) := by
  refine ((rightErosionUpperBound_tendsto hTarget hTargetBox hU hHausdorff hlevel hc hrate hwidth
    hright).sub (leftErosionUpperBound_tendsto hTarget hTargetBox hU hHausdorff hlevel hc hrate
      hwidth hleft)).congr fun n => ?_
  simp only [finite_erosion_moment_balance (hU n).isCap _ (normal_snd_pos _)
    (wallSlopes_injective _) (hU n).polygon_eq, rightPressure, leftPressure]
  ring

/-- Both actual selected erosion moments converge to the exact endpoint
defects. At least one pressure is nonnegative because their sum is the
average of two nonnegative roof-plus-niche heights. That side has zero
limiting moment; translation balance determines the other side as well.
No convergence of the target's endpoint face heights is used. -/
theorem erosionMoments_tendsto (hleft : a < horizontalLeft target)
    (hright : horizontalRight target < b) :
    Tendsto (fun n => finiteRightMoment (U n) (normal (dyadic (level n)))
      (pairList (dyadic (level n))) none) atTop (𝓝 (max (-capRightEndpointPressure target) 0)) ∧
    Tendsto (fun n => finiteLeftMoment (U n) (normal (dyadic (level n)))
      (pairList (dyadic (level n))) none) atTop (𝓝 (max (-capLeftEndpointPressure target) 0)) := by
  have hbalance := erosionMoment_difference_tendsto hTarget hTargetBox hU hHausdorff hlevel hc hrate
    hwidth hleft hright
  by_cases hR : 0 ≤ capRightEndpointPressure target
  · have hRlim := rightMoment_tendsto_zero_of_pressure_nonneg hTarget hTargetBox hU hHausdorff
      hlevel hc hrate hwidth hright hR
    rw [max_eq_right (neg_nonpos.2 hR)] at hbalance ⊢
    exact ⟨hRlim, by simpa using hRlim.sub hbalance⟩
  · have hL : 0 ≤ capLeftEndpointPressure target := by
      linarith [hTarget.capEndpointPressure_sum_nonneg]
    have hLlim := leftMoment_tendsto_zero_of_pressure_nonneg hTarget hTargetBox hU hHausdorff
      hlevel hc hrate hwidth hleft hL
    rw [max_eq_right (neg_nonpos.2 hL)] at hbalance ⊢
    exact ⟨by simpa using hbalance.add hLlim, hLlim⟩

end Limits

end AngularGrid

end AmbidextrousSofa
