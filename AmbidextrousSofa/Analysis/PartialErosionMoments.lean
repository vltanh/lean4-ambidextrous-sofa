module

public import AmbidextrousSofa.Analysis.PartialPressureLimit
public import AmbidextrousSofa.Analysis.SelectedErosionMoments

@[expose] public section

/-!
# Actual proper-angle selected erosion moments

The selected exposure inequality bounds each signed physical source
balance from below by its persistent support error. Actual endpoint
variations supply the upper bound. Both barriers include the whole
terminal first wall throughout the finite identities and the limit.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa
namespace PartialGrid

open FinitePolygon AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

theorem finiteExposureDefect_div_eq_integrals {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (j : SourceIndex α grid) :
    finiteExposureDefect U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) j / (normal α grid j).2 =
      (∫ x in (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)..
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4),
        innerDensity U α hαL grid j x) -
      (∫ x in (horizontalLeft U)..
        (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4),
        outerDensity U α grid j x) -
      (∫ x in (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)..
        (horizontalRight U), outerDensity U α grid j x) := by
  classical
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  unfold innerDensity outerDensity
  rw [integral_sourceDensity_outward _ _ _ _ ?_, integral_sourceDensity_outward _ _ _ _ ?_,
    integral_sourceDensity_outward _ _ _ _ ?_]
  · unfold finiteExposureDefect WallExpr.sourceMass; ring
  all_goals linarith

/-- Actual curvature and the retained middle facet give the outward
derivative bound even when the selected outer facet has zero length. -/
theorem IsSelectedPolygon.exposure_defect_div_ge {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U) (hc : 0 ≤ coefficient)
    (j : SourceIndex α (dyadic level)) :
    -selectionDefect target U α level coefficient j ≤
      finiteExposureDefect U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))) j /
        (normal α (dyadic level) j).2 := by
  classical
  have hcurv := hU.curvature_atom_le hc j
  have hfull : (∫ x in (horizontalLeft U)..(horizontalRight U), outerDensity U α (dyadic level) j x) =
      (upperCurvature U {fullAngle α (dyadic level) j}).toReal :=
    integral_outerSource_eq_curvature_atom hU.isCap _ (normal_snd_pos α _)
      (wallSlopes_injective α _) hU.polygon_eq j (normal_eq_unitNormal α _ j)
  rw [finiteExposureDefect_div_eq_integrals hU.isCap]
  set l := horizontalLeft U
  set r := horizontalRight U
  have hint (s t : ℝ) := intervalIntegrable_outerDensity U α (dyadic level) j s t
  linarith [intervalIntegral.integral_add_adjacent_intervals (hint l (l + (r - l) / 4))
      (hint _ (r - (r - l) / 4)),
    intervalIntegral.integral_add_adjacent_intervals (hint l (r - (r - l) / 4)) (hint _ r)]

theorem IsSelectedPolygon.rightMoment_ge_neg_selectionDefect {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U) (hc : 0 ≤ coefficient) :
    -(∑ j, selectionDefect target U α level coefficient j) ≤
      finiteRightMoment U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))) := by
  rw [finiteRightMoment_eq_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have hm : max (normal α (dyadic level) j).1 0 ≤ 1 :=
    max_le (by rw [normal_eq_unitNormal]; exact Real.cos_le_one _) zero_le_one
  rw [← mul_div_assoc, ← div_mul_eq_mul_div]
  linarith [mul_le_mul_of_nonneg_right (hU.exposure_defect_div_ge hc j)
      (le_max_right (normal α (dyadic level) j).1 0),
    mul_le_mul_of_nonneg_left hm (selectionDefect_nonneg target U α level hc j)]

theorem IsSelectedPolygon.leftMoment_ge_neg_selectionDefect {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U) (hc : 0 ≤ coefficient) :
    -(∑ j, selectionDefect target U α level coefficient j) ≤
      finiteLeftMoment U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))) := by
  rw [finiteLeftMoment_eq_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have hm : max (-(normal α (dyadic level) j).1) 0 ≤ 1 :=
    max_le (by rw [normal_eq_unitNormal]; exact neg_le.mpr (Real.neg_one_le_cos _)) zero_le_one
  rw [← mul_div_assoc, ← div_mul_eq_mul_div]
  linarith [mul_le_mul_of_nonneg_right (hU.exposure_defect_div_ge hc j)
      (le_max_right (-(normal α (dyadic level) j).1) 0),
    mul_le_mul_of_nonneg_left hm (selectionDefect_nonneg target U α level hc j)]

theorem rightErosionUpperBound_tendsto {target : Set Plane} {U : ℕ → Set Plane}
    {a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : horizontalRight target < b) :
    Tendsto (fun n => capRoof (U n) (horizontalRight (U n)) -
      rightPressure (U n) α hαL (dyadic (level n)) + endpointSelectionError a b (coefficient n))
      atTop (𝓝 (max (-partialRightEndpointPressure target α) 0)) := by
  simpa only [add_zero, positivePart_sub_self] using
    ((selected_right_height_tendsto hTarget hTargetBox hU hHausdorff hlevel hc hrate hwidth
      hslack).sub (rightPressure_tendsto (α := α) (hαL := hαL) hHausdorff (fun n => (hU n).isCap)
        hTarget hlevel (fun n => (hU n).inBox) (by unfold capWidth at hwidth; linarith))).add
      (endpointSelectionError_tendsto a b hrate)

theorem leftErosionUpperBound_tendsto {target : Set Plane} {U : ℕ → Set Plane}
    {a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : a < horizontalLeft target) :
    Tendsto (fun n => capRoof (U n) (horizontalLeft (U n)) -
      leftPressure (U n) α hαL (dyadic (level n)) + endpointSelectionError a b (coefficient n))
      atTop (𝓝 (max (-partialLeftEndpointPressure target α) 0)) := by
  simpa only [add_zero, positivePart_sub_self] using
    ((selected_left_height_tendsto hTarget hTargetBox hU hHausdorff hlevel hc hrate hwidth
      hslack).sub (leftPressure_tendsto (α := α) (hαL := hαL) hHausdorff (fun n => (hU n).isCap)
        hTarget hlevel (fun n => (hU n).inBox) (by unfold capWidth at hwidth; linarith))).add
      (endpointSelectionError_tendsto a b hrate)

/-- At a nonnegative pressure, the actual right erosion moment tends to
zero. Its lower estimate is supplied by the literal selected sources. -/
theorem rightMoment_tendsto_zero_of_pressure_nonneg
    {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : horizontalRight target < b)
    (hpressure : 0 ≤ partialRightEndpointPressure target α) :
    Tendsto (fun n => finiteRightMoment (U n) (normal α (dyadic (level n)))
      (pairList α (dyadic (level n))) (some (terminalIndex α hαL (dyadic (level n))))) atTop (𝓝 0) := by
  have hupper := rightErosionUpperBound_tendsto hTarget hTargetBox hU
    hHausdorff hlevel hc hrate hwidth hslack
  rw [max_eq_right (neg_nonpos.mpr hpressure)] at hupper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa only [neg_zero] using
    (selectionDefect_sum_tendsto (α := α) hTarget (fun n => (hU n).isCap) (level := level) hc hrate
      hHausdorff).neg) hupper
    (.of_forall fun n => (hU n).rightMoment_ge_neg_selectionDefect (hc n)) ?_
  filter_upwards [(hHausdorff.capWidth_tendsto (fun n => (hU n).isCap) hTarget).eventually
    (Ioi_mem_nhds hwidth)] with n hn
  exact (hU n).right_erosion_bound hTarget hTargetBox (hc n) hn.le

theorem leftMoment_tendsto_zero_of_pressure_nonneg
    {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : a < horizontalLeft target)
    (hpressure : 0 ≤ partialLeftEndpointPressure target α) :
    Tendsto (fun n => finiteLeftMoment (U n) (normal α (dyadic (level n)))
      (pairList α (dyadic (level n))) (some (terminalIndex α hαL (dyadic (level n))))) atTop (𝓝 0) := by
  have hupper := leftErosionUpperBound_tendsto hTarget hTargetBox hU
    hHausdorff hlevel hc hrate hwidth hslack
  rw [max_eq_right (neg_nonpos.mpr hpressure)] at hupper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa only [neg_zero] using
    (selectionDefect_sum_tendsto (α := α) hTarget (fun n => (hU n).isCap) (level := level) hc hrate
      hHausdorff).neg) hupper
    (.of_forall fun n => (hU n).leftMoment_ge_neg_selectionDefect (hc n)) ?_
  filter_upwards [(hHausdorff.capWidth_tendsto (fun n => (hU n).isCap) hTarget).eventually
    (Ioi_mem_nhds hwidth)] with n hn
  exact (hU n).left_erosion_bound hTarget hTargetBox (hc n) hn.le

/-- The exact finite translation identity passes to the selected limit
without first postulating separate limits for either signed moment. -/
theorem erosionMoment_difference_tendsto
    {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target)
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b) :
    Tendsto (fun n =>
      finiteRightMoment (U n) (normal α (dyadic (level n))) (pairList α (dyadic (level n))) (some (terminalIndex α hαL (dyadic (level n)))) -
      finiteLeftMoment (U n) (normal α (dyadic (level n))) (pairList α (dyadic (level n))) (some (terminalIndex α hαL (dyadic (level n)))))
      atTop (𝓝 (max (-partialRightEndpointPressure target α) 0 -
        max (-partialLeftEndpointPressure target α) 0)) := by
  refine ((rightErosionUpperBound_tendsto hTarget hTargetBox hU hHausdorff hlevel hc hrate hwidth
    hright).sub (leftErosionUpperBound_tendsto hTarget hTargetBox hU hHausdorff hlevel hc hrate
      hwidth hleft)).congr fun n => ?_
  rw [finite_erosion_moment_balance (hU n).isCap _ (normal_snd_pos α _) (wallSlopes_injective α _)
    (hU n).polygon_eq, rightPressure, leftPressure]
  ring

/-- Both actual selected erosion moments converge to the exact endpoint
defects. At least one pressure is nonnegative because their sum is the
average of two nonnegative roof-plus-niche heights. That side has zero
limiting moment; translation balance determines the other side as well.
No convergence of the target's endpoint face heights is used. -/
theorem erosionMoments_tendsto
    {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target)
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b) :
    Tendsto (fun n => finiteRightMoment (U n) (normal α (dyadic (level n)))
      (pairList α (dyadic (level n))) (some (terminalIndex α hαL (dyadic (level n))))) atTop (𝓝 (max (-partialRightEndpointPressure target α) 0)) ∧
    Tendsto (fun n => finiteLeftMoment (U n) (normal α (dyadic (level n)))
      (pairList α (dyadic (level n))) (some (terminalIndex α hαL (dyadic (level n))))) atTop (𝓝 (max (-partialLeftEndpointPressure target α) 0)) := by
  have hbalance := erosionMoment_difference_tendsto hTarget hTargetBox hU
    hHausdorff hlevel hc hrate hwidth hleft hright
  by_cases hR : 0 ≤ partialRightEndpointPressure target α
  · rw [max_eq_right (neg_nonpos.mpr hR)] at hbalance ⊢
    have hRlim := rightMoment_tendsto_zero_of_pressure_nonneg hTarget hTargetBox hU
      hHausdorff hlevel hc hrate hwidth hright hR
    exact ⟨hRlim, by simpa only [sub_sub_cancel] using hRlim.sub hbalance⟩
  · have hL : 0 ≤ partialLeftEndpointPressure target α := by
      linarith [hTarget.partialEndpointPressure_sum_nonneg α, lt_of_not_ge hR]
    rw [max_eq_right (neg_nonpos.mpr hL)] at hbalance ⊢
    have hLlim := leftMoment_tendsto_zero_of_pressure_nonneg hTarget hTargetBox hU
      hHausdorff hlevel hc hrate hwidth hleft hL
    exact ⟨by simpa only [sub_add_cancel, sub_zero, add_zero] using hbalance.add hLlim, hLlim⟩

end PartialGrid
end AmbidextrousSofa
