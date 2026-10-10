import AmbidextrousSofa.Analysis.PartialPressureLimit
import AmbidextrousSofa.Analysis.SelectedErosionMoments

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
  have hleft : horizontalLeft U ≤
      horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 := by linarith
  have hmiddle : horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 ≤
      horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 := by linarith
  have hright : horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 ≤
      horizontalRight U := by linarith
  unfold innerDensity outerDensity
  rw [integral_sourceDensity_outward _ _ _ _ hmiddle,
    integral_sourceDensity_outward _ _ _ _ hleft,
    integral_sourceDensity_outward _ _ _ _ hright]
  unfold finiteExposureDefect WallExpr.sourceMass
  ring

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
  let grid := dyadic level
  let l := horizontalLeft U
  let r := horizontalRight U
  let left := l + (r - l) / 4
  let right := r - (r - l) / 4
  have hcurvature := hU.curvature_atom_le hc j
  have hfull := integral_outerSource_eq_curvature_atom hU.isCap (normal α grid)
    (normal_snd_pos α grid) (wallSlopes_injective α grid) hU.polygon_eq j
    (normal_eq_unitNormal α grid j)
  change (∫ x in l..r, outerDensity U α grid j x) =
    (upperCurvature U {fullAngle α grid j}).toReal at hfull
  have hfirst := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerDensity U α grid j l left)
    (intervalIntegrable_outerDensity U α grid j left right)
  have hsecond := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerDensity U α grid j l right)
    (intervalIntegrable_outerDensity U α grid j right r)
  rw [finiteExposureDefect_div_eq_integrals hU.isCap]
  change -selectionDefect target U α level coefficient j ≤
    (∫ x in left..right, innerDensity U α hαL grid j x) -
      (∫ x in l..left, outerDensity U α grid j x) -
      (∫ x in right..r, outerDensity U α grid j x)
  change (upperCurvature U {fullAngle α grid j}).toReal ≤
    (∫ x in left..right, innerDensity U α hαL grid j x) +
      (∫ x in left..right, outerDensity U α grid j x) +
      selectionDefect target U α level coefficient j at hcurvature
  linarith

theorem IsSelectedPolygon.rightMoment_ge_neg_selectionDefect {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U) (hc : 0 ≤ coefficient) :
    -(∑ j, selectionDefect target U α level coefficient j) ≤
      finiteRightMoment U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))) := by
  classical
  rw [finiteRightMoment_eq_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro j _
  have hdefect := hU.exposure_defect_div_ge hc j
  have hnonneg := selectionDefect_nonneg target U α level hc j
  have hnormal : (normal α (dyadic level) j).1 ≤ 1 := by
    rw [normal_eq_unitNormal]
    exact Real.cos_le_one _
  have hmax : max (normal α (dyadic level) j).1 0 ≤ 1 := max_le hnormal zero_le_one
  have hmul := mul_le_mul_of_nonneg_right hdefect
    (le_max_right (normal α (dyadic level) j).1 0)
  have herr := mul_le_mul_of_nonneg_left hmax hnonneg
  have hterm : finiteExposureDefect U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))) j *
      (max (normal α (dyadic level) j).1 0 / (normal α (dyadic level) j).2) =
    (finiteExposureDefect U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))) j /
      (normal α (dyadic level) j).2) * max (normal α (dyadic level) j).1 0 := by ring
  rw [hterm]
  nlinarith

theorem IsSelectedPolygon.leftMoment_ge_neg_selectionDefect {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U) (hc : 0 ≤ coefficient) :
    -(∑ j, selectionDefect target U α level coefficient j) ≤
      finiteLeftMoment U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))) := by
  classical
  rw [finiteLeftMoment_eq_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro j _
  have hdefect := hU.exposure_defect_div_ge hc j
  have hnonneg := selectionDefect_nonneg target U α level hc j
  have hnormal : -(normal α (dyadic level) j).1 ≤ 1 := by
    rw [normal_eq_unitNormal]
    change -Real.cos (fullAngle α (dyadic level) j) ≤ 1
    linarith [Real.neg_one_le_cos (fullAngle α (dyadic level) j)]
  have hmax : max (-(normal α (dyadic level) j).1) 0 ≤ 1 := max_le hnormal zero_le_one
  have hmul := mul_le_mul_of_nonneg_right hdefect
    (le_max_right (-(normal α (dyadic level) j).1) 0)
  have herr := mul_le_mul_of_nonneg_left hmax hnonneg
  have hterm : finiteExposureDefect U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))) j *
      (max (-(normal α (dyadic level) j).1) 0 / (normal α (dyadic level) j).2) =
    (finiteExposureDefect U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))) j /
      (normal α (dyadic level) j).2) * max (-(normal α (dyadic level) j).1) 0 := by ring
  rw [hterm]
  nlinarith

theorem rightMoment_limit_nonneg {target : Set Plane} {U : ℕ → Set Plane}
    {a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    {m : ℝ} (hm : Tendsto (fun n => finiteRightMoment (U n)
      (normal α (dyadic (level n))) (pairList α (dyadic (level n))) (some (terminalIndex α hαL (dyadic (level n))))) atTop (𝓝 m)) :
    0 ≤ m := by
  have herr := (selectionDefect_sum_tendsto (α := α) hTarget (fun n => (hU n).isCap)
    (level := level) hc hrate hHausdorff).neg
  simpa only [neg_zero] using le_of_tendsto_of_tendsto herr hm
    (Eventually.of_forall (fun n => (hU n).rightMoment_ge_neg_selectionDefect (hc n)))

theorem leftMoment_limit_nonneg {target : Set Plane} {U : ℕ → Set Plane}
    {a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    {m : ℝ} (hm : Tendsto (fun n => finiteLeftMoment (U n)
      (normal α (dyadic (level n))) (pairList α (dyadic (level n))) (some (terminalIndex α hαL (dyadic (level n))))) atTop (𝓝 m)) :
    0 ≤ m := by
  have herr := (selectionDefect_sum_tendsto (α := α) hTarget (fun n => (hU n).isCap)
    (level := level) hc hrate hHausdorff).neg
  simpa only [neg_zero] using le_of_tendsto_of_tendsto herr hm
    (Eventually.of_forall (fun n => (hU n).leftMoment_ge_neg_selectionDefect (hc n)))

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
  have he := selected_right_height_tendsto hTarget hTargetBox hU
    hHausdorff hlevel hc hrate hwidth hslack
  have hpositive : horizontalLeft target < horizontalRight target := by
    unfold capWidth at hwidth
    linarith
  have hp := rightPressure_tendsto (α := α) (hαL := hαL) hHausdorff (fun n => (hU n).isCap) hTarget hlevel
    (fun n => (hU n).inBox) hpositive
  simpa only [add_zero, positivePart_sub_self] using
    (he.sub hp).add (endpointSelectionError_tendsto a b hrate)

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
  have he := selected_left_height_tendsto hTarget hTargetBox hU
    hHausdorff hlevel hc hrate hwidth hslack
  have hpositive : horizontalLeft target < horizontalRight target := by
    unfold capWidth at hwidth
    linarith
  have hp := leftPressure_tendsto (α := α) (hαL := hαL) hHausdorff (fun n => (hU n).isCap) hTarget hlevel
    (fun n => (hU n).inBox) hpositive
  simpa only [add_zero, positivePart_sub_self] using
    (he.sub hp).add (endpointSelectionError_tendsto a b hrate)

theorem rightMoment_limit_le_neg_pressure {target : Set Plane} {U : ℕ → Set Plane}
    {a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : horizontalRight target < b)
    {m : ℝ} (hm : Tendsto (fun n => finiteRightMoment (U n)
      (normal α (dyadic (level n))) (pairList α (dyadic (level n))) (some (terminalIndex α hαL (dyadic (level n))))) atTop (𝓝 m)) :
    m ≤ max (-partialRightEndpointPressure target α) 0 := by
  apply le_of_tendsto_of_tendsto hm
    (rightErosionUpperBound_tendsto hTarget hTargetBox hU hHausdorff hlevel hc hrate hwidth hslack)
  have hW := (hHausdorff.capWidth_tendsto (fun n => (hU n).isCap) hTarget).eventually
    (Ioi_mem_nhds hwidth)
  filter_upwards [hW] with n hn
  exact (hU n).right_erosion_bound hTarget hTargetBox (hc n) hn.le

theorem leftMoment_limit_le_neg_pressure {target : Set Plane} {U : ℕ → Set Plane}
    {a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : a < horizontalLeft target)
    {m : ℝ} (hm : Tendsto (fun n => finiteLeftMoment (U n)
      (normal α (dyadic (level n))) (pairList α (dyadic (level n))) (some (terminalIndex α hαL (dyadic (level n))))) atTop (𝓝 m)) :
    m ≤ max (-partialLeftEndpointPressure target α) 0 := by
  apply le_of_tendsto_of_tendsto hm
    (leftErosionUpperBound_tendsto hTarget hTargetBox hU hHausdorff hlevel hc hrate hwidth hslack)
  have hW := (hHausdorff.capWidth_tendsto (fun n => (hU n).isCap) hTarget).eventually
    (Ioi_mem_nhds hwidth)
  filter_upwards [hW] with n hn
  exact (hU n).left_erosion_bound hTarget hTargetBox (hc n) hn.le

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
  have hlower : Tendsto
      (fun n => -(∑ j, selectionDefect target (U n) α (level n) (coefficient n) j))
      atTop (𝓝 0) := by
    simpa only [neg_zero] using
      (selectionDefect_sum_tendsto (α := α) hTarget (fun n => (hU n).isCap)
        (level := level) hc hrate hHausdorff).neg
  have hupper := rightErosionUpperBound_tendsto hTarget hTargetBox hU
    hHausdorff hlevel hc hrate hwidth hslack
  rw [max_eq_right (neg_nonpos.mpr hpressure)] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    (Eventually.of_forall (fun n => (hU n).rightMoment_ge_neg_selectionDefect (hc n)))
  have hW := (hHausdorff.capWidth_tendsto (fun n => (hU n).isCap) hTarget).eventually
    (Ioi_mem_nhds hwidth)
  filter_upwards [hW] with n hn
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
  have hlower : Tendsto
      (fun n => -(∑ j, selectionDefect target (U n) α (level n) (coefficient n) j))
      atTop (𝓝 0) := by
    simpa only [neg_zero] using
      (selectionDefect_sum_tendsto (α := α) hTarget (fun n => (hU n).isCap)
        (level := level) hc hrate hHausdorff).neg
  have hupper := leftErosionUpperBound_tendsto hTarget hTargetBox hU
    hHausdorff hlevel hc hrate hwidth hslack
  rw [max_eq_right (neg_nonpos.mpr hpressure)] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    (Eventually.of_forall (fun n => (hU n).leftMoment_ge_neg_selectionDefect (hc n)))
  have hW := (hHausdorff.capWidth_tendsto (fun n => (hU n).isCap) hTarget).eventually
    (Ioi_mem_nhds hwidth)
  filter_upwards [hW] with n hn
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
  have hpositive : horizontalLeft target < horizontalRight target := by
    unfold capWidth at hwidth
    linarith
  have heR := selected_right_height_tendsto hTarget hTargetBox hU
    hHausdorff hlevel hc hrate hwidth hright
  have heL := selected_left_height_tendsto hTarget hTargetBox hU
    hHausdorff hlevel hc hrate hwidth hleft
  have hpR := rightPressure_tendsto (α := α) (hαL := hαL) hHausdorff (fun n => (hU n).isCap) hTarget hlevel
    (fun n => (hU n).inBox) hpositive
  have hpL := leftPressure_tendsto (α := α) (hαL := hαL) hHausdorff (fun n => (hU n).isCap) hTarget hlevel
    (fun n => (hU n).inBox) hpositive
  have hlim := (heR.sub hpR).sub (heL.sub hpL)
  have hbalance (n : ℕ) := finite_erosion_moment_balance (hU n).isCap
    (normal α (dyadic (level n))) (normal_snd_pos α (dyadic (level n)))
    (wallSlopes_injective α (dyadic (level n))) (hU n).polygon_eq
    (pairList α (dyadic (level n))) (some (terminalIndex α hαL (dyadic (level n))))
  simpa only [hbalance, rightPressure, leftPressure, positivePart_sub_self] using hlim

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
  · have hRlim := rightMoment_tendsto_zero_of_pressure_nonneg hTarget hTargetBox hU
      hHausdorff hlevel hc hrate hwidth hright hR
    have hmaxR : max (-partialRightEndpointPressure target α) 0 = 0 :=
      max_eq_right (neg_nonpos.mpr hR)
    refine ⟨by simpa only [hmaxR] using hRlim, ?_⟩
    have hLlim := hRlim.sub hbalance
    simp only [hmaxR, zero_sub, neg_neg] at hLlim
    convert hLlim using 1
    funext n
    ring
  · have hL : 0 ≤ partialLeftEndpointPressure target α := by
      linarith [hTarget.partialEndpointPressure_sum_nonneg α, lt_of_not_ge hR]
    have hLlim := leftMoment_tendsto_zero_of_pressure_nonneg hTarget hTargetBox hU
      hHausdorff hlevel hc hrate hwidth hleft hL
    have hmaxL : max (-partialLeftEndpointPressure target α) 0 = 0 :=
      max_eq_right (neg_nonpos.mpr hL)
    refine ⟨?_, by simpa only [hmaxL] using hLlim⟩
    have hRlim := hbalance.add hLlim
    rw [hmaxL, sub_zero, add_zero] at hRlim
    convert hRlim using 1
    funext n
    ring


end PartialGrid
end AmbidextrousSofa
