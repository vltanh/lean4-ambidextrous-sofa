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
    (hU : IsSelectedPolygon target a b level coefficient U) (hc : 0 ≤ coefficient)
    (j : SourceIndex (dyadic level)) :
    -selectionDefect target U level coefficient j ≤
      finiteExposureDefect U (normal (dyadic level)) (pairList (dyadic level)) none j /
        (normal (dyadic level) j).2 := by
  classical
  let grid := dyadic level
  let l := horizontalLeft U
  let r := horizontalRight U
  let left := l + (r - l) / 4
  let right := r - (r - l) / 4
  have hcurvature := hU.curvature_atom_le hc j
  have hfull := integral_outerSource_eq_curvature_atom hU.isCap (normal grid)
    (normal_snd_pos grid) (wallSlopes_injective grid) hU.polygon_eq j
    (normal_eq_unitNormal grid j)
  change (∫ x in l..r, outerDensity U grid j x) =
    (upperCurvature U {fullAngle grid j}).toReal at hfull
  have hfirst := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerDensity U grid j l left)
    (intervalIntegrable_outerDensity U grid j left right)
  have hsecond := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerDensity U grid j l right)
    (intervalIntegrable_outerDensity U grid j right r)
  rw [finiteExposureDefect_div_eq_integrals hU.isCap]
  change -selectionDefect target U level coefficient j ≤
    (∫ x in left..right, innerDensity U grid j x) -
      (∫ x in l..left, outerDensity U grid j x) -
      (∫ x in right..r, outerDensity U grid j x)
  change (upperCurvature U {fullAngle grid j}).toReal ≤
    (∫ x in left..right, innerDensity U grid j x) +
      (∫ x in left..right, outerDensity U grid j x) +
      selectionDefect target U level coefficient j at hcurvature
  linarith

theorem IsSelectedPolygon.rightMoment_ge_neg_selectionDefect {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hc : 0 ≤ coefficient) :
    -(∑ j, selectionDefect target U level coefficient j) ≤
      finiteRightMoment U (normal (dyadic level)) (pairList (dyadic level)) none := by
  classical
  rw [finiteRightMoment_eq_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro j _
  have hdefect := hU.exposure_defect_div_ge hc j
  have hnonneg := selectionDefect_nonneg target U level hc j
  have hnormal : (normal (dyadic level) j).1 ≤ 1 := by
    rw [normal_eq_unitNormal]
    exact Real.cos_le_one _
  have hmax : max (normal (dyadic level) j).1 0 ≤ 1 := max_le hnormal zero_le_one
  have hmul := mul_le_mul_of_nonneg_right hdefect
    (le_max_right (normal (dyadic level) j).1 0)
  have herr := mul_le_mul_of_nonneg_left hmax hnonneg
  have hterm : finiteExposureDefect U (normal (dyadic level)) (pairList (dyadic level)) none j *
      (max (normal (dyadic level) j).1 0 / (normal (dyadic level) j).2) =
    (finiteExposureDefect U (normal (dyadic level)) (pairList (dyadic level)) none j /
      (normal (dyadic level) j).2) * max (normal (dyadic level) j).1 0 := by ring
  rw [hterm]
  nlinarith

theorem IsSelectedPolygon.leftMoment_ge_neg_selectionDefect {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hc : 0 ≤ coefficient) :
    -(∑ j, selectionDefect target U level coefficient j) ≤
      finiteLeftMoment U (normal (dyadic level)) (pairList (dyadic level)) none := by
  classical
  rw [finiteLeftMoment_eq_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro j _
  have hdefect := hU.exposure_defect_div_ge hc j
  have hnonneg := selectionDefect_nonneg target U level hc j
  have hnormal : -(normal (dyadic level) j).1 ≤ 1 := by
    rw [normal_eq_unitNormal]
    change -Real.cos (fullAngle (dyadic level) j) ≤ 1
    linarith [Real.neg_one_le_cos (fullAngle (dyadic level) j)]
  have hmax : max (-(normal (dyadic level) j).1) 0 ≤ 1 := max_le hnormal zero_le_one
  have hmul := mul_le_mul_of_nonneg_right hdefect
    (le_max_right (-(normal (dyadic level) j).1) 0)
  have herr := mul_le_mul_of_nonneg_left hmax hnonneg
  have hterm : finiteExposureDefect U (normal (dyadic level)) (pairList (dyadic level)) none j *
      (max (-(normal (dyadic level) j).1) 0 / (normal (dyadic level) j).2) =
    (finiteExposureDefect U (normal (dyadic level)) (pairList (dyadic level)) none j /
      (normal (dyadic level) j).2) * max (-(normal (dyadic level) j).1) 0 := by ring
  rw [hterm]
  nlinarith

theorem positivePart_sub_self (c : ℝ) : max c 0 - c = max (-c) 0 := by
  by_cases hc : 0 ≤ c
  · rw [max_eq_left hc, max_eq_right (neg_nonpos.mpr hc)]
    ring
  · have hc' : c ≤ 0 := (lt_of_not_ge hc).le
    rw [max_eq_right hc', max_eq_left (neg_nonneg.mpr hc')]
    ring

theorem rightErosionUpperBound_tendsto {target : Set Plane} {U : ℕ → Set Plane}
    {a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : horizontalRight target < b) :
    Tendsto (fun n => capRoof (U n) (horizontalRight (U n)) -
      rightPressure (U n) (dyadic (level n)) + endpointSelectionError a b (coefficient n))
      atTop (𝓝 (max (-capRightEndpointPressure target) 0)) := by
  have he := selected_right_height_tendsto hTarget hTargetBox hU
    hHausdorff hlevel hc hrate hwidth hslack
  have hpositive : horizontalLeft target < horizontalRight target := by
    unfold capWidth at hwidth
    linarith
  have hp := rightPressure_tendsto hHausdorff (fun n => (hU n).isCap) hTarget hlevel
    (fun n => (hU n).inBox) hpositive
  simpa only [add_zero, positivePart_sub_self] using
    (he.sub hp).add (endpointSelectionError_tendsto a b hrate)

theorem leftErosionUpperBound_tendsto {target : Set Plane} {U : ℕ → Set Plane}
    {a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : a < horizontalLeft target) :
    Tendsto (fun n => capRoof (U n) (horizontalLeft (U n)) -
      leftPressure (U n) (dyadic (level n)) + endpointSelectionError a b (coefficient n))
      atTop (𝓝 (max (-capLeftEndpointPressure target) 0)) := by
  have he := selected_left_height_tendsto hTarget hTargetBox hU
    hHausdorff hlevel hc hrate hwidth hslack
  have hpositive : horizontalLeft target < horizontalRight target := by
    unfold capWidth at hwidth
    linarith
  have hp := leftPressure_tendsto hHausdorff (fun n => (hU n).isCap) hTarget hlevel
    (fun n => (hU n).inBox) hpositive
  simpa only [add_zero, positivePart_sub_self] using
    (he.sub hp).add (endpointSelectionError_tendsto a b hrate)

/-- At a nonnegative pressure, the actual right erosion moment tends to
zero. Its lower estimate is supplied by the literal selected sources. -/
theorem rightMoment_tendsto_zero_of_pressure_nonneg
    {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : horizontalRight target < b)
    (hpressure : 0 ≤ capRightEndpointPressure target) :
    Tendsto (fun n => finiteRightMoment (U n) (normal (dyadic (level n)))
      (pairList (dyadic (level n))) none) atTop (𝓝 0) := by
  have hlower : Tendsto
      (fun n => -(∑ j, selectionDefect target (U n) (level n) (coefficient n) j))
      atTop (𝓝 0) := by
    simpa only [neg_zero] using
      (selectionDefect_sum_tendsto hTarget (fun n => (hU n).isCap)
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
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : a < horizontalLeft target)
    (hpressure : 0 ≤ capLeftEndpointPressure target) :
    Tendsto (fun n => finiteLeftMoment (U n) (normal (dyadic (level n)))
      (pairList (dyadic (level n))) none) atTop (𝓝 0) := by
  have hlower : Tendsto
      (fun n => -(∑ j, selectionDefect target (U n) (level n) (coefficient n) j))
      atTop (𝓝 0) := by
    simpa only [neg_zero] using
      (selectionDefect_sum_tendsto hTarget (fun n => (hU n).isCap)
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
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target)
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b) :
    Tendsto (fun n =>
      finiteRightMoment (U n) (normal (dyadic (level n))) (pairList (dyadic (level n))) none -
      finiteLeftMoment (U n) (normal (dyadic (level n))) (pairList (dyadic (level n))) none)
      atTop (𝓝 (max (-capRightEndpointPressure target) 0 -
        max (-capLeftEndpointPressure target) 0)) := by
  have hpositive : horizontalLeft target < horizontalRight target := by
    unfold capWidth at hwidth
    linarith
  have heR := selected_right_height_tendsto hTarget hTargetBox hU
    hHausdorff hlevel hc hrate hwidth hright
  have heL := selected_left_height_tendsto hTarget hTargetBox hU
    hHausdorff hlevel hc hrate hwidth hleft
  have hpR := rightPressure_tendsto hHausdorff (fun n => (hU n).isCap) hTarget hlevel
    (fun n => (hU n).inBox) hpositive
  have hpL := leftPressure_tendsto hHausdorff (fun n => (hU n).isCap) hTarget hlevel
    (fun n => (hU n).inBox) hpositive
  have hlim := (heR.sub hpR).sub (heL.sub hpL)
  have hbalance (n : ℕ) := finite_erosion_moment_balance (hU n).isCap
    (normal (dyadic (level n))) (normal_snd_pos (dyadic (level n)))
    (wallSlopes_injective (dyadic (level n))) (hU n).polygon_eq
    (pairList (dyadic (level n))) none
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
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target)
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b) :
    Tendsto (fun n => finiteRightMoment (U n) (normal (dyadic (level n)))
      (pairList (dyadic (level n))) none) atTop (𝓝 (max (-capRightEndpointPressure target) 0)) ∧
    Tendsto (fun n => finiteLeftMoment (U n) (normal (dyadic (level n)))
      (pairList (dyadic (level n))) none) atTop (𝓝 (max (-capLeftEndpointPressure target) 0)) := by
  have hbalance := erosionMoment_difference_tendsto hTarget hTargetBox hU
    hHausdorff hlevel hc hrate hwidth hleft hright
  by_cases hR : 0 ≤ capRightEndpointPressure target
  · have hRlim := rightMoment_tendsto_zero_of_pressure_nonneg hTarget hTargetBox hU
      hHausdorff hlevel hc hrate hwidth hright hR
    have hmaxR : max (-capRightEndpointPressure target) 0 = 0 :=
      max_eq_right (neg_nonpos.mpr hR)
    refine ⟨by simpa only [hmaxR] using hRlim, ?_⟩
    have hLlim := hRlim.sub hbalance
    simp only [hmaxR, zero_sub, neg_neg] at hLlim
    convert hLlim using 1
    funext n
    ring
  · have hL : 0 ≤ capLeftEndpointPressure target := by
      linarith [hTarget.capEndpointPressure_sum_nonneg, lt_of_not_ge hR]
    have hLlim := leftMoment_tendsto_zero_of_pressure_nonneg hTarget hTargetBox hU
      hHausdorff hlevel hc hrate hwidth hleft hL
    have hmaxL : max (-capLeftEndpointPressure target) 0 = 0 :=
      max_eq_right (neg_nonpos.mpr hL)
    refine ⟨?_, by simpa only [hmaxL] using hLlim⟩
    have hRlim := hbalance.add hLlim
    rw [hmaxL, sub_zero, add_zero] at hRlim
    convert hRlim using 1
    funext n
    ring

end AngularGrid

end AmbidextrousSofa
