import AmbidextrousSofa.Analysis.EndpointComplementarity
import AmbidextrousSofa.Analysis.LowHeightMaximizer
import AmbidextrousSofa.Analysis.SelectedErosionMoments

/-!
# Strict endpoint stationarity for canonical full maxima

The low-middle-height exclusion and the actual endpoint complementarity
law force both endpoint pressures to be positive. A nonpositive pressure
would force the opposite axis face above the unit strip. Consequently
both endpoint heights equal their pressures, and both actual selected
erosion moments converge to zero.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AmbidextrousSofa

theorem IsFullCapMaximizer.endpoint_pressures_pos_of_middle_gt_half
    {U : Set Plane} (hU : IsFullCapMaximizer U)
    (hleft : 1 / 2 < capRoof U
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4))
    (hright : 1 / 2 < capRoof U
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)) :
    0 < capRightEndpointPressure U ∧ 0 < capLeftEndpointPressure U := by
  have hR : capRightEndpointPressure U ≤ 1 := calc
    _ ≤ max (capRightEndpointPressure U) 0 := le_max_left _ _
    _ = capRoof U (horizontalRight U) := hU.right_endpoint_complementarity.symm
    _ ≤ 1 := capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _
  have hL : capLeftEndpointPressure U ≤ 1 := calc
    _ ≤ max (capLeftEndpointPressure U) 0 := le_max_left _ _
    _ = capRoof U (horizontalLeft U) := hU.left_endpoint_complementarity.symm
    _ ≤ 1 := capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _
  have hnL := sweptNiche_nonneg U (Real.pi / 2)
    (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)
  have hnR := sweptNiche_nonneg U (Real.pi / 2)
    (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)
  unfold capRightEndpointPressure rightEndpointPressure at hR ⊢
  unfold capLeftEndpointPressure leftEndpointPressure at hL ⊢
  constructor <;> linarith

theorem IsFullCapMaximizer.endpoint_pressures_pos_of_affine
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    0 < capRightEndpointPressure U ∧ 0 < capLeftEndpointPressure U := by
  have hmid := hU.middle_endpoints_gt_half_of_affine hheight haffine
  exact hU.endpoint_pressures_pos_of_middle_gt_half hmid.1 hmid.2

theorem IsFullCapMaximizer.endpoint_heights_eq_pressures_of_affine
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    capRoof U (horizontalRight U) = capRightEndpointPressure U ∧
      capRoof U (horizontalLeft U) = capLeftEndpointPressure U := by
  have hpos := hU.endpoint_pressures_pos_of_affine hheight haffine
  simpa only [max_eq_left hpos.1.le, max_eq_left hpos.2.le] using
    hU.endpoint_complementarity

theorem IsFullCapMaximizer.endpoint_heights_pos_of_affine
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    0 < capRoof U (horizontalRight U) ∧ 0 < capRoof U (horizontalLeft U) := by
  have heq := hU.endpoint_heights_eq_pressures_of_affine hheight haffine
  rw [heq.1, heq.2]
  exact hU.endpoint_pressures_pos_of_affine hheight haffine

theorem IsFullCapMaximizer.endpoint_height_sum_of_affine
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    capRoof U (horizontalRight U) + capRoof U (horizontalLeft U) =
      ((capRoof U (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) +
        sweptNiche U (Real.pi / 2)
          (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)) +
       (capRoof U (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) +
        sweptNiche U (Real.pi / 2)
          (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4))) / 2 := by
  have heq := hU.endpoint_heights_eq_pressures_of_affine hheight haffine
  rw [heq.1, heq.2]
  exact capEndpointPressure_sum U

namespace AngularGrid

open FinitePolygon

/-- These are the literal finite moments of the selected polygons. Their
vanishing is now a consequence of full maximality and canonicalization. -/
theorem erosionMoments_tendsto_zero_of_canonical_maximum
    {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsFullCapMaximizer target)
    (hheight : capHeight target = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval
      (horizontalLeft target) (horizontalRight target), capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b) :
    Tendsto (fun n => finiteRightMoment (U n) (normal (dyadic (level n)))
      (pairList (dyadic (level n))) none) atTop (𝓝 0) ∧
    Tendsto (fun n => finiteLeftMoment (U n) (normal (dyadic (level n)))
      (pairList (dyadic (level n))) none) atTop (𝓝 0) := by
  have hpos := hTarget.endpoint_pressures_pos_of_affine hheight haffine
  have hwidth : 1 < capWidth target := one_lt_M.trans_le hTarget.width_bounds.1
  simpa only [max_eq_right (neg_nonpos.mpr hpos.1.le),
    max_eq_right (neg_nonpos.mpr hpos.2.le)] using
    erosionMoments_tendsto hTarget.isCap hTargetBox hU hHausdorff hlevel hc hrate
      hwidth hleft hright

end AngularGrid

end AmbidextrousSofa
