module

public import AmbidextrousSofa.Analysis.EndpointComplementarity
public import AmbidextrousSofa.Analysis.LowHeightMaximizer
public import AmbidextrousSofa.Analysis.SelectedErosionMoments

@[expose] public section

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

section

variable {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
  (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
include hU hheight haffine

theorem IsFullCapMaximizer.endpoint_pressures_pos_of_affine :
    0 < capRightEndpointPressure U ∧ 0 < capLeftEndpointPressure U :=
  endpointPressures_pos (sweptNiche_nonneg U _) (hU.middle_endpoints_gt_half_of_affine hheight
    haffine) (hU.endpoint_complementarity.1 ▸ capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _)
    (hU.endpoint_complementarity.2 ▸ capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _)

theorem IsFullCapMaximizer.endpoint_heights_eq_pressures_of_affine :
    capRoof U (horizontalRight U) = capRightEndpointPressure U ∧
      capRoof U (horizontalLeft U) = capLeftEndpointPressure U := by
  obtain ⟨h1, h2⟩ := hU.endpoint_pressures_pos_of_affine hheight haffine
  simpa only [max_eq_left h1.le, max_eq_left h2.le] using hU.endpoint_complementarity

theorem IsFullCapMaximizer.endpoint_heights_pos_of_affine :
    0 < capRoof U (horizontalRight U) ∧ 0 < capRoof U (horizontalLeft U) := by
  obtain ⟨h1, h2⟩ := hU.endpoint_heights_eq_pressures_of_affine hheight haffine
  exact h1 ▸ h2 ▸ hU.endpoint_pressures_pos_of_affine hheight haffine

theorem IsFullCapMaximizer.endpoint_height_sum_of_affine :
    capRoof U (horizontalRight U) + capRoof U (horizontalLeft U) =
      ((capRoof U (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) +
        sweptNiche U (Real.pi / 2)
          (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)) +
       (capRoof U (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) +
        sweptNiche U (Real.pi / 2)
          (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4))) / 2 := by
  rw [(hU.endpoint_heights_eq_pressures_of_affine hheight haffine).1,
    (hU.endpoint_heights_eq_pressures_of_affine hheight haffine).2]
  unfold capRightEndpointPressure capLeftEndpointPressure rightEndpointPressure leftEndpointPressure
  ring

end

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
  obtain ⟨h1, h2⟩ := hTarget.endpoint_pressures_pos_of_affine hheight haffine
  simp only [capRightEndpointPressure, capLeftEndpointPressure] at h1 h2
  simpa only [max_eq_right (neg_nonpos.mpr h1.le), max_eq_right (neg_nonpos.mpr h2.le)] using
    (selectedLimit hTarget.isCap hTargetBox hU hHausdorff hlevel hc hrate
      (one_lt_M.trans_le hTarget.width_bounds.1)).erosionMoments_tendsto (sweptNiche_nonneg _ _)
      (fun n => selectionDefect_nonneg target (U n) (level n) (hc n))
      (fun n => (hU n).exposure_defect_div_ge (hc n))
      (selectionDefect_sum_tendsto hTarget.isCap (fun n => (hU n).isCap) hc hrate hHausdorff)
      hleft hright

end AngularGrid

end AmbidextrousSofa
