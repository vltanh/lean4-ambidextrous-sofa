module

public import AmbidextrousSofa.Analysis.PartialAxisHeightLimit
public import AmbidextrousSofa.Analysis.PartialErosionMoments
public import AmbidextrousSofa.Analysis.PartialLowHeight

@[expose] public section

/-!
# Positive actual proper endpoint pressures and vanishing erosion

The literal proper selected sequence is constructed inside the proof.
Both endpoint heights converge to the target heights by the punctured
axis estimates, and to the positive parts of the actual partial pressures
by the finite endpoint variations. The diagonal low-height exclusion then
makes both pressures positive. Consequently both actual selected erosion
moments tend to zero, with the terminal wall retained.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AmbidextrousSofa

theorem IsJointCapMaximizer.partial_endpoint_complementarity {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) (hproper : α < Real.pi / 2) :
    capRoof U (horizontalRight U) = max (partialRightEndpointPressure U α) 0 ∧
      capRoof U (horizontalLeft U) = max (partialLeftEndpointPressure U α) 0 := by
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, hH⟩ :=
    hU.exists_selected_polygons hproper
  have hwidth : 1 < capWidth U := one_lt_M.trans_le hU.width_bounds.1
  have hS := PartialGrid.selectedLimit hU.isCap hU.isCap.subset_slack_box hV hH hlevel hc hrate
    hwidth
  exact ⟨tendsto_nhds_unique (PartialGrid.selected_right_height_tendsto_actual hU.isCap
      hU.isCap.subset_slack_box hV hH hlevel hc hrate hwidth (lt_add_one _))
      (hS.right_height_tendsto (lt_add_one _)),
    tendsto_nhds_unique (PartialGrid.selected_left_height_tendsto_actual hU.isCap
      hU.isCap.subset_slack_box hV hH hlevel hc hrate hwidth (sub_one_lt _))
      (hS.left_height_tendsto (sub_one_lt _))⟩

theorem IsJointCapMaximizer.partial_endpoint_pressures_pos_of_affine
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    0 < partialRightEndpointPressure U α ∧ 0 < partialLeftEndpointPressure U α :=
  endpointPressures_pos (partialBarrier_nonneg U α) (hU.middle_endpoints_gt_half_of_affine hheight
    haffine) ((hU.partial_endpoint_complementarity hproper).1 ▸
      capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _)
    ((hU.partial_endpoint_complementarity hproper).2 ▸
      capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _)

namespace PartialGrid

open FinitePolygon AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

theorem erosionMoments_tendsto_zero_of_canonical_maximum
    {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsJointCapMaximizer target α) (hheight : capHeight target = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval
      (horizontalLeft target) (horizontalRight target), capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b) :
    Tendsto (fun n => finiteRightMoment (U n) (normal α (dyadic (level n)))
      (pairList α (dyadic (level n))) (some (terminalIndex α hαL (dyadic (level n)))))
        atTop (𝓝 0) ∧
    Tendsto (fun n => finiteLeftMoment (U n) (normal α (dyadic (level n)))
      (pairList α (dyadic (level n))) (some (terminalIndex α hαL (dyadic (level n)))))
        atTop (𝓝 0) := by
  obtain ⟨h1, h2⟩ := hTarget.partial_endpoint_pressures_pos_of_affine hαL hheight haffine
  simp only [partialRightEndpointPressure, partialLeftEndpointPressure] at h1 h2
  simpa only [max_eq_right (neg_nonpos.mpr h1.le), max_eq_right (neg_nonpos.mpr h2.le)] using
    (selectedLimit hTarget.isCap hTargetBox hU hHausdorff hlevel hc hrate
      (one_lt_M.trans_le hTarget.width_bounds.1)).erosionMoments_tendsto
      (partialBarrier_nonneg _ _) (fun n => selectionDefect_nonneg target (U n) α (level n) (hc n))
      (fun n => (hU n).exposure_defect_div_ge (hc n))
      (selectionDefect_sum_tendsto hTarget.isCap (fun n => (hU n).isCap) hc hrate hHausdorff)
      hleft hright

end PartialGrid
end AmbidextrousSofa
