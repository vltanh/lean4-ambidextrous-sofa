import AmbidextrousSofa.Analysis.PartialErosionMoments
import AmbidextrousSofa.Analysis.PartialLowHeight

/-!
# Positive actual proper endpoint pressures and vanishing erosion

The actual selected endpoint heights lie in the unit strip, so their
proved limits bound both proper pressures by one. The diagonal low-height
exclusion then makes both pressures positive. Consequently both actual
selected erosion moments tend to zero, with the terminal wall retained.
No endpoint-height continuity is needed for this conclusion.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AmbidextrousSofa

theorem IsJointCapMaximizer.partial_endpoint_pressures_le_one
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2) :
    partialRightEndpointPressure U α ≤ 1 ∧ partialLeftEndpointPressure U α ≤ 1 := by
  let a := horizontalLeft U - 1
  let b := horizontalRight U + 1
  let β : TerminalAngle := ⟨α, hU.angle_mem⟩
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hbox : U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 := by
    intro p hp
    have hx : p.1 ∈ Icc (horizontalLeft U) (horizontalRight U) := by
      rw [← horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex]
      exact ⟨p, hp, rfl⟩
    refine ⟨⟨?_, ?_⟩, hU.isCap.inStrip hp⟩ <;> dsimp [a, b] <;> linarith [hx.1, hx.2]
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, _, hHausdorff⟩ :=
    PartialGrid.exists_selected_sequence β hproper hU hab hbox
  have hlevelTop : Tendsto level atTop atTop := tendsto_atTop_mono hlevel tendsto_id
  have hc0 : ∀ n, 0 ≤ coefficient n := fun n => (hc n).le
  have hwidth : 1 < capWidth U := one_lt_M.trans_le hU.width_bounds.1
  have hright : horizontalRight U < b := by dsimp [b]; linarith
  have hleft : a < horizontalLeft U := by dsimp [a]; linarith
  have hRlim := PartialGrid.selected_right_height_tendsto hU.isCap hbox hV hHausdorff
    hlevelTop hc0 hrate hwidth hright
  have hLlim := PartialGrid.selected_left_height_tendsto hU.isCap hbox hV hHausdorff
    hlevelTop hc0 hrate hwidth hleft
  have hR : max (partialRightEndpointPressure U α) 0 ≤ 1 :=
    le_of_tendsto hRlim (Eventually.of_forall (fun n =>
      capRoof_le_one (hV n).isCap.isCompact (hV n).isCap.inStrip _))
  have hL : max (partialLeftEndpointPressure U α) 0 ≤ 1 :=
    le_of_tendsto hLlim (Eventually.of_forall (fun n =>
      capRoof_le_one (hV n).isCap.isCompact (hV n).isCap.inStrip _))
  exact ⟨(le_max_left _ _).trans hR, (le_max_left _ _).trans hL⟩

theorem IsJointCapMaximizer.partial_endpoint_pressures_pos_of_middle_gt_half
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2)
    (hleft : 1 / 2 < capRoof U
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4))
    (hright : 1 / 2 < capRoof U
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)) :
    0 < partialRightEndpointPressure U α ∧ 0 < partialLeftEndpointPressure U α := by
  obtain ⟨hR, hL⟩ := hU.partial_endpoint_pressures_le_one hproper
  have hnL := partialBarrier_nonneg U α
    (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)
  have hnR := partialBarrier_nonneg U α
    (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)
  unfold partialRightEndpointPressure rightEndpointPressure at hR ⊢
  unfold partialLeftEndpointPressure leftEndpointPressure at hL ⊢
  constructor <;> linarith

theorem IsJointCapMaximizer.partial_endpoint_pressures_pos_of_affine
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    0 < partialRightEndpointPressure U α ∧ 0 < partialLeftEndpointPressure U α := by
  have hmid := hU.middle_endpoints_gt_half_of_affine hheight haffine
  exact hU.partial_endpoint_pressures_pos_of_middle_gt_half hproper hmid.1 hmid.2

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
  have hpos := hTarget.partial_endpoint_pressures_pos_of_affine hαL hheight haffine
  have hwidth : 1 < capWidth target := one_lt_M.trans_le hTarget.width_bounds.1
  simpa only [max_eq_right (neg_nonpos.mpr hpos.1.le),
    max_eq_right (neg_nonpos.mpr hpos.2.le)] using
    erosionMoments_tendsto hTarget.isCap hTargetBox hU hHausdorff hlevel hc hrate
      hwidth hleft hright

end PartialGrid
end AmbidextrousSofa
