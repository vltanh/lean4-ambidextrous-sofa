module

public import AmbidextrousSofa.Analysis.PartialErosionMoments
public import AmbidextrousSofa.Analysis.PartialLowHeight

@[expose] public section

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

theorem IsJointCapMaximizer.partial_endpoint_pressures_pos_of_affine
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    0 < partialRightEndpointPressure U α ∧ 0 < partialLeftEndpointPressure U α := by
  -- Both pressures are at most one: they bound limits of selected heights in the unit strip.
  have hbox : U ⊆ Icc (horizontalLeft U - 1) (horizontalRight U + 1) ×ˢ Icc (0 : ℝ) 1 :=
    fun p hp => ⟨⟨by linarith only [(hU.isCap.fst_mem_Icc hp).1],
      by linarith only [(hU.isCap.fst_mem_Icc hp).2]⟩, hU.isCap.inStrip hp⟩
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, _, hHausdorff⟩ :=
    PartialGrid.exists_selected_sequence ⟨α, hU.angle_mem⟩ hproper hU
      (by linarith [horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact]) hbox
  have hlevelTop : Tendsto level atTop atTop := tendsto_atTop_mono hlevel tendsto_id
  have hc0 : ∀ n, 0 ≤ coefficient n := fun n => (hc n).le
  have hwidth : 1 < capWidth U := one_lt_M.trans_le hU.width_bounds.1
  have hone (n : ℕ) (x : ℝ) : capRoof (V n) x ≤ 1 :=
    capRoof_le_one (hV n).isCap.isCompact (hV n).isCap.inStrip x
  have hR := le_of_tendsto (PartialGrid.selected_right_height_tendsto hU.isCap hbox hV hHausdorff
    hlevelTop hc0 hrate hwidth (lt_add_one _)) (.of_forall fun n => hone n _)
  have hL := le_of_tendsto (PartialGrid.selected_left_height_tendsto hU.isCap hbox hV hHausdorff
    hlevelTop hc0 hrate hwidth (sub_one_lt _)) (.of_forall fun n => hone n _)
  rw [max_le_iff] at hR hL
  -- The diagonal low-height exclusion then makes both pressures positive.
  have hmid := hU.middle_endpoints_gt_half_of_affine hheight haffine
  simp only [partialRightEndpointPressure, rightEndpointPressure, partialLeftEndpointPressure,
    leftEndpointPressure] at hR hL ⊢
  constructor <;> linarith [hR.1, hL.1, hmid.1, hmid.2,
    partialBarrier_nonneg U α (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4),
    partialBarrier_nonneg U α (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)]

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
  simpa only [max_eq_right (neg_nonpos.mpr h1.le), max_eq_right (neg_nonpos.mpr h2.le)] using
    erosionMoments_tendsto hTarget.isCap hTargetBox hU hHausdorff hlevel hc hrate
      (one_lt_M.trans_le hTarget.width_bounds.1) hleft hright

end PartialGrid
end AmbidextrousSofa
