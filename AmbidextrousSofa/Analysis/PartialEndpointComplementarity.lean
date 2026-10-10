import AmbidextrousSofa.Analysis.PartialAxisHeightLimit
import AmbidextrousSofa.Analysis.PartialEndpointPositivity

/-!
# Endpoint complementarity for actual proper maxima

The literal proper selected sequence is constructed inside the proof.
Both endpoint heights converge to the target heights by the punctured
axis estimates, and to the positive parts of the actual partial pressures
by the finite endpoint variations. For a height-one affine-middle maximum
both pressures are positive, giving the exact partial endpoint identities.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AmbidextrousSofa

theorem IsJointCapMaximizer.partial_endpoint_complementarity {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) (hproper : α < Real.pi / 2) :
    capRoof U (horizontalRight U) = max (partialRightEndpointPressure U α) 0 ∧
      capRoof U (horizontalLeft U) = max (partialLeftEndpointPressure U α) 0 := by
  let a := horizontalLeft U - 1
  let b := horizontalRight U + 1
  let β : TerminalAngle := ⟨α, hU.angle_mem⟩
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hab : a ≤ b := by dsimp [a, b]; linarith only [hlr]
  have hbox : U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 := by
    intro p hp
    have hx : p.1 ∈ Icc (horizontalLeft U) (horizontalRight U) := hU.isCap.fst_mem_Icc hp
    refine ⟨⟨?_, ?_⟩, hU.isCap.inStrip hp⟩
    · dsimp [a]
      linarith only [hx.1]
    · dsimp [b]
      linarith only [hx.2]
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, _, hHausdorff⟩ :=
    PartialGrid.exists_selected_sequence β hproper hU hab hbox
  have hlevelTop : Tendsto level atTop atTop := tendsto_atTop_mono hlevel tendsto_id
  have hc0 : ∀ n, 0 ≤ coefficient n := fun n => (hc n).le
  have hwidth : 1 < capWidth U := one_lt_M.trans_le hU.width_bounds.1
  have hright : horizontalRight U < b := by dsimp [b]; linarith
  have hleft : a < horizontalLeft U := by dsimp [a]; linarith
  have hR := PartialGrid.selected_right_height_tendsto_actual hU.isCap hbox hV hHausdorff
    hlevelTop hc0 hrate hwidth hright
  have hL := PartialGrid.selected_left_height_tendsto_actual hU.isCap hbox hV hHausdorff
    hlevelTop hc0 hrate hwidth hleft
  exact ⟨PartialGrid.right_complementarity_of_height_tendsto hU.isCap hbox hV hHausdorff
      hlevelTop hc0 hrate hwidth hright hR,
    PartialGrid.left_complementarity_of_height_tendsto hU.isCap hbox hV hHausdorff
      hlevelTop hc0 hrate hwidth hleft hL⟩

theorem IsJointCapMaximizer.partial_endpoint_heights_eq_pressures_of_affine
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    capRoof U (horizontalRight U) = partialRightEndpointPressure U α ∧
      capRoof U (horizontalLeft U) = partialLeftEndpointPressure U α := by
  have hpositive := hU.partial_endpoint_pressures_pos_of_affine hproper hheight haffine
  simpa only [max_eq_left hpositive.1.le, max_eq_left hpositive.2.le] using
    hU.partial_endpoint_complementarity hproper

/-- These are the actual proper endpoint laws, with the complete
terminal first wall included in both values of `partialBarrier`. -/
theorem IsJointCapMaximizer.centered_partial_endpoint_laws {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) {a h : ℝ}
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c) :
    capRoof U a = 1 / 2 + h / 4 +
      (3 * partialBarrier U α (a / 2) - partialBarrier U α (-a / 2)) / 4 ∧
    capRoof U (-a) = 1 / 2 - 3 * h / 4 +
      (3 * partialBarrier U α (-a / 2) - partialBarrier U α (a / 2)) / 4 := by
  have hAff : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c := by
    simpa only [hl, hr, middleHalfInterval_centered] using haffine
  obtain ⟨hR, hL⟩ := hU.partial_endpoint_heights_eq_pressures_of_affine hproper hheight hAff
  unfold partialRightEndpointPressure rightEndpointPressure at hR
  unfold partialLeftEndpointPressure leftEndpointPressure at hL
  rw [hl, hr, show a - (a - -a) / 4 = a / 2 by ring,
    show -a + (a - -a) / 4 = -a / 2 by ring, hleft, hright] at hR hL
  constructor <;> linarith only [hR, hL]

end AmbidextrousSofa
