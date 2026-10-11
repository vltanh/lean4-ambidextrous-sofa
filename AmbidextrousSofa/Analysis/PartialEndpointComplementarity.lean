module

public import AmbidextrousSofa.Analysis.PartialAxisHeightLimit
public import AmbidextrousSofa.Analysis.PartialEndpointPositivity

@[expose] public section

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

theorem IsJointCapMaximizer.partial_endpoint_heights_eq_pressures_of_affine
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    capRoof U (horizontalRight U) = partialRightEndpointPressure U α ∧
      capRoof U (horizontalLeft U) = partialLeftEndpointPressure U α := by
  have hbox : U ⊆ Icc (horizontalLeft U - 1) (horizontalRight U + 1) ×ˢ Icc (0 : ℝ) 1 :=
    fun p hp => ⟨⟨by linarith only [(hU.isCap.fst_mem_Icc hp).1],
      by linarith only [(hU.isCap.fst_mem_Icc hp).2]⟩, hU.isCap.inStrip hp⟩
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, _, hHausdorff⟩ :=
    PartialGrid.exists_selected_sequence ⟨α, hU.angle_mem⟩ hproper hU
      (by linarith [horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact]) hbox
  have hlevelTop : Tendsto level atTop atTop := tendsto_atTop_mono hlevel tendsto_id
  have hc0 : ∀ n, 0 ≤ coefficient n := fun n => (hc n).le
  have hwidth : 1 < capWidth U := one_lt_M.trans_le hU.width_bounds.1
  have hpos := hU.partial_endpoint_pressures_pos_of_affine hproper hheight haffine
  exact ⟨(PartialGrid.right_complementarity_of_height_tendsto hU.isCap hbox hV hHausdorff
      hlevelTop hc0 hrate hwidth (lt_add_one _) (PartialGrid.selected_right_height_tendsto_actual
        hU.isCap hbox hV hHausdorff hlevelTop hc0 hrate hwidth (lt_add_one _))).trans
      (max_eq_left hpos.1.le),
    (PartialGrid.left_complementarity_of_height_tendsto hU.isCap hbox hV hHausdorff
      hlevelTop hc0 hrate hwidth (sub_one_lt _) (PartialGrid.selected_left_height_tendsto_actual
        hU.isCap hbox hV hHausdorff hlevelTop hc0 hrate hwidth (sub_one_lt _))).trans
      (max_eq_left hpos.2.le)⟩

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
  obtain ⟨m, c, hmc⟩ := haffine
  obtain ⟨hR, hL⟩ := hU.partial_endpoint_heights_eq_pressures_of_affine hproper hheight
    ⟨m, c, fun x hx => hmc x (by
      rw [hl, hr, middleHalfInterval] at hx; constructor <;> linarith only [hx.1, hx.2])⟩
  simp only [partialRightEndpointPressure, rightEndpointPressure, partialLeftEndpointPressure,
    leftEndpointPressure, hl, hr, show a - (a - -a) / 4 = a / 2 by ring,
    show -a + (a - -a) / 4 = -a / 2 by ring, hleft, hright] at hR hL
  constructor <;> linarith only [hR, hL]

end AmbidextrousSofa
