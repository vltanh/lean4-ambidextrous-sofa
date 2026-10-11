module

public import AmbidextrousSofa.Analysis.PartialEndpointPositivity

@[expose] public section

/-!
# Endpoint laws for actual proper maxima

Endpoint complementarity identifies both endpoint heights with the positive
parts of the actual partial pressures. For a height-one affine-middle
maximum both pressures are positive, giving the exact partial endpoint
identities, and in centered coordinates explicit laws for both heights.
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
  obtain ⟨h1, h2⟩ := hU.partial_endpoint_pressures_pos_of_affine hproper hheight haffine
  simpa only [max_eq_left h1.le, max_eq_left h2.le] using
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
  obtain ⟨m, c, hmc⟩ := haffine
  obtain ⟨hR, hL⟩ := hU.partial_endpoint_heights_eq_pressures_of_affine hproper hheight
    ⟨m, c, fun x hx => hmc x (by
      rw [hl, hr, middleHalfInterval] at hx; constructor <;> linarith only [hx.1, hx.2])⟩
  simp only [partialRightEndpointPressure, rightEndpointPressure, partialLeftEndpointPressure,
    leftEndpointPressure, hl, hr, show a - (a - -a) / 4 = a / 2 by ring,
    show -a + (a - -a) / 4 = -a / 2 by ring, hleft, hright] at hR hL
  constructor <;> linarith only [hR, hL]

end AmbidextrousSofa
