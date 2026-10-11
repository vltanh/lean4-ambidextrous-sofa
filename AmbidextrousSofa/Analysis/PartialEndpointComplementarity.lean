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

end AmbidextrousSofa
