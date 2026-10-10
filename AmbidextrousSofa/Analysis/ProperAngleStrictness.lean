module

public import AmbidextrousSofa.Analysis.ProperTerminalExclusion

@[expose] public section

/-!
# From full-cap affine rigidity to strict individual proper angles

The same-cap completion branch is excluded by full-cap rigidity. In
the remaining tail regime, the actual atom proof supplies the terminal
facet bound and the complete reflected-moment comparison gives the
contradiction. Centering and height/middle replacement preserve the
original angle. The final comparison below is strict against an actual
full maximizer and assumes no sharp numerical cap bound.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem IsJointCapMaximizer.false_of_centered_proper_of_full_affine_rigidity
    {U : Set Plane} {α C m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hrigid : IsFullCapMaximizer U → m = 0) : False :=
  hU.false_of_centered_proper_tail_regime
    (hU.properTailRegime_of_full_affine_rigidity hproper hheight haffine hrigid)
    hproper hl hr hheight haffine

/-- Every canonical replacement remains at the prescribed original
angle. Full-cap rigidity is used only on a same-cap negative completion. -/
theorem IsJointCapMaximizer.angle_eq_pi_div_two_of_full_affine_rigidity
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hrigid : ∀ (V : Set Plane) (m c : ℝ), IsFullCapMaximizer V → capHeight V = 1 →
      (∀ x ∈ middleHalfInterval (horizontalLeft V) (horizontalRight V),
        capRoof V x = m * x + c) → m = 0) : α = Real.pi / 2 := by
  apply le_antisymm hU.angle_mem.2
  by_contra hnot
  have hproper : α < Real.pi / 2 := lt_of_not_ge hnot
  have hcenter : IsJointCapMaximizer (centeredCap U) α :=
    hU.of_score_le hU.isCap.centeredCap hU.angle_mem (by rw [capScore_centeredCap hU.isCap])
  obtain ⟨V, hV, hproj, hheight, _, m, c, haffine⟩ := hcenter.exists_heightOne_affine_middle
  let C := capWidth U / 4
  have hl : horizontalLeft V = -2 * C := by
    calc
      _ = horizontalLeft (centeredCap U) := by unfold horizontalLeft; rw [hproj]
      _ = _ := by rw [horizontalLeft_centeredCap hU.isCap]; dsimp only [C]; ring
  have hr : horizontalRight V = 2 * C := by
    calc
      _ = horizontalRight (centeredCap U) := by unfold horizontalRight; rw [hproj]
      _ = _ := by rw [horizontalRight_centeredCap hU.isCap]; dsimp only [C]; ring
  exact hV.false_of_centered_proper_of_full_affine_rigidity hproper hl hr hheight haffine
    (fun hfull => hrigid V m c hfull hheight haffine)

end AmbidextrousSofa
