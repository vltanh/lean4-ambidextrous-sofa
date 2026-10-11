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

/-- Every canonical replacement remains at the prescribed original
angle. Full-cap rigidity is used only on a same-cap negative completion. -/
theorem IsJointCapMaximizer.angle_eq_pi_div_two_of_full_affine_rigidity
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hrigid : ∀ (V : Set Plane) (m c : ℝ), IsFullCapMaximizer V → capHeight V = 1 →
      (∀ x ∈ middleHalfInterval (horizontalLeft V) (horizontalRight V),
        capRoof V x = m * x + c) → m = 0) : α = Real.pi / 2 := by
  refine le_antisymm hU.angle_mem.2 (not_lt.mp fun hproper => ?_)
  obtain ⟨V, hV, hproj, hheight, -, m, c, haffine⟩ := (hU.of_score_le hU.isCap.centeredCap
    hU.angle_mem (capScore_centeredCap hU.isCap α).ge).exists_heightOne_affine_middle
  have hl : horizontalLeft V = -2 * (capWidth U / 4) := (congrArg sInf hproj).trans
    (by rw [← horizontalLeft, horizontalLeft_centeredCap hU.isCap]; ring)
  have hr : horizontalRight V = 2 * (capWidth U / 4) := (congrArg sSup hproj).trans
    (by rw [← horizontalRight, horizontalRight_centeredCap hU.isCap]; ring)
  exact hV.false_of_centered_proper_tail_regime (hV.properTailRegime_of_full_affine_rigidity
    hproper hheight haffine (hrigid V m c · hheight haffine)) hproper hl hr hheight haffine

end AmbidextrousSofa
