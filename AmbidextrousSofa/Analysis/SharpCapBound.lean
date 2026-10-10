import AmbidextrousSofa.Analysis.FullCapRigidity
import AmbidextrousSofa.Analysis.ProperTerminalExclusion

/-!
# The sharp cap bound on the whole terminal-angle interval

An actual full maximum has the reference value by full-cap rigidity.
The proved largest-angle value reduction makes that full maximum a
joint maximum over every allowed angle. This gives the universal bound
without using the separate strictness argument for individual proper
angles.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem IsDownwardCap.capScore_le_half_M
    {U : Set Plane} (hU : IsDownwardCap U) {α : ℝ}
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 2)) : capScore U α ≤ M / 2 := by
  obtain ⟨V, hV, _⟩ := exists_fullCapMaximizer
  have hbound := hV.isJointCapMaximizer.score_le hU hα
  rwa [hV.capScore_eq_half_M] at hbound

theorem Reference.isFullCapMaximizer_referenceCap :
    IsFullCapMaximizer Reference.referenceCap := by
  refine ⟨Reference.isDownwardCap_referenceCap, ?_⟩
  intro U hU
  rw [Reference.capScore_referenceCap]
  exact hU.capScore_le_half_M ⟨by linarith only [Real.pi_pos], le_rfl⟩

theorem Reference.isJointCapMaximizer_referenceCap :
    IsJointCapMaximizer Reference.referenceCap (Real.pi / 2) :=
  Reference.isFullCapMaximizer_referenceCap.isJointCapMaximizer

end AmbidextrousSofa
