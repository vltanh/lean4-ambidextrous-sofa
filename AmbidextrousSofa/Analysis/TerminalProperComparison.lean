import AmbidextrousSofa.Analysis.TerminalActualComparison
import AmbidextrousSofa.Analysis.PartialWidthBounds

/-!
# The actual proper companion must have positive early excess

The proper width range is proved from the original maximizer's endpoint
identities and the literal symmetric three-angle comparison. It supplies
the final geometric width inputs to the actual companion moment and
terminal-margin argument. The only remaining terminal obstruction is
the analytic upper bound on the displayed weighted density excess.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsJointCapMaximizer.exists_proper_leftCompanion_density_excess_gt_of_tail_regime
    {U : Set Plane} {α m c C : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity U t)) ∧
      (∀ t, ρ t ≤ 8 * (|horizontalLeft U| + |horizontalRight U| + 1) + 24) ∧
      (∀ t ≤ max (Real.pi / 2) (affineNormalAngle m), ρ t = 0) ∧
      (upperCurvature (leftCompanionCap U (-C))).restrict (Ioo (Real.pi / 2) Real.pi) =
        (volume.restrict (Ioo (Real.pi / 2) Real.pi)).withDensity
          (fun t => ENNReal.ofReal (ρ t)) ∧
      (39 / 4400 : ℝ) * Real.cos α <
        terminalWeightedExcess (fun t => ρ (t + Real.pi / 2))
          (Real.arcsin (C - topOverhangLeft U)) := by
  have hwidth : capWidth U / 4 = C := by unfold capWidth; rw [hleft, hright]; ring
  have hC := hU.proper_quarter_width_bounds hproper
  rw [hwidth] at hC
  exact hU.exists_actual_leftCompanion_density_excess_gt_of_tail_regime hregime hproper hheight haffine
    hleft hright (by linarith only [hC.1]) hC.2.le

theorem IsJointCapMaximizer.exists_proper_leftCompanion_density_excess_gt
    {U : Set Plane} {α m c C : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity U t)) ∧
      (∀ t, ρ t ≤ 8 * (|horizontalLeft U| + |horizontalRight U| + 1) + 24) ∧
      (∀ t ≤ max (Real.pi / 2) (affineNormalAngle m), ρ t = 0) ∧
      (upperCurvature (leftCompanionCap U (-C))).restrict (Ioo (Real.pi / 2) Real.pi) =
        (volume.restrict (Ioo (Real.pi / 2) Real.pi)).withDensity
          (fun t => ENNReal.ofReal (ρ t)) ∧
      (39 / 4400 : ℝ) * Real.cos α <
        terminalWeightedExcess (fun t => ρ (t + Real.pi / 2))
          (Real.arcsin (C - topOverhangLeft U)) := by
  exact IsJointCapMaximizer.exists_proper_leftCompanion_density_excess_gt_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hproper hheight haffine) hproper hheight haffine hleft
    hright

end AmbidextrousSofa
