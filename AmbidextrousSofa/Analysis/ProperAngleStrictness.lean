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

/-- All quantitative proper branches are excluded for this individual
cap. The only remaining possibility is a negative middle for which the
proved completion makes this very same cap a full maximizer. No full-cap
rigidity premise is used in this reduction. -/
theorem IsJointCapMaximizer.centered_proper_forces_negative_full_maximizer
    {U : Set Plane} {α C m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    m < 0 ∧ (affineNormalAngle m ≤ α ∨
      capRoof U (horizontalRight U - capWidth U / 4) ≤ Real.sin α) ∧
      IsFullCapMaximizer U := by
  have hm : m < 0 := by
    by_contra hnot
    have hregime : ProperTailRegime U α m := ⟨fun hn => False.elim (hnot hn)⟩
    exact hU.false_of_centered_proper_tail_regime hregime hproper hl hr hheight haffine
  have hcomplete : affineNormalAngle m ≤ α ∨
      capRoof U (horizontalRight U - capWidth U / 4) ≤ Real.sin α := by
    by_contra hnot
    have hregime : ProperTailRegime U α m := ⟨fun _ =>
      ⟨lt_of_not_ge (fun h => hnot (Or.inl h)),
        lt_of_not_ge (fun h => hnot (Or.inr h))⟩⟩
    exact hU.false_of_centered_proper_tail_regime hregime hproper hl hr hheight haffine
  have hfull := hU.full_jointMaximizer_of_negative_completion
    hproper hheight hm haffine hcomplete
  exact ⟨hm, hcomplete, hfull.isCap, fun V hV =>
    hfull.score_le hV ⟨by linarith only [Real.pi_pos], le_rfl⟩⟩

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

/-- Strict proper-angle comparison with the actual full maximum. The
universal non-strict comparison follows from the earlier value reduction;
an equality would make this individual cap an impossible proper joint
maximizer. -/
theorem IsDownwardCap.capScore_lt_full_maximum_of_proper_of_full_affine_rigidity
    {U V : Set Plane} {α : ℝ} (hU : IsDownwardCap U) (hV : IsFullCapMaximizer V)
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 2)) (hproper : α < Real.pi / 2)
    (hrigid : ∀ (W : Set Plane) (m c : ℝ), IsFullCapMaximizer W → capHeight W = 1 →
      (∀ x ∈ middleHalfInterval (horizontalLeft W) (horizontalRight W),
        capRoof W x = m * x + c) → m = 0) :
    capScore U α < capScore V (Real.pi / 2) := by
  have hmax := hV.isJointCapMaximizer
  apply lt_of_le_of_ne (hmax.score_le hU hα)
  intro hequal
  have hUmax := hmax.of_score_le hU hα hequal.ge
  exact hproper.ne (hUmax.angle_eq_pi_div_two_of_full_affine_rigidity hrigid)

end AmbidextrousSofa
