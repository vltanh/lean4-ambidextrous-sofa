module

public import AmbidextrousSofa.Analysis.FullCapRigidity
public import AmbidextrousSofa.Analysis.ProperAngleStrictness

@[expose] public section

/-!
# Individual-angle strictness and sharp cap equality

Full-cap affine rigidity rules out the same-cap completed negative
branch. The terminal atom and reflected-moment argument excludes every
remaining proper branch for each individual cap. Thus every joint
maximum has the full angle and is a horizontal reference translate.
The universal non-strict bound is independent of this module.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

/-- The angle is that of this prescribed joint maximum. No selection of
a different maximum or a largest maximizing angle occurs here. -/
theorem IsJointCapMaximizer.angle_eq_pi_div_two
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) : α = Real.pi / 2 :=
  hU.angle_eq_pi_div_two_of_full_affine_rigidity fun _ _ _ hV => hV.affine_middle_slope_eq_zero

theorem IsJointCapMaximizer.isFullCapMaximizer
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) : IsFullCapMaximizer U := by
  obtain rfl := hU.angle_eq_pi_div_two
  exact ⟨hU.isCap, fun V hV => hU.score_le hV ⟨by linarith only [Real.pi_pos], le_rfl⟩⟩

theorem IsJointCapMaximizer.eq_reference_translate
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) :
    ∃ b : ℝ, U = horizontalTranslate Reference.referenceCap b :=
  hU.isFullCapMaximizer.eq_reference_translate

theorem IsDownwardCap.capScore_eq_half_M_iff
    {U : Set Plane} (hU : IsDownwardCap U) {α : ℝ}
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 2)) :
    capScore U α = M / 2 ↔ α = Real.pi / 2 ∧
      ∃ b : ℝ, U = AmbidextrousSofa.horizontalTranslate Reference.referenceCap b := by
  refine ⟨fun hscore => ?_, fun ⟨hα, b, hb⟩ => ?_⟩
  · obtain ⟨V, hV, _⟩ := exists_fullCapMaximizer
    have hmax := hV.isJointCapMaximizer.of_score_le hU hα
      (hV.capScore_eq_half_M.trans hscore.symm).le
    exact ⟨hmax.angle_eq_pi_div_two, hmax.eq_reference_translate⟩
  · rw [hα, hb, capScore_horizontalTranslate Reference.isDownwardCap_referenceCap,
      Reference.capScore_referenceCap]

end AmbidextrousSofa
