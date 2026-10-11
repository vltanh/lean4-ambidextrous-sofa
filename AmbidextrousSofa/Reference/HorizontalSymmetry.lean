module

public import AmbidextrousSofa.Analysis.CapNormalization
public import AmbidextrousSofa.Geometry.UpwardSupport
public import AmbidextrousSofa.Reference.Value

@[expose] public section

/-!
# Exact horizontal symmetry of the reference cap

The displayed reference is centered at the abscissa `k`. Complementary
angles exchange its two support coordinates, with the exact translation
correction `2k`. Matching at both phase joins makes the symmetry valid on
the whole closed quarter, and upward supports determine the literal cap.
-/

noncomputable section

open Set

namespace AmbidextrousSofa.Reference

theorem referenceG_complement (t : ℝ) :
    referenceG (Real.pi / 2 - t) = referenceF t - 2 * k * Real.cos t := by
  -- With right-closed phases, the switches of `referenceG` at `π / 2 - t` are those of
  -- `referenceF` at `t`.
  have h1 : Real.pi / 2 - t < beta ↔ ¬t ≤ lateSwitch := by rw [not_le, sub_lt_comm]; rfl
  have h2 : Real.pi / 2 - t < lateSwitch ↔ ¬t ≤ beta := by
    rw [not_le, sub_lt_comm, lateSwitch, sub_sub_cancel]
  simp only [referenceG_eq_right_phases, referenceF, h1, h2]
  split_ifs
  all_goals first
    | exact gLate_reflection t | exact gMiddle_reflection t
    | (exfalso; linarith [beta_lt_lateSwitch])
    | (simp only [gEarly, fLate, k, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]; ring)

theorem referenceF_complement (t : ℝ) :
    referenceF (Real.pi / 2 - t) = referenceG t + 2 * k * Real.sin t := by
  have h := referenceG_complement (Real.pi / 2 - t)
  rw [sub_sub_cancel, Real.cos_pi_div_two_sub] at h
  linarith

/-- Reflection of the actual downward reference cap is precisely its
horizontal translate by `-2k`, including all axis and top faces. -/
theorem horizontalMirror_referenceCap :
    horizontalMirror referenceCap = horizontalTranslate referenceCap (-2 * k) := by
  have hRef := isDownwardCap_referenceCap
  refine hRef.horizontalMirror.eq_of_quarter_support_eq (hRef.horizontalTranslate (-2 * k))
    (fun t ht => ?_) (fun t ht => ?_) <;>
    have hs : Real.pi / 2 - t ∈ Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
  on_goal 1 =>
    have h := angleSupport_referenceCap_eq_g hs
    rw [referenceG_complement, ← angleSupport_referenceCap_eq_f ht] at h
  on_goal 2 =>
    have h := angleSupport_referenceCap_eq_f hs
    rw [referenceF_complement, ← angleSupport_referenceCap_eq_g ht] at h
  all_goals
    simp only [support_horizontalMirror, horizontalTranslate,
      support_translate hRef.isCompact hRef.nonempty, horizontalReflection, companionNormal,
      angleSupport, unitNormal, coordDot, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two,
      Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, neg_neg] at h ⊢
    linarith

theorem eq_reference_translate_of_horizontalMirror_eq
    {U : Set Plane} {b : ℝ} (h : horizontalMirror U = horizontalTranslate referenceCap b) :
    U = horizontalTranslate referenceCap (-2 * k - b) := by
  have hinv := congrArg horizontalMirror h
  simpa only [horizontalMirror_involutive, horizontalMirror_horizontalTranslate,
    horizontalMirror_referenceCap, horizontalTranslate_add, sub_eq_add_neg] using hinv

end AmbidextrousSofa.Reference
