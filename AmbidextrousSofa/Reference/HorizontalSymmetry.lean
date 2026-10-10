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

theorem referenceF_eq_middle_of_mem {t : ℝ}
    (hfirst : beta ≤ t) (hlast : t ≤ lateSwitch) : referenceF t = fMiddle t := by
  by_cases ht : t ≤ beta
  · have heq : t = beta := le_antisymm ht hfirst
    subst t
    simp only [referenceF, if_pos le_rfl]
    exact f_matching_first.symm
  · simp only [referenceF, if_neg ht, if_pos hlast]

theorem referenceG_eq_middle_of_mem {t : ℝ}
    (hfirst : beta ≤ t) (hlast : t ≤ lateSwitch) : referenceG t = gMiddle t := by
  by_cases ht : t ≤ beta
  · have heq : t = beta := le_antisymm ht hfirst
    subst t
    simp only [referenceG, if_pos le_rfl]
    exact g_matching_first.symm
  · simp only [referenceG, if_neg ht, if_pos hlast]

theorem referenceF_eq_late_of_le {t : ℝ}
    (ht : lateSwitch ≤ t) : referenceF t = fLate t := by
  have hfirst : ¬t ≤ beta := not_le.mpr (beta_lt_lateSwitch.trans_le ht)
  by_cases hlast : t ≤ lateSwitch
  · have heq : t = lateSwitch := le_antisymm hlast ht
    subst t
    simp only [referenceF, if_neg hfirst, if_pos le_rfl]
    exact f_matching_last
  · simp only [referenceF, if_neg hfirst, if_neg hlast]

theorem referenceG_eq_late_of_le {t : ℝ}
    (ht : lateSwitch ≤ t) : referenceG t = gLate t := by
  have hfirst : ¬t ≤ beta := not_le.mpr (beta_lt_lateSwitch.trans_le ht)
  by_cases hlast : t ≤ lateSwitch
  · have heq : t = lateSwitch := le_antisymm hlast ht
    subst t
    simp only [referenceG, if_neg hfirst, if_pos le_rfl]
    exact g_matching_last
  · simp only [referenceG, if_neg hfirst, if_neg hlast]

theorem referenceG_complement (t : ℝ) :
    referenceG (Real.pi / 2 - t) = referenceF t - 2 * k * Real.cos t := by
  by_cases ht : t ≤ beta
  · rw [referenceG_eq_late_of_le (show lateSwitch ≤ Real.pi / 2 - t by
        dsimp only [lateSwitch]; linarith only [ht])]
    simp only [referenceF, if_pos ht]
    exact gLate_reflection t
  · by_cases hlast : t ≤ lateSwitch
    · rw [referenceF_eq_middle_of_mem (le_of_not_ge ht) hlast,
        referenceG_eq_middle_of_mem
          (show beta ≤ Real.pi / 2 - t by dsimp only [lateSwitch] at hlast; linarith only [hlast])
          (show Real.pi / 2 - t ≤ lateSwitch by
            dsimp only [lateSwitch]; linarith only [le_of_not_ge ht])]
      exact gMiddle_reflection t
    · have hs : Real.pi / 2 - t ≤ beta := by
        dsimp only [lateSwitch] at hlast
        linarith only [le_of_not_ge hlast]
      rw [referenceF_eq_late_of_le (le_of_not_ge hlast)]
      simp only [referenceG, if_pos hs]
      have h := fLate_reflection (Real.pi / 2 - t)
      rw [show Real.pi / 2 - (Real.pi / 2 - t) = t by ring,
        Real.sin_pi_div_two_sub] at h
      linarith only [h]

theorem referenceF_complement (t : ℝ) :
    referenceF (Real.pi / 2 - t) = referenceG t + 2 * k * Real.sin t := by
  have h := referenceG_complement (Real.pi / 2 - t)
  rw [show Real.pi / 2 - (Real.pi / 2 - t) = t by ring,
    Real.cos_pi_div_two_sub] at h
  linarith only [h]

/-- Reflection of the actual downward reference cap is precisely its
horizontal translate by `-2k`, including all axis and top faces. -/
theorem horizontalMirror_referenceCap :
    horizontalMirror referenceCap = horizontalTranslate referenceCap (-2 * k) := by
  have hRef := isDownwardCap_referenceCap
  apply hRef.horizontalMirror.eq_of_quarter_support_eq (hRef.horizontalTranslate (-2 * k))
  · intro t ht
    have hs : Real.pi / 2 - t ∈ Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith only [ht.2], by linarith only [ht.1]⟩
    have hnormal : horizontalReflection (unitNormal t) =
        companionNormal (Real.pi / 2 - t) := by
      simp only [horizontalReflection, unitNormal, companionNormal,
        Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    rw [support_horizontalMirror, hnormal, companionNormal_eq_unitNormal]
    change angleSupport referenceCap ((Real.pi / 2 - t) + Real.pi / 2) = _
    rw [angleSupport_referenceCap_eq_g hs, referenceG_complement,
      horizontalTranslate, support_translate hRef.isCompact hRef.nonempty]
    change referenceF t - 2 * k * Real.cos t =
      angleSupport referenceCap t + coordDot (-2 * k, 0) (unitNormal t)
    rw [angleSupport_referenceCap_eq_f ht]
    simp only [coordDot, unitNormal, zero_mul, add_zero]
    ring
  · intro t ht
    have hs : Real.pi / 2 - t ∈ Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith only [ht.2], by linarith only [ht.1]⟩
    have hnormal : horizontalReflection (companionNormal t) =
        unitNormal (Real.pi / 2 - t) := by
      simp only [horizontalReflection, unitNormal, companionNormal, neg_neg,
        Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    rw [support_horizontalMirror, hnormal]
    change angleSupport referenceCap (Real.pi / 2 - t) = _
    rw [angleSupport_referenceCap_eq_f hs, referenceF_complement,
      horizontalTranslate, support_translate hRef.isCompact hRef.nonempty]
    have hg : support referenceCap (companionNormal t) = referenceG t := by
      rw [companionNormal_eq_unitNormal]
      exact angleSupport_referenceCap_eq_g ht
    rw [hg]
    simp only [coordDot, companionNormal, zero_mul, add_zero]
    ring

theorem eq_reference_translate_of_horizontalMirror_eq
    {U : Set Plane} {b : ℝ} (h : horizontalMirror U = horizontalTranslate referenceCap b) :
    U = horizontalTranslate referenceCap (-2 * k - b) := by
  have hinv := congrArg horizontalMirror h
  simpa only [horizontalMirror_involutive, horizontalMirror_horizontalTranslate,
    horizontalMirror_referenceCap, horizontalTranslate_add, sub_eq_add_neg] using hinv

end AmbidextrousSofa.Reference
