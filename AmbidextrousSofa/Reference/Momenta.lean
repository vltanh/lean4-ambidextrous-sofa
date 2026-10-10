module

public import AmbidextrousSofa.Reference.Realization

@[expose] public section

/-!
# Exact contact momenta and unit-curvature margins

These are the actual three-phase quantities `f' - g + 1` and `g' + f - 1`.
Their switch values and signs determine the active pieces of the reference
niche boundary. The upper curvature bound is proved for the right-hand
second derivatives, including both switches.
-/

noncomputable section

open Set

namespace AmbidextrousSofa.Reference

def momentP (t : ℝ) : ℝ := referenceFD t - referenceG t + 1

def momentQ (t : ℝ) : ℝ := referenceGD t + referenceF t - 1

theorem momentP_phases (t : ℝ) :
    momentP t = if t ≤ beta then 1 / 2 - 2 * A * Real.sin t
      else if t ≤ lateSwitch then 1 - 3 / 2 * R * Real.sin (t / 2 + Real.pi / 8)
      else 1 - 2 * A * Real.sin t := by
  unfold momentP referenceFD referenceG
  split_ifs <;> simp only [fEarlyD, gEarly, fMiddleD, gMiddle, fLateD, gLate] <;> ring

theorem momentQ_phases (t : ℝ) :
    momentQ t = if t ≤ beta then 2 * A * Real.cos t - 1
      else if t ≤ lateSwitch then 3 / 2 * R * Real.cos (t / 2 + Real.pi / 8) - 1
      else 2 * A * Real.cos t - 1 / 2 := by
  unfold momentQ referenceGD referenceF
  split_ifs <;> simp only [gEarlyD, fEarly, gMiddleD, fMiddle, gLateD, fLate] <;> ring

theorem R_mul_cos_lastPhase : R * Real.cos (lateSwitch / 2 + Real.pi / 8) = 2 / 3 := by
  have hangle : lateSwitch / 2 + Real.pi / 8 = Real.pi / 2 - (beta / 2 + Real.pi / 8) := by
    unfold lateSwitch
    ring
  rw [hangle, Real.cos_pi_div_two_sub]
  exact R_mul_sin_firstPhase

theorem one_lt_two_mul_A_mul_cosBeta : 1 < 2 * A * cosBeta := by
  have hhalf : 1 / 2 < A * cosBeta := by
    rw [A_mul_cosBeta]
    apply (lt_div_iff₀ (mul_pos (by norm_num) Y_pos)).mpr
    linarith [Y_lt_three_tenths]
  linarith

theorem momentP_beta : momentP beta = 0 := by
  rw [momentP_phases, if_pos le_rfl]
  change 1 / 2 - 2 * A * sinBeta = 0
  nlinarith [four_mul_A_mul_sinBeta]

theorem momentQ_lateSwitch : momentQ lateSwitch = 0 := by
  rw [momentQ_phases, if_neg (not_le.mpr beta_lt_lateSwitch), if_pos le_rfl]
  nlinarith [R_mul_cos_lastPhase]

theorem momentP_nonneg_early {t : ℝ} (ht : t ∈ Icc (0 : ℝ) beta) : 0 ≤ momentP t := by
  rw [momentP_phases, if_pos ht.2]
  have hsin : Real.sin t ≤ sinBeta := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [ht.1, Real.pi_pos]) beta_lt_pi_div_two.le ht.2
  have hmul := mul_le_mul_of_nonneg_left hsin (show 0 ≤ 2 * A by linarith [A_pos])
  nlinarith [four_mul_A_mul_sinBeta]

theorem momentP_nonpos_after_beta {t : ℝ} (ht : t ∈ Icc beta (Real.pi / 2)) : momentP t ≤ 0 := by
  by_cases hearly : t ≤ beta
  · have heq : t = beta := le_antisymm hearly ht.1
    simp [heq, momentP_beta]
  rw [momentP_phases, if_neg hearly]
  by_cases hmiddle : t ≤ lateSwitch
  · rw [if_pos hmiddle]
    have hsin : Real.sin (beta / 2 + Real.pi / 8) ≤ Real.sin (t / 2 + Real.pi / 8) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · linarith [beta_pos, Real.pi_pos]
      · linarith [ht.2, Real.pi_pos]
      · linarith [ht.1]
    have hmul := mul_le_mul_of_nonneg_left hsin R_pos.le
    nlinarith [R_mul_sin_firstPhase]
  · rw [if_neg hmiddle]
    have hsin : cosBeta ≤ Real.sin t := by
      have h := Real.sin_le_sin_of_le_of_le_pi_div_two
        (show -(Real.pi / 2) ≤ lateSwitch by linarith [lateSwitch_pos, Real.pi_pos])
        ht.2 (le_of_lt (lt_of_not_ge hmiddle))
      simpa only [lateSwitch, Real.sin_pi_div_two_sub, cosBeta] using h
    have hmul := mul_le_mul_of_nonneg_left hsin (show 0 ≤ 2 * A by linarith [A_pos])
    nlinarith [one_lt_two_mul_A_mul_cosBeta]

theorem momentQ_nonneg_before_lateSwitch {t : ℝ} (ht : t ∈ Icc (0 : ℝ) lateSwitch) :
    0 ≤ momentQ t := by
  rw [momentQ_phases]
  by_cases hearly : t ≤ beta
  · rw [if_pos hearly]
    have hcos : cosBeta ≤ Real.cos t := Real.cos_le_cos_of_nonneg_of_le_pi ht.1
      (by linarith [beta_lt_pi_div_two, Real.pi_pos]) hearly
    have hmul := mul_le_mul_of_nonneg_left hcos (show 0 ≤ 2 * A by linarith [A_pos])
    nlinarith [one_lt_two_mul_A_mul_cosBeta]
  · rw [if_neg hearly, if_pos ht.2]
    have hcos : Real.cos (lateSwitch / 2 + Real.pi / 8) ≤ Real.cos (t / 2 + Real.pi / 8) := by
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      · linarith [ht.1, Real.pi_pos]
      · linarith [lateSwitch_lt_pi_div_two, Real.pi_pos]
      · linarith [ht.2]
    have hmul := mul_le_mul_of_nonneg_left hcos R_pos.le
    nlinarith [R_mul_cos_lastPhase]

theorem momentQ_nonpos_late {t : ℝ} (ht : t ∈ Icc lateSwitch (Real.pi / 2)) : momentQ t ≤ 0 := by
  by_cases hswitch : t = lateSwitch
  · simp [hswitch, momentQ_lateSwitch]
  have hlate : lateSwitch < t := lt_of_le_of_ne ht.1 (Ne.symm hswitch)
  rw [momentQ_phases, if_neg (not_le.mpr (beta_lt_lateSwitch.trans hlate)),
    if_neg (not_le.mpr hlate)]
  have hcos : Real.cos t ≤ sinBeta := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi lateSwitch_pos.le
      (by linarith [ht.2, Real.pi_pos]) ht.1
    simpa only [lateSwitch, Real.cos_pi_div_two_sub, sinBeta] using h
  have hmul := mul_le_mul_of_nonneg_left hcos (show 0 ≤ 2 * A by linarith [A_pos])
  nlinarith [four_mul_A_mul_sinBeta]

theorem referenceF_right_curvature_lt_one {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : referenceF t + referenceFSecond t < 1 := by
  rw [referenceF_eq_right_phases]
  unfold referenceFSecond
  split_ifs with hearly hmiddle
  · unfold fEarly
    nlinarith
  · have hbound := curvature_fMiddle_lt_seven_eighths
      ⟨(le_of_not_gt hearly), hmiddle.le⟩
    rw [curvature_fMiddle] at hbound
    unfold fMiddle
    nlinarith
  · unfold fLate
    nlinarith

theorem referenceG_right_curvature_lt_one {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : referenceG t + referenceGSecond t < 1 := by
  rw [referenceG_eq_right_phases]
  unfold referenceGSecond
  split_ifs with hearly hmiddle
  · unfold gEarly
    nlinarith
  · have hbound := curvature_gMiddle_lt_seven_eighths
      ⟨(le_of_not_gt hearly), hmiddle.le⟩
    rw [curvature_gMiddle] at hbound
    unfold gMiddle
    nlinarith
  · unfold gLate
    nlinarith

theorem referenceF_right_curvature_le_one {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : referenceF t + referenceFSecond t ≤ 1 :=
  (referenceF_right_curvature_lt_one ht).le

theorem referenceG_right_curvature_le_one {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : referenceG t + referenceGSecond t ≤ 1 :=
  (referenceG_right_curvature_lt_one ht).le

end AmbidextrousSofa.Reference
