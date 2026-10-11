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
  rw [show lateSwitch / 2 + Real.pi / 8 = Real.pi / 2 - (beta / 2 + Real.pi / 8) by
    unfold lateSwitch; ring, Real.cos_pi_div_two_sub, R_mul_sin_firstPhase]

theorem one_lt_two_mul_A_mul_cosBeta : 1 < 2 * A * cosBeta := by
  rw [mul_assoc, A_mul_cosBeta, mul_one_div, lt_div_iff₀ (by linarith [Y_pos])]
  linarith [Y_lt_three_tenths]

theorem momentP_beta : momentP beta = 0 := by
  rw [momentP_phases, ite_eq_left le_rfl]
  change 1 / 2 - 2 * A * sinBeta = 0
  linarith [four_mul_A_mul_sinBeta]

theorem momentQ_lateSwitch : momentQ lateSwitch = 0 := by
  rw [momentQ_phases, ite_eq_right (not_le.2 beta_lt_lateSwitch), ite_eq_left le_rfl]
  linarith [R_mul_cos_lastPhase]

theorem momentP_nonneg_early {t : ℝ} (ht : t ∈ Icc (0 : ℝ) beta) : 0 ≤ momentP t := by
  rw [momentP_phases, ite_eq_left ht.2]
  have hsin : Real.sin t ≤ sinBeta := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [ht.1, Real.pi_pos]) beta_lt_pi_div_two.le ht.2
  nlinarith [four_mul_A_mul_sinBeta, A_pos]

theorem momentP_nonpos_after_beta {t : ℝ} (ht : t ∈ Icc beta (Real.pi / 2)) : momentP t ≤ 0 := by
  rcases ht.1.eq_or_lt with rfl | hbeta
  · exact momentP_beta.le
  rw [momentP_phases, ite_eq_right (not_le.2 hbeta)]
  split_ifs with hmiddle
  · have hsin : Real.sin (beta / 2 + Real.pi / 8) ≤ Real.sin (t / 2 + Real.pi / 8) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [beta_pos, Real.pi_pos])
        (by linarith [ht.2, Real.pi_pos]) (by linarith)
    nlinarith [R_mul_sin_firstPhase, R_pos]
  · have hsin : cosBeta ≤ Real.sin t := by
      simpa only [lateSwitch, Real.sin_pi_div_two_sub, cosBeta] using
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [lateSwitch_pos, Real.pi_pos]) ht.2
          (not_le.1 hmiddle).le
    nlinarith [one_lt_two_mul_A_mul_cosBeta, A_pos]

theorem momentQ_nonneg_before_lateSwitch {t : ℝ} (ht : t ∈ Icc (0 : ℝ) lateSwitch) :
    0 ≤ momentQ t := by
  rw [momentQ_phases]
  by_cases hearly : t ≤ beta
  · rw [ite_eq_left hearly]
    have hcos : cosBeta ≤ Real.cos t := Real.cos_le_cos_of_nonneg_of_le_pi ht.1
      (by linarith [beta_lt_pi_div_two, Real.pi_pos]) hearly
    nlinarith [one_lt_two_mul_A_mul_cosBeta, A_pos]
  · rw [ite_eq_right hearly, ite_eq_left ht.2]
    have hcos : Real.cos (lateSwitch / 2 + Real.pi / 8) ≤ Real.cos (t / 2 + Real.pi / 8) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [ht.1, Real.pi_pos])
        (by linarith [lateSwitch_lt_pi_div_two, Real.pi_pos]) (by linarith [ht.2])
    nlinarith [R_mul_cos_lastPhase, R_pos]

theorem momentQ_nonpos_late {t : ℝ} (ht : t ∈ Icc lateSwitch (Real.pi / 2)) : momentQ t ≤ 0 := by
  rcases ht.1.eq_or_lt with rfl | hlate
  · exact momentQ_lateSwitch.le
  rw [momentQ_phases, ite_eq_right (not_le.2 (beta_lt_lateSwitch.trans hlate)),
    ite_eq_right (not_le.2 hlate)]
  have hcos : Real.cos t ≤ sinBeta := by
    simpa only [lateSwitch, Real.cos_pi_div_two_sub, sinBeta] using
      Real.cos_le_cos_of_nonneg_of_le_pi lateSwitch_pos.le (by linarith [ht.2, Real.pi_pos]) ht.1
  nlinarith [four_mul_A_mul_sinBeta, A_pos]

theorem referenceF_right_curvature_lt_one {t : ℝ}
    (_ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : referenceF t + referenceFSecond t < 1 := by
  rw [referenceF_eq_right_phases, referenceFSecond]
  split_ifs with hearly hmiddle
  · simp only [fEarly]; linarith
  · have h := curvature_fMiddle_lt_seven_eighths ⟨le_of_not_gt hearly, hmiddle.le⟩
    rw [curvature_fMiddle] at h
    simp only [fMiddle]; linarith
  · simp only [fLate]; linarith

theorem referenceG_right_curvature_lt_one {t : ℝ}
    (_ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : referenceG t + referenceGSecond t < 1 := by
  rw [referenceG_eq_right_phases, referenceGSecond]
  split_ifs with hearly hmiddle
  · simp only [gEarly]; linarith
  · have h := curvature_gMiddle_lt_seven_eighths ⟨le_of_not_gt hearly, hmiddle.le⟩
    rw [curvature_gMiddle] at h
    simp only [gMiddle]; linarith
  · simp only [gLate]; linarith

theorem referenceF_right_curvature_le_one {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : referenceF t + referenceFSecond t ≤ 1 :=
  (referenceF_right_curvature_lt_one ht).le

theorem referenceG_right_curvature_le_one {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : referenceG t + referenceGSecond t ≤ 1 :=
  (referenceG_right_curvature_lt_one ht).le

end AmbidextrousSofa.Reference
