module

public import AmbidextrousSofa.Reference.Realization

@[expose] public section

/-!
# Exact contact momenta

These are the actual three-phase quantities `f' - g + 1` and `g' + f - 1`.
Their switch values and signs determine the active pieces of the reference
niche boundary. Complementary angles exchange the two momenta up to sign, so
the second inherits its zero and its signs from the first.
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

/-- Complementary angles exchange the two momenta up to sign. -/
theorem momentQ_complement (t : ℝ) : momentQ (Real.pi / 2 - t) = -momentP t := by
  rw [momentQ, momentP, referenceGD_complement, referenceF_complement]; ring

theorem one_lt_two_mul_A_mul_cosBeta : 1 < 2 * A * cosBeta := by
  rw [mul_assoc, A_mul_cosBeta, mul_one_div, lt_div_iff₀ (by linarith [Y_pos])]
  linarith [Y_lt_three_tenths]

theorem momentP_beta : momentP beta = 0 := by
  rw [momentP_phases, ite_eq_left le_rfl]
  change 1 / 2 - 2 * A * sinBeta = 0
  linarith [four_mul_A_mul_sinBeta]

theorem momentQ_lateSwitch : momentQ lateSwitch = 0 := by
  rw [lateSwitch, momentQ_complement, momentP_beta, neg_zero]

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
  rw [← sub_sub_cancel (Real.pi / 2) t, momentQ_complement, neg_nonneg]
  exact momentP_nonpos_after_beta ⟨by unfold lateSwitch at ht; linarith [ht.2], by linarith [ht.1]⟩

theorem momentQ_nonpos_late {t : ℝ} (ht : t ∈ Icc lateSwitch (Real.pi / 2)) : momentQ t ≤ 0 := by
  rw [← sub_sub_cancel (Real.pi / 2) t, momentQ_complement, neg_nonpos]
  exact momentP_nonneg_early ⟨by linarith [ht.2], by unfold lateSwitch at ht; linarith [ht.1]⟩

end AmbidextrousSofa.Reference
