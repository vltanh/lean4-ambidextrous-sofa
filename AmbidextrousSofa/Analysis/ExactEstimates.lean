import AmbidextrousSofa.ExactConstant

/-!
# Exact rational cuts below the reference constant

These inequalities use a polynomial lower bound for arctangent and the exact
cubic equation. They provide the strict margins needed to discard small-area
motion cases; no floating-point comparison is used.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem self_sub_cube_div_three_le_arctan {y : ℝ} (hy : 0 ≤ y) :
    y - y ^ 3 / 3 ≤ Real.arctan y := by
  have hpoly : Continuous (fun x : ℝ => 1 - x ^ 2) := by fun_prop
  have hbound := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hy
    Real.continuous_arctan.continuousOn
    (fun x _ => (Real.hasDerivAt_arctan x).hasDerivWithinAt)
    (hpoly.integrableOn_Icc)
    (fun x _ => show 1 - x ^ 2 ≤ 1 / (1 + x ^ 2) from by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + x ^ 2)).2
      nlinarith [sq_nonneg (x ^ 2)])
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((continuous_id.pow 2).intervalIntegrable 0 y),
    intervalIntegral.integral_const, integral_pow, Real.arctan_zero] at hbound
  simpa only [sub_zero, zero_pow (by norm_num : 3 ≠ 0), smul_eq_mul, mul_one,
    Nat.cast_ofNat] using hbound

/-- The cubic lower estimate is already strong enough to cross `8/5`. -/
theorem eight_fifths_lt_M : (8 / 5 : ℝ) < M := by
  have hbeta : Y - Y ^ 3 / 3 ≤ beta := self_sub_cube_div_three_le_arctan Y_pos.le
  have hYsq := mul_pos (sub_pos.mpr two_sevenths_lt_Y)
    (show 0 < Y + 2 / 7 by linarith [Y_pos])
  unfold M
  nlinarith [Y_equation, two_sevenths_lt_Y]

theorem sqrt_two_lt_M : Real.sqrt 2 < M := by
  have hsqrt : Real.sqrt (2 : ℝ) < 8 / 5 :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  exact hsqrt.trans eight_fifths_lt_M

end AmbidextrousSofa
