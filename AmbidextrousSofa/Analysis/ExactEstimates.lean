module

public import AmbidextrousSofa.ExactConstant

@[expose] public section

/-!
# Exact rational cuts below the reference constant

These inequalities use a polynomial lower bound for arctangent and the exact
cubic equation. They provide the strict margins needed to discard small-area
motion cases; no floating-point comparison is used. The file also records
rational bounds on the diagonal offset `√2 - 1` and its quadratic equation.
-/

noncomputable section

namespace AmbidextrousSofa

theorem self_sub_cube_div_three_le_arctan {y : ℝ} (hy : 0 ≤ y) :
    y - y ^ 3 / 3 ≤ Real.arctan y := by
  have h := monotone_of_hasDerivAt_nonneg (fun x => (Real.hasDerivAt_arctan x).sub
    ((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 3))) fun x => by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + x ^ 2)).2
        (by nlinarith [sq_nonneg (x ^ 2)] : (1 - x ^ 2) * (1 + x ^ 2) ≤ 1)
      norm_num [← one_div]
      linarith
  simpa using h hy

/-- The cubic lower estimate is already strong enough to cross `8/5`. -/
theorem eight_fifths_lt_M : (8 / 5 : ℝ) < M := by
  unfold M
  linarith [show Y - Y ^ 3 / 3 ≤ beta from self_sub_cube_div_three_le_arctan Y_pos.le,
    Y_equation, two_sevenths_lt_Y,
    mul_pos (sub_pos.mpr two_sevenths_lt_Y) (by linarith [Y_pos] : (0 : ℝ) < Y + 2 / 7)]

theorem sqrt_two_lt_M : Real.sqrt 2 < M :=
  ((Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)).trans eight_fifths_lt_M

theorem sqrt_two_sub_one_bounds :
    (41 / 99 : ℝ) < Real.sqrt 2 - 1 ∧ Real.sqrt 2 - 1 < 169 / 408 ∧
      Real.sqrt 2 - 1 < 29 / 70 := by
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hroot := Real.sqrt_nonneg (2 : ℝ)
  exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem sqrt_two_sub_one_quadratic :
    (Real.sqrt 2 - 1) ^ 2 + 2 * (Real.sqrt 2 - 1) = (1 : ℝ) := by
  linear_combination Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)

/-- `41/50 < M/2`, the reference comparison level used by the width exclusions. -/
theorem forty_one_fiftieths_lt_half_M : (41 / 50 : ℝ) < M / 2 := by
  have hY : (19 / 64 : ℝ) < Y := cubic_strictMono.lt_iff_lt.mp (by rw [Y_cubic]; norm_num [cubic])
  unfold M beta
  linarith [Y_equation, self_sub_cube_div_three_le_arctan Y_pos.le,
    mul_pos (sub_pos.mpr hY) (show 0 < Y + 19 / 64 by linarith [Y_pos])]

end AmbidextrousSofa
