module

public import AmbidextrousSofa.Analysis.ExactEstimates

@[expose] public section

/-!
# Exact scalar estimates for the initial-angle relaxation

The three-support calculation has an explicit stationary value. This file
optimizes that value in the width and cotangent parameters, retaining the
exact square-root endpoint and its rational margin below the reference
constant. The square-root comparison uses squared inequalities, so no
derivative or numerical optimization is required.

The preliminary width estimates and two quadratic variation inequalities
are also proved here. The comparison of the actual finite-support integral
with its stationary value is a separate obligation; it is not assumed as
a scalar certificate in this file.
-/

noncomputable section

namespace AmbidextrousSofa

def initialAngleStationaryValue (K C k d : ℝ) : ℝ :=
  2 * C - 2 * (C - K / 2) ^ 2 - k * K * (C - d / 2)

/-- Unrestricted optimization in `C` gives the exact strict margin. -/
theorem initialAngle_stationary_lt_rational {C k d s : ℝ}
    (hk0 : 3 / 8 ≤ k) (hk1 : k ≤ 4 / 5) (hs0 : 0 ≤ s)
    (hs2 : s ^ 2 = 1 + k ^ 2) (hkd : k * d = s - 1) :
    initialAngleStationaryValue (Real.sqrt 2 - 1) C k d < (5259 / 6400 : ℝ) := by
  obtain ⟨hK0, -, hK1⟩ := sqrt_two_sub_one_bounds
  have hK := sqrt_two_sub_one_quadratic
  have hr0 : (8 : ℝ) ≤ √73 := Real.le_sqrt_of_sq_le (by norm_num)
  have hr1 : √(73 : ℝ) < 171 / 20 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hr2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 73)
  generalize Real.sqrt 2 - 1 = K at *
  -- A secant bound for `s = √(1 + k²)` on `[3/8, 4/5]`.
  have hs : s ≤ √73 / 8 + 4 / 5 * (k - 3 / 8) := by
    refine (sq_le_sq₀ hs0 (by linarith)).mp ?_
    linarith only [hr2, hs2, mul_nonneg (sub_nonneg.2 hk0)
      (show 0 ≤ √73 / 5 - 3 / 4 - 9 / 25 * (k - 3 / 8) by linarith)]
  -- Complete the square in `C`, move `k` to `3/8`, and evaluate the endpoint.
  unfold initialAngleStationaryValue
  linarith [sq_nonneg (C - (1 / 2 + K * (2 - k) / 4)), congrArg (k * ·) hK,
    congrArg (K * ·) hkd, congrArg ((k - 3 / 8) * ·) hK,
    mul_le_mul_of_nonneg_left hs (by linarith : (0 : ℝ) ≤ K),
    mul_nonneg (sq_nonneg K) (mul_nonneg (sub_nonneg.2 hk0) (by linarith : (0 : ℝ) ≤ 49 / 40 - k)),
    mul_nonneg (sub_nonneg.2 hk0) (by linarith : (0 : ℝ) ≤ 3 - 5 * K),
    mul_pos (sub_pos.2 hK1) (by positivity : (0 : ℝ) < 167 + 16 * √73)]

theorem initialAngle_rational_lt_half_M : (5259 / 6400 : ℝ) < M / 2 := by
  have hY : (149 / 500 : ℝ) < Y := by
    apply cubic_strictMono.lt_iff_lt.mp
    rw [Y_cubic]
    norm_num [cubic]
  have hbeta : (149 / 500 : ℝ) - (149 / 500 : ℝ) ^ 3 / 3 < beta :=
    (self_sub_cube_div_three_le_arctan (by norm_num)).trans_lt (Real.arctan_lt_arctan_iff.mpr hY)
  unfold M
  linarith [mul_pos (sub_pos.2 hY) (show 0 < Y + 149 / 500 by linarith [Y_pos])]

/-- The diagonal stationary value is below `41/50` for the entire small-width range. -/
theorem initialAngle_diagonal_small_width {C : ℝ} (hC : C ≤ 49 / 100) :
    2 * C - 2 * (C - (Real.sqrt 2 - 1) / 2) ^ 2 < (41 / 50 : ℝ) := by
  obtain ⟨hK0, -, hK1⟩ := sqrt_two_sub_one_bounds
  have hK := sqrt_two_sub_one_quadratic
  generalize Real.sqrt 2 - 1 = K at *
  linarith [mul_pos (show 0 < 49 / 50 - K - 2 / 5 * (1 + K) by linarith)
      (show 0 < 49 / 50 - K + 2 / 5 * (1 + K) by linarith),
    mul_nonneg (show 0 ≤ 49 / 100 - C by linarith)
      (show 0 ≤ 2 + 2 * K - 2 * (49 / 100 + C) by linarith)]

/-- The complement of the two calibration regions has a fixed strict margin. -/
theorem initialAngle_complement_bound {K C h : ℝ}
    (hK : K ^ 2 + 2 * K = 1) (hgap : 9 / 20 < h - C) :
    2 * C - 2 * C ^ 2 + 2 * K * C - (h - C) ^ 2 < (319 / 400 : ℝ) := by
  linarith [sq_nonneg (2 * C - 1 - K), mul_pos (sub_pos.mpr hgap)
    (show 0 < h - C + 9 / 20 by linarith)]

/-- The two wall crossings jointly pay the negative tent-apex quadratic. -/
theorem initialAngle_apex_variation_budget {k ξ η ζ : ℝ}
    (hk0 : -1 < k) (hk1 : k < 1) :
    (ξ - η) ^ 2 / 2 ≤ (ξ - k * ζ) ^ 2 / (1 - k) +
      (η - k * ζ) ^ 2 / (1 + k) := by
  have hm : 0 < 1 - k := by linarith
  have hp : 0 < 1 + k := by linarith
  rw [div_add_div _ _ hm.ne' hp.ne', div_le_div_iff₀ two_pos (mul_pos hm hp)]
  linarith [sq_nonneg ((1 + k) * (ξ - k * ζ) + (1 - k) * (η - k * ζ))]

end AmbidextrousSofa
