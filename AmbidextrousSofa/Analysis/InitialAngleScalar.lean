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

def initialAngleWidthValue (K k s : ℝ) : ℝ :=
  1 / 2 + K / 2 + K * s / 2 - k * (1 - K) / 2 + k ^ 2 * K ^ 2 / 8

theorem initialAngle_offset_sq :
    (Real.sqrt 2 - 1) ^ 2 + 2 * (Real.sqrt 2 - 1) = (1 : ℝ) := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem initialAngle_offset_bounds :
    (41 / 100 : ℝ) < Real.sqrt 2 - 1 ∧ Real.sqrt 2 - 1 < 29 / 70 := by
  have hroot0 := Real.sqrt_nonneg (2 : ℝ)
  have hroot2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  constructor <;> nlinarith

/-- The width error is exactly a nonnegative square. The relation `k*d=s-1`
is the natural trigonometric identity for the terminal inset. -/
theorem initialAngle_width_completion {K C k d s : ℝ}
    (hK : K ^ 2 + 2 * K = 1) (hkd : k * d = s - 1) :
    initialAngleWidthValue K k s - initialAngleStationaryValue K C k d =
      2 * (C - (1 / 2 + K * (2 - k) / 4)) ^ 2 := by
  have hKk := congrArg (fun t : ℝ => k * t) hK
  have hkdK := congrArg (fun t : ℝ => K * t) hkd
  unfold initialAngleWidthValue initialAngleStationaryValue
  nlinarith only [hKk, hkdK]

theorem initialAngle_stationary_le_width {K C k d s : ℝ}
    (hK : K ^ 2 + 2 * K = 1) (hkd : k * d = s - 1) :
    initialAngleStationaryValue K C k d ≤ initialAngleWidthValue K k s := by
  have h := initialAngle_width_completion (C := C) hK hkd
  nlinarith [sq_nonneg (C - (1 / 2 + K * (2 - k) / 4))]

/-- A secant bound sufficient for the cotangent optimization on `[3/8,4/5]`. -/
theorem initialAngle_sqrt_increment {k s : ℝ}
    (hk0 : 3 / 8 ≤ k) (hk1 : k ≤ 4 / 5) (hs0 : 0 ≤ s)
    (hs2 : s ^ 2 = 1 + k ^ 2) :
    s ≤ Real.sqrt 73 / 8 + (4 / 5) * (k - 3 / 8) := by
  have hr0 : (8 : ℝ) ≤ Real.sqrt 73 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  have hr2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 73)
  have hprod := mul_nonneg (show 0 ≤ k - 3 / 8 by linarith)
    (show 0 ≤ Real.sqrt 73 / 5 - 3 / 4 - (9 / 25) * (k - 3 / 8) by
      linarith)
  apply (sq_le_sq₀ hs0 (by linarith :
    0 ≤ Real.sqrt 73 / 8 + (4 / 5) * (k - 3 / 8))).mp
  nlinarith only [hr2, hs2, hprod]

/-- The square-root increment and the defining equation for `K` imply
that the width maximum is largest at cotangent `3/8`. -/
theorem initialAngle_width_le_left_endpoint {K k s : ℝ}
    (hK0 : 0 ≤ K) (hK1 : K ≤ 3 / 5) (hK : K ^ 2 + 2 * K = 1)
    (hk0 : 3 / 8 ≤ k) (hk1 : k ≤ 4 / 5) (hs0 : 0 ≤ s)
    (hs2 : s ^ 2 = 1 + k ^ 2) :
    initialAngleWidthValue K k s ≤
      initialAngleWidthValue K (3 / 8) (Real.sqrt 73 / 8) := by
  have hroot := mul_le_mul_of_nonneg_left
    (initialAngle_sqrt_increment hk0 hk1 hs0 hs2) hK0
  have hquad : k ^ 2 - 9 / 64 ≤ (8 / 5) * (k - 3 / 8) := by
    nlinarith [mul_nonneg (show 0 ≤ k - 3 / 8 by linarith)
      (show 0 ≤ 8 / 5 - k - 3 / 8 by linarith)]
  have hquadK := mul_le_mul_of_nonneg_left hquad (sq_nonneg K)
  have hKdiff := congrArg (fun t : ℝ => (k - 3 / 8) * t) hK
  have hnegative := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ k - 3 / 8 by linarith)
    (show 5 * K - 3 ≤ 0 by linarith)
  unfold initialAngleWidthValue
  nlinarith only [hroot, hquadK, hKdiff, hnegative]

theorem initialAngle_width_left_endpoint {K : ℝ}
    (hK : K ^ 2 + 2 * K = 1) :
    initialAngleWidthValue K (3 / 8) (Real.sqrt 73 / 8) =
      169 / 512 + K * (167 + 16 * Real.sqrt 73) / 256 := by
  unfold initialAngleWidthValue
  nlinarith only [hK]

theorem initialAngle_width_endpoint_lt_rational :
    initialAngleWidthValue (Real.sqrt 2 - 1) (3 / 8) (Real.sqrt 73 / 8) <
      (5259 / 6400 : ℝ) := by
  have hK := initialAngle_offset_bounds
  have hr : Real.sqrt (73 : ℝ) < 171 / 20 :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  have hfirst := mul_lt_mul_of_pos_right hK.2
    (by positivity : 0 < 167 + 16 * Real.sqrt (73 : ℝ))
  have hsecond := mul_lt_mul_of_pos_left
    (show 167 + 16 * Real.sqrt (73 : ℝ) < 167 + 16 * (171 / 20) by linarith)
    (by norm_num : (0 : ℝ) < 29 / 70)
  rw [initialAngle_width_left_endpoint initialAngle_offset_sq]
  nlinarith [hfirst.trans hsecond]

/-- Unrestricted optimization in `C` gives the exact strict AT margin. -/
theorem initialAngle_stationary_lt_rational {C k d s : ℝ}
    (hk0 : 3 / 8 ≤ k) (hk1 : k ≤ 4 / 5) (hs0 : 0 ≤ s)
    (hs2 : s ^ 2 = 1 + k ^ 2) (hkd : k * d = s - 1) :
    initialAngleStationaryValue (Real.sqrt 2 - 1) C k d < (5259 / 6400 : ℝ) := by
  have hK := initialAngle_offset_bounds
  calc
    _ ≤ initialAngleWidthValue (Real.sqrt 2 - 1) k s :=
      initialAngle_stationary_le_width initialAngle_offset_sq hkd
    _ ≤ initialAngleWidthValue (Real.sqrt 2 - 1) (3 / 8) (Real.sqrt 73 / 8) :=
      initialAngle_width_le_left_endpoint (by linarith) (by linarith)
        initialAngle_offset_sq hk0 hk1 hs0 hs2
    _ < (5259 / 6400 : ℝ) := initialAngle_width_endpoint_lt_rational

/-- The exact cubic root supplies a reference margin stronger than `411/500`. -/
theorem initialAngle_reference_rational_cut :
    (616648051 / 750000000 : ℝ) < M / 2 := by
  have hY : (149 / 500 : ℝ) < Y := by
    apply (cubic_strictMono.lt_iff_lt).mp
    rw [Y_cubic]
    norm_num [cubic]
  have hbeta : (149 / 500 : ℝ) - (149 / 500 : ℝ) ^ 3 / 3 < beta :=
    (self_sub_cube_div_three_le_arctan (by norm_num : (0 : ℝ) ≤ 149 / 500)).trans_lt
      (Real.arctan_lt_arctan_iff.mpr hY)
  have hYsq := mul_pos (sub_pos.mpr hY)
    (show 0 < Y + 149 / 500 by linarith [Y_pos])
  unfold M
  nlinarith only [hbeta, hYsq]

theorem four_hundred_eleven_five_hundredths_lt_half_M :
    (411 / 500 : ℝ) < M / 2 := by
  exact (by norm_num : (411 / 500 : ℝ) < 616648051 / 750000000).trans
    initialAngle_reference_rational_cut

theorem initialAngle_rational_lt_half_M : (5259 / 6400 : ℝ) < M / 2 := by
  exact (by norm_num : (5259 / 6400 : ℝ) < 411 / 500).trans
    four_hundred_eleven_five_hundredths_lt_half_M

theorem initialAngle_stationary_lt_half_M {C k d s : ℝ}
    (hk0 : 3 / 8 ≤ k) (hk1 : k ≤ 4 / 5) (hs0 : 0 ≤ s)
    (hs2 : s ^ 2 = 1 + k ^ 2) (hkd : k * d = s - 1) :
    initialAngleStationaryValue (Real.sqrt 2 - 1) C k d < M / 2 :=
  (initialAngle_stationary_lt_rational hk0 hk1 hs0 hs2 hkd).trans
    initialAngle_rational_lt_half_M

/-- The diagonal stationary value is below `41/50` for the entire small-width range. -/
theorem initialAngle_diagonal_small_width {C : ℝ} (hC : C ≤ 49 / 100) :
    2 * C - 2 * (C - (Real.sqrt 2 - 1) / 2) ^ 2 < (41 / 50 : ℝ) := by
  let K := Real.sqrt (2 : ℝ) - 1
  have hK0 : (41 / 100 : ℝ) < K := initialAngle_offset_bounds.1
  have hK1 : K < (29 / 70 : ℝ) := initialAngle_offset_bounds.2
  have hK : K ^ 2 + 2 * K = 1 := initialAngle_offset_sq
  have hgap : (2 / 5) * (1 + K) < 49 / 50 - K := by linarith
  have hgapSq := mul_pos (sub_pos.mpr hgap)
    (show 0 < (49 / 50 - K) + (2 / 5) * (1 + K) by linarith)
  have hendpoint : 49 / 50 - (49 / 50 - K) ^ 2 / 2 < (41 / 50 : ℝ) := by
    nlinarith only [hK, hgapSq]
  have hwidth := mul_nonneg (show 0 ≤ 49 / 100 - C by linarith)
    (show 0 ≤ 2 + 2 * K - 2 * (49 / 100 + C) by linarith)
  change 2 * C - 2 * (C - K / 2) ^ 2 < (41 / 50 : ℝ)
  nlinarith only [hendpoint, hwidth]

/-- The complement of the two calibration regions has a fixed strict margin. -/
theorem initialAngle_complement_bound {K C h : ℝ}
    (hK : K ^ 2 + 2 * K = 1) (hgap : 9 / 20 < h - C) :
    2 * C - 2 * C ^ 2 + 2 * K * C - (h - C) ^ 2 < (319 / 400 : ℝ) := by
  have hgapSq := mul_pos (sub_pos.mpr hgap)
    (show 0 < h - C + 9 / 20 by linarith)
  nlinarith [sq_nonneg (2 * C - 1 - K)]

/-- The outgoing-only expression has a uniform small-width bound on the
upper cotangent subinterval. -/
theorem initialAngle_outgoing_small_width {C k s : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1 / 2)
    (hk0 : 3 / 5 ≤ k) (hk1 : k ≤ 4 / 5)
    (hs0 : 0 ≤ s) (hs2 : s ^ 2 = 1 + k ^ 2) :
    (1 + s) * C - 2 * k * C ^ 2 ≤ (2 + Real.sqrt 34) / 10 := by
  have hs1 : 1 ≤ s := by
    apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) hs0).mp
    nlinarith [sq_nonneg k]
  have hkC : k * C ≤ k / 2 := by
    have h := mul_le_mul_of_nonneg_left hC1 (show 0 ≤ k by linarith)
    linarith
  have hwidth := mul_nonneg (show 0 ≤ 1 / 2 - C by linarith)
    (show 0 ≤ 1 + s - k - 2 * k * C by linarith)
  have hr0 : (3 : ℝ) ≤ Real.sqrt 34 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  have hr2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 34)
  have hroot : s ≤ k + (Real.sqrt 34 - 3) / 5 := by
    have hprod := mul_nonneg (show 0 ≤ k - 3 / 5 by linarith)
      (show 0 ≤ Real.sqrt 34 - 3 by linarith)
    apply (sq_le_sq₀ hs0 (by linarith : 0 ≤ k + (Real.sqrt 34 - 3) / 5)).mp
    nlinarith only [hr2, hs2, hprod]
  nlinarith only [hwidth, hroot]

theorem initialAngle_outgoing_small_width_endpoint :
    (2 + Real.sqrt 34) / 10 < (4 / 5 : ℝ) := by
  have hr : Real.sqrt (34 : ℝ) < 6 :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  linarith

/-- The outgoing floor crossing pays the missing diagonal-floor quadratic. -/
theorem initialAngle_outgoing_variation_budget {k ξ ζ : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) :
    ξ ^ 2 ≤ (ξ - k * ζ) ^ 2 / (1 - k) + k * ζ ^ 2 := by
  have h : ξ ^ 2 - k * ζ ^ 2 ≤ (ξ - k * ζ) ^ 2 / (1 - k) := by
    apply (le_div_iff₀ (show 0 < 1 - k by linarith)).2
    nlinarith [mul_nonneg hk0 (sq_nonneg (ξ - ζ))]
  linarith

/-- The two wall crossings jointly pay the negative tent-apex quadratic. -/
theorem initialAngle_apex_variation_budget {k ξ η ζ : ℝ}
    (hk0 : -1 < k) (hk1 : k < 1) :
    (ξ - η) ^ 2 / 2 ≤ (ξ - k * ζ) ^ 2 / (1 - k) +
      (η - k * ζ) ^ 2 / (1 + k) := by
  have hm : 0 < 1 - k := by linarith
  have hp : 0 < 1 + k := by linarith
  have hden : 0 < 1 - k ^ 2 := by nlinarith [mul_pos hm hp]
  have hfirst : ((ξ - k * ζ) ^ 2 / (1 - k)) * (1 - k ^ 2) =
      (1 + k) * (ξ - k * ζ) ^ 2 := by
    calc
      _ = (((ξ - k * ζ) ^ 2 / (1 - k)) * (1 - k)) * (1 + k) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ (ne_of_gt hm)]; ring
  have hsecond : ((η - k * ζ) ^ 2 / (1 + k)) * (1 - k ^ 2) =
      (1 - k) * (η - k * ζ) ^ 2 := by
    calc
      _ = (((η - k * ζ) ^ 2 / (1 + k)) * (1 + k)) * (1 - k) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ (ne_of_gt hp)]; ring
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  apply (mul_le_mul_iff_left₀ hden).mp
  have hnum : (ξ - η) ^ 2 * (1 - k ^ 2) ≤
      2 * ((1 + k) * (ξ - k * ζ) ^ 2 + (1 - k) * (η - k * ζ) ^ 2) := by
    nlinarith only [sq_nonneg ((1 + k) * (ξ - k * ζ) + (1 - k) * (η - k * ζ))]
  nlinarith only [hnum, hfirst, hsecond]

end AmbidextrousSofa
