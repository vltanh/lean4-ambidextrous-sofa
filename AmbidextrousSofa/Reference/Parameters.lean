import AmbidextrousSofa.ExactConstant

/-!
# Exact parameters for the reference support functions

The definitions and identities here are those of MS.11--MS.12 and calibration
chapter 14 of the written manuscript. In particular, the second matching
identity is proved from the cubic equation; it is not a hypothesis.

This source is an uncompiled draft.
-/

noncomputable section

namespace AmbidextrousSofa.Reference

/-- The sine of the first switching angle. -/
def sinBeta : ℝ := Real.sin beta

/-- The cosine of the first switching angle. -/
def cosBeta : ℝ := Real.cos beta

/-- The support coefficient in the early and late phases. -/
def A : ℝ := 1 / (4 * sinBeta)

/-- The horizontal translation coefficient of the displayed reference. -/
def k : ℝ := 1 - 4 / 3 * A

/-- The angular parameter in the matching equation. -/
def T : ℝ := 3 / 2 * (Real.pi / 4 - beta)

/-- The amplitude of the middle support phase. -/
def R : ℝ := cosBeta / Real.cos T

/-- The second switching angle in the upper quarter. -/
def lateSwitch : ℝ := Real.pi / 2 - beta

theorem sinBeta_pos : 0 < sinBeta := by
  exact Real.sin_pos_of_pos_of_lt_pi beta_pos
    (by linarith [beta_lt_pi_div_two, Real.pi_pos])

theorem cosBeta_pos : 0 < cosBeta := by
  exact Real.cos_arctan_pos Y

theorem sinBeta_ne_zero : sinBeta ≠ 0 := ne_of_gt sinBeta_pos

theorem cosBeta_ne_zero : cosBeta ≠ 0 := ne_of_gt cosBeta_pos

theorem sinBeta_sq_add_cosBeta_sq : sinBeta ^ 2 + cosBeta ^ 2 = 1 := by
  exact Real.sin_sq_add_cos_sq beta

/-- A division-free version of `tan beta = Y`. -/
theorem sinBeta_eq_Y_mul_cosBeta : sinBeta = Y * cosBeta := by
  have h := tan_beta
  rw [Real.tan_eq_sin_div_cos] at h
  change sinBeta / cosBeta = Y at h
  exact (div_eq_iff cosBeta_ne_zero).mp h

theorem A_pos : 0 < A := by
  unfold A
  exact div_pos (by norm_num) (mul_pos (by norm_num) sinBeta_pos)

theorem four_mul_A_mul_sinBeta : 4 * A * sinBeta = 1 := by
  unfold A
  field_simp [sinBeta_ne_zero]

theorem A_mul_cosBeta : A * cosBeta = 1 / (4 * Y) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) Y_ne_zero)).2
  calc
    _ = 4 * A * sinBeta := by rw [sinBeta_eq_Y_mul_cosBeta]; ring
    _ = 1 := four_mul_A_mul_sinBeta

/-- The exact rational margin behind the curvature upper bound. -/
theorem A_mul_cosBeta_lt_seven_eighths : A * cosBeta < 7 / 8 := by
  rw [A_mul_cosBeta]
  apply (div_lt_iff₀ (mul_pos (by norm_num) Y_pos)).2
  linarith [two_sevenths_lt_Y]

theorem T_pos : 0 < T := by
  unfold T
  linarith [beta_lt_pi_div_four]

theorem T_lt_pi_div_two : T < Real.pi / 2 := by
  unfold T
  linarith [beta_pos, Real.pi_pos]

theorem sin_T_pos : 0 < Real.sin T := by
  exact Real.sin_pos_of_pos_of_lt_pi T_pos
    (by linarith [T_lt_pi_div_two, Real.pi_pos])

theorem cos_T_pos : 0 < Real.cos T := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · linarith [T_pos, Real.pi_pos]
  · exact T_lt_pi_div_two

theorem cos_T_ne_zero : Real.cos T ≠ 0 := ne_of_gt cos_T_pos

theorem R_pos : 0 < R := div_pos cosBeta_pos cos_T_pos

theorem beta_lt_lateSwitch : beta < lateSwitch := by
  unfold lateSwitch
  linarith [beta_lt_pi_div_four]

theorem lateSwitch_lt_pi_div_two : lateSwitch < Real.pi / 2 := by
  unfold lateSwitch
  linarith [beta_pos]

theorem lateSwitch_pos : 0 < lateSwitch := lt_trans beta_pos beta_lt_lateSwitch

/-- The immediate half of the trigonometric matching relation. -/
theorem R_mul_cos_T : R * Real.cos T = cosBeta := by
  unfold R
  exact div_mul_cancel₀ cosBeta cos_T_ne_zero

/-- Expansion of the doubled matching angle in the cubic parameter. -/
theorem sin_two_T :
    Real.sin (2 * T) = Real.sqrt 2 / 2 *
      (cosBeta ^ 3 - 3 * cosBeta * sinBeta ^ 2 +
        3 * sinBeta * cosBeta ^ 2 - sinBeta ^ 3) := by
  have hangle : 2 * T = (Real.pi / 2 + Real.pi / 4) -
      (beta + (beta + beta)) := by
    unfold T
    ring
  rw [hangle]
  simp only [Real.sin_sub, Real.sin_add, Real.cos_add, Real.sin_pi_div_two,
    Real.cos_pi_div_two, Real.sin_pi_div_four, Real.cos_pi_div_four]
  unfold sinBeta cosBeta
  ring

/-- Companion expansion of the doubled matching angle. -/
theorem cos_two_T :
    Real.cos (2 * T) = Real.sqrt 2 / 2 *
      (3 * sinBeta * cosBeta ^ 2 - sinBeta ^ 3 -
        cosBeta ^ 3 + 3 * cosBeta * sinBeta ^ 2) := by
  have hangle : 2 * T = (Real.pi / 2 + Real.pi / 4) -
      (beta + (beta + beta)) := by
    unfold T
    ring
  rw [hangle]
  simp only [Real.cos_sub, Real.sin_add, Real.cos_add, Real.sin_pi_div_two,
    Real.cos_pi_div_two, Real.sin_pi_div_four, Real.cos_pi_div_four]
  unfold sinBeta cosBeta
  ring

/-- The cubic cancels the complete doubled-angle cross-product. -/
theorem matching_cross_product :
    Real.sin (2 * T) * ((3 * Y) ^ 2 - (1 - 2 * Y ^ 2) ^ 2) -
      2 * (3 * Y) * (1 - 2 * Y ^ 2) * Real.cos (2 * T) = 0 := by
  rw [sin_two_T, cos_two_T, sinBeta_eq_Y_mul_cosBeta]
  calc
    _ = (Real.sqrt 2 / 2 * cosBeta ^ 3 * (1 + Y ^ 2) ^ 2) *
        (4 * Y ^ 3 + 3 * Y - 1) := by ring
    _ = 0 := by
      rw [show 4 * Y ^ 3 + 3 * Y - 1 = 0 by linarith [Y_equation]]
      ring

/-- Positivity selects the correct factor, without a tangent branch assumption. -/
theorem three_Y_mul_sin_T :
    3 * Y * Real.sin T = (1 - 2 * Y ^ 2) * Real.cos T := by
  have hcoef : 0 < 1 - 2 * Y ^ 2 := by
    have hproduct := mul_pos (sub_pos.mpr Y_lt_three_tenths)
      (show 0 < (3 / 10 : ℝ) + Y by linarith [Y_pos])
    nlinarith [hproduct]
  have hpositive : 0 <
      3 * Y * Real.cos T + (1 - 2 * Y ^ 2) * Real.sin T := by
    exact add_pos (mul_pos (mul_pos (by norm_num) Y_pos) cos_T_pos)
      (mul_pos hcoef sin_T_pos)
  have hsin : Real.sin (2 * T) = 2 * Real.sin T * Real.cos T := by
    rw [two_mul, Real.sin_add]
    ring
  have hcos : Real.cos (2 * T) = Real.cos T ^ 2 - Real.sin T ^ 2 := by
    rw [two_mul, Real.cos_add]
    ring
  have hprod :
      (3 * Y * Real.sin T - (1 - 2 * Y ^ 2) * Real.cos T) *
        (3 * Y * Real.cos T + (1 - 2 * Y ^ 2) * Real.sin T) = 0 := by
    calc
      _ = (Real.sin (2 * T) * ((3 * Y) ^ 2 - (1 - 2 * Y ^ 2) ^ 2) -
          2 * (3 * Y) * (1 - 2 * Y ^ 2) * Real.cos (2 * T)) / 2 := by
        rw [hsin, hcos]
        ring
      _ = 0 := by rw [matching_cross_product]; ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (ne_of_gt hpositive))

/-- The nontrivial half of MS.12, proved from the root equation. -/
theorem R_mul_sin_T : R * Real.sin T = 1 / (3 * sinBeta) - sinBeta := by
  have hscaled : 3 * Y * (R * Real.sin T) = (1 - 2 * Y ^ 2) * cosBeta := by
    calc
      _ = R * (3 * Y * Real.sin T) := by ring
      _ = R * ((1 - 2 * Y ^ 2) * Real.cos T) := by rw [three_Y_mul_sin_T]
      _ = (1 - 2 * Y ^ 2) * (R * Real.cos T) := by ring
      _ = (1 - 2 * Y ^ 2) * cosBeta := by rw [R_mul_cos_T]
  have hsum : 3 * sinBeta * (R * Real.sin T + sinBeta) = 1 := by
    calc
      _ = cosBeta * (3 * Y * (R * Real.sin T)) + 3 * sinBeta ^ 2 := by
        rw [sinBeta_eq_Y_mul_cosBeta]
        ring
      _ = cosBeta * ((1 - 2 * Y ^ 2) * cosBeta) + 3 * sinBeta ^ 2 := by
        rw [hscaled]
      _ = cosBeta ^ 2 + sinBeta ^ 2 := by
        rw [sinBeta_eq_Y_mul_cosBeta]
        ring
      _ = 1 := by linarith [sinBeta_sq_add_cosBeta_sq]
  apply (eq_sub_iff_add_eq).2
  apply (eq_div_iff (mul_ne_zero (by norm_num) sinBeta_ne_zero)).2
  nlinarith [hsum]

/-- The middle phase evaluated at the first switch has this cosine component. -/
theorem R_mul_cos_firstPhase :
    R * Real.cos (beta / 2 + Real.pi / 8) = (1 - k) * cosBeta := by
  have hangle : beta / 2 + Real.pi / 8 = Real.pi / 2 - (T + beta) := by
    unfold T
    ring
  rw [hangle, Real.cos_pi_div_two_sub, Real.sin_add]
  calc
    _ = (R * Real.sin T) * cosBeta + (R * Real.cos T) * sinBeta := by
      unfold cosBeta sinBeta
      ring
    _ = (1 / (3 * sinBeta) - sinBeta) * cosBeta + cosBeta * sinBeta := by
      rw [R_mul_sin_T, R_mul_cos_T]
    _ = (1 - k) * cosBeta := by
      unfold k A
      field_simp [sinBeta_ne_zero]
      <;> ring

/-- Companion sine component at the first switch. -/
theorem R_mul_sin_firstPhase :
    R * Real.sin (beta / 2 + Real.pi / 8) = 2 / 3 := by
  have hangle : beta / 2 + Real.pi / 8 = Real.pi / 2 - (T + beta) := by
    unfold T
    ring
  rw [hangle, Real.sin_pi_div_two_sub, Real.cos_add]
  calc
    _ = (R * Real.cos T) * cosBeta - (R * Real.sin T) * sinBeta := by
      unfold cosBeta sinBeta
      ring
    _ = cosBeta ^ 2 - (1 / (3 * sinBeta) - sinBeta) * sinBeta := by
      rw [R_mul_cos_T, R_mul_sin_T]
      ring
    _ = 2 / 3 := by
      have hcancel : 1 / (3 * sinBeta) * sinBeta = (1 / 3 : ℝ) := by
        field_simp [sinBeta_ne_zero]
      rw [sub_mul, hcancel]
      nlinarith [sinBeta_sq_add_cosBeta_sq]

end AmbidextrousSofa.Reference
