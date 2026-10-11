module

public import AmbidextrousSofa.ExactConstant

@[expose] public section

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

theorem sinBeta_pos : 0 < sinBeta :=
  Real.sin_pos_of_pos_of_lt_pi beta_pos (by linarith [beta_lt_pi_div_two, Real.pi_pos])

theorem cosBeta_pos : 0 < cosBeta := Real.cos_arctan_pos Y

theorem sinBeta_ne_zero : sinBeta ≠ 0 := sinBeta_pos.ne'

/-- A division-free version of `tan beta = Y`. -/
theorem sinBeta_eq_Y_mul_cosBeta : sinBeta = Y * cosBeta := by
  rw [← tan_beta, Real.tan_eq_sin_div_cos]
  exact (div_mul_cancel₀ _ cosBeta_pos.ne').symm

theorem A_pos : 0 < A := div_pos one_pos (mul_pos four_pos sinBeta_pos)

theorem four_mul_A_mul_sinBeta : 4 * A * sinBeta = 1 := by
  unfold A; field_simp [sinBeta_ne_zero]

theorem A_mul_cosBeta : A * cosBeta = 1 / (4 * Y) := by
  rw [A, sinBeta_eq_Y_mul_cosBeta]; field_simp [cosBeta_pos.ne', Y_ne_zero]

/-- The exact rational margin behind the curvature upper bound. -/
theorem A_mul_cosBeta_lt_seven_eighths : A * cosBeta < 7 / 8 := by
  rw [A_mul_cosBeta, div_lt_iff₀ (mul_pos four_pos Y_pos)]; linarith [two_sevenths_lt_Y]

theorem cos_T_pos : 0 < Real.cos T := by
  apply Real.cos_pos_of_mem_Ioo; unfold T
  constructor <;> linarith [beta_pos, beta_lt_pi_div_four, Real.pi_pos]

theorem R_pos : 0 < R := div_pos cosBeta_pos cos_T_pos

theorem beta_lt_lateSwitch : beta < lateSwitch := by
  unfold lateSwitch; linarith [beta_lt_pi_div_four]

theorem lateSwitch_lt_pi_div_two : lateSwitch < Real.pi / 2 := by
  unfold lateSwitch; linarith [beta_pos]

theorem lateSwitch_pos : 0 < lateSwitch := beta_pos.trans beta_lt_lateSwitch

/-- Positivity selects the correct factor, without a tangent branch assumption: the
cubic cancels the doubled-angle cross-product, where `2 * T = 3 * π / 4 - 3 * beta`. -/
theorem three_Y_mul_sin_T : 3 * Y * Real.sin T = (1 - 2 * Y ^ 2) * Real.cos T := by
  have h2T : 2 * T = Real.pi / 2 + Real.pi / 4 - (beta + (beta + beta)) := by unfold T; ring
  have hsin := congrArg Real.sin h2T
  have hcos := congrArg Real.cos h2T
  have hY : Real.sin beta = Y * Real.cos beta := sinBeta_eq_Y_mul_cosBeta
  simp only [Real.sin_two_mul, Real.cos_two_mul, Real.sin_sub, Real.cos_sub, Real.sin_add,
    Real.cos_add, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_four,
    Real.cos_pi_div_four, hY] at hsin hcos
  have hpos : 0 < 3 * Y * Real.cos T + (1 - 2 * Y ^ 2) * Real.sin T :=
    add_pos (mul_pos (mul_pos three_pos Y_pos) cos_T_pos)
      (mul_pos (by nlinarith [Y_pos, Y_lt_three_tenths]) (Real.sin_pos_of_pos_of_lt_pi
        (by unfold T; linarith [beta_lt_pi_div_four])
        (by unfold T; linarith [beta_pos, Real.pi_pos])))
  refine mul_right_cancel₀ hpos.ne' ?_
  linear_combination ((9 * Y ^ 2 - (1 - 2 * Y ^ 2) ^ 2) / 2) * hsin -
    (3 * Y * (1 - 2 * Y ^ 2)) * hcos + (3 * Y * (1 - 2 * Y ^ 2)) * Real.sin_sq_add_cos_sq T +
    (Real.sqrt 2 / 4 * Real.cos beta ^ 3 * (1 + Y ^ 2) ^ 2) * Y_equation

/-- MS.12 at the first switch, where `beta / 2 + π / 8 = π / 2 - (T + beta)`; the
nontrivial half is proved from the root equation. -/
private theorem R_mul_trig_firstPhase :
    R * Real.cos (beta / 2 + Real.pi / 8) = (1 - k) * cosBeta ∧
      R * Real.sin (beta / 2 + Real.pi / 8) = 2 / 3 := by
  have hR : R * Real.cos T = Real.cos beta := div_mul_cancel₀ _ cos_T_pos.ne'
  have hY : Real.sin beta = Y * Real.cos beta := sinBeta_eq_Y_mul_cosBeta
  have h3 := three_Y_mul_sin_T
  have hp := Real.sin_sq_add_cos_sq beta
  have hc : Real.cos beta ≠ 0 := cosBeta_pos.ne'
  rw [show beta / 2 + Real.pi / 8 = Real.pi / 2 - (T + beta) by unfold T; ring,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, Real.sin_add, Real.cos_add, k, A,
    sinBeta, cosBeta, hY]
  rw [hY] at hp
  field_simp [Y_ne_zero]
  constructor
  · linear_combination Real.cos beta * R * h3 + (1 + Y ^ 2) * Real.cos beta * hR + hp
  · linear_combination -(Real.cos beta * R) * h3 + (2 + 2 * Y ^ 2) * Real.cos beta * hR + 2 * hp

/-- The middle phase evaluated at the first switch has this cosine component. -/
theorem R_mul_cos_firstPhase :
    R * Real.cos (beta / 2 + Real.pi / 8) = (1 - k) * cosBeta := R_mul_trig_firstPhase.1

/-- Companion sine component at the first switch. -/
theorem R_mul_sin_firstPhase :
    R * Real.sin (beta / 2 + Real.pi / 8) = 2 / 3 := R_mul_trig_firstPhase.2

end AmbidextrousSofa.Reference
