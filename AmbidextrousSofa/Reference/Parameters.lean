module

public import AmbidextrousSofa.ExactConstant

@[expose] public section

/-!
# Exact parameters for the reference support functions

These are the parameters of the reference support functions and the identities
that match their phases. In particular, the second matching identity is proved
from the cubic equation; it is not a hypothesis.
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

/-- The cubic is the angle-matching equation in tangent coordinates. -/
theorem firstPhaseAngle_eq_arctan_two_Y :
    beta / 2 + Real.pi / 8 = Real.arctan (2 * Y) := by
  have hY1 : Y < 1 := by linarith [Y_lt_three_tenths]
  have htwo : 2 * Y < 1 := by linarith [Y_lt_three_tenths]
  have hden : 1 - (2 * Y) ^ 2 ≠ 0 := by nlinarith [Y_pos, Y_lt_three_tenths]
  have hden1 : 1 - Y * 1 ≠ 0 := by linarith
  have hquot : 2 * (2 * Y) / (1 - (2 * Y) ^ 2) = (Y + 1) / (1 - Y * 1) := by
    apply (div_eq_div_iff hden hden1).mpr
    nlinarith [Y_equation]
  have hdouble := Real.two_mul_arctan (x := 2 * Y) (by linarith [Y_pos]) htwo
  rw [hquot, ← Real.arctan_add (show Y * 1 < 1 by linarith), Real.arctan_one] at hdouble
  unfold beta
  linarith

theorem firstPhase_sin_eq_two_Y_mul_cos :
    Real.sin (beta / 2 + Real.pi / 8) = 2 * Y * Real.cos (beta / 2 + Real.pi / 8) := by
  rw [firstPhaseAngle_eq_arctan_two_Y]
  have ht := Real.tan_arctan (2 * Y)
  rw [Real.tan_eq_sin_div_cos] at ht
  exact (div_eq_iff (Real.cos_arctan_pos _).ne').mp ht

/-- Angle addition turns the matching equation into this division-free identity. -/
theorem three_Y_mul_sin_T : 3 * Y * Real.sin T = (1 - 2 * Y ^ 2) * Real.cos T := by
  have hangle : T = Real.pi / 2 - (beta + (beta / 2 + Real.pi / 8)) := by unfold T; ring
  have hY : Real.sin beta = Y * Real.cos beta := sinBeta_eq_Y_mul_cosBeta
  rw [hangle, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub,
    Real.sin_add, Real.cos_add, hY, firstPhase_sin_eq_two_Y_mul_cos]
  ring

/-- The reference phases match because `tan (beta/2+π/8) = 2Y`. -/
theorem firstSwitch_eqs :
    R * Real.cos (beta / 2 + Real.pi / 8) = 4 / 3 * A * Real.cos beta ∧
      R * Real.sin (beta / 2 + Real.pi / 8) = 2 / 3 ∧ 4 * A * Real.sin beta = 1 := by
  have hR : R * Real.cos T = Real.cos beta := div_mul_cancel₀ _ cos_T_pos.ne'
  have hY : Real.sin beta = Y * Real.cos beta := sinBeta_eq_Y_mul_cosBeta
  have hphase := firstPhase_sin_eq_two_Y_mul_cos
  have hangle : T = Real.pi / 2 - (beta + (beta / 2 + Real.pi / 8)) := by unfold T; ring
  have hcos : Real.cos T = 3 / 2 * Real.cos beta * Real.sin (beta / 2 + Real.pi / 8) := by
    rw [hangle, Real.cos_pi_div_two_sub, Real.sin_add, hY, hphase]
    ring
  rw [hcos] at hR
  have hs : R * Real.sin (beta / 2 + Real.pi / 8) = 2 / 3 := by
    apply mul_left_cancel₀ (show Real.cos beta ≠ 0 from cosBeta_pos.ne')
    linear_combination (2 / 3) * hR
  have hA : 4 * A * Real.sin beta = 1 := four_mul_A_mul_sinBeta
  refine ⟨?_, hs, hA⟩
  rw [hY] at hA
  apply mul_left_cancel₀ Y_ne_zero
  linear_combination -(R / 2) * hphase + hs / 2 - hA / 3

/-- The middle phase evaluated at the first switch has this cosine component. -/
theorem R_mul_cos_firstPhase :
    R * Real.cos (beta / 2 + Real.pi / 8) = (1 - k) * cosBeta := by
  rw [firstSwitch_eqs.1, k, cosBeta]; ring

/-- Companion sine component at the first switch. -/
theorem R_mul_sin_firstPhase :
    R * Real.sin (beta / 2 + Real.pi / 8) = 2 / 3 := firstSwitch_eqs.2.1

/-- The phase angles at the second switch, reflected to the first switch. -/
theorem lateSwitch_trig :
    Real.sin (lateSwitch / 2 + Real.pi / 8) = Real.cos (beta / 2 + Real.pi / 8) ∧
      Real.cos (lateSwitch / 2 + Real.pi / 8) = Real.sin (beta / 2 + Real.pi / 8) ∧
      Real.sin lateSwitch = Real.cos beta ∧ Real.cos lateSwitch = Real.sin beta := by
  rw [show lateSwitch / 2 + Real.pi / 8 = Real.pi / 2 - (beta / 2 + Real.pi / 8) by
    unfold lateSwitch; ring, lateSwitch]
  simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, and_self]

end AmbidextrousSofa.Reference
