module

public import AmbidextrousSofa.Analysis.NearDiagonalWalls

@[expose] public section

/-!
# Exact constants for the short-width two-tail payment

All numerical margins are rational consequences of `k²+2k=1` and the
displayed rational bounds for k. The final paid envelope decreases with
nonnegative tilt and lies strictly below 41/50, including widths up to
1001/1000 in the half-projection parameter.
-/

noncomputable section

namespace AmbidextrousSofa

def nearTriangleCoefficient (k : ℝ) : ℝ := 1 / (2 * k * (1 - k))

def shortOuterTipAllowance (k : ℝ) : ℝ := 323 / 1000 - k + (2 / 25) / k

def shortWidthPaidEnvelope (k h : ℝ) : ℝ :=
  (2001 / 1000) * k - 1 / 2000000 - k * h / 2 - h ^ 2 / 8 -
    nearTriangleCoefficient k / 2 * (((2 / 25) - (1 - k) * h) ^ 2 + (2 / 25) ^ 2) +
      k * (shortOuterTipAllowance k + h / 4) ^ 2

/-- Division by the diagonal offset, using `k ^ 2 + 2 * k = 1`. -/
theorem div_diagonal_offset {k : ℝ} (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1) (x : ℝ) :
    x / k = x * (k + 2) :=
  (div_eq_iff hk.ne').mpr (by linear_combination -x * hksq)

theorem diagonal_complement_inv {k : ℝ} (hk1 : k < 1) (hksq : k ^ 2 + 2 * k = 1) :
    1 / (1 - k) = (3 + k) / 2 :=
  (div_eq_iff (sub_pos.mpr hk1).ne').mpr (by linear_combination hksq / 2)

theorem nearTriangleCoefficient_eq {k : ℝ} (hk : 0 < k) (hk1 : k < 1)
    (hksq : k ^ 2 + 2 * k = 1) : nearTriangleCoefficient k = (7 + 3 * k) / 4 :=
  (div_eq_iff (mul_pos (mul_pos two_pos hk) (sub_pos.mpr hk1)).ne').mpr
    (by linear_combination (3 * k / 2 - 1) * hksq)

theorem shortOuterTipAllowance_eq {k : ℝ} (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1) :
    shortOuterTipAllowance k = (483 - 920 * k) / 1000 := by
  rw [shortOuterTipAllowance, div_diagonal_offset hk hksq]
  ring

theorem short_nearDiagonal_constants {k : ℝ}
    (hk0 : 41 / 99 < k) (hk1 : k < 169 / 408) (hksq : k ^ 2 + 2 * k = 1) :
    (2 / 25 : ℝ) < 1 - nearDiagonalNorm k + k ^ 2 ∧
      nearDiagonalNorm k + (2 / 25) / k < 32 / 25 ∧
      k + (2 / 25) / (1 - k) < 3 / 5 ∧
      0 < shortOuterTipAllowance k := by
  have hk : 0 < k := by linarith
  have hb := nearDiagonalNorm_pos k
  have hbsq := nearDiagonalNorm_sq k
  have hk7 : 7 / 17 < k := by nlinarith
  have hb2 : nearDiagonalNorm k < (28 - 2 * k) / 25 := by nlinarith
  rw [div_diagonal_offset hk hksq, div_eq_mul_one_div (2 / 25 : ℝ) (1 - k),
    diagonal_complement_inv (by linarith) hksq, shortOuterTipAllowance_eq hk hksq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem shortWidthPaidEnvelope_lt {k h : ℝ}
    (hk0 : 41 / 99 < k) (hk1 : k < 169 / 408) (hksq : k ^ 2 + 2 * k = 1)
    (hh : 0 ≤ h) : shortWidthPaidEnvelope k h < (41 / 50 : ℝ) := by
  have hk : 0 < k := by linarith
  -- The coefficients of `h` and of `h ^ 2` in the envelope are nonpositive.
  have hlin : -k / 2 + (7 + 3 * k) / 4 * (2 / 25) * (1 - k) +
      k * ((483 - 920 * k) / 1000) / 2 ≤ 0 := by linarith
  have hquad : -1 / 8 - (7 + 3 * k) / 4 * (1 - k) ^ 2 / 2 + k / 16 ≤ 0 := by
    linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 7 + 3 * k) (sq_nonneg (1 - k))]
  rw [shortWidthPaidEnvelope, nearTriangleCoefficient_eq hk (by linarith) hksq,
    shortOuterTipAllowance_eq hk hksq]
  linarith [mul_nonpos_of_nonpos_of_nonneg hlin hh,
    mul_nonpos_of_nonpos_of_nonneg hquad (sq_nonneg h), congrArg (HMul.hMul k) hksq]

end AmbidextrousSofa
