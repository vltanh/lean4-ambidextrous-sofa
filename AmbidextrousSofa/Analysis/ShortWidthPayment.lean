module

public import AmbidextrousSofa.Analysis.NearDiagonalWalls

@[expose] public section

/-!
# Geometric parameters for the short-width two-tail payment

The tail height is the actual available wall height; its tip and companion
thresholds follow from that choice. The final paid envelope decreases with
nonnegative tilt and lies below the generated reference budget for
half-projection widths at most one, the natural unit-width boundary.
No independent tail-height or tip allowance is chosen.
-/

noncomputable section

namespace AmbidextrousSofa

def nearTriangleCoefficient (k : ℝ) : ℝ := 1 / (2 * k * (1 - k))

def shortOuterTipAllowance (k : ℝ) : ℝ := shortTipThreshold k - k + shortTailHeight k / k

def shortWidthPaidEnvelope (k h : ℝ) : ℝ :=
  1 - (1 - k) ^ 2 / 2 - k * h / 2 - h ^ 2 / 8 -
    nearTriangleCoefficient k / 2 * ((shortTailHeight k - (1 - k) * h) ^ 2 + shortTailHeight k ^ 2) +
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
    shortOuterTipAllowance k = 4 * k - (1 + k) * nearDiagonalNorm k := by
  unfold shortOuterTipAllowance shortTipThreshold
  rw [shortTailHeight_eq hksq, div_diagonal_offset hk hksq]
  linear_combination -2 * hksq

theorem shortOuterTipAllowance_height {k : ℝ} (hk : 0 < k) :
    shortOuterTipAllowance k = shortTailHeight k * (1 - k) / k := by
  unfold shortOuterTipAllowance shortTipThreshold
  field_simp
  ring

theorem short_nearDiagonal_constants {k : ℝ}
    (hk0 : diagonalOffsetLower < k) (hk1 : k < (diagonalOffsetUpper)) (hksq : k ^ 2 + 2 * k = 1) :
    shortTailHeight k ≤ 1 - nearDiagonalNorm k + k ^ 2 ∧
      nearDiagonalNorm k + shortTailHeight k / k = 2 * shortApexThreshold k ∧
      k + shortTailHeight k / (1 - k) + k ^ 2 / 16 < shortApexThreshold k ∧
      0 < shortOuterTipAllowance k := by
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  have hk : 0 < k := by linarith
  obtain ⟨hη, -, -, -, -, -, -, -, -, -, -⟩ := short_geometry_scalar_estimates hk0 hk1 hksq
  have hN0 := (nearDiagonalNorm_short_bounds hk0 hk1 hksq).1
  have hgap : shortApexThreshold k - (k + shortTailHeight k / (1 - k)) =
      nearDiagonalNorm k - 1 := by
    rw [shortApexThreshold_eq hk hksq, shortTailHeight_eq hksq,
      div_eq_mul_one_div _ (1 - k), diagonal_complement_inv (by linarith) hksq]
    linear_combination hksq
  have hreserve := (short_tail_reserves hk0 hk1 hksq).2
  refine ⟨le_rfl, by unfold shortApexThreshold; ring, by linarith only [hgap, hreserve], ?_⟩
  rw [shortOuterTipAllowance_height hk]
  exact div_pos (mul_pos hη (by linarith)) hk

theorem shortWidthPaidEnvelope_lt {k h : ℝ}
    (hk0 : diagonalOffsetLower < k) (hk1 : k < (diagonalOffsetUpper)) (hksq : k ^ 2 + 2 * k = 1)
    (hh : 0 ≤ h) : shortWidthPaidEnvelope k h < referenceHalfAreaLower := by
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  have hk : 0 < k := by linarith
  have hNsq := nearDiagonalNorm_sq k
  have hN0 := nearDiagonalNorm_pos k
  obtain ⟨hNlo, hNhi⟩ := nearDiagonalNorm_short_bounds hk0 hk1 hksq
  have hNlow : 1 + k / 8 < nearDiagonalNorm k := by
    nlinarith [mul_pos hk (show 0 < 63 * k - 16 by linarith)]
  have hlin : -k / 2 + (7 + 3 * k) / 4 * shortTailHeight k * (1 - k) +
      k * shortOuterTipAllowance k / 2 ≤ 0 := by
    rw [shortTailHeight_eq hksq, shortOuterTipAllowance_eq hk hksq]
    have heq : -k / 2 + (7 + 3 * k) / 4 * (2 - 2 * k - nearDiagonalNorm k) * (1 - k) +
        k * (4 * k - (1 + k) * nearDiagonalNorm k) / 2 =
        3 - 3 * nearDiagonalNorm k / 2 - 7 * k / 2 := by
      linear_combination (nearDiagonalNorm k / 4 + 3 * k / 2 - 1 / 2) * hksq
    rw [heq]
    linarith only [hNlow, hk0]
  have hquad : -1 / 8 - (7 + 3 * k) / 4 * (1 - k) ^ 2 / 2 + k / 16 ≤ 0 := by
    linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 7 + 3 * k) (sq_nonneg (1 - k))]
  have hbase : 2 * k - (7 + 3 * k) / 4 * shortTailHeight k ^ 2 +
      k * shortOuterTipAllowance k ^ 2 < referenceHalfAreaLower := by
    rw [shortTailHeight_eq hksq, shortOuterTipAllowance_eq hk hksq]
    have heq : 2 * k - (7 + 3 * k) / 4 * (2 - 2 * k - nearDiagonalNorm k) ^ 2 +
        k * (4 * k - (1 + k) * nearDiagonalNorm k) ^ 2 =
        (12 - 22 * k) * nearDiagonalNorm k + 91 * k - 40 := by
      linear_combination (k ^ 3 + 2 * k ^ 2 + k / 4 - 7 / 4) * hNsq +
        (k ^ 3 - 8 * nearDiagonalNorm k * k + 5 * nearDiagonalNorm k + 61 * k / 4 - 125 / 4) * hksq
    rw [heq]
    have hcheck : (12 - 22 * (diagonalOffsetUpper : ℝ)) * shortNormUpper +
        91 * (diagonalOffsetUpper : ℝ) - 40 < referenceHalfAreaLower := by
      norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton, shortNormUpper, referenceHalfAreaLower, referenceRootLower,
        cubicBracketLower, cubicBracketUpper, cubic]
    norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton, shortNormUpper] at hNhi hcheck
    nlinarith [mul_nonneg (sub_nonneg.2 hk1.le)
      (show 0 ≤ 91 - 22 * nearDiagonalNorm k by linarith),
      mul_nonneg (sub_nonneg.2 hNhi.le)
        (show (0 : ℝ) ≤ 12 - 22 * (diagonalOffsetUpper) by norm_num)]
  rw [shortWidthPaidEnvelope, nearTriangleCoefficient_eq hk (by linarith) hksq]
  linarith only [mul_nonpos_of_nonpos_of_nonneg hlin hh,
    mul_nonpos_of_nonpos_of_nonneg hquad (sq_nonneg h), hbase, hksq]

end AmbidextrousSofa
