module

public import AmbidextrousSofa.Analysis.ExactEstimates

@[expose] public section

/-!
# Geometric parameters for the unit-width exclusion

The available extra-tail height is the actual nearby wall height at the
zero of the diagonal tent. All other short-width parameters are derived
from this height and the diagonal offset, rather than chosen independently.
-/

noncomputable section

namespace AmbidextrousSofa

def nearDiagonalNorm (k : ℝ) : ℝ := Real.sqrt (1 + k ^ 2)

theorem nearDiagonalNorm_pos (k : ℝ) : 0 < nearDiagonalNorm k := Real.sqrt_pos.mpr (by positivity)

theorem nearDiagonalNorm_sq (k : ℝ) : nearDiagonalNorm k ^ 2 = 1 + k ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- Full available height of the nearby companion wall at a diagonal zero. -/
def shortTailHeight (k : ℝ) : ℝ := 1 - nearDiagonalNorm k + k ^ 2

/-- The support displacement complementary to the available tail height. -/
def shortTipThreshold (k : ℝ) : ℝ := k - shortTailHeight k

/-- Exactly the midpoint required by the companion support inequality. -/
def shortApexThreshold (k : ℝ) : ℝ :=
  (nearDiagonalNorm k + shortTailHeight k / k) / 2

/-- The area of a complete outer cut whose horizontal leg is `k/3`. -/
def shortOuterCutBudget (k : ℝ) : ℝ := (1 + k) / 2 * (k / 3) ^ 2

/-- Two Newton steps for the nearby norm, from the seed one.
The squared norm is bounded using the existing diagonal-offset enclosure. -/
def shortNormUpper : ℝ :=
  let q := 2 - 2 * (diagonalOffsetLower : ℝ)
  let u := (1 + q) / 2
  (u + q / u) / 2

theorem nearDiagonalNorm_short_bounds {k : ℝ}
    (hk0 : diagonalOffsetLower < k) (hk1 : k < (diagonalOffsetUpper))
    (hksq : k ^ 2 + 2 * k = 1) :
    1 < nearDiagonalNorm k ∧ nearDiagonalNorm k < shortNormUpper := by
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  have hN := nearDiagonalNorm_sq k
  have hN0 := nearDiagonalNorm_pos k
  have hupper : (2 - 2 * (diagonalOffsetLower : ℝ)) < shortNormUpper ^ 2 := by
    norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton, shortNormUpper]
  have hu0 : 0 < shortNormUpper := by norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton, shortNormUpper]
  dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  constructor <;> nlinarith

theorem shortTailHeight_eq {k : ℝ} (hksq : k ^ 2 + 2 * k = 1) :
    shortTailHeight k = 2 - 2 * k - nearDiagonalNorm k := by
  unfold shortTailHeight
  linarith only [hksq]

theorem shortApexThreshold_eq {k : ℝ} (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1) :
    shortApexThreshold k = (1 + k) * (1 - nearDiagonalNorm k / 2) := by
  unfold shortApexThreshold
  rw [shortTailHeight_eq hksq]
  field_simp
  linear_combination (nearDiagonalNorm k - 2) * hksq

theorem short_tail_reserves {k : ℝ}
    (hk0 : diagonalOffsetLower < k) (hk1 : k < (diagonalOffsetUpper))
    (hksq : k ^ 2 + 2 * k = 1) :
    k ^ 2 / 16 < shortTailHeight k ∧ k ^ 2 / 16 < nearDiagonalNorm k - 1 := by
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  obtain ⟨hNlo, hNhi⟩ := nearDiagonalNorm_short_bounds hk0 hk1 hksq
  have hNsq := nearDiagonalNorm_sq k
  norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton, shortNormUpper] at hNhi
  rw [shortTailHeight_eq hksq]
  constructor
  · nlinarith only [hk0, hk1, hksq, hNhi]
  · nlinarith [mul_pos (sub_pos.2 hNlo) (show 0 < 15 - nearDiagonalNorm k by linarith)]

/-- The boundary comparisons needed by the constrained quadratic maximum.
Each parameter has already been fixed by the wall geometry. -/
theorem short_geometry_scalar_estimates {k : ℝ}
    (hk0 : diagonalOffsetLower < k) (hk1 : k < (diagonalOffsetUpper))
    (hksq : k ^ 2 + 2 * k = 1) :
    0 < shortTailHeight k ∧ 0 < shortTipThreshold k ∧ shortTipThreshold k < k ∧
      1 / 2 < shortApexThreshold k ∧ shortApexThreshold k ≤ (1 + k) / 2 ∧
      (1 - k ^ 2 / 4) - ((1 - k ^ 2 / 4) - k) ^ 2 / 2 < referenceHalfAreaLower ∧
      2 * k - k * (k ^ 2 / 4) / 2 - (k ^ 2 / 4) ^ 2 / 8 < referenceHalfAreaLower ∧
      2 * k - 2 / 3 * (shortTipThreshold k - k / 2) ^ 2 < referenceHalfAreaLower ∧
      1 - (1 - shortApexThreshold k) ^ 2 - (shortApexThreshold k - k) ^ 2 <
        referenceHalfAreaLower ∧
      k / 3 < (1 - k ^ 2 / 4) / 2 - shortTipThreshold k - (k ^ 2 / 4) / 4 ∧
      2 * k - referenceHalfAreaLower < shortOuterCutBudget k := by
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  have hk : 0 < k := by linarith
  obtain ⟨hNlo, hNhi⟩ := nearDiagonalNorm_short_bounds hk0 hk1 hksq
  have hNsq := nearDiagonalNorm_sq k
  have hNeq : nearDiagonalNorm k ^ 2 + 2 * k = 2 := by linarith only [hNsq, hksq]
  rw [shortTailHeight_eq hksq, shortApexThreshold_eq hk hksq]
  unfold shortTipThreshold
  rw [shortTailHeight_eq hksq]
  have ha : (1 - k ^ 2 / 4) - ((1 - k ^ 2 / 4) - k) ^ 2 / 2 =
      9 * k / 8 + 11 / 32 := by
    linear_combination (-k ^ 2 / 32 - 3 * k / 16 - 5 / 32) * hksq
  have hh : 2 * k - k * (k ^ 2 / 4) / 2 - (k ^ 2 / 4) ^ 2 / 8 =
      47 * k / 32 + 27 / 128 := by
    linear_combination (-k ^ 2 / 128 - 7 * k / 64 + 27 / 128) * hksq
  have ht : 2 * k - 2 / 3 * (k - (2 - 2 * k - nearDiagonalNorm k) - k / 2) ^ 2 =
      (8 - 10 * k) * nearDiagonalNorm k / 3 + 55 * k / 3 - 49 / 6 := by
    linear_combination (-2 / 3 : ℝ) * hNeq - (25 / 6 : ℝ) * hksq
  have hm : 1 - (1 - (1 + k) * (1 - nearDiagonalNorm k / 2)) ^ 2 -
      ((1 + k) * (1 - nearDiagonalNorm k / 2) - k) ^ 2 =
      2 * nearDiagonalNorm k + 4 * k - 3 := by
    linear_combination (-k ^ 2 / 2 - k - 1 / 2) * hNeq +
      (nearDiagonalNorm k + k - 2) * hksq
  have hb : shortOuterCutBudget k = k / 6 - 1 / 18 := by
    unfold shortOuterCutBudget
    linear_combination (k / 18 - 1 / 18) * hksq
  rw [ha, hh, ht, hm, hb]
  have htcheck :
      (8 - 10 * (diagonalOffsetUpper : ℝ)) * shortNormUpper / 3 +
      55 * (diagonalOffsetUpper : ℝ) / 3 - 49 / 6 < referenceHalfAreaLower := by
    norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton, shortNormUpper, referenceHalfAreaLower, referenceRootLower,
      cubicBracketLower, cubicBracketUpper, cubic]
  norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton, shortNormUpper, referenceHalfAreaLower, referenceRootLower,
    cubicBracketLower, cubicBracketUpper, cubic] at hNhi htcheck ⊢
  refine ⟨by linarith, by linarith, by linarith, by nlinarith,
    by nlinarith, by linarith, by linarith, ?_, by linarith, by nlinarith, by linarith⟩
  nlinarith [mul_nonneg (sub_nonneg.2 hk1.le)
    (show 0 ≤ 55 - 10 * nearDiagonalNorm k by linarith),
    mul_nonneg (sub_nonneg.2 hNhi.le)
      (show (0 : ℝ) ≤ 8 - 10 * (diagonalOffsetUpper) by norm_num)]

end AmbidextrousSofa
