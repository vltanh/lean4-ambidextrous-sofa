module

public import AmbidextrousSofa.Analysis.IntermediateTilt

@[expose] public section

/-!
# Perspective tangents for the actual wide diagonal majorant

The lower diagonal coordinate in this file is the literal support minus
one. The tilted ceiling is retained in the left exterior term. The two
positive squares are the portions of the diagonal niche beyond the
middle interval, so clipping is included in every comparison.
-/

noncomputable section

namespace AmbidextrousSofa

def wideDiagonalMajorant (a h k u v : ℝ) : ℝ :=
  a - 5 * a * h / 8 -
    ((a - u) ^ 2 + (a - v - 3 * h / 2) ^ 2 / (1 - h / a)) / 2 -
    ((u + v) / 2 - k) ^ 2 +
    ((max (u - k - a / 2) 0) ^ 2 + (max (v - k - a / 2) 0) ^ 2) / 2

def wideHalfBound (a m h k : ℝ) : ℝ :=
  m + 1 / 4 - (m - k) ^ 2 - (5 * a / 8 - 3 / 4 + 1 / (8 * a)) * h


theorem wideDiagonalMajorant_le_tangent {a h k t : ℝ}
    (ha : 0 < a) (hh : 0 ≤ h) (hha : h < a)
    (ht0 : a / 2 - k ≤ t) (ht1 : t / a ≤ 3 / 2) (u v : ℝ) :
    wideDiagonalMajorant a h k u v ≤
      a - 2 * t * (a - (u + v) / 2) + t ^ 2 - ((u + v) / 2 - k) ^ 2 -
        (5 * a / 8 - 3 * t / 2 + t ^ 2 / (2 * a)) * h := by
  have hR := clipped_perspective_ge_tangent ha le_rfl ha ht1 (a - u)
    (c := u - k - a / 2) (by linarith)
  have hL := clipped_perspective_ge_tangent ha hh hha ht1 (a - v) (c := v - k - a / 2)
    (by linarith)
  simp only [mul_zero, add_zero, zero_div, sub_zero, div_one] at hR
  rw [wideDiagonalMajorant]
  linarith [show t ^ 2 / (2 * a) * h = t ^ 2 / a * h / 2 by ring]

theorem wideDiagonalMajorant_le_half {a h k : ℝ}
    (ha : 8 / 5 ≤ a) (hh : 0 ≤ h) (hh1 : h < 1 / 2)
    (hak : a ≤ 1 + 2 * k) (u v : ℝ) :
    wideDiagonalMajorant a h k u v ≤ wideHalfBound a ((u + v) / 2) h k := by
  have ha0 : 0 < a := by linarith only [ha]
  refine (wideDiagonalMajorant_le_tangent (t := 1 / 2) ha0 hh (by linarith only [ha, hh1])
    (by linarith only [hak]) (by rw [div_le_iff₀ ha0]; linarith only [ha]) u v).trans_eq ?_
  rw [wideHalfBound]
  ring

theorem wide_tilt_coefficient_ge {a : ℝ} (ha : 8 / 5 ≤ a) :
    (21 / 64 : ℝ) ≤ 5 * a / 8 - 3 / 4 + 1 / (8 * a) := by
  have ha0 : 0 < a := by linarith only [ha]
  refine le_of_mul_le_mul_right ?_ ha0
  have hinv : 1 / (8 * a) * a = 1 / 8 := by field_simp
  linarith only [hinv, mul_nonneg (sub_nonneg.2 ha)
    (show (0 : ℝ) ≤ 5 * a / 8 - 5 / 64 by linarith only [ha])]

/-- The endpoint budget gives a supporting plane at the first wide width.
Its width and height prices directly pay for fitting both nearby-angle peaks;
no separate small-height or width-plus-height cuts are needed. -/
theorem wide_diagonal_high_score_fitting {a h k u v : ℝ}
    (ha0 : 8 / 5 ≤ a) (ha1 : a < 3) (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    (hk0 : diagonalOffsetLower < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hm : a - 1 / 2 - h / 4 ≤ (u + v) / 2)
    (hscore : 41 / 50 ≤ wideDiagonalMajorant a h k u v) :
    a ≤ 1 + 2 * k ∧ (1 - k / 2) * a + h < (1 + k) * nearDiagonalNorm k := by
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  have ha : 0 < a := by linarith only [ha0]
  have hak : a ≤ 1 + 2 * k := by
    by_contra hbad
    -- Beyond `1 + 2k`, the tangent at `t = a / 2 - k` falls below `41 / 50`.
    have hak' := lt_of_not_ge hbad
    have ht := wideDiagonalMajorant_le_tangent (t := a / 2 - k) ha hh0
      (by linarith only [ha0, hh1]) le_rfl (by rw [div_le_iff₀ ha]; linarith only [ha, hk0]) u v
    rw [show (a / 2 - k) ^ 2 / (2 * a) = a / 8 - k / 2 + k ^ 2 / (2 * a) by field_simp; ring]
      at ht
    have hk2 : 0 ≤ k ^ 2 / (2 * a) := by positivity
    linarith only [hscore, ht, hksq, hk1, sq_nonneg h, mul_nonneg hh0 hk2,
      mul_nonneg (sub_nonneg.2 hm)
        (by linarith only [hm, ha0, hh1] : 0 ≤ (u + v) / 2 + (a - 1 / 2 - h / 4) - a),
      mul_nonneg (by linarith only [hak'] : 0 ≤ a - (1 + 2 * k))
        (by linarith only [ha0, hk0] : 0 ≤ 3 * a / 4 - 3 / 4 + k / 2),
      mul_nonneg hh0 (by linarith only [ha1] : 0 ≤ 3 - a),
      mul_le_mul_of_nonneg_left hh1.le (by linarith only [hk1] : 0 ≤ 1 / 2 - k)]
  have hF := wideDiagonalMajorant_le_half ha0 hh0 hh1 hak u v
  have hcoef := mul_le_mul_of_nonneg_right (wide_tilt_coefficient_ge ha0) hh0
  rw [wideHalfBound] at hF
  -- At `a₀ = 8/5`, the endpoint law gives `m₀ = a₀ - 1/2`.
  let m0 : ℝ := 8 / 5 - 1 / 2
  let p : ℝ := 2 * (m0 - k) - 1
  let q : ℝ := 21 / 64 - p / 4
  let reserve : ℝ := m0 + 1 / 4 - (m0 - k) ^ 2 - 41 / 50
  have hp : 0 ≤ p := by dsimp [p, m0]; linarith only [hk1]
  have hbudget : p * (a - 8 / 5) + q * h ≤ reserve := by
    have hpressure := mul_nonneg hp (sub_nonneg.mpr hm)
    dsimp [p, m0] at hpressure
    dsimp [p, q, reserve, m0]
    nlinarith only [hscore, hF, hcoef, sq_nonneg ((u + v) / 2 - (8 / 5 - 1 / 2)), hpressure]
  -- One width unit costs more than its contribution to the peak span.
  have hprice : q * (1 - k / 2) ≤ p := by
    dsimp [q, p, m0]
    nlinarith only [hksq, hk1]
  have hq : 0 < q := by dsimp [q, p, m0]; linarith only [hk0]
  have hN : 27 / 25 < nearDiagonalNorm k := Real.lt_sqrt_of_sq_lt (by nlinarith only [hk0])
  have hmargin : reserve < q * ((1 + k) * (27 / 25) - (1 - k / 2) * (8 / 5)) := by
    dsimp [reserve, q, p, m0]
    nlinarith only [hksq, hk1]
  have hspan : (1 - k / 2) * a + h < (1 + k) * (27 / 25) := by
    have hpaid := mul_le_mul_of_nonneg_right hprice (sub_nonneg.mpr ha0)
    nlinarith only [hbudget, hpaid, hmargin, hq]
  exact ⟨hak, hspan.trans (mul_lt_mul_of_pos_left hN (by linarith only [hk0]))⟩

end AmbidextrousSofa
