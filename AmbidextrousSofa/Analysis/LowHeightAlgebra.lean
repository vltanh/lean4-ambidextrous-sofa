module

public import AmbidextrousSofa.Analysis.PositiveTent
public import AmbidextrousSofa.Analysis.ExactEstimates

@[expose] public section

/-!
# Exact scalar bounds for the low-middle-height exclusion

The variables are a quarter-width and the two actual diagonal-support
excesses. This file bounds the explicit reward-minus-tent expression by
rational arithmetic and completed squares. The geometric derivation of
that expression is separate. No finite numerical search is used.
-/

noncomputable section

namespace AmbidextrousSofa

/-- A common coarse score bound for a middle endpoint below half-height.
The geometric split occurs at `C = √2 - 1/4`, where the left diagonal
tent tail first reaches the middle endpoint. -/
def lowHeightBound : ℝ := 4 / 5

def lowHeightSurrogate (C u v : ℝ) : ℝ :=
  11 * C / 8 - (1 - u) ^ 2 / 2 - (1 / 4 - v) ^ 2 / 2 -
    (max (2 * C + (u + v) / 2 - Real.sqrt 2) 0) ^ 2 +
      (max (C + u - Real.sqrt 2) 0) ^ 2 / 2

theorem lowHeightBound_lt_half_M : lowHeightBound < M / 2 := by
  unfold lowHeightBound; linarith [eight_fifths_lt_M]

theorem positivePart_square_pair_bound {H w : ℝ} (hH : 0 ≤ H) :
    H ^ 2 / 2 ≤ w ^ 2 + (max (H - w) 0) ^ 2 := by
  rcases le_total 0 (H - w) with h | h
  · rw [max_eq_left h]; linarith [sq_nonneg (H - 2 * w)]
  · rw [max_eq_right h]; nlinarith

/-- The branch whose right tent tail has not crossed the middle endpoint. -/
theorem lowHeight_unclipped_bound {C u v : ℝ} (hC : 1 / 2 ≤ C)
    (hz : C + u - Real.sqrt 2 ≤ 0) : lowHeightSurrogate C u v < lowHeightBound := by
  have hsqrt := sqrt_two_sub_one_bounds.2.2
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  have hp := positivePart_square_pair_bound (w := ((1 - u) + (1 / 4 - v)) / 2)
    (show 0 ≤ 2 * C + 5 / 8 - Real.sqrt 2 by linarith)
  rw [show 2 * C + 5 / 8 - Real.sqrt 2 - ((1 - u) + (1 / 4 - v)) / 2 =
    2 * C + (u + v) / 2 - Real.sqrt 2 by ring] at hp
  rw [lowHeightSurrogate, max_eq_right hz, lowHeightBound]
  linarith [sq_nonneg ((1 - u) - (1 / 4 - v)), sq_nonneg (C - Real.sqrt 2 / 2 - 1 / 32)]

/-- The one-tail expression has a uniform strict rational bound. Its
clipped branch is an explicit concave quadratic in the right excess. -/
theorem lowHeight_surrogate_bound {C u v : ℝ} (hC : 1 / 2 ≤ C) (hv : 0 ≤ v) :
    lowHeightSurrogate C u v < lowHeightBound := by
  rcases le_or_gt (C + u - Real.sqrt 2) 0 with hz | hz
  · exact lowHeight_unclipped_bound hC hz
  obtain ⟨hs1, -, hs2⟩ := sqrt_two_sub_one_bounds
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  have hh : 0 < 2 * C + (u + v) / 2 - Real.sqrt 2 := by linarith
  -- On the clipped branch the surrogate is concave in `u`, with vertex `s = 2 - 2C - v`.
  rcases le_or_gt (2 - 2 * C - v) (Real.sqrt 2 - C) with hs | hs
  · -- The vertex precedes the clipping point `√2 - C`, where the unclipped bound applies.
    refine lt_of_le_of_lt ?_
      (lowHeight_unclipped_bound (u := Real.sqrt 2 - C) (v := v) hC (by linarith))
    rw [lowHeightSurrogate, lowHeightSurrogate, max_eq_left hh.le, max_eq_left hz.le,
      max_eq_left (by linarith), show C + (Real.sqrt 2 - C) - Real.sqrt 2 = 0 by ring, max_self]
    linarith [mul_nonneg hz.le (show 0 ≤ u + (Real.sqrt 2 - C) - 2 * (2 - 2 * C - v) by linarith)]
  · -- Otherwise the surrogate is at most its value at the vertex.
    have hzs : 0 ≤ 2 - C - v - Real.sqrt 2 := by linarith
    rw [lowHeightSurrogate, max_eq_left hh.le, max_eq_left hz.le, lowHeightBound]
    linarith [sq_nonneg (u - (2 - 2 * C - v)), sq_nonneg (2 * C + v - 1),
      sq_nonneg (C + 1 - Real.sqrt 2), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
      pow_le_pow_left₀ hzs (show 2 - C - v - Real.sqrt 2 ≤ C + 1 - Real.sqrt 2 by linarith) 2,
      pow_le_pow_left₀ (by linarith : 0 ≤ Real.sqrt 2 - 5 / 4)
        (show Real.sqrt 2 - 5 / 4 ≤ 1 / 4 - v by linarith) 2]

/-- At larger quarter-widths the baseline tent alone suffices. -/
theorem lowHeight_large_width_unclipped_bound {C : ℝ}
    (hC : Real.sqrt 2 - 1 / 4 ≤ C) :
    11 * C / 8 - (2 * C - Real.sqrt 2) ^ 2 < lowHeightBound := by
  have hsqrt := sqrt_two_sub_one_bounds.2.2
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  unfold lowHeightBound
  have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hslo : (1 : ℝ) < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
  have hcorner : 11 * (Real.sqrt 2 - 1 / 4) / 8 -
      (Real.sqrt 2 - 1 / 2) ^ 2 < (4 / 5 : ℝ) := by nlinarith
  linarith [hcorner, mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hC)
      (show 11 / 8 - 4 * (C - 1 / 4) ≤ 0 by linarith)]

theorem lowHeight_large_width_clipped_bound {C : ℝ} (hC : Real.sqrt 2 ≤ C) :
    (11 / 8 + 2 * Real.sqrt 2) * C - 3 * C ^ 2 < lowHeightBound := by
  have hsqrt := sqrt_two_sub_one_bounds
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  unfold lowHeightBound
  linarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hC)
      (show 11 / 8 + 2 * Real.sqrt 2 - 3 * (C + Real.sqrt 2) ≤ 0 by linarith),
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem lowHeight_small_width_bound {C : ℝ} (hC : C ≤ 1 / 2) :
    11 * C / 8 < lowHeightBound := by
  unfold lowHeightBound; linarith

end AmbidextrousSofa
