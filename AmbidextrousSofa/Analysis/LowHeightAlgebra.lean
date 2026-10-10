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

def lowHeightBound : ℝ := 31233 / 39200

def lowHeightSurrogate (C u v : ℝ) : ℝ :=
  11 * C / 8 - (1 - u) ^ 2 / 2 - (1 / 4 - v) ^ 2 / 2 -
    (max (2 * C + (u + v) / 2 - Real.sqrt 2) 0) ^ 2 +
      (max (C + u - Real.sqrt 2) 0) ^ 2 / 2

theorem lowHeightBound_lt_four_fifths : lowHeightBound < 4 / 5 := by
  norm_num [lowHeightBound]

theorem lowHeightBound_lt_half_M : lowHeightBound < M / 2 := by
  linarith [lowHeightBound_lt_four_fifths, eight_fifths_lt_M]

theorem lowHeight_sqrt_bounds :
    (7 / 5 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 99 / 70 ∧ Real.sqrt 2 < 10 / 7 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg 2
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem positivePart_square_pair_bound {H w : ℝ} (hH : 0 ≤ H) :
    H ^ 2 / 2 ≤ w ^ 2 + (max (H - w) 0) ^ 2 := by
  by_cases hHw : 0 ≤ H - w
  · rw [max_eq_left hHw]
    nlinarith [sq_nonneg (H - 2 * w)]
  · rw [max_eq_right (le_of_not_ge hHw)]
    have hsw : H ^ 2 ≤ w ^ 2 := by
      exact (sq_le_sq₀ hH (by linarith)).mpr (by linarith)
    nlinarith [sq_nonneg H]

/-- The branch whose right tent tail has not crossed the middle endpoint. -/
theorem lowHeight_unclipped_bound {C u v : ℝ} (hC : 1 / 2 ≤ C)
    (hz : C + u - Real.sqrt 2 ≤ 0) : lowHeightSurrogate C u v < lowHeightBound := by
  have hsqrt := lowHeight_sqrt_bounds.2.2
  have hH : 0 ≤ 2 * C + 5 / 8 - Real.sqrt 2 := by linarith
  have hp := positivePart_square_pair_bound
    (w := ((1 - u) + (1 / 4 - v)) / 2) hH
  have harg : 2 * C + 5 / 8 - Real.sqrt 2 - ((1 - u) + (1 / 4 - v)) / 2 =
      2 * C + (u + v) / 2 - Real.sqrt 2 := by ring
  rw [harg] at hp
  have hxy : ((1 - u) ^ 2 + (1 / 4 - v) ^ 2) / 2 ≥
      (((1 - u) + (1 / 4 - v)) / 2) ^ 2 := by
    nlinarith [sq_nonneg ((1 - u) - (1 / 4 - v))]
  have hbound : lowHeightSurrogate C u v ≤
      11 * Real.sqrt 2 / 16 - 99 / 512 := by
    unfold lowHeightSurrogate
    rw [max_eq_right hz]
    nlinarith [sq_nonneg (C - Real.sqrt 2 / 2 - 1 / 32)]
  have hnumber : 11 * Real.sqrt 2 / 16 - 99 / 512 < lowHeightBound := by
    unfold lowHeightBound
    linarith
  exact hbound.trans_lt hnumber

/-- The one-tail expression has a uniform strict rational bound. Its
clipped branch is an explicit concave quadratic in the right excess. -/
theorem lowHeight_surrogate_bound {C u v : ℝ} (hC : 1 / 2 ≤ C)
    (hu : u ≤ 1) (hv : 0 ≤ v) : lowHeightSurrogate C u v < lowHeightBound := by
  by_cases hz : C + u - Real.sqrt 2 ≤ 0
  · exact lowHeight_unclipped_bound hC hz
  have hzpos : 0 < C + u - Real.sqrt 2 := lt_of_not_ge hz
  let u0 : ℝ := Real.sqrt 2 - C
  let s : ℝ := 2 - 2 * C - v
  have hsmall : Real.sqrt 2 < 3 / 2 := by linarith [lowHeight_sqrt_bounds.2.2]
  have hu0 : u0 < u := by dsimp [u0]; linarith
  have hs1 : s ≤ 1 := by dsimp [s]; linarith
  have hh0 : 0 < 2 * C + (u0 + v) / 2 - Real.sqrt 2 := by dsimp [u0]; linarith
  have hh : 0 < 2 * C + (u + v) / 2 - Real.sqrt 2 := by linarith
  by_cases hs : s ≤ u0
  · have hboundary : lowHeightSurrogate C u v ≤ lowHeightSurrogate C u0 v := by
      have hfactor : (u - u0) * (u + u0 - 2 * s) ≥ 0 :=
        mul_nonneg (sub_nonneg.mpr hu0.le) (by linarith)
      unfold lowHeightSurrogate
      rw [max_eq_left hh.le, max_eq_left hzpos.le, max_eq_left hh0.le,
        show C + u0 - Real.sqrt 2 = 0 by dsimp [u0]; ring, max_self]
      dsimp [s, u0] at hfactor ⊢
      nlinarith
    exact hboundary.trans_lt (lowHeight_unclipped_bound hC (by dsimp [u0]; linarith))
  · have hs0 : u0 ≤ s := (le_of_not_ge hs)
    have hzs : 0 ≤ C + s - Real.sqrt 2 := by dsimp [u0] at hs0; linarith
    have hhs : 0 ≤ 2 * C + (s + v) / 2 - Real.sqrt 2 := by linarith
    have hparabola : lowHeightSurrogate C u v ≤ lowHeightSurrogate C s v := by
      unfold lowHeightSurrogate
      rw [max_eq_left hh.le, max_eq_left hzpos.le, max_eq_left hhs, max_eq_left hzs]
      dsimp [s]
      nlinarith [sq_nonneg (u - (2 - 2 * C - v))]
    have hzh : C + s - Real.sqrt 2 ≤ 2 * C + (s + v) / 2 - Real.sqrt 2 := by
      linarith
    have hzsq := (sq_le_sq₀ hzs hhs).mpr hzh
    have hdrop : lowHeightSurrogate C s v ≤ 11 * C / 8 - (1 / 4 - v) ^ 2 / 2 := by
      unfold lowHeightSurrogate
      rw [max_eq_left hhs, max_eq_left hzs]
      nlinarith [sq_nonneg (1 - s), sq_nonneg (C + s - Real.sqrt 2)]
    have hCv : C + v ≤ 2 - Real.sqrt 2 := by dsimp [u0, s] at hs0; linarith
    have hy : Real.sqrt 2 - 5 / 4 ≤ 1 / 4 - v := by linarith
    have hy0 : 0 ≤ Real.sqrt 2 - 5 / 4 := by linarith [lowHeight_sqrt_bounds.1]
    have hysq := (sq_le_sq₀ hy0 (by linarith)).mpr hy
    have hbound : lowHeightSurrogate C s v ≤ 31 / 32 - Real.sqrt 2 / 8 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hnumber : 31 / 32 - Real.sqrt 2 / 8 < lowHeightBound := by
      unfold lowHeightBound
      linarith [lowHeight_sqrt_bounds.1]
    exact (hparabola.trans hbound).trans_lt hnumber

/-- At larger quarter-widths the baseline tent alone suffices. -/
theorem lowHeight_large_width_unclipped_bound {C : ℝ} (hC : 23 / 20 ≤ C) :
    11 * C / 8 - (2 * C - Real.sqrt 2) ^ 2 < lowHeightBound := by
  have hsqrt := lowHeight_sqrt_bounds.2.1
  have hfactor : (C - 23 / 20) * (11 / 8 - 4 * (C + 23 / 20 - Real.sqrt 2)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hdecrease : 11 * C / 8 - (2 * C - Real.sqrt 2) ^ 2 ≤
      253 / 160 - (23 / 10 - Real.sqrt 2) ^ 2 := by nlinarith
  have hpositive : (0 : ℝ) ≤ 31 / 35 := by norm_num
  have hsq : (31 / 35 : ℝ) ^ 2 < (23 / 10 - Real.sqrt 2) ^ 2 :=
    (sq_lt_sq₀ hpositive (by linarith)).mpr (by linarith)
  unfold lowHeightBound
  nlinarith

theorem lowHeight_large_width_clipped_bound {C : ℝ} (hC : Real.sqrt 2 ≤ C) :
    (11 / 8 + 2 * Real.sqrt 2) * C - 3 * C ^ 2 < lowHeightBound := by
  have hsqrt := lowHeight_sqrt_bounds.2.2
  have hroot := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hfactor : (C - Real.sqrt 2) * (11 / 8 + 2 * Real.sqrt 2 -
      3 * (C + Real.sqrt 2)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hC)
      (by linarith [lowHeight_sqrt_bounds.1])
  have hbound : (11 / 8 + 2 * Real.sqrt 2) * C - 3 * C ^ 2 ≤
      11 * Real.sqrt 2 / 8 - 2 := by nlinarith
  unfold lowHeightBound
  linarith

theorem lowHeight_small_width_bound {C : ℝ} (hC : C ≤ 1 / 2) :
    11 * C / 8 < lowHeightBound := by
  unfold lowHeightBound
  linarith

end AmbidextrousSofa
