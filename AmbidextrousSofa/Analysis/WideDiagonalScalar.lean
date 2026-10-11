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

/-- The tangent of the clipped perspective term at slope `t`, valid when `c ≤ t - w`. -/
theorem clipped_perspective_ge_tangent {a h c t : ℝ}
    (ha : 0 < a) (hh : 0 ≤ h) (hha : h < a) (ht : t / a ≤ 3 / 2) (w : ℝ) (hct : c ≤ t - w) :
    2 * t * w - t ^ 2 + (-3 * t + t ^ 2 / a) * h ≤
      (w - 3 * h / 2) ^ 2 / (1 - h / a) - (max c 0) ^ 2 := by
  have hd : 0 < 1 - h / a := sub_pos.mpr ((div_lt_one ha).mpr hha)
  obtain ⟨q, hq⟩ : ∃ q, q = w - t - h * (3 / 2 - t / a) := ⟨_, rfl⟩
  have hqt : q ≤ w - t := hq ▸ sub_le_self _ (mul_nonneg hh (sub_nonneg.mpr ht))
  have hclip : max c 0 ^ 2 ≤ q ^ 2 := (pow_le_pow_left₀ (le_max_right _ _)
    (max_le (by linarith [neg_le_abs q]) (abs_nonneg q)) 2).trans_eq (sq_abs q)
  have hid : (w - 3 * h / 2) ^ 2 / (1 - h / a) =
      2 * t * w - t ^ 2 + (-3 * t + t ^ 2 / a) * h + q ^ 2 / (1 - h / a) := by
    rw [hq]
    field_simp [(sub_pos.mpr hha).ne']
    ring
  linarith [le_div_self (sq_nonneg q) hd (by linarith [div_nonneg hh ha.le] : 1 - h / a ≤ 1)]

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

/-- The endpoint height sum imposes the lower bound on `m`. Before any
nearby-angle payment, a high score forces this compact small-tilt box. -/
theorem wide_diagonal_high_score_box {a h k u v : ℝ}
    (ha0 : 8 / 5 ≤ a) (ha1 : a < 3) (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hm : a - 1 / 2 - h / 4 ≤ (u + v) / 2)
    (hscore : 41 / 50 ≤ wideDiagonalMajorant a h k u v) :
    a < 9 / 5 ∧ h < 1 / 4 ∧ a + h < 37 / 20 := by
  have ha : 0 < a := by linarith only [ha0]
  by_cases hak : a ≤ 1 + 2 * k
  swap
  · -- Beyond `1 + 2k`, the tangent at `t = a / 2 - k` falls below `41 / 50`.
    have hak' := lt_of_not_ge hak
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
  -- Below `1 + 2k`, the half tangent bounds the score by a decreasing function of the midpoint.
  have hF := wideDiagonalMajorant_le_half ha0 hh0 hh1 hak u v
  have hcoef := mul_le_mul_of_nonneg_right (wide_tilt_coefficient_ge ha0) hh0
  rw [wideHalfBound] at hF
  have key : ∀ m0, k + 1 / 2 ≤ m0 → m0 ≤ (u + v) / 2 →
      41 / 50 ≤ m0 + 1 / 4 - (m0 - k) ^ 2 - 21 / 64 * h := fun m0 h0 h1 => by
    linarith only [hscore, hF, hcoef, mul_nonneg (sub_nonneg.2 h1)
      (by linarith only [h0, h1] : 0 ≤ (u + v) / 2 + m0 - 2 * k - 1)]
  have ha9 : a < 9 / 5 := by
    by_contra hbad
    linarith only [key (13 / 10 - h / 4) (by linarith only [hk1, hh1])
      (by linarith only [hm, hbad]), hh0, hksq, hk1, sq_nonneg h,
      mul_nonneg hh0 (sub_nonneg.2 hk0.le)]
  have hh4 : h < 1 / 4 := by
    by_contra hbad
    linarith only [key (11 / 10 - h / 4) (by linarith only [hk1, hh1])
      (by linarith only [hm, ha0]), hksq, hk1, mul_nonneg (by linarith only [hbad] : 0 ≤ h - 1 / 4)
        (by linarith only [hk0, hh0] : 0 ≤ 9 / 320 + k / 2 + (h + 1 / 4) / 16)]
  refine ⟨ha9, hh4, ?_⟩
  by_contra hbad
  linarith only [key (27 / 20 - 5 * h / 4) (by linarith only [hh4, hk1])
    (by linarith only [hm, hbad]), sq_nonneg ((27 / 20 - k - 5 * h / 4) - 101 / 160), hk1]

end AmbidextrousSofa
