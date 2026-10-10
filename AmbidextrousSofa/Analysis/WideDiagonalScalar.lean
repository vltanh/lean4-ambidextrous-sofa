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

theorem clipped_square_ge_tangent {b t : ℝ} (hbt : b ≤ t) (w : ℝ) :
    2 * t * w - t ^ 2 ≤ w ^ 2 - (max (b - w) 0) ^ 2 := by
  have h := shifted_positive_square_le_displacement (-w)
    (show -t ≤ -b by linarith only [hbt])
  rw [show -w - -b = b - w by ring] at h
  nlinarith only [h]

theorem clipped_perspective_ge_tangent {a h b t : ℝ}
    (ha : 0 < a) (hh : 0 ≤ h) (hha : h < a)
    (hbt : b ≤ t) (ht : t / a ≤ 3 / 2) (w : ℝ) :
    2 * t * w - t ^ 2 + (-3 * t + t ^ 2 / a) * h ≤
      (w - 3 * h / 2) ^ 2 / (1 - h / a) - (max (b - w) 0) ^ 2 := by
  let d := 1 - h / a
  let q := w - t - h * (3 / 2 - t / a)
  have hd : 0 < d := sub_pos.mpr ((div_lt_one ha).mpr hha)
  have hd1 : d ≤ 1 := by dsimp [d]; linarith only [div_nonneg hh ha.le]
  have hq : q ≤ w - t := by
    dsimp [q]
    exact sub_le_self _ (mul_nonneg hh (sub_nonneg.mpr ht))
  have hclip : (max (b - w) 0) ^ 2 ≤ q ^ 2 := by
    by_cases hw : b ≤ w
    · rw [max_eq_right (sub_nonpos.mpr hw)]
      simpa only [zero_pow] using sq_nonneg q
    · rw [max_eq_left (by linarith only [le_of_not_ge hw] : 0 ≤ b - w)]
      have hprod := mul_nonneg
        (show 0 ≤ -q - (b - w) by linarith only [hq, hbt])
        (show 0 ≤ -q + (b - w) by linarith only [hq, hbt, le_of_not_ge hw])
      nlinarith only [hprod]
  have hdiv : q ^ 2 ≤ q ^ 2 / d := by
    apply (le_div_iff₀ hd).mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hd1) (sq_nonneg q)]
  have hid : (w - 3 * h / 2) ^ 2 / d =
      2 * t * w - t ^ 2 + (-3 * t + t ^ 2 / a) * h + q ^ 2 / d := by
    dsimp [q, d]
    field_simp [ha.ne', hd.ne'] <;> ring
  change _ ≤ (w - 3 * h / 2) ^ 2 / d - _
  linarith only [hid, hclip, hdiv]

theorem wideDiagonalMajorant_le_tangent {a h k t : ℝ}
    (ha : 0 < a) (hh : 0 ≤ h) (hha : h < a)
    (ht0 : a / 2 - k ≤ t) (ht1 : t / a ≤ 3 / 2) (u v : ℝ) :
    wideDiagonalMajorant a h k u v ≤
      a - 2 * t * (a - (u + v) / 2) + t ^ 2 - ((u + v) / 2 - k) ^ 2 -
        (5 * a / 8 - 3 * t / 2 + t ^ 2 / (2 * a)) * h := by
  have hR := clipped_square_ge_tangent ht0 (a - u)
  have hL := clipped_perspective_ge_tangent ha hh hha ht0 ht1 (a - v)
  rw [show a / 2 - k - (a - u) = u - k - a / 2 by ring] at hR
  rw [show a / 2 - k - (a - v) = v - k - a / 2 by ring] at hL
  unfold wideDiagonalMajorant
  nlinarith only [hR, hL]

theorem wideDiagonalMajorant_le_half {a h k : ℝ}
    (ha : 8 / 5 ≤ a) (hh : 0 ≤ h) (hh1 : h < 1 / 2)
    (hak : a ≤ 1 + 2 * k) (u v : ℝ) :
    wideDiagonalMajorant a h k u v ≤ wideHalfBound a ((u + v) / 2) h k := by
  have ha0 : 0 < a := by linarith only [ha]
  have ht := wideDiagonalMajorant_le_tangent ha0 hh (by linarith only [ha, hh1])
    (show a / 2 - k ≤ 1 / 2 by linarith only [hak])
    (show (1 / 2 : ℝ) / a ≤ 3 / 2 by
      apply (div_le_iff₀ ha0).mpr; linarith only [ha]) u v
  convert ht using 1 <;> unfold wideHalfBound <;> ring

theorem wide_tilt_coefficient_ge {a : ℝ} (ha : 8 / 5 ≤ a) :
    (21 / 64 : ℝ) ≤ 5 * a / 8 - 3 / 4 + 1 / (8 * a) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hprod := mul_nonneg (show 0 ≤ a - 8 / 5 by linarith only [ha])
    (show 0 ≤ 5 * a / 8 - 5 / 64 by linarith only [ha])
  have hinv : (1 / (8 * a)) * a = (1 / 8 : ℝ) := by field_simp [ha0.ne']
  have hscaled : (21 / 64 : ℝ) * a ≤ (5 * a / 8 - 3 / 4 + 1 / (8 * a)) * a := by
    nlinarith only [hprod, hinv]
  exact (mul_le_mul_right ha0).mp hscaled

theorem wide_mid_value_antitone {k m m0 : ℝ} (h0 : k + 1 / 2 ≤ m0) (hm : m0 ≤ m) :
    m + 1 / 4 - (m - k) ^ 2 ≤ m0 + 1 / 4 - (m0 - k) ^ 2 := by
  have hprod := mul_nonneg (sub_nonneg.mpr hm)
    (show 0 ≤ m + m0 - 2 * k - 1 by linarith only [hm, h0])
  nlinarith only [hprod]

theorem wideHalfBound_le_zero_tilt {a m h k : ℝ}
    (ha : 8 / 5 ≤ a) (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    (hk0 : 2 / 5 < k) (hk1 : k < 29 / 70) (hm : a - 1 / 2 - h / 4 ≤ m) :
    wideHalfBound a m h k ≤ a - 1 / 4 - (a - 1 / 2 - k) ^ 2 := by
  have ha0 : 0 < a := by linarith only [ha]
  have hmid := wide_mid_value_antitone
    (show k + 1 / 2 ≤ a - 1 / 2 - h / 4 by linarith only [ha, hh1, hk1]) hm
  have hcoef : (a - 1 - k) / 2 ≤ 5 * a / 8 - 3 / 4 + 1 / (8 * a) := by
    have hi : 0 ≤ 1 / (8 * a) := by positivity
    linarith only [ha, hk0, hi]
  have hpay := mul_le_mul_of_nonneg_right hcoef hh0
  unfold wideHalfBound
  nlinarith only [hmid, hpay, sq_nonneg h]

theorem wideDiagonalMajorant_lt_of_width_ge_nine_fifths {a h k u v : ℝ}
    (ha0 : 9 / 5 ≤ a) (ha1 : a < 3) (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    (hk0 : 2 / 5 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hm : a - 1 / 2 - h / 4 ≤ (u + v) / 2) :
    wideDiagonalMajorant a h k u v < (41 / 50 : ℝ) := by
  have ha : 8 / 5 ≤ a := by linarith only [ha0]
  have haP : 0 < a := by linarith only [ha0]
  by_cases hak : a ≤ 1 + 2 * k
  · have hF := (wideDiagonalMajorant_le_half ha hh0 hh1 hak u v).trans
      (wideHalfBound_le_zero_tilt ha hh0 hh1 hk0 hk1 hm)
    have hmono := wide_mid_value_antitone
      (show k + 1 / 2 ≤ 9 / 5 - 1 / 2 by linarith only [hk1])
      (show 9 / 5 - 1 / 2 ≤ a - 1 / 2 by linarith only [ha0])
    nlinarith only [hF, hmono, hksq, hk1]
  · have hak' : 1 + 2 * k ≤ a := le_of_not_ge hak
    have ht := wideDiagonalMajorant_le_tangent haP hh0 (by linarith only [ha0, hh1])
      (le_refl (a / 2 - k))
      (show (a / 2 - k) / a ≤ 3 / 2 by
        apply (div_le_iff₀ haP).mpr; linarith only [ha0, hk0]) u v
    let m := (u + v) / 2
    let m0 := a - 1 / 2 - h / 4
    have hmm : m0 ≤ m := hm
    have hmid : a * m - m ^ 2 ≤ a * m0 - m0 ^ 2 := by
      have hp := mul_nonneg (sub_nonneg.mpr hmm)
        (show 0 ≤ m + m0 - a by dsimp [m0] at hmm ⊢; linarith only [hmm, ha0, hh1])
      nlinarith only [hp]
    have hformula : a - 2 * (a / 2 - k) * (a - m) + (a / 2 - k) ^ 2 - (m - k) ^ 2 -
        (5 * a / 8 - 3 * (a / 2 - k) / 2 + (a / 2 - k) ^ 2 / (2 * a)) * h =
      a - 3 * a ^ 2 / 4 + a * k + a * m - m ^ 2 - (k + k ^ 2 / (2 * a)) * h := by
      field_simp [haP.ne'] <;> ring
    change wideDiagonalMajorant a h k u v ≤ _ at ht
    rw [hformula] at ht
    have h0 : 3 * a / 2 - 3 * a ^ 2 / 4 + a * k - 1 / 4 ≤ 3 * k - 1 / 2 := by
      have hp := mul_nonneg (show 0 ≤ a - (1 + 2 * k) by linarith only [hak'])
        (show 0 ≤ 3 * (a + (1 + 2 * k)) / 4 - 3 / 2 - k by
          linarith only [hak', hk0])
      nlinarith only [hp, hksq]
    have hrat : 0 ≤ k ^ 2 / (2 * a) := by positivity
    have hcoef : (a - 1) / 4 - k - k ^ 2 / (2 * a) ≤ 1 / 2 - k := by
      linarith only [ha1, hrat]
    have hpay := mul_le_mul_of_nonneg_right hcoef hh0
    have hpay2 := mul_le_mul_of_nonneg_left hh1.le
      (show 0 ≤ 1 / 2 - k by linarith only [hk1])
    dsimp [m0] at hmid
    nlinarith only [ht, hmid, h0, hpay, hpay2, sq_nonneg h, hk1]

/-- The endpoint height sum imposes the lower bound on `m`. Before any
nearby-angle payment, a high score forces this compact small-tilt box. -/
theorem wide_diagonal_high_score_box {a h k u v : ℝ}
    (ha0 : 8 / 5 ≤ a) (ha1 : a < 3) (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    (hk0 : 2 / 5 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hm : a - 1 / 2 - h / 4 ≤ (u + v) / 2)
    (hscore : 41 / 50 ≤ wideDiagonalMajorant a h k u v) :
    a < 9 / 5 ∧ h < 1 / 4 ∧ a + h < 37 / 20 := by
  have ha9 : a < 9 / 5 := by
    by_contra hbad
    exact (not_lt_of_ge hscore) (wideDiagonalMajorant_lt_of_width_ge_nine_fifths
      (le_of_not_gt hbad) ha1 hh0 hh1 hk0 hk1 hksq hm)
  have hak : a ≤ 1 + 2 * k := by linarith only [ha9, hk0]
  have hF := wideDiagonalMajorant_le_half ha0 hh0 hh1 hak u v
  have hcoef := mul_le_mul_of_nonneg_right (wide_tilt_coefficient_ge ha0) hh0
  have hmid := wide_mid_value_antitone
    (show k + 1 / 2 ≤ 11 / 10 - h / 4 by linarith only [hh1, hk1])
    (show 11 / 10 - h / 4 ≤ (u + v) / 2 by linarith only [hm, ha0])
  have hP : 41 / 50 ≤ 27 / 20 - h / 4 - (11 / 10 - h / 4 - k) ^ 2 - (21 / 64) * h := by
    unfold wideHalfBound at hF
    linarith only [hscore, hF, hcoef, hmid]
  have hhquarter : h < 1 / 4 := by
    by_contra hbad
    have hhge : 1 / 4 ≤ h := le_of_not_gt hbad
    have hprod := mul_nonneg (show 0 ≤ h - 1 / 4 by linarith only [hhge])
      (show 0 ≤ 9 / 320 + k / 2 + (h + 1 / 4) / 16 by linarith only [hk0, hh0])
    nlinarith only [hP, hprod, hksq, hk1]
  refine ⟨ha9, hhquarter, ?_⟩
  by_contra hbad
  have hah : 37 / 20 ≤ a + h := le_of_not_gt hbad
  have hmid2 := wide_mid_value_antitone
    (show k + 1 / 2 ≤ 27 / 20 - 5 * h / 4 by linarith only [hhquarter, hk1])
    (show 27 / 20 - 5 * h / 4 ≤ (u + v) / 2 by linarith only [hm, hah])
  have hP2 : 41 / 50 ≤ 8 / 5 - (101 / 64) * h - (27 / 20 - k - 5 * h / 4) ^ 2 := by
    unfold wideHalfBound at hF
    nlinarith only [hscore, hF, hcoef, hmid2]
  nlinarith only [hP2, sq_nonneg ((27 / 20 - k - 5 * h / 4) - 101 / 160), hk1]

end AmbidextrousSofa
