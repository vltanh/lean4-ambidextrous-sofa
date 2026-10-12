module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Corner confinement from the unit circle

Below the sign change of `1 - 3s²`, the circle identity gives a quadratic
lower bound for cosine. A tangent to `s³` reduces the margin to a positive
quadratic. Above the sign change, the 3–4–5 tangent to the circle gives a
second positive quadratic. Both tests are ordinary discriminant tests.
-/

noncomputable section

namespace AmbidextrousSofa

private theorem quadratic_pos {a b d x : ℝ} (ha : 0 < a)
    (hdisc : 0 < 4 * a * d - b ^ 2) : 0 < a * x ^ 2 + b * x + d := by
  by_contra! hn
  nlinarith only [hdisc, sq_nonneg (2 * a * x + b), mul_nonpos_of_nonneg_of_nonpos ha.le hn]

theorem corner_margin_pos {s c C h : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hcircle : c ^ 2 + s ^ 2 = 1)
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 1 / 3) :
    0 < c - s - C * (1 - 3 * s ^ 2) - h * s * c := by
  have hs1 : s < 1 := by nlinarith [sq_pos_of_pos hc]
  have hhsc := mul_le_mul_of_nonneg_right hh (mul_nonneg hs.le hc.le)
  rcases le_total (s ^ 2) (1 / 3) with hsq | hsq
  · have hc0 : 4 / 5 ≤ c := by nlinarith
    have hchord : 1 - 5 / 9 * s ^ 2 ≤ c := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hc0) (sub_nonneg.mpr
        (show c ≤ 1 by nlinarith))]
    have hfactor : 0 ≤ 1 - 1 / 3 * s := by linarith
    have hbound := mul_le_mul_of_nonneg_right hchord hfactor
    have hcubic : s / 3 - 2 / 27 ≤ s ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg (s - 1 / 3))
        (by linarith : 0 ≤ s + 2 / 3)]
    have hquad := quadratic_pos (x := s)
      (a := 3 * (37 / 50) - 5 / 9)
      (b := -(1 + 1 / 3) + 5 * (1 / 3) / 27)
      (d := 1 - 37 / 50 - 10 * (1 / 3) / 243)
      (by norm_num) (by norm_num)
    have hC := mul_le_mul_of_nonneg_right hC1
      (by linarith : 0 ≤ 1 - 3 * s ^ 2)
    nlinarith only [hbound, hcubic, hquad, hC, hhsc]
  · have htangent : 3 * s + 4 * c ≤ 5 := by
      nlinarith [sq_nonneg (4 * s - 3 * c)]
    have hq := quadratic_pos (x := s) (a := 29) (b := -36) (d := 15)
      (by norm_num) (by norm_num)
    have hprod := mul_nonneg (by linarith [hs.le] : 0 ≤ 5 - 3 * s - 4 * c)
      (by linarith : 0 ≤ 3 * s + 1)
    have hbracket : 0 < 2 * (1 + s) * (1 - 2 / 5 * s) - c * (3 * s + 1) := by
      nlinarith only [hprod, hq]
    have hmargin := mul_pos hc hbracket
    have hid : c * (2 * (1 + s) * (1 - 2 / 5 * s) - c * (3 * s + 1)) =
        2 * (1 + s) * (c - s - 1 / 2 * (1 - 3 * s ^ 2) - 2 / 5 * s * c) := by
      nlinarith [hcircle]
    rw [hid] at hmargin
    have hbase : 0 < c - s - 1 / 2 * (1 - 3 * s ^ 2) - 2 / 5 * s * c :=
      (mul_pos_iff_of_pos_left (by linarith : 0 < 2 * (1 + s))).mp hmargin
    have hC := mul_le_mul_of_nonpos_right hC0
      (by linarith : 1 - 3 * s ^ 2 ≤ 0)
    have hhsc' := mul_le_mul_of_nonneg_right (by linarith : h ≤ 2 / 5)
      (mul_nonneg hs.le hc.le)
    linarith

theorem corner_margin_trig_pos {θ C h : ℝ}
    (hθ0 : 0 < θ) (hθL : θ < Real.pi / 2)
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 1 / 3) :
    0 < Real.cos θ - Real.sin θ - C * (1 - 3 * Real.sin θ ^ 2) -
      h * Real.sin θ * Real.cos θ :=
  corner_margin_pos (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos]))
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθL⟩) (Real.cos_sq_add_sin_sq θ)
    hC0 hC1 hh

end AmbidextrousSofa
