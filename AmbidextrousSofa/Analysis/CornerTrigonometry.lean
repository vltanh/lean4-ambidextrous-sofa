module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Exact corner confinement margins

Two rational polynomial certificates prove the strict trigonometric
margin on the entire stated range. They use only the unit-circle
identity and signs of sine and cosine. The first certificate is a
translated quartic; the second is a cubic with a positive quadratic
lower bound. Neither uses numerical approximation or curvature bounds.
-/

noncomputable section

namespace AmbidextrousSofa

theorem corner_quartic_pos {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 3 / 5) :
    0 < 1131 - 5400 * s + 3503 * s ^ 2 + 12800 * s ^ 3 - 12610 * s ^ 4 := by
  nlinarith [mul_nonneg (sq_nonneg (s - 3 / 8)) (mul_nonneg hs0 (sub_nonneg.mpr hs1)),
    sq_nonneg (s - 3 / 8), sq_nonneg (s - 3 / 8 - 2091 / 640000)]

theorem corner_cubic_pos {s : ℝ} (hs : 1 / 2 ≤ s) :
    0 < 75 - 105 * s - 139 * s ^ 2 + 241 * s ^ 3 := by
  linarith [pow_nonneg (sub_nonneg.mpr hs) 3, sq_nonneg (s - 1 / 2 - 253 / 1780)]

theorem corner_margin_pos {s c C h : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hcircle : c ^ 2 + s ^ 2 = 1)
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50) :
    0 < c - s - C * (1 - 3 * s ^ 2) - h * s * c := by
  have hc2 : c ^ 2 = 1 - s ^ 2 := by linarith
  have hsc := mul_nonneg hs.le hc.le
  have hhsc := mul_le_mul_of_nonneg_right hh hsc
  rcases le_total (s ^ 2) (1 / 3) with hsq | hsq
  · have hs1 : s ≤ 3 / 5 := by nlinarith
    have key : 37 + 50 * s - 111 * s ^ 2 < c * (50 - 17 * s) := by
      refine lt_of_pow_lt_pow_left₀ 2 (mul_nonneg hc.le (by linarith)) ?_
      rw [mul_pow c, hc2]
      linarith [corner_quartic_pos hs.le hs1]
    linarith [mul_le_mul_of_nonneg_right hC1 (by linarith : 0 ≤ 1 - 3 * s ^ 2)]
  · have hs0 : 1 / 2 ≤ s := by nlinarith
    have hs1 : s < 1 := by nlinarith
    have key : (1 + 3 * s) * (1 - s) < c * (2 - 4 / 5 * s) := by
      refine lt_of_pow_lt_pow_left₀ 2 (mul_nonneg hc.le (by linarith)) ?_
      rw [mul_pow c, hc2]
      linarith [mul_pos (sub_pos.mpr hs1) (corner_cubic_pos hs0)]
    linarith [mul_le_mul_of_nonpos_right hC0 (by linarith : 1 - 3 * s ^ 2 ≤ 0)]

theorem corner_margin_trig_pos {θ C h : ℝ}
    (hθ0 : 0 < θ) (hθL : θ < Real.pi / 2)
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50) :
    0 < Real.cos θ - Real.sin θ - C * (1 - 3 * Real.sin θ ^ 2) -
      h * Real.sin θ * Real.cos θ :=
  corner_margin_pos (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos]))
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθL⟩) (Real.cos_sq_add_sin_sq θ)
    hC0 hC1 hh

end AmbidextrousSofa
