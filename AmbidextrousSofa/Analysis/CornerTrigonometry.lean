import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

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
  let z := s - 3 / 8
  have hz0 : -(3 : ℝ) / 8 ≤ z := by dsimp [z]; linarith
  have hz1 : z ≤ 9 / 40 := by dsimp [z]; linarith
  have hinterval := mul_nonneg (sub_nonneg.mpr hz0) (sub_nonneg.mpr hz1)
  have hbracket : 5000 ≤ 116213 / 16 - 6115 * z - 12610 * z ^ 2 := by
    nlinarith
  have hproduct := mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hbracket)
  have hpositive : 0 < 49647 / 2048 - (2091 / 64) * z +
      z ^ 2 * (116213 / 16 - 6115 * z - 12610 * z ^ 2) := by
    nlinarith [sq_nonneg (z - 2091 / 640000)]
  have hid : 1131 - 5400 * s + 3503 * s ^ 2 + 12800 * s ^ 3 - 12610 * s ^ 4 =
      49647 / 2048 - (2091 / 64) * z +
        z ^ 2 * (116213 / 16 - 6115 * z - 12610 * z ^ 2) := by
    dsimp [z]
    ring
  rwa [hid]

theorem corner_cubic_pos {s : ℝ} (hs : 1 / 2 ≤ s) :
    0 < 75 - 105 * s - 139 * s ^ 2 + 241 * s ^ 3 := by
  let z := 2 * s - 1
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hz3 := mul_nonneg (sq_nonneg z) hz
  have hpositive : 0 < 143 - 253 * z + 445 * z ^ 2 + 241 * z ^ 3 := by
    nlinarith [sq_nonneg (z - 253 / 890)]
  have hid : 8 * (75 - 105 * s - 139 * s ^ 2 + 241 * s ^ 3) =
      143 - 253 * z + 445 * z ^ 2 + 241 * z ^ 3 := by
    dsimp [z]
    ring
  nlinarith

theorem corner_margin_small_s {s c C h : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hcircle : c ^ 2 + s ^ 2 = 1)
    (hsq : s ^ 2 ≤ 1 / 3) (hC : C ≤ 37 / 50) (hh : h ≤ 17 / 50) :
    0 < c - s - C * (1 - 3 * s ^ 2) - h * s * c := by
  have hs1 : s ≤ 3 / 5 := by nlinarith
  have hquartic := corner_quartic_pos hs.le hs1
  have hA : 0 ≤ c * (50 - 17 * s) :=
    mul_nonneg hc.le (by linarith)
  have hB : 0 ≤ 37 + 50 * s - 111 * s ^ 2 := by
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hs1)]
  have hcircle' := congrArg (fun x : ℝ => x * (50 - 17 * s) ^ 2) hcircle
  have hsqdiff : 0 < (c * (50 - 17 * s)) ^ 2 -
      (37 + 50 * s - 111 * s ^ 2) ^ 2 := by
    nlinarith
  have hcompare : 37 + 50 * s - 111 * s ^ 2 < c * (50 - 17 * s) := by
    by_contra hnot
    have hprod := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hnot)) (add_nonneg hA hB)
    nlinarith
  have hCmul := mul_le_mul_of_nonneg_right hC (by nlinarith : 0 ≤ 1 - 3 * s ^ 2)
  have hhmul := mul_le_mul_of_nonneg_right hh (mul_nonneg hs.le hc.le)
  nlinarith

theorem corner_margin_large_s {s c C h : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hcircle : c ^ 2 + s ^ 2 = 1)
    (hsq : 1 / 3 ≤ s ^ 2) (hC : 1 / 2 ≤ C) (hh : h ≤ 2 / 5) :
    0 < c - s - C * (1 - 3 * s ^ 2) - h * s * c := by
  have hs0 : 1 / 2 ≤ s := by nlinarith
  have hs1 : s ≤ 1 := by nlinarith [sq_nonneg c]
  have hcubic := corner_cubic_pos hs0
  have hA : 0 ≤ 2 * (1 + s) * (1 - (2 / 5) * s) := by
    apply mul_nonneg
    · positivity
    · linarith
  have hB : 0 ≤ c * (3 * s + 1) := by positivity
  have hcircle' := congrArg (fun x : ℝ => x * (3 * s + 1) ^ 2) hcircle
  have hprod := mul_pos (by linarith : 0 < 1 + s) hcubic
  have hsqdiff : 0 < (2 * (1 + s) * (1 - (2 / 5) * s)) ^ 2 -
      (c * (3 * s + 1)) ^ 2 := by
    nlinarith
  have hcompare : c * (3 * s + 1) < 2 * (1 + s) * (1 - (2 / 5) * s) := by
    by_contra hnot
    have hproduct := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hnot)) (add_nonneg hA hB)
    nlinarith
  have hden : 0 < 2 * (1 + s) := by linarith
  have hbase : 0 < c - s - (1 - 3 * s ^ 2) / 2 - (2 / 5) * s * c := by
    have hpositive := mul_pos hc (sub_pos.mpr hcompare)
    have hcircle'' := congrArg (fun x : ℝ => x * (3 * s + 1)) hcircle
    have hid : (c - s - (1 - 3 * s ^ 2) / 2 - (2 / 5) * s * c) *
        (2 * (1 + s)) = c * (2 * (1 + s) * (1 - (2 / 5) * s) - c * (3 * s + 1)) := by
      nlinarith
    by_contra hnot
    have hnonpos := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot) hden.le
    rw [hid] at hnonpos
    exact (not_lt_of_ge hnonpos) hpositive
  have hCmul := mul_le_mul_of_nonpos_right hC (by nlinarith : 1 - 3 * s ^ 2 ≤ 0)
  have hhmul := mul_le_mul_of_nonneg_right hh (mul_nonneg hs.le hc.le)
  nlinarith

theorem corner_margin_pos {s c C h : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hcircle : c ^ 2 + s ^ 2 = 1)
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50) :
    0 < c - s - C * (1 - 3 * s ^ 2) - h * s * c := by
  by_cases hsq : s ^ 2 ≤ 1 / 3
  · exact corner_margin_small_s hs hc hcircle hsq hC1 hh
  · exact corner_margin_large_s hs hc hcircle (le_of_not_ge hsq) hC0 (by linarith)

theorem corner_margin_trig_pos {θ C h : ℝ}
    (hθ0 : 0 < θ) (hθL : θ < Real.pi / 2)
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50) :
    0 < Real.cos θ - Real.sin θ - C * (1 - 3 * Real.sin θ ^ 2) -
      h * Real.sin θ * Real.cos θ := by
  apply corner_margin_pos
    (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos]))
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθL⟩)
    (Real.cos_sq_add_sin_sq θ) hC0 hC1 hh

end AmbidextrousSofa
