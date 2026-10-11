module

public import AmbidextrousSofa.Analysis.CircleAverage

@[expose] public section

/-!
# Exact endpoint margins for the terminal circle comparison

The two comparison averages have widths `1/3` and `44/125`. Their
linear gaps are concave in the cap half-width, so four exact radical
endpoint bounds control the whole interval `[1/2,37/50]`. A tangent line
of the unit circle bounds the outgoing linear term throughout the
small-cosine range.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

/-- An upper bound for a circle average from rational bounds on its two endpoint heights. -/
theorem circleAverage_lt_of_heights {q y L R : ℝ} (hq : 0 < q)
    (hy : y ∈ Ioo (q / 2) (1 - q / 2)) (hL0 : 0 < L) (hL : 1 - (y - q / 2) ^ 2 < L ^ 2)
    (hR : R ^ 2 < 1 - (y + q / 2) ^ 2) :
    circleAverage q y < (L - R) / q := by
  rw [circleAverage_eq_height_difference hq hy, circleHeight, circleHeight]
  exact div_lt_div_of_pos_right
    (by linarith [(Real.sqrt_lt' hL0).2 hL, Real.lt_sqrt_of_sq_lt hR]) hq

theorem terminal_circle_small_average_gap {C : ℝ}
    (hC0 : (1 / 2 : ℝ) ≤ C) (hC1 : C ≤ 37 / 50) :
    (8 / 495 : ℝ) < (35 / 33 : ℝ) * (2 * C - 1 / 3) - circleAverage (1 / 3) C := by
  have h := (circleAverage_linear_gap_concave (q := 1 / 3) (e := 0) (l := 1 / 2) (u := 37 / 50)
    (A := 70 / 33) (B := -35 / 99) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).min_le_of_mem_Icc (by norm_num) (by norm_num) ⟨hC0, hC1⟩
  have h1 := circleAverage_lt_of_heights (q := 1 / 3) (y := 1 / 2) (L := 19 / 20)
    (R := 11 / 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := circleAverage_lt_of_heights (q := 1 / 3) (y := 37 / 50) (L := 308 / 375)
    (R := 158 / 375) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [sub_zero, min_le_iff] at h
  rcases h with h | h <;> linarith

theorem terminal_circle_large_average_gap {C : ℝ}
    (hC0 : (1 / 2 : ℝ) ≤ C) (hC1 : C ≤ 37 / 50) :
    (39 / 4400 : ℝ) < (35 / 33 : ℝ) * (2 * C - 44 / 125) -
      circleAverage (44 / 125) (C - 1 / 216) := by
  have h := (circleAverage_linear_gap_concave (q := 44 / 125) (e := 1 / 216) (l := 1 / 2)
    (u := 37 / 50) (A := 70 / 33) (B := -308 / 825) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).min_le_of_mem_Icc (by norm_num) (by norm_num) ⟨hC0, hC1⟩
  have h1 := circleAverage_lt_of_heights (q := 44 / 125) (y := 1 / 2 - 1 / 216) (L := 19 / 20)
    (R := 37 / 50) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := circleAverage_lt_of_heights (q := 44 / 125) (y := 37 / 50 - 1 / 216)
    (L := 829 / 1000) (R := 411 / 1000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  rcases min_le_iff.mp h with h | h <;> linarith

/-- The tangent line of the unit circle at `(145/433, 408/433)` gives the bound. -/
theorem terminal_circle_small_linear_lower {C c s : ℝ}
    (hC0 : (1 / 2 : ℝ) ≤ C) (hC1 : C ≤ 37 / 50)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 3) (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1) :
    (35 / 33 : ℝ) * (2 * C - 1 / 3) < (2 * C - c) / s := by
  have h : 145 * c + 408 * s ≤ 433 := by nlinarith [sq_nonneg (408 * c - 145 * s)]
  rw [lt_div_iff₀ hs]
  nlinarith [mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 2 * C - 1 / 3)]

theorem terminal_cosine_lt_forty_four_one_twenty_fifths {c : ℝ}
    (hc : 0 < c) (hcut : 73 * c ^ 2 ≤ 9) : c < (44 / 125 : ℝ) := by nlinarith

theorem terminal_circle_large_linear_lower {C c s : ℝ}
    (hC : (1 / 2 : ℝ) ≤ C) (hc0 : (1 / 3 : ℝ) ≤ c)
    (hc1 : c < 44 / 125) (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1) :
    (35 / 33 : ℝ) * (2 * C - 44 / 125) < (2 * C - c) / s := by
  have hs1 : s < 33 / 35 := by nlinarith
  rw [lt_div_iff₀ hs]
  nlinarith [mul_lt_mul_of_pos_left hs1 (by linarith : (0 : ℝ) < 2 * C - 44 / 125)]

end AmbidextrousSofa
