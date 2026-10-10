import AmbidextrousSofa.Analysis.CircleAverage

/-!
# Exact endpoint margins for the terminal circle comparison

The two comparison averages have widths `1/3` and `44/125`. Their
linear gaps are concave in the cap half-width, so four exact radical
endpoint bounds control the whole interval `[1/2,37/50]`. A separate
derivative calculation bounds the outgoing linear term throughout the
small-cosine range.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem circleAverage_third_half_lt :
    circleAverage (1 / 3 : ℝ) (1 / 2 : ℝ) < (2 / 3 : ℝ) := by
  have hleft : circleHeight (1 / 3 : ℝ) < (19 / 20 : ℝ) := by
    exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hright : (11 / 15 : ℝ) < circleHeight (2 / 3 : ℝ) := by
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  rw [circleAverage_eq_height_difference (by norm_num) (by constructor <;> norm_num),
    show (1 / 2 : ℝ) - (1 / 3) / 2 = 1 / 3 by norm_num,
    show (1 / 2 : ℝ) + (1 / 3) / 2 = 2 / 3 by norm_num]
  apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 1 / 3)).2
  linarith

theorem circleAverage_third_upper_lt :
    circleAverage (1 / 3 : ℝ) (37 / 50 : ℝ) < (6 / 5 : ℝ) := by
  have hleft : circleHeight (43 / 75 : ℝ) < (308 / 375 : ℝ) := by
    exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hright : (158 / 375 : ℝ) < circleHeight (68 / 75 : ℝ) := by
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  rw [circleAverage_eq_height_difference (by norm_num) (by constructor <;> norm_num),
    show (37 / 50 : ℝ) - (1 / 3) / 2 = 43 / 75 by norm_num,
    show (37 / 50 : ℝ) + (1 / 3) / 2 = 68 / 75 by norm_num]
  apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 1 / 3)).2
  linarith

theorem circleAverage_shifted_half_lt :
    circleAverage (44 / 125 : ℝ) (1 / 2 - 1 / 216 : ℝ) < (2 / 3 : ℝ) := by
  have hleft : circleHeight (8623 / 27000 : ℝ) < (19 / 20 : ℝ) := by
    exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hright : (37 / 50 : ℝ) < circleHeight (18127 / 27000 : ℝ) := by
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  rw [circleAverage_eq_height_difference (by norm_num) (by constructor <;> norm_num),
    show (1 / 2 - 1 / 216 : ℝ) - (44 / 125) / 2 = 8623 / 27000 by norm_num,
    show (1 / 2 - 1 / 216 : ℝ) + (44 / 125) / 2 = 18127 / 27000 by norm_num]
  apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 44 / 125)).2
  linarith

theorem circleAverage_shifted_upper_lt :
    circleAverage (44 / 125 : ℝ) (37 / 50 - 1 / 216 : ℝ) < (19 / 16 : ℝ) := by
  have hleft : circleHeight (15103 / 27000 : ℝ) < (829 / 1000 : ℝ) := by
    exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hright : (411 / 1000 : ℝ) < circleHeight (24607 / 27000 : ℝ) := by
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  rw [circleAverage_eq_height_difference (by norm_num) (by constructor <;> norm_num),
    show (37 / 50 - 1 / 216 : ℝ) - (44 / 125) / 2 = 15103 / 27000 by norm_num,
    show (37 / 50 - 1 / 216 : ℝ) + (44 / 125) / 2 = 24607 / 27000 by norm_num]
  apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 44 / 125)).2
  linarith

theorem terminal_circle_small_average_gap {C : ℝ}
    (hC0 : (1 / 2 : ℝ) ≤ C) (hC1 : C ≤ 37 / 50) :
    (8 / 495 : ℝ) < (35 / 33 : ℝ) * (2 * C - 1 / 3) - circleAverage (1 / 3) C := by
  have hconcave : ConcaveOn ℝ (Icc (1 / 2 : ℝ) (37 / 50 : ℝ))
      (fun x : ℝ => (35 / 33) * (2 * x - 1 / 3) - circleAverage (1 / 3) x) := by
    have h := circleAverage_linear_gap_concave
      (q := (1 / 3 : ℝ)) (e := 0) (l := (1 / 2 : ℝ)) (u := (37 / 50 : ℝ))
      (A := (70 / 33 : ℝ)) (B := (-35 / 99 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact h.congr (fun x _hx => by simp only [sub_zero]; ring)
  have hleft : (8 / 495 : ℝ) <
      (35 / 33 : ℝ) * (2 * (1 / 2) - 1 / 3) - circleAverage (1 / 3) (1 / 2) := by
    linarith [circleAverage_third_half_lt]
  have hright : (8 / 495 : ℝ) <
      (35 / 33 : ℝ) * (2 * (37 / 50) - 1 / 3) - circleAverage (1 / 3) (37 / 50) := by
    linarith [circleAverage_third_upper_lt]
  exact (lt_min hleft hright).trans_le (hconcave.min_le_of_mem_Icc
    (by constructor <;> norm_num) (by constructor <;> norm_num) ⟨hC0, hC1⟩)

theorem terminal_circle_large_average_gap {C : ℝ}
    (hC0 : (1 / 2 : ℝ) ≤ C) (hC1 : C ≤ 37 / 50) :
    (39 / 4400 : ℝ) < (35 / 33 : ℝ) * (2 * C - 44 / 125) -
      circleAverage (44 / 125) (C - 1 / 216) := by
  have hconcave : ConcaveOn ℝ (Icc (1 / 2 : ℝ) (37 / 50 : ℝ))
      (fun x : ℝ => (35 / 33) * (2 * x - 44 / 125) -
        circleAverage (44 / 125) (x - 1 / 216)) := by
    have h := circleAverage_linear_gap_concave
      (q := (44 / 125 : ℝ)) (e := (1 / 216 : ℝ))
      (l := (1 / 2 : ℝ)) (u := (37 / 50 : ℝ))
      (A := (70 / 33 : ℝ)) (B := (-308 / 825 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact h.congr (fun x _hx => by ring)
  have hleft : (39 / 4400 : ℝ) <
      (35 / 33 : ℝ) * (2 * (1 / 2) - 44 / 125) -
        circleAverage (44 / 125) (1 / 2 - 1 / 216) := by
    linarith [circleAverage_shifted_half_lt]
  have hright : (39 / 4400 : ℝ) <
      (35 / 33 : ℝ) * (2 * (37 / 50) - 44 / 125) -
        circleAverage (44 / 125) (37 / 50 - 1 / 216) := by
    linarith [circleAverage_shifted_upper_lt]
  exact (lt_min hleft hright).trans_le (hconcave.min_le_of_mem_Icc
    (by constructor <;> norm_num) (by constructor <;> norm_num) ⟨hC0, hC1⟩)

def circleTerminalLinearRatio (C x : ℝ) : ℝ := (2 * C - x) / circleHeight x

theorem hasDerivAt_circleTerminalLinearRatio {C x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (circleTerminalLinearRatio C) ((2 * C * x - 1) / circleHeight x ^ 3) x := by
  have hroot := (circleHeight_pos hx).ne'
  have hd := ((hasDerivAt_id x).const_sub (2 * C)).div (hasDerivAt_circleHeight hx) hroot
  apply hd.congr_deriv
  calc
    _ = (-circleHeight x ^ 2 + (2 * C - x) * x) / circleHeight x ^ 3 := by
      unfold circleSlope
      field_simp [hroot] <;> ring
    _ = _ := by rw [circleHeight_sq hx]; ring

theorem circleTerminalLinearRatio_antitone_small {C c : ℝ}
    (hC : C ≤ 37 / 50) (hc0 : 0 < c) (hc1 : c ≤ 1 / 3) :
    AntitoneOn (circleTerminalLinearRatio C) (Icc c (1 / 3 : ℝ)) := by
  have hdom (x : ℝ) (hx : x ∈ Icc c (1 / 3 : ℝ)) : x ∈ Ioo (0 : ℝ) 1 :=
    ⟨hc0.trans_le hx.1, by linarith [hx.2]⟩
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    (fun x hx => (hasDerivAt_circleTerminalLinearRatio (hdom x hx)).continuousAt.continuousWithinAt)
    (fun x hx => (hasDerivAt_circleTerminalLinearRatio (hdom x (interior_subset hx))).hasDerivWithinAt)
    ?_
  intro x hx
  have hxm := interior_subset hx
  have hx0 := (hdom x hxm).1
  apply div_nonpos_of_nonpos_of_nonneg _ (pow_nonneg (circleHeight_nonneg x) 3)
  nlinarith [mul_nonneg (show 0 ≤ 37 / 50 - C by linarith) hx0.le,
    mul_nonneg (show 0 ≤ 1 / 3 - x by linarith [hxm.2])
      (by norm_num : (0 : ℝ) ≤ 37 / 50)]

theorem terminal_circle_small_linear_lower {C c s : ℝ}
    (hC0 : (1 / 2 : ℝ) ≤ C) (hC1 : C ≤ 37 / 50)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 3) (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1) :
    (35 / 33 : ℝ) * (2 * C - 1 / 3) < (2 * C - c) / s := by
  have hroot : circleHeight (1 / 3 : ℝ) < (33 / 35 : ℝ) := by
    exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hpositive : 0 < 2 * C - 1 / 3 := by linarith
  have hlower : (35 / 33 : ℝ) * (2 * C - 1 / 3) < circleTerminalLinearRatio C (1 / 3) := by
    have h := div_lt_div_of_pos_left hpositive
      (circleHeight_pos (by constructor <;> norm_num : (1 / 3 : ℝ) ∈ Ioo (0 : ℝ) 1)) hroot
    change (2 * C - 1 / 3) / (33 / 35) < (2 * C - 1 / 3) / circleHeight (1 / 3) at h
    unfold circleTerminalLinearRatio
    convert h using 1 <;> ring
  have hsroot : s = circleHeight c := by
    unfold circleHeight
    symm
    apply (Real.sqrt_eq_iff_eq_sq (by nlinarith [sq_nonneg s]) hs.le).2
    nlinarith
  rw [hsroot]
  exact hlower.trans_le ((circleTerminalLinearRatio_antitone_small hC1 hc0 hc1)
    ⟨le_rfl, hc1⟩ ⟨hc1, le_rfl⟩ hc1)

theorem terminal_cosine_lt_forty_four_one_twenty_fifths {c : ℝ}
    (hc : 0 < c) (hcut : 73 * c ^ 2 ≤ 9) : c < (44 / 125 : ℝ) := by
  by_contra h
  have hs := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 44 / 125) hc.le).2 (le_of_not_gt h)
  nlinarith only [hs, hcut]

theorem terminal_circle_large_linear_lower {C c s : ℝ}
    (hC : (1 / 2 : ℝ) ≤ C) (hc0 : (1 / 3 : ℝ) ≤ c)
    (hc1 : c < 44 / 125) (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1) :
    (35 / 33 : ℝ) * (2 * C - 44 / 125) < (2 * C - c) / s := by
  have hcsq := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (show 0 ≤ c by linarith)).2 hc0
  have hsbound : s < (33 / 35 : ℝ) := by
    by_contra h
    have hsq := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 33 / 35) hs.le).2 (le_of_not_gt h)
    nlinarith only [hcsq, hsq, hcs]
  have hpos : 0 < 2 * C - 44 / 125 := by linarith
  calc
    _ = (2 * C - 44 / 125) / (33 / 35 : ℝ) := by ring
    _ < (2 * C - 44 / 125) / s := div_lt_div_of_pos_left hpos hs hsbound
    _ < (2 * C - c) / s := (div_lt_div_iff_of_pos_right hs).2 (by linarith)

end AmbidextrousSofa
