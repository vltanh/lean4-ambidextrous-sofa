module

public import AmbidextrousSofa.Analysis.TerminalCircleEndpoints

@[expose] public section

/-!
# The uniform proper-terminal circle margin

The two exact circle-average comparisons cover every cosine left by AT.
Their strict margin is retained after restoring the actual terminal
height, both top overhangs, and every point of the terminal reserve
interval. This is the scalar inequality MP.24. The hypotheses concern
the displayed geometric parameters, not a bound on the cap score.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

/-- The margin for a comparison interval `[C - d, C + c - d]` whose shift `d - c/2` is at
least cubic in the cosine. -/
theorem terminal_circle_normalized_margin {C c s d : ℝ}
    (hC0 : (1 / 2 : ℝ) ≤ C) (hC1 : C ≤ 37 / 50)
    (hc : 0 < c) (hcut : 73 * c ^ 2 ≤ 9) (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hd : c / 2 + c ^ 3 / 8 ≤ d) (hdc : d < c) :
    (39 / 4400 : ℝ) * c <
      c / s * (2 * C - c) - (circleHeight (C - d) - circleHeight (C + c - d)) := by
  have hcQ := terminal_cosine_lt_forty_four_one_twenty_fifths hc hcut
  have hc3 : 0 ≤ c ^ 3 := by positivity
  have hy : C + c / 2 - d ∈ Ioo (c / 2) (1 - c / 2) := ⟨by linarith, by linarith⟩
  have hm : (39 / 4400 : ℝ) < (2 * C - c) / s - circleAverage c (C + c / 2 - d) := by
    rcases le_or_gt c (1 / 3) with hc1 | hc1
    · have := (circleAverage_mono_center hc.le hy ⟨by linarith, by linarith⟩
        (by linarith : C + c / 2 - d ≤ C)).trans (circleAverage_mono_width hc.le
          (by norm_num : (0 : ℝ) < 1 / 3) hc1 ⟨by linarith, by linarith⟩)
      linarith [terminal_circle_small_linear_lower hC0 hC1 hc hc1 hs hcs,
        terminal_circle_small_average_gap hC0 hC1]
    · have h216 : C + c / 2 - d ≤ C - 1 / 216 := by
        linarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 3) hc1.le 3]
      have := (circleAverage_mono_center hc.le hy ⟨by linarith, by linarith⟩ h216).trans
        (circleAverage_mono_width hc.le (by norm_num : (0 : ℝ) < 44 / 125) hcQ.le
          ⟨by linarith, by linarith⟩)
      linarith [terminal_circle_large_linear_lower hC0 hc1.le hcQ hs hcs,
        terminal_circle_large_average_gap hC0 hC1]
  calc (39 / 4400 : ℝ) * c < ((2 * C - c) / s - circleAverage c (C + c / 2 - d)) * c :=
        mul_lt_mul_of_pos_right hm hc
    _ = _ := by
      rw [circleAverage_eq_height_difference hc hy, show C + c / 2 - d - c / 2 = C - d by ring,
        show C + c / 2 - d + c / 2 = C + c - d by ring]
      field_simp

/-- Restoring the exact terminal height gives MP.24 with
`d = (1 - H*s)/c`, including the residual negative-tilt case. -/
theorem terminal_circle_margin_of_height {C c s H T_L T_R z : ℝ}
    (hC0 : (1 / 2 : ℝ) ≤ C) (hC1 : C ≤ 37 / 50)
    (hc : 0 < c) (hcut : 73 * c ^ 2 ≤ 9) (hs : 0 < s)
    (hcs : c ^ 2 + s ^ 2 = 1) (hHs : s < H) (hH1 : H ≤ 1)
    (hTL : 0 ≤ T_L) (hTR : 0 ≤ T_R)
    (htop : T_L + 2 * T_R ≤ (1 - H * s) / c)
    (hz0 : 0 ≤ z) (hz1 : z ≤ c - (1 - H * s) / c) :
    (39 / 4400 : ℝ) * c < c / s * (2 * C + T_R - (1 - H * s) / c - z) -
      (circleHeight (C - T_L) - circleHeight (C + z)) := by
  have hs1 : s ≤ 1 := by nlinarith
  have hd : c / 2 + c ^ 3 / 8 ≤ (1 - H * s) / c := by
    rw [le_div_iff₀ hc]
    nlinarith [mul_nonneg (pow_nonneg (sub_nonneg.2 hs1) 3) (by linarith : (0 : ℝ) ≤ 3 + s),
      mul_nonneg (sub_nonneg.2 hH1) hs.le, show c ^ 4 = (1 - s ^ 2) ^ 2 by rw [← hcs]; ring]
  have hdc : (1 - H * s) / c < c := (div_lt_iff₀ hc).2 (by nlinarith [mul_pos (sub_pos.2 hHs) hs])
  generalize (1 - H * s) / c = d at *
  have hcQ := terminal_cosine_lt_forty_four_one_twenty_fifths hc hcut
  have hc3 : 0 ≤ c ^ 3 := by positivity
  have h1 := circleHeight_antitoneOn (show C - d ∈ Ioo 0 1 from ⟨by linarith, by linarith⟩)
    (show C - T_L ∈ Ioo 0 1 from ⟨by linarith, by linarith⟩) (by linarith)
  have h2 := circleHeight_antitoneOn (show C + z ∈ Ioo 0 1 from ⟨by linarith, by linarith⟩)
    (show C + c - d ∈ Ioo 0 1 from ⟨by linarith, by linarith⟩) (by linarith)
  linarith [terminal_circle_normalized_margin hC0 hC1 hc hcut hs hcs hd hdc,
    mul_le_mul_of_nonneg_left (show 2 * C - c ≤ 2 * C + T_R - d - z by linarith)
      (div_nonneg hc.le hs.le)]

end AmbidextrousSofa
