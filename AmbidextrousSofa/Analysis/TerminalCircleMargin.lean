import AmbidextrousSofa.Analysis.TerminalCircleEndpoints

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

theorem terminal_circle_normalized_margin {C c s η : ℝ}
    (hC0 : (1 / 2 : ℝ) ≤ C) (hC1 : C ≤ 37 / 50)
    (hc : 0 < c) (hcut : 73 * c ^ 2 ≤ 9) (hs : 0 < s)
    (hcs : c ^ 2 + s ^ 2 = 1)
    (hη0 : 0 ≤ η) (hη1 : η < c / 2) (hηcube : c ^ 3 / 8 ≤ η) :
    (39 / 4400 : ℝ) < (2 * C - c) / s - circleAverage c (C - η) := by
  have hcQ := terminal_cosine_lt_forty_four_one_twenty_fifths hc hcut
  have hy : C - η ∈ Ioo (c / 2) (1 - c / 2) :=
    ⟨by linarith, by linarith⟩
  by_cases hcsmall : c ≤ 1 / 3
  · have hCy : C ∈ Ioo (c / 2) (1 - c / 2) := ⟨by linarith, by linarith⟩
    have hCQ : C ∈ Ioo ((1 / 3 : ℝ) / 2) (1 - (1 / 3 : ℝ) / 2) :=
      ⟨by linarith, by linarith⟩
    have havg := (circleAverage_mono_center hc.le hy hCy (by linarith)).trans
      (circleAverage_mono_width hc.le (by norm_num : (0 : ℝ) < 1 / 3) hcsmall hCQ)
    have hlinear := terminal_circle_small_linear_lower hC0 hC1 hc hcsmall hs hcs
    have hgap := terminal_circle_small_average_gap hC0 hC1
    have hrat : (39 / 4400 : ℝ) < 8 / 495 := by norm_num
    linarith
  · have hclarge : (1 / 3 : ℝ) ≤ c := le_of_not_ge hcsmall
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 3) hclarge 3
    have hηcut : (1 / 216 : ℝ) ≤ η := by nlinarith only [hpow, hηcube]
    have hCy : C - 1 / 216 ∈ Ioo (c / 2) (1 - c / 2) :=
      ⟨by linarith, by linarith⟩
    have hCQ : C - 1 / 216 ∈ Ioo ((44 / 125 : ℝ) / 2) (1 - (44 / 125 : ℝ) / 2) :=
      ⟨by linarith, by linarith⟩
    have havg := (circleAverage_mono_center hc.le hy hCy (by linarith)).trans
      (circleAverage_mono_width hc.le (by norm_num : (0 : ℝ) < 44 / 125) hcQ.le hCQ)
    have hlinear := terminal_circle_large_linear_lower hC0 hclarge hcQ hs hcs
    have hgap := terminal_circle_large_average_gap hC0 hC1
    linarith

/-- The exact shift of the symmetric comparison interval is cubic in
the cosine. Its lower bound supplies the second comparison's shift. -/
theorem terminal_circle_shift_bounds {c s : ℝ}
    (hc : 0 < c) (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1) :
    0 ≤ c / (1 + s) - c / 2 ∧
      c / (1 + s) - c / 2 < c / 2 ∧
      c ^ 3 / 8 ≤ c / (1 + s) - c / 2 := by
  have hden : 0 < 1 + s := by linarith
  have hs1 : s ≤ 1 :=
    (sq_le_sq₀ hs.le (by norm_num : (0 : ℝ) ≤ 1)).1 (by nlinarith [sq_nonneg c])
  have hhalf : c / 2 ≤ c / (1 + s) := by
    apply (le_div_iff₀ hden).2
    nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hs1)]
  have hfull : c / (1 + s) < c := by
    apply (div_lt_iff₀ hden).2
    nlinarith [mul_pos hc hs]
  have hidentity : c / (1 + s) - c / 2 = c ^ 3 / (2 * (1 + s) ^ 2) := by
    have hscaled := congrArg (fun x : ℝ => c * x) hcs
    field_simp [hden.ne'] <;> nlinarith only [hscaled]
  refine ⟨by linarith, by linarith, ?_⟩
  rw [hidentity]
  exact div_le_div_of_nonneg_left (pow_nonneg hc.le 3)
    (by positivity : 0 < 2 * (1 + s) ^ 2)
    (by nlinarith [sq_nonneg c])

/-- The terminal inset is allowed to be larger than its height-one
value. Its whole actual value, both top overhangs, and every reserve
abscissa are retained in the conclusion. -/
theorem terminal_circle_margin {C c s d T_L T_R z : ℝ}
    (hC0 : (1 / 2 : ℝ) ≤ C) (hC1 : C ≤ 37 / 50)
    (hc : 0 < c) (hcut : 73 * c ^ 2 ≤ 9) (hs : 0 < s)
    (hcs : c ^ 2 + s ^ 2 = 1)
    (hdlo : c / (1 + s) ≤ d) (hdhi : d < c)
    (hTL : 0 ≤ T_L) (hTR : 0 ≤ T_R) (htop : T_L + 2 * T_R ≤ d)
    (hz0 : 0 ≤ z) (hz1 : z ≤ c - d) :
    (39 / 4400 : ℝ) * c < c / s * (2 * C + T_R - d - z) -
      (circleHeight (C - T_L) - circleHeight (C + z)) := by
  have hcQ := terminal_cosine_lt_forty_four_one_twenty_fifths hc hcut
  obtain ⟨hη0, hη1, hηcube⟩ := terminal_circle_shift_bounds hc hs hcs
  let η := c / (1 + s) - c / 2
  have hdhalf : c / 2 ≤ d := by linarith
  have hd0 : 0 < d := by linarith
  have hTLd : T_L ≤ d := by linarith
  have hCd : C - d ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hCT : C - T_L ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hCz : C + z ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hCend : C + c - d ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hcircle : circleHeight (C - T_L) - circleHeight (C + z) ≤
      circleHeight (C - d) - circleHeight (C + c - d) := by
    have hleft := circleHeight_antitoneOn hCd hCT (by linarith)
    have hright := circleHeight_antitoneOn hCz hCend (by linarith)
    linarith
  have hD : C + c / 2 - d ∈ Ioo (c / 2) (1 - c / 2) :=
    ⟨by linarith [hCd.1], by linarith [hCend.2]⟩
  have hηmem : C - η ∈ Ioo (c / 2) (1 - c / 2) := by
    dsimp [η]
    constructor <;> linarith
  have hdiff : circleHeight (C - d) - circleHeight (C + c - d) =
      c * circleAverage c (C + c / 2 - d) := by
    rw [circleAverage_eq_height_difference hc hD,
      show C + c / 2 - d - c / 2 = C - d by ring,
      show C + c / 2 - d + c / 2 = C + c - d by ring]
    field_simp [hc.ne'] <;> ring
  have havg := circleAverage_mono_center hc.le hD hηmem
    (show C + c / 2 - d ≤ C - η by dsimp [η]; linarith)
  have hcircle' : circleHeight (C - T_L) - circleHeight (C + z) ≤
      c * circleAverage c (C - η) := by
    rw [hdiff] at hcircle
    exact hcircle.trans (mul_le_mul_of_nonneg_left havg hc.le)
  have hnorm := terminal_circle_normalized_margin hC0 hC1 hc hcut hs hcs hη0 hη1 hηcube
  change (39 / 4400 : ℝ) < (2 * C - c) / s - circleAverage c (C - η) at hnorm
  have hscaled := mul_lt_mul_of_pos_left hnorm hc
  have hscaled' : (39 / 4400 : ℝ) * c <
      c / s * (2 * C - c) - c * circleAverage c (C - η) := by
    convert hscaled using 1 <;> ring
  have hwall : c / s * (2 * C - c) ≤ c / s * (2 * C + T_R - d - z) :=
    mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hc.le hs.le)
  linarith

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
  have hden : 0 < 1 + s := by linarith
  have hidentity : c / (1 + s) = (1 - s) / c := by
    field_simp [hc.ne', hden.ne'] <;> nlinarith only [hcs]
  have hdlo : c / (1 + s) ≤ (1 - H * s) / c := by
    rw [hidentity]
    apply div_le_div_of_nonneg_right _ hc.le
    nlinarith [mul_le_mul_of_nonneg_right hH1 hs.le]
  have hdhi : (1 - H * s) / c < c := by
    apply (div_lt_iff₀ hc).2
    nlinarith [mul_pos (sub_pos.mpr hHs) hs]
  exact terminal_circle_margin hC0 hC1 hc hcut hs hcs hdlo hdhi hTL hTR htop hz0 hz1

end AmbidextrousSofa
