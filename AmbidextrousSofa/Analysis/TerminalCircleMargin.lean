module

public import AmbidextrousSofa.Analysis.TerminalCircleEndpoints

@[expose] public section

/-!
# The uniform proper-terminal circle margin

A tangent to the circle controls widening the comparison chord. Its
linear gain pays for the cubic shift of the chord center, using the
circle slope bound three. One comparison covers every remaining cosine;
its available gap survives the actual terminal height and overhangs.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

private theorem circleHeight_drop_le_three {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 37 / 50 + 3 / 16) :
    circleHeight x - circleHeight y ≤ 3 * (y - x) := by
  have hxm : x ∈ Ioo (0 : ℝ) 1 := ⟨hx, by linarith⟩
  have hym : y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hsx := circleHeight_sq hxm
  have hsy := circleHeight_sq hym
  have hlx : x ≤ 3 * circleHeight x := by
    nlinarith [circleHeight_pos hxm]
  have hly : y ≤ 3 * circleHeight y := by
    nlinarith [circleHeight_pos hym]
  have hp : (circleHeight x - circleHeight y) * (circleHeight x + circleHeight y) ≤
      (3 * (y - x)) * (circleHeight x + circleHeight y) := by
    nlinarith only [hsx, hsy, mul_nonneg (sub_nonneg.mpr hxy)
      (by linarith only [hlx, hly] : 0 ≤ 3 * (circleHeight x + circleHeight y) - (x + y))]
  exact le_of_mul_le_mul_right hp (by linarith [circleHeight_pos hxm, circleHeight_pos hym])

private theorem circleAverage_center_payment {q x y : ℝ}
    (hq : 0 < q) (hx : x ∈ Ioo (q / 2) (1 - q / 2))
    (hy : y ∈ Ioo (q / 2) (1 - q / 2)) (hxy : x ≤ y)
    (hy1 : y + q / 2 ≤ 37 / 50 + 3 / 16) :
    circleAverage q y - circleAverage q x ≤ 3 / q * (y - x) := by
  have hl := circleHeight_antitoneOn
    (show x - q / 2 ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    (show y - q / 2 ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    (by linarith)
  have hr := circleHeight_drop_le_three (by linarith [hx.1] : 0 < x + q / 2)
    (by linarith : x + q / 2 ≤ y + q / 2) hy1
  rw [circleAverage_eq_height_difference hq hy, circleAverage_eq_height_difference hq hx,
    div_sub_div_same, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hq]
  linarith

private theorem terminal_linear_tangent_payment {C c s q S : ℝ}
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 37 / 50) (hc : 0 < c) (hcq : c ≤ q)
    (hq : 0 < q) (hq1 : q ≤ 3 / 8) (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hS : 0 < S) (hqS : q ^ 2 + S ^ 2 = 1) :
    (2 * C - q) / S + (q - c) * (1 - 2 * C * q) ≤ (2 * C - c) / s := by
  have htangent : q * c + S * s ≤ 1 := by
    nlinarith only [sq_nonneg (q - c), sq_nonneg (S - s), hcs, hqS]
  have hS1 : S ≤ 1 := by nlinarith
  have hden : 0 < 1 - q * c := by nlinarith
  have hg : 0 ≤ 1 - 2 * C * q := by nlinarith
  have hA : 0 ≤ 2 * C - c := by linarith
  have hmul := mul_le_mul_of_nonneg_left htangent hA
  have hpayment := mul_nonneg (mul_nonneg (sub_nonneg.mpr hcq) hg)
    (show 0 ≤ 1 - S * (1 - q * c) by nlinarith [mul_nonneg hS.le (mul_nonneg hq.le hc.le)])
  have hbase : (2 * C - c) * S / (1 - q * c) ≤ (2 * C - c) / s := by
    rw [div_le_div_iff₀ hden hs]
    nlinarith only [hmul]
  have hid : (2 * C - c) * S / (1 - q * c) - (2 * C - q) / S =
      (q - c) * (1 - 2 * C * q) / (S * (1 - q * c)) := by
    have hdenc : 1 - c * q ≠ 0 := by simpa only [mul_comm] using hden.ne'
    field_simp [hS.ne', hden.ne', hdenc]
    linear_combination (2 * C - c) * hqS
  have hgain : (q - c) * (1 - 2 * C * q) ≤
      (q - c) * (1 - 2 * C * q) / (S * (1 - q * c)) := by
    rw [le_div_iff₀ (mul_pos hS hden)]
    nlinarith only [hpayment]
  linarith only [hbase, hid, hgain]


/-- Widen the comparison chord while paying for its cubic center shift. -/
theorem terminal_circle_joint_average_comparison {C c s q S : ℝ}
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 37 / 50) (hc : 0 < c) (hcq : c ≤ q)
    (hq : 0 < q) (hq1 : q ≤ 3 / 8) (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hS : 0 < S) (hqS : q ^ 2 + S ^ 2 = 1) :
    (2 * C - q) / S - circleAverage q (C - q ^ 3 / 8) ≤
      (2 * C - c) / s - circleAverage c (C - c ^ 3 / 8) := by
  have hq3 := pow_le_pow_left₀ hq.le hq1 3
  have hc3 := pow_le_pow_left₀ hc.le hcq 3
  have hyc : C - c ^ 3 / 8 ∈ Ioo (q / 2) (1 - q / 2) := by
    constructor <;> nlinarith only [hC0, hC1, hq1, hc3, hq3, pow_nonneg hc.le 3]
  have hyq : C - q ^ 3 / 8 ∈ Ioo (q / 2) (1 - q / 2) := by
    constructor <;> nlinarith only [hC0, hC1, hq1, hq3, pow_nonneg hq.le 3]
  have havg := circleAverage_mono_width hc.le hq hcq hyc
  have hcenter := circleAverage_center_payment hq hyq hyc (by linarith only [hc3])
    (by nlinarith only [hC1, hq1, pow_nonneg hc.le 3])
  have hsum : q ^ 2 + q * c + c ^ 2 ≤ 3 * q ^ 2 := by
    nlinarith only [pow_le_pow_left₀ hc.le hcq 2, mul_nonneg hq.le (sub_nonneg.mpr hcq)]
  have hpay : 3 / q * ((q ^ 3 - c ^ 3) / 8) ≤ 9 * q / 8 * (q - c) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hq]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hcq) (sub_nonneg.mpr hsum)]
  have hloss : 9 * q / 8 < 1 - 2 * C * q := by
    nlinarith only [hq1, mul_nonneg hq.le (by linarith only [hC1] : 0 ≤ 3 / 4 - C)]
  have hlinear := terminal_linear_tangent_payment hC0 hC1 hc hcq hq hq1 hs hcs hS hqS
  have hcoef := mul_le_mul_of_nonneg_right hloss.le (sub_nonneg.mpr hcq)
  linarith only [havg, hcenter, hpay, hlinear, hcoef]


/-- The margin for a comparison interval `[C - d, C + c - d]` whose shift `d - c/2` is at
least cubic in the cosine. -/
theorem terminal_circle_normalized_margin {C c s d : ℝ}
    (hC0 : (1 / 2 : ℝ) ≤ C) (hC1 : C ≤ 37 / 50)
    (hc : 0 < c) (hcut : 73 * c ^ 2 ≤ 9) (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hd : c / 2 + c ^ 3 / 8 ≤ d) (hdc : d < c) :
    terminalCircleGap * c ≤
      c / s * (2 * C - c) - (circleHeight (C - d) - circleHeight (C + c - d)) := by
  let q : ℝ := Real.sqrt (9 / 73)
  let S : ℝ := circleHeight q
  have hq : 0 < q := Real.sqrt_pos.mpr (by norm_num)
  have hq2 : q ^ 2 = 9 / 73 := Real.sq_sqrt (by norm_num)
  have hq1 : q < 3 / 8 := by nlinarith only [hq, hq2]
  have hcq : c ≤ q := Real.le_sqrt_of_sq_le (by nlinarith only [hcut])
  have hS : 0 < S := circleHeight_pos ⟨hq, by linarith only [hq1]⟩
  have hqS : q ^ 2 + S ^ 2 = 1 := by
    linarith only [circleHeight_sq (show q ∈ Ioo (0 : ℝ) 1 from ⟨hq, by linarith only [hq1]⟩)]
  have hc3 : 0 ≤ c ^ 3 := by positivity
  have hy : C + c / 2 - d ∈ Ioo (c / 2) (1 - c / 2) := ⟨by linarith, by linarith⟩
  have hyc : C - c ^ 3 / 8 ∈ Ioo (c / 2) (1 - c / 2) := by
    have hc3' := pow_le_pow_left₀ hc.le (hcq.trans hq1.le) 3
    constructor <;> nlinarith only [hC0, hC1, hcq, hq1, hc3, hc3']
  have havg := circleAverage_mono_center hc.le hy hyc
    (by linarith only [hd] : C + c / 2 - d ≤ C - c ^ 3 / 8)
  have hwidth := terminal_circle_joint_average_comparison hC0 hC1 hc hcq hq hq1.le hs hcs hS hqS
  have hSeq : S = terminalCircleSine := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 64 / 73)
    have hroot := Real.sqrt_nonneg (64 / 73 : ℝ)
    dsimp [terminalCircleSine]
    nlinarith only [hsq, hroot, hqS, hq2, hS]
  have hm : terminalCircleGap ≤ (2 * C - c) / s - circleAverage c (C + c / 2 - d) := by
    have hbase := terminal_circle_average_gap hq hq2 hC0 hC1
    rw [← hSeq] at hbase
    linarith only [hbase, hwidth, havg]

  calc terminalCircleGap * c ≤ ((2 * C - c) / s - circleAverage c (C + c / 2 - d)) * c :=
        mul_le_mul_of_nonneg_right hm hc.le
    _ = _ := by
      rw [circleAverage_eq_height_difference hc hy, show C + c / 2 - d - c / 2 = C - d by ring,
        show C + c / 2 - d + c / 2 = C + c - d by ring]
      field_simp

/-- Restoring the exact terminal height gives the circle margin with
`d = (1 - H*s)/c`, including the residual negative-tilt case. -/
theorem terminal_circle_margin_of_height {C c s H T_L T_R z : ℝ}
    (hC0 : (1 / 2 : ℝ) ≤ C) (hC1 : C ≤ 37 / 50)
    (hc : 0 < c) (hcut : 73 * c ^ 2 ≤ 9) (hs : 0 < s)
    (hcs : c ^ 2 + s ^ 2 = 1) (hHs : s < H) (hH1 : H ≤ 1)
    (hTL : 0 ≤ T_L) (hTR : 0 ≤ T_R)
    (htop : T_L + 2 * T_R ≤ (1 - H * s) / c)
    (hz0 : 0 ≤ z) (hz1 : z ≤ c - (1 - H * s) / c) :
    terminalCircleGap * c ≤ c / s * (2 * C + T_R - (1 - H * s) / c - z) -
      (circleHeight (C - T_L) - circleHeight (C + z)) := by
  have hs1 : s ≤ 1 := by nlinarith
  have hd : c / 2 + c ^ 3 / 8 ≤ (1 - H * s) / c := by
    rw [le_div_iff₀ hc]
    nlinarith [mul_nonneg (pow_nonneg (sub_nonneg.2 hs1) 3) (by linarith : (0 : ℝ) ≤ 3 + s),
      mul_nonneg (sub_nonneg.2 hH1) hs.le, show c ^ 4 = (1 - s ^ 2) ^ 2 by rw [← hcs]; ring]
  have hdc : (1 - H * s) / c < c := (div_lt_iff₀ hc).2 (by nlinarith [mul_pos (sub_pos.2 hHs) hs])
  generalize (1 - H * s) / c = d at *
  have hcQ := terminal_cosine_lt_three_eighths hc hcut
  have hc3 : 0 ≤ c ^ 3 := by positivity
  have h1 := circleHeight_antitoneOn (show C - d ∈ Ioo 0 1 from ⟨by linarith, by linarith⟩)
    (show C - T_L ∈ Ioo 0 1 from ⟨by linarith, by linarith⟩) (by linarith)
  have h2 := circleHeight_antitoneOn (show C + z ∈ Ioo 0 1 from ⟨by linarith, by linarith⟩)
    (show C + c - d ∈ Ioo 0 1 from ⟨by linarith, by linarith⟩) (by linarith)
  linarith [terminal_circle_normalized_margin hC0 hC1 hc hcut hs hcs hd hdc,
    mul_le_mul_of_nonneg_left (show 2 * C - c ≤ 2 * C + T_R - d - z by linarith)
      (div_nonneg hc.le hs.le)]

end AmbidextrousSofa
