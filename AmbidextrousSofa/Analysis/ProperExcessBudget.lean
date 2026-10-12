module

public import AmbidextrousSofa.Analysis.ProperExcessScalar

@[expose] public section

/-!
# One angular budget for the proper reflected excess

Compare the whole crossing-and-decay time with its zero-tilt baseline.
Differences of squares price changes in width, height and impulse energy.
The two middle orientations spend one common angular budget, and a single
Newton baseline check bounds the excess deadline linearly in terminal slope.
-/

noncomputable section
namespace AmbidextrousSofa.Analysis

abbrev properBaselineSpan : ℝ := 3 * (37 / 50)
abbrev properPressureExcess (k : ℝ) : ℝ := max ((37 / 25) * k - 1 / 3) 0
abbrev properAngularDeadline (k : ℝ) : ℝ := 11 / 15 + 2 * k / 3
private abbrev rootUpper (q x : ℝ) : ℝ :=
  squareRootNewton q (squareRootNewton q (squareRootNewton q x))
private abbrev rootLower (q x : ℝ) : ℝ := q / rootUpper q x

private theorem rootUpper_pos {q x : ℝ} (hq : 0 ≤ q) (hx : 0 < x) : 0 < rootUpper q x := by
  dsimp [rootUpper, squareRootNewton]; positivity
private theorem sqrt_le_rootUpper {q x : ℝ} (hq : 0 ≤ q) (hx : 0 < x) :
    Real.sqrt q ≤ rootUpper q x :=
  sqrt_le_squareRootNewton hq (by dsimp [squareRootNewton]; positivity)
private theorem rootLower_le_sqrt {q x : ℝ} (hq : 0 ≤ q) (hx : 0 < x) :
    rootLower q x ≤ Real.sqrt q := by
  rw [rootLower, div_le_iff₀ (rootUpper_pos hq hx)]
  linarith only [Real.sq_sqrt hq,
    mul_nonneg (Real.sqrt_nonneg q) (sub_nonneg.2 (sqrt_le_rootUpper hq hx))]

private theorem baseline_payment :
    (3 / 5 : ℝ) * (properBaselineSpan + 3 / 32 + properBaselineSpan) ≤
      properEnergyRoot properBaselineSpan (3 / 4) 0 * properDecayRoot properBaselineSpan (3 / 4) 0 ∧
    (5 / 2 : ℝ) ≤ properEnergyRoot properBaselineSpan (3 / 4) 0 * properDecayRoot properBaselineSpan (3 / 4) 0 ∧
    properExcessEnd properBaselineSpan (3 / 4) 0 <
      11 / 15 - (3 / 8) * (3 / 8 + (27 / 40) * (37 / 25 - 8 / 9) + 3 / 80 - 2 / 3) := by
  let q : ℝ := properBaselineSpan ^ 2 - 3 / 16
  let ylo := rootLower q 2
  let yhi := rootUpper q 2
  let zlo := rootLower (4 * ylo - 7) 1
  let zhi := rootUpper (4 * yhi - 7) 1
  have hq : 0 ≤ q := by norm_num [q, properBaselineSpan]
  have hylo : ylo ≤ properEnergyRoot properBaselineSpan (3 / 4) 0 := by
    convert rootLower_le_sqrt hq (by norm_num : (0 : ℝ) < 2) using 1; norm_num [ylo, q, properEnergyRoot, properBaselineSpan]
  have hyhi : properEnergyRoot properBaselineSpan (3 / 4) 0 ≤ yhi := by
    convert sqrt_le_rootUpper hq (by norm_num : (0 : ℝ) < 2) using 1; norm_num [yhi, q, properEnergyRoot, properBaselineSpan]
  have hzlo : zlo ≤ properDecayRoot properBaselineSpan (3 / 4) 0 :=
    (rootLower_le_sqrt (by norm_num [ylo, q, rootLower, rootUpper, squareRootNewton, properBaselineSpan]) (by norm_num)).trans
      (Real.sqrt_le_sqrt (by linarith only [hylo]))
  have hzhi : properDecayRoot properBaselineSpan (3 / 4) 0 ≤ zhi :=
    (Real.sqrt_le_sqrt (by linarith only [hyhi])).trans
      (sqrt_le_rootUpper (by norm_num [yhi, q, rootUpper, squareRootNewton, properBaselineSpan]) (by norm_num))
  have hlo0 : 0 ≤ ylo := by norm_num [ylo, q, rootLower, rootUpper, squareRootNewton, properBaselineSpan]
  have hprod := mul_le_mul hylo hzlo (by norm_num [zlo, ylo, q, rootLower, rootUpper, squareRootNewton, properBaselineSpan])
    (hlo0.trans hylo)
  refine ⟨(by norm_num [zlo, ylo, q, rootLower, rootUpper, squareRootNewton, properBaselineSpan] at hprod ⊢; linarith only [hprod]),
    (by norm_num [zlo, ylo, q, rootLower, rootUpper, squareRootNewton, properBaselineSpan] at hprod ⊢; linarith only [hprod]), ?_⟩
  have hxlo := rootLower_le_sqrt (by norm_num : (0 : ℝ) ≤ properBaselineSpan ^ 2 - 3 / 2)
    (by norm_num : (0 : ℝ) < 2)
  unfold properExcessEnd properFirstZeroTime properDecayLength properCrossingRoot
  have hcheck : properBaselineSpan - rootLower (properBaselineSpan ^ 2 - 3 / 2) 2 + zhi - 1 <
      11 / 15 - (3 / 8) * (3 / 8 + (27 / 40) * (37 / 25 - 8 / 9) + 3 / 80 - 2 / 3) := by
    norm_num [zhi, yhi, q, rootLower, rootUpper, squareRootNewton, properBaselineSpan]
  linarith only [hxlo, hzhi, hcheck]

/-- Differences of squares bound the movement of the crossing and decay together. -/
theorem properExcessEnd_le_baseline_payment {d e η : ℝ}
    (hd : properBaselineSpan ≤ d) (hd1 : d ≤ properBaselineSpan + (3 / 8) / 4)
    (he : 3 / 4 ≤ e) (he1 : e ≤ 1) (hη : 0 ≤ η) (hη1 : η ≤ (3 / 8) ^ 2 / 4) :
    properExcessEnd d e η ≤ properExcessEnd properBaselineSpan (3 / 4) 0 +
      (3 / 2) * (d - properBaselineSpan) + (9 / 10) * (e - 3 / 4) + (2 / 5) * η := by
  have hd0 : (2 - 1 / 2 ^ 6 : ℝ) ≤ d := by
    norm_num [properBaselineSpan] at hd; linarith only [hd]
  have hdpos : 0 < d := by linarith only [hd0]
  have hd2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ properBaselineSpan) hd 2
  have hd2' := pow_le_pow_left₀ hdpos.le hd1 2
  obtain ⟨⟨-, -, hx2⟩, ⟨hy0, -, hy2⟩, ⟨hz0, -, hz2⟩⟩ :=
    properExcess_roots_bounds hd0 hd1 (by linarith only [he]) he1 hη hη1
  obtain ⟨⟨-, -, hX2⟩, -, -⟩ := properExcess_roots_bounds hd0 hd1
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num) (by norm_num : (0 : ℝ) ≤ 0) (by norm_num)
  obtain ⟨⟨-, -, hx02⟩, ⟨-, -, hy02⟩, ⟨-, -, hz02⟩⟩ :=
    properExcess_roots_bounds (d := properBaselineSpan) (e := 3 / 4) (δ := 0)
      (by norm_num [properBaselineSpan]) (by norm_num [properBaselineSpan])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hx0 : 5 / 3 ≤ properCrossingRoot d e :=
    Real.le_sqrt_of_sq_le (by norm_num [properBaselineSpan] at hd2; linarith only [hd2, he1])
  have hX0 : 5 / 3 ≤ properCrossingRoot d (3 / 4) :=
    Real.le_sqrt_of_sq_le (by norm_num [properBaselineSpan] at hd2; linarith only [hd2])
  have hx00 : 5 / 3 ≤ properCrossingRoot properBaselineSpan (3 / 4) :=
    Real.le_sqrt_of_sq_le (by norm_num [properBaselineSpan])
  have hX1 : properCrossingRoot d (3 / 4) ≤ (6 / 7) * d :=
    (Real.sqrt_le_left (by positivity)).2 (by
      norm_num [properBaselineSpan] at hd2'; nlinarith only [hd2'])
  have hx01 : properCrossingRoot properBaselineSpan (3 / 4) ≤ (6 / 7) * properBaselineSpan :=
    (Real.sqrt_le_left (by norm_num [properBaselineSpan])).2 (by norm_num [properBaselineSpan])
  have hy00 : 2 ≤ properEnergyRoot properBaselineSpan (3 / 4) 0 :=
    Real.le_sqrt_of_sq_le (by norm_num [properBaselineSpan])
  have hy : properEnergyRoot properBaselineSpan (3 / 4) 0 ≤ properEnergyRoot d e η :=
    Real.sqrt_le_sqrt (by
      norm_num [properBaselineSpan] at hd2 ⊢
      nlinarith only [hd2, hη, mul_nonneg (sub_nonneg.2 he) (show 0 ≤ e - 1 / 4 by linarith only [he])])
  have hz00 : 1 ≤ properDecayRoot properBaselineSpan (3 / 4) 0 :=
    Real.le_sqrt_of_sq_le (by linarith only [hy00])
  have hz : properDecayRoot properBaselineSpan (3 / 4) 0 ≤ properDecayRoot d e η :=
    Real.sqrt_le_sqrt (by linarith only [hy])
  have hP := baseline_payment.1
  have hP' := baseline_payment.2.1
  unfold properExcessEnd properFirstZeroTime properDecayLength
  generalize properCrossingRoot d e = x, properCrossingRoot d (3 / 4) = X,
    properCrossingRoot properBaselineSpan (3 / 4) = x0,
    properEnergyRoot d e η = y, properEnergyRoot properBaselineSpan (3 / 4) 0 = y0,
    properDecayRoot d e η = z, properDecayRoot properBaselineSpan (3 / 4) 0 = z0 at *
  norm_num only at hX2 hx02 hy02
  have hwidth' : (7 / 6) * (d - properBaselineSpan) * (X + x0) ≤ (X - x0) * (X + x0) := by
    linarith only [hX2, hx02, mul_nonneg (sub_nonneg.2 hd)
      (show 0 ≤ d + properBaselineSpan - (7 / 6) * (X + x0) by linarith only [hX1, hx01])]
  have hwidth := le_of_mul_le_mul_right hwidth' (by linarith only [hX0, hx00] : 0 < X + x0)
  have hheight' : (X - x) * (X + x) ≤ (3 / 5) * (e - 3 / 4) * (X + x) := by
    linarith only [hX2, hx2, mul_nonneg (sub_nonneg.2 he)
      (show 0 ≤ (3 / 5) * (X + x) - 2 by linarith only [hX0, hx0])]
  have hheight := le_of_mul_le_mul_right hheight' (by linarith only [hX0, hx0] : 0 < X + x)
  have hbalance : (z - z0) * (z + z0) * (y + y0) =
      4 * (d ^ 2 - properBaselineSpan ^ 2 + (e - 3 / 4) * (e - 1 / 4) + η) := by
    linear_combination (y + y0) * (hz2 - hz02) + 4 * (hy2 - hy02)
  have hsum : 4 * y0 * z0 ≤ (y + y0) * (z + z0) := by
    linarith only [mul_nonneg (sub_nonneg.2 hy) (by linarith only [hz00, hz] : 0 ≤ z + z0),
      mul_nonneg (sub_nonneg.2 hz) (by linarith only [hy00] : 0 ≤ 2 * y0)]
  have hdiff : (z - z0) * (y0 * z0) ≤ d ^ 2 - properBaselineSpan ^ 2 +
      (e - 3 / 4) * (e - 1 / 4) + η := by
    linarith only [hbalance, mul_nonneg (sub_nonneg.2 hz) (sub_nonneg.2 hsum)]
  have hpay : d ^ 2 - properBaselineSpan ^ 2 + (e - 3 / 4) * (e - 1 / 4) + η ≤
      ((5 / 3) * (d - properBaselineSpan) + (3 / 10) * (e - 3 / 4) + (2 / 5) * η) * (y0 * z0) := by
    linarith only [mul_nonneg (sub_nonneg.2 hd)
      (show 0 ≤ (5 / 3) * (y0 * z0) - d - properBaselineSpan by linarith only [hP, hd1]),
      mul_nonneg (sub_nonneg.2 he)
      (show 0 ≤ (3 / 10) * (y0 * z0) - e + 1 / 4 by linarith only [hP', he1]),
      mul_nonneg hη (show 0 ≤ (2 / 5) * (y0 * z0) - 1 by linarith only [hP'])]
  have hdecay := le_of_mul_le_mul_right (hdiff.trans hpay) (by positivity : 0 < y0 * z0)
  linarith only [hwidth, hheight, hdecay]

/-- Both middle orientations use the same angular budget. -/
theorem properExcessEnd_le_angular_deadline {d e η k : ℝ}
    (hk : 0 ≤ k) (hk1 : k ≤ 3 / 8)
    (hd0 : (2 - 1 / 2 ^ 6) ≤ d) (hd1 : d ≤ properBaselineSpan + (3 / 8) / 4)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ (3 / 8) ^ 2 / 4)
    (hηk : η ≤ k ^ 2 / 4)
    (hbudget : (3 / 2) * max (d - properBaselineSpan) 0 +
      (9 / 10) * max (e - 3 / 4 - (3 / 4) * properPressureExcess k) 0 ≤ (3 / 8) * k) :
    properExcessEnd d e η ≤ properAngularDeadline k := by
  set D := max d properBaselineSpan
  set E := max e (3 / 4)
  have hD : properBaselineSpan ≤ D := le_max_right _ _
  have hD1 : D ≤ properBaselineSpan + (3 / 8) / 4 := max_le hd1 (by linarith)
  have hE : 3 / 4 ≤ E := le_max_right _ _
  have hE1 : E ≤ 1 := max_le he1 (by norm_num)
  have hdD : d ≤ D := le_max_left _ _
  have heE : e ≤ E := le_max_left _ _
  have hW := (properExcessEnd_mono_width hd0 hdD hD1 he0 he1 hη0 hη1).trans
    (properExcessEnd_mono_height (hd0.trans hdD) hD1 he0 heE hE1 hη0 hη1 (by
      have hD2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ properBaselineSpan) hD 2
      norm_num [properBaselineSpan] at hD2; linarith only [hD2, hη0]))
  have hinc := properExcessEnd_le_baseline_payment hD hD1 hE hE1 hη0 hη1
  have hg : 0 ≤ properPressureExcess k := le_max_right _ _
  have hEbound : E - 3 / 4 ≤ (3 / 4) * properPressureExcess k +
      max (e - 3 / 4 - (3 / 4) * properPressureExcess k) 0 := by
    dsimp only [E]
    have hmax := le_max_left (e - 3 / 4 - (3 / 4) * properPressureExcess k) 0
    have hmax0 := le_max_right (e - 3 / 4 - (3 / 4) * properPressureExcess k) 0
    rw [sub_le_iff_le_add]
    exact max_le (by linarith only [hmax]) (by linarith only [hg, hmax0])
  have hDdiff : D - properBaselineSpan = max (d - properBaselineSpan) 0 := by
    simp only [D, ← max_sub_sub_right, sub_self]
  have hgline : properPressureExcess k ≤ (37 / 25 - 8 / 9) * k := by
    apply max_le <;> linarith only [hk, hk1]
  have hksq : k ^ 2 ≤ (3 / 8) * k := by nlinarith only [hk, hk1]
  have hline : (3 / 2) * (D - properBaselineSpan) + (9 / 10) * (E - 3 / 4) + (2 / 5) * η ≤
      (3 / 8 + (27 / 40) * (37 / 25 - 8 / 9) + 3 / 80) * k := by
    rw [hDdiff]
    linarith only [hbudget, hEbound, hgline, hηk, hksq]
  have hbase := baseline_payment.2.2
  unfold properAngularDeadline
  linarith only [hW, hinc, hline, hbase, hk1]

/-- A common decay length controls the affine remainder in the excess envelope. -/
theorem properDecayLength_lt_three_fifths {d e η : ℝ}
    (hd0 : (2 - 1 / 2 ^ 6) ≤ d) (hd1 : d ≤ properBaselineSpan + (3 / 8) / 4)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hη1 : η ≤ (3 / 8) ^ 2 / 4) :
    properDecayLength d e η < 3 / 5 := by
  apply properDecayLength_lt_of_energy (by norm_num)
  have hd2 := pow_le_pow_left₀ (by linarith only [hd0] : 0 ≤ d) hd1 2
  norm_num [properBaselineSpan] at hd2
  linarith only [hd2, mul_nonneg he0 (sub_nonneg.2 he1), hη1]

end AmbidextrousSofa.Analysis
