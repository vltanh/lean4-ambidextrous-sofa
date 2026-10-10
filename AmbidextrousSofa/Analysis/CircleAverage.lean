module

public import AmbidextrousSofa.Analysis.ExactEstimates

@[expose] public section

/-!
# Symmetric averages of the circle slope

On the positive unit interval the circle slope `x / sqrt (1 - x^2)`
is increasing and convex. Its symmetric interval average is consequently
increasing in the center and in the interval width, and convex in the
center. The average is also evaluated exactly as a difference of two
circle heights. These are the continuum scalar comparisons in MP.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def circleHeight (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)

def circleSlope (x : ℝ) : ℝ := x / circleHeight x

def circleAverage (q y : ℝ) : ℝ :=
  ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), circleSlope (y + q * t)

theorem circleHeight_nonneg (x : ℝ) : 0 ≤ circleHeight x := Real.sqrt_nonneg _

theorem circleHeight_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < circleHeight x := by
  apply Real.sqrt_pos.mpr
  nlinarith [mul_pos (sub_pos.mpr hx.2) (by linarith : 0 < 1 + x)]

theorem circleHeight_sq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    circleHeight x ^ 2 = 1 - x ^ 2 := by
  exact Real.sq_sqrt (by nlinarith [mul_nonneg
    (sub_nonneg.mpr hx.2.le) (by linarith : 0 ≤ 1 + x)])

theorem continuous_circleHeight : Continuous circleHeight := by
  unfold circleHeight
  fun_prop

theorem circleHeight_antitoneOn : AntitoneOn circleHeight (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  apply Real.sqrt_le_sqrt
  have hs := (sq_le_sq₀ hx.1.le hy.1.le).2 hxy
  linarith

theorem continuousAt_circleSlope {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt circleSlope x :=
  continuousAt_id.div continuous_circleHeight.continuousAt (circleHeight_pos hx).ne'

theorem continuousOn_circleSlope : ContinuousOn circleSlope (Ioo (0 : ℝ) 1) :=
  fun _x hx => (continuousAt_circleSlope hx).continuousWithinAt

theorem hasDerivAt_circleHeight {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt circleHeight (-circleSlope x) x := by
  have hnum : 1 - x ^ 2 ≠ 0 := by
    apply ne_of_gt
    nlinarith [mul_pos (sub_pos.mpr hx.2) (by linarith : 0 < 1 + x)]
  have hd := (((hasDerivAt_id x).pow 2).const_sub 1).sqrt hnum
  apply hd.congr_deriv
  unfold circleSlope circleHeight
  ring

theorem hasDerivAt_circleSlope {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt circleSlope (1 / circleHeight x ^ 3) x := by
  have hroot := (circleHeight_pos hx).ne'
  have hd := (hasDerivAt_id x).div (hasDerivAt_circleHeight hx) hroot
  apply hd.congr_deriv
  have hs := circleHeight_sq hx
  calc
    _ = (circleHeight x ^ 2 + x ^ 2) / circleHeight x ^ 3 := by
      unfold circleSlope
      field_simp [hroot] <;> ring
    _ = _ := by rw [hs]; ring

theorem circleSlope_monotoneOn : MonotoneOn circleSlope (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  exact div_le_div₀ hy.1.le hxy (circleHeight_pos hy)
    (circleHeight_antitoneOn hx hy hxy)

theorem circleSlope_convexOn : ConvexOn ℝ (Ioo (0 : ℝ) 1) circleSlope := by
  refine MonotoneOn.convexOn_of_deriv (convex_Ioo _ _) continuousOn_circleSlope
    (fun x hx => (hasDerivAt_circleSlope (interior_subset hx)).differentiableAt.differentiableWithinAt)
    ?_
  intro x hx y hy hxy
  rw [(hasDerivAt_circleSlope (interior_subset hx)).deriv,
    (hasDerivAt_circleSlope (interior_subset hy)).deriv]
  exact one_div_le_one_div_of_le (pow_pos (circleHeight_pos (interior_subset hy)) 3)
    (pow_le_pow_left₀ (circleHeight_nonneg y)
      (circleHeight_antitoneOn (interior_subset hx) (interior_subset hy) hxy) 3)

theorem circleSlope_affine_intervalIntegrable {a b q y : ℝ}
    (hdom : ∀ t ∈ uIcc a b, y + q * t ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun t : ℝ => circleSlope (y + q * t)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  exact ((continuousAt_circleSlope (hdom t ht)).comp t
    (by fun_prop : ContinuousAt (fun r : ℝ => y + q * r) t)).continuousWithinAt

theorem circleAverage_point_mem {q y t : ℝ} (hq : 0 ≤ q)
    (hy : y ∈ Ioo (q / 2) (1 - q / 2))
    (ht : t ∈ Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)) :
    y + q * t ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · nlinarith [mul_nonneg hq (show 0 ≤ t + 1 / 2 by linarith [ht.1])]
  · nlinarith [mul_nonneg hq (show 0 ≤ 1 / 2 - t by linarith [ht.2])]

theorem circleAverage_intervalIntegrable {q y : ℝ} (hq : 0 ≤ q)
    (hy : y ∈ Ioo (q / 2) (1 - q / 2)) :
    IntervalIntegrable (fun t : ℝ => circleSlope (y + q * t)) volume
      (-1 / 2 : ℝ) (1 / 2 : ℝ) := by
  apply circleSlope_affine_intervalIntegrable
  rw [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)]
  exact fun t ht => circleAverage_point_mem hq hy ht

theorem integral_circleSlope {a b : ℝ}
    (hab : a ≤ b) (ha : 0 < a) (hb : b < 1) :
    (∫ t in a..b, circleSlope t) = circleHeight a - circleHeight b := by
  have hcont : ContinuousOn circleSlope (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact continuousOn_circleSlope.mono (fun t ht => ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b) (f := fun t => -circleHeight t) (f' := circleSlope)
    (fun t ht => by
      have htm : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
      simpa only [neg_neg] using
        (hasDerivAt_circleHeight ⟨ha.trans_le htm.1, htm.2.trans_lt hb⟩).neg)
    hcont.intervalIntegrable
  linarith

theorem circleAverage_eq_height_difference {q y : ℝ} (hq : 0 < q)
    (hy : y ∈ Ioo (q / 2) (1 - q / 2)) :
    circleAverage q y = (circleHeight (y - q / 2) - circleHeight (y + q / 2)) / q := by
  unfold circleAverage
  rw [intervalIntegral.integral_comp_add_mul circleSlope hq.ne' y]
  rw [show y + q * (-1 / 2 : ℝ) = y - q / 2 by ring,
    show y + q * (1 / 2 : ℝ) = y + q / 2 by ring]
  rw [integral_circleSlope (by linarith) (by linarith [hy.1]) (by linarith [hy.2])]
  simp only [smul_eq_mul]
  ring

theorem circleAverage_mono_center {q x y : ℝ} (hq : 0 ≤ q)
    (hx : x ∈ Ioo (q / 2) (1 - q / 2))
    (hy : y ∈ Ioo (q / 2) (1 - q / 2)) (hxy : x ≤ y) :
    circleAverage q x ≤ circleAverage q y := by
  apply intervalIntegral.integral_mono_on (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)
    (circleAverage_intervalIntegrable hq hx) (circleAverage_intervalIntegrable hq hy)
  intro t ht
  exact circleSlope_monotoneOn (circleAverage_point_mem hq hx ht)
    (circleAverage_point_mem hq hy ht) (by linarith)

theorem circleAverage_convexOn {q : ℝ} (hq : 0 ≤ q) :
    ConvexOn ℝ (Ioo (q / 2) (1 - q / 2)) (circleAverage q) := by
  refine ⟨convex_Ioo _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hmix : a * x + b * y ∈ Ioo (q / 2) (1 - q / 2) := by
    simpa only [smul_eq_mul] using (convex_Ioo (q / 2) (1 - q / 2)) hx hy ha hb hab
  have hfx := circleAverage_intervalIntegrable hq hx
  have hfy := circleAverage_intervalIntegrable hq hy
  have hi := intervalIntegral.integral_mono_on
    (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)
    (circleAverage_intervalIntegrable hq hmix) ((hfx.const_mul a).add (hfy.const_mul b))
    (fun t ht => show circleSlope (a * x + b * y + q * t) ≤
      a * circleSlope (x + q * t) + b * circleSlope (y + q * t) from by
      have h := circleSlope_convexOn.2 (circleAverage_point_mem hq hx ht)
        (circleAverage_point_mem hq hy ht) ha hb hab
      simp only [smul_eq_mul] at h
      have hid : a * (x + q * t) + b * (y + q * t) = a * x + b * y + q * t := by
        calc
          _ = a * x + b * y + (a + b) * (q * t) := by ring
          _ = _ := by rw [hab, one_mul]
      rwa [hid] at h)
  rw [intervalIntegral.integral_add (hfx.const_mul a) (hfy.const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  simpa only [smul_eq_mul, circleAverage] using hi

theorem circleAverage_pair_integrable {q y : ℝ} (hq : 0 ≤ q)
    (hy : y ∈ Ioo (q / 2) (1 - q / 2)) :
    IntervalIntegrable (fun t : ℝ => circleSlope (y - q * t) +
      circleSlope (y + q * t)) volume 0 (1 / 2 : ℝ) := by
  have hplus : IntervalIntegrable (fun t : ℝ => circleSlope (y + q * t)) volume 0 (1 / 2 : ℝ) := by
    apply circleSlope_affine_intervalIntegrable
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    intro t ht
    exact circleAverage_point_mem hq hy ⟨by linarith [ht.1], ht.2⟩
  have hminus : IntervalIntegrable (fun t : ℝ => circleSlope (y - q * t)) volume 0 (1 / 2 : ℝ) := by
    have h : IntervalIntegrable (fun t : ℝ => circleSlope (y + (-q) * t)) volume 0 (1 / 2 : ℝ) := by
      apply circleSlope_affine_intervalIntegrable
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      intro t ht
      simpa only [mul_neg, neg_mul, sub_eq_add_neg] using
        circleAverage_point_mem hq hy (t := -t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa only [neg_mul, sub_eq_add_neg] using h
  exact hminus.add hplus

theorem circleAverage_eq_paired_integral {q y : ℝ} (hq : 0 ≤ q)
    (hy : y ∈ Ioo (q / 2) (1 - q / 2)) :
    circleAverage q y = ∫ t in 0..(1 / 2 : ℝ),
      circleSlope (y - q * t) + circleSlope (y + q * t) := by
  have hfull := circleAverage_intervalIntegrable hq hy
  have hleft := hfull.mono_set (show uIcc (-1 / 2 : ℝ) 0 ⊆
      uIcc (-1 / 2 : ℝ) (1 / 2 : ℝ) by
    rw [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 0),
      uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)]
    exact Icc_subset_Icc le_rfl (by norm_num))
  have hright := hfull.mono_set (show uIcc 0 (1 / 2 : ℝ) ⊆
      uIcc (-1 / 2 : ℝ) (1 / 2 : ℝ) by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
      uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)]
    exact Icc_subset_Icc (by norm_num) le_rfl)
  have hminus : IntervalIntegrable (fun t : ℝ => circleSlope (y - q * t)) volume 0 (1 / 2 : ℝ) := by
    have h : IntervalIntegrable (fun t : ℝ => circleSlope (y + (-q) * t)) volume 0 (1 / 2 : ℝ) := by
      apply circleSlope_affine_intervalIntegrable
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      intro t ht
      simpa only [mul_neg, neg_mul, sub_eq_add_neg] using
        circleAverage_point_mem hq hy (t := -t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa only [neg_mul, sub_eq_add_neg] using h
  have hreflect : (∫ t in (-1 / 2 : ℝ)..0, circleSlope (y + q * t)) =
      ∫ t in 0..(1 / 2 : ℝ), circleSlope (y - q * t) := by
    have h := intervalIntegral.integral_comp_neg
      (f := fun t : ℝ => circleSlope (y + q * t)) (a := 0) (b := (1 / 2 : ℝ))
    simpa only [neg_zero, mul_neg, sub_eq_add_neg] using h.symm
  unfold circleAverage
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright, hreflect,
    intervalIntegral.integral_add hminus hright]

/-- Pairing the positive and negative integration variables proves
width monotonicity from convexity; no derivative in the width is used. -/
theorem circleAverage_mono_width {q Q y : ℝ} (hq : 0 ≤ q) (hQ : 0 < Q)
    (hqQ : q ≤ Q) (hy : y ∈ Ioo (Q / 2) (1 - Q / 2)) :
    circleAverage q y ≤ circleAverage Q y := by
  have hyq : y ∈ Ioo (q / 2) (1 - q / 2) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  rw [circleAverage_eq_paired_integral hq hyq, circleAverage_eq_paired_integral hQ.le hy]
  apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (circleAverage_pair_integrable hq hyq) (circleAverage_pair_integrable hQ.le hy)
  intro t ht
  let a := (Q + q) / (2 * Q)
  let b := (Q - q) / (2 * Q)
  have ha : 0 ≤ a := div_nonneg (by linarith) (by positivity)
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hqQ) (by positivity)
  have hab : a + b = 1 := by dsimp [a, b]; field_simp [hQ.ne']; ring
  have hneg : y - Q * t ∈ Ioo (0 : ℝ) 1 := by
    simpa only [mul_neg, sub_eq_add_neg] using circleAverage_point_mem hQ.le hy
      (t := -t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hpos := circleAverage_point_mem hQ.le hy
    (t := t) ⟨by linarith [ht.1], ht.2⟩
  have h₁ := circleSlope_convexOn.2 hneg hpos ha hb hab
  have h₂ := circleSlope_convexOn.2 hneg hpos hb ha (by linarith)
  simp only [smul_eq_mul] at h₁ h₂
  have hminus : a * (y - Q * t) + b * (y + Q * t) = y - q * t := by
    dsimp [a, b]
    field_simp [hQ.ne'] <;> ring
  have hplus : b * (y - Q * t) + a * (y + Q * t) = y + q * t := by
    dsimp [a, b]
    field_simp [hQ.ne'] <;> ring
  rw [hminus] at h₁
  rw [hplus] at h₂
  have hsum : (a * circleSlope (y - Q * t) + b * circleSlope (y + Q * t)) +
      (b * circleSlope (y - Q * t) + a * circleSlope (y + Q * t)) =
        circleSlope (y - Q * t) + circleSlope (y + Q * t) := by
    calc
      _ = (a + b) * (circleSlope (y - Q * t) + circleSlope (y + Q * t)) := by ring
      _ = _ := by rw [hab, one_mul]
  linarith

/-- A linear function minus a translated symmetric average is concave
on every interval on which the average remains in the positive unit arc. -/
theorem circleAverage_linear_gap_concave {q e l u A B : ℝ}
    (hq : 0 ≤ q) (hA : 0 ≤ A)
    (hl : q / 2 < l - e) (hu : u - e < 1 - q / 2) :
    ConcaveOn ℝ (Icc l u) (fun x : ℝ => A * x + B - circleAverage q (x - e)) := by
  have hlin : ConcaveOn ℝ (Icc l u) (fun x : ℝ => A * x + B) := by
    simpa only [Pi.add_apply, smul_eq_mul, id_eq] using
      ((concaveOn_id (convex_Icc l u)).smul hA).add_const B
  have havg : ConvexOn ℝ (Icc l u) (fun x : ℝ => circleAverage q (x - e)) := by
    refine ⟨convex_Icc l u, ?_⟩
    intro x hx y hy a b ha hb hab
    have hxq : x - e ∈ Ioo (q / 2) (1 - q / 2) :=
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hyq : y - e ∈ Ioo (q / 2) (1 - q / 2) :=
      ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have h := (circleAverage_convexOn hq).2 hxq hyq ha hb hab
    simp only [smul_eq_mul] at h ⊢
    have hid : a * (x - e) + b * (y - e) = a * x + b * y - e := by
      calc
        _ = a * x + b * y - (a + b) * e := by ring
        _ = _ := by rw [hab, one_mul]
    rwa [hid] at h
  exact hlin.sub havg

end AmbidextrousSofa
