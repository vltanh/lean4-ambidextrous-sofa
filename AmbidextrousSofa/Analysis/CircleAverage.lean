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

theorem circleHeight_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < circleHeight x :=
  Real.sqrt_pos.mpr (by nlinarith [hx.1, hx.2])

theorem circleHeight_sq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    circleHeight x ^ 2 = 1 - x ^ 2 :=
  Real.sq_sqrt (by nlinarith [hx.1, hx.2])

theorem continuous_circleHeight : Continuous circleHeight := by
  unfold circleHeight; fun_prop

theorem circleHeight_antitoneOn : AntitoneOn circleHeight (Ioo (0 : ℝ) 1) :=
  fun _ hx _ _ hxy => Real.sqrt_le_sqrt (by nlinarith [hx.1])

theorem hasDerivAt_circleHeight {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt circleHeight (-circleSlope x) x := by
  refine (((hasDerivAt_pow 2 x).const_sub 1).sqrt (by nlinarith [hx.1, hx.2])).congr_deriv ?_
  simp [circleSlope, circleHeight]
  ring

theorem hasDerivAt_circleSlope {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt circleSlope (1 / circleHeight x ^ 3) x := by
  have h0 := (circleHeight_pos hx).ne'
  refine ((hasDerivAt_id x).div (hasDerivAt_circleHeight hx) h0).congr_deriv ?_
  simp only [circleSlope, id]
  field_simp
  linear_combination circleHeight_sq hx

theorem circleSlope_convexOn : ConvexOn ℝ (Ioo (0 : ℝ) 1) circleSlope := by
  refine MonotoneOn.convexOn_of_deriv (convex_Ioo 0 1)
    (HasDerivAt.continuousOn fun x hx => hasDerivAt_circleSlope hx) ?_ ?_ <;> rw [interior_Ioo]
  · exact fun x hx => (hasDerivAt_circleSlope hx).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    rw [(hasDerivAt_circleSlope hx).deriv, (hasDerivAt_circleSlope hy).deriv]
    have := circleHeight_pos hy
    gcongr
    exact circleHeight_antitoneOn hx hy hxy

theorem intervalIntegrable_circleSlope {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hg : Continuous g)
    (hdom : ∀ t ∈ Icc a b, g t ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun t => circleSlope (g t)) volume a b :=
  ContinuousOn.intervalIntegrable_of_Icc hab fun t ht =>
    ((hasDerivAt_circleSlope (hdom t ht)).continuousAt.comp hg.continuousAt).continuousWithinAt

theorem circleAverage_point_mem {q y t : ℝ} (hq : 0 ≤ q) (hy : y ∈ Ioo (q / 2) (1 - q / 2))
    (ht : t ∈ Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)) :
    y + q * t ∈ Ioo (0 : ℝ) 1 ∧ y - q * t ∈ Ioo (0 : ℝ) 1 := by
  have h₁ := mul_nonneg hq (sub_nonneg.2 ht.1)
  have h₂ := mul_nonneg hq (sub_nonneg.2 ht.2)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hy.1, hy.2]

theorem circleAverage_intervalIntegrable {q y : ℝ} (hq : 0 ≤ q)
    (hy : y ∈ Ioo (q / 2) (1 - q / 2)) :
    IntervalIntegrable (fun t : ℝ => circleSlope (y + q * t)) volume (-1 / 2 : ℝ) (1 / 2 : ℝ) :=
  intervalIntegrable_circleSlope (by norm_num) (by fun_prop) fun _ ht =>
    (circleAverage_point_mem hq hy ht).1

theorem circleAverage_eq_height_difference {q y : ℝ} (hq : 0 < q)
    (hy : y ∈ Ioo (q / 2) (1 - q / 2)) :
    circleAverage q y = (circleHeight (y - q / 2) - circleHeight (y + q / 2)) / q := by
  have hmem : ∀ t ∈ uIcc (y - q / 2) (y + q / 2), t ∈ Ioo (0 : ℝ) 1 := fun t ht => by
    rw [uIcc_of_le (by linarith)] at ht
    exact ⟨by linarith [ht.1, hy.1], by linarith [ht.2, hy.2]⟩
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := -circleHeight)
    (fun t ht => by simpa using (hasDerivAt_circleHeight (hmem t ht)).neg)
    (HasDerivAt.continuousOn fun t ht => hasDerivAt_circleSlope (hmem t ht)).intervalIntegrable
  rw [circleAverage, intervalIntegral.integral_comp_add_mul circleSlope hq.ne' y,
    show y + q * (-1 / 2) = y - q / 2 by ring, show y + q * (1 / 2) = y + q / 2 by ring, h,
    Pi.neg_apply, Pi.neg_apply, smul_eq_mul]
  field_simp
  ring

theorem circleAverage_mono_center {q x y : ℝ} (hq : 0 ≤ q)
    (hx : x ∈ Ioo (q / 2) (1 - q / 2))
    (hy : y ∈ Ioo (q / 2) (1 - q / 2)) (hxy : x ≤ y) :
    circleAverage q x ≤ circleAverage q y := by
  refine intervalIntegral.integral_mono_on (by norm_num) (circleAverage_intervalIntegrable hq hx)
    (circleAverage_intervalIntegrable hq hy) fun t ht => ?_
  obtain ⟨h₁, -⟩ := circleAverage_point_mem hq hx ht
  obtain ⟨h₂, -⟩ := circleAverage_point_mem hq hy ht
  exact div_le_div₀ h₂.1.le (by linarith) (circleHeight_pos h₂)
    (circleHeight_antitoneOn h₁ h₂ (by linarith))

theorem circleAverage_convexOn {q : ℝ} (hq : 0 ≤ q) :
    ConvexOn ℝ (Ioo (q / 2) (1 - q / 2)) (circleAverage q) := by
  refine ⟨convex_Ioo _ _, fun x hx y hy a b ha hb hab => ?_⟩
  have hi := fun z (hz : z ∈ Ioo (q / 2) (1 - q / 2)) => circleAverage_intervalIntegrable hq hz
  simp only [smul_eq_mul, circleAverage, ← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_add ((hi x hx).const_mul a) ((hi y hy).const_mul b)]
  refine intervalIntegral.integral_mono_on (by norm_num) (hi _ (convex_Ioo _ _ hx hy ha hb hab))
    (((hi x hx).const_mul a).add ((hi y hy).const_mul b)) fun t ht => ?_
  have h := circleSlope_convexOn.2 (circleAverage_point_mem hq hx ht).1
    (circleAverage_point_mem hq hy ht).1 ha hb hab
  simp only [smul_eq_mul] at h
  convert h using 2
  linear_combination -q * t * hab

/-- Integrability of the symmetrized integrand, and the symmetrized form of the average. -/
theorem circleAverage_symm {q y : ℝ} (hq : 0 ≤ q) (hy : y ∈ Ioo (q / 2) (1 - q / 2)) :
    IntervalIntegrable (fun t => circleSlope (y - q * t) + circleSlope (y + q * t)) volume
      (-1 / 2 : ℝ) (1 / 2) ∧
    2 * circleAverage q y =
      ∫ t in (-1 / 2 : ℝ)..(1 / 2), circleSlope (y - q * t) + circleSlope (y + q * t) := by
  have hm := intervalIntegrable_circleSlope (g := fun t => y - q * t) (by norm_num) (by fun_prop)
    fun _ ht => (circleAverage_point_mem hq hy ht).2
  have hp := circleAverage_intervalIntegrable hq hy
  refine ⟨hm.add hp, ?_⟩
  rw [intervalIntegral.integral_add hm hp, two_mul]
  congr 1
  simpa [circleAverage, neg_div, ← sub_eq_add_neg] using (intervalIntegral.integral_comp_neg
    (a := -1 / 2) (b := 1 / 2) fun t => circleSlope (y + q * t)).symm

/-- Pairing the positive and negative integration variables proves
width monotonicity from convexity; no derivative in the width is used. -/
theorem circleAverage_mono_width {q Q y : ℝ} (hq : 0 ≤ q) (hQ : 0 < Q)
    (hqQ : q ≤ Q) (hy : y ∈ Ioo (Q / 2) (1 - Q / 2)) :
    circleAverage q y ≤ circleAverage Q y := by
  have hyq : y ∈ Ioo (q / 2) (1 - q / 2) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  obtain ⟨hi, he⟩ := circleAverage_symm hq hyq
  obtain ⟨hI, hE⟩ := circleAverage_symm hQ.le hy
  have := intervalIntegral.integral_mono_on (by norm_num) hi hI fun t ht => by
    obtain ⟨hpos, hneg⟩ := circleAverage_point_mem hQ.le hy ht
    have h2a : 2 * ((Q + q) / (2 * Q)) * Q = Q + q := by field_simp
    have ha : 0 ≤ (Q + q) / (2 * Q) := by positivity
    have ha1 : 0 ≤ 1 - (Q + q) / (2 * Q) :=
      sub_nonneg.2 ((div_le_one (by positivity)).2 (by linarith))
    set a := (Q + q) / (2 * Q)
    have h₁ := circleSlope_convexOn.2 hneg hpos ha ha1 (add_sub_cancel a 1)
    have h₂ := circleSlope_convexOn.2 hneg hpos ha1 ha (sub_add_cancel 1 a)
    simp only [smul_eq_mul] at h₁ h₂
    rw [show a * (y - Q * t) + (1 - a) * (y + Q * t) = y - q * t by
      linear_combination -t * h2a] at h₁
    rw [show (1 - a) * (y - Q * t) + a * (y + Q * t) = y + q * t by
      linear_combination t * h2a] at h₂
    linarith
  linarith

/-- A linear function minus a translated symmetric average is concave
on every interval on which the average remains in the positive unit arc. -/
theorem circleAverage_linear_gap_concave {q e l u A B : ℝ}
    (hq : 0 ≤ q) (hA : 0 ≤ A)
    (hl : q / 2 < l - e) (hu : u - e < 1 - q / 2) :
    ConcaveOn ℝ (Icc l u) (fun x : ℝ => A * x + B - circleAverage q (x - e)) :=
  (((concaveOn_id (convex_Icc l u)).smul hA).add_const B).sub
    (((circleAverage_convexOn hq).translate_left (-e)).subset
      (fun _ hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩) (convex_Icc l u))

end AmbidextrousSofa
