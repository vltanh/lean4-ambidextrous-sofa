module

public import AmbidextrousSofa.ExactConstant

@[expose] public section

/-!
# An elementary Dirichlet energy estimate

For a function vanishing at both endpoints, Cauchy--Schwarz on the two
subintervals gives the pointwise weight `t * (L - t) / L`. Its integral
yields the constant `L² / 6`. At `L = π / 2` this is already sufficient
for strict fixed-width concavity of the adaptive functional; a sharp
Poincaré constant is unnecessary.

The hypotheses retain actual derivatives and square integrability. No
existence, maximization, or sofa-area conclusion is assumed.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa.Analysis

/-- Cauchy--Schwarz against a constant on a real interval, proved by
integrating a square. The statement includes a zero-length interval. -/
theorem square_integral_le_length_mul_integral_square {a b : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun x => f x ^ 2) volume a b) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, f x ^ 2 := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  set I := ∫ x in a..b, f x
  have h := intervalIntegral.integral_nonneg (μ := volume) hab.le fun x _ =>
    sq_nonneg ((b - a) * f x - I)
  have hexpand (x : ℝ) : ((b - a) * f x - I) ^ 2 =
      (b - a) ^ 2 * f x ^ 2 - 2 * (b - a) * I * f x + I ^ 2 := by ring
  simp only [hexpand] at h
  rw [intervalIntegral.integral_add ((hf2.const_mul _).sub (hf.const_mul _))
    intervalIntegrable_const, intervalIntegral.integral_sub (hf2.const_mul _) (hf.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul] at h
  nlinarith [sub_pos.2 hab]

/-- The exact polynomial weight appearing in the two-endpoint estimate. -/
theorem integral_dirichlet_weight (L : ℝ) :
    (∫ t in (0 : ℝ)..L, t * (L - t)) = L ^ 3 / 6 := by
  simp only [mul_sub, ← sq]
  rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_mul_const, integral_id, integral_pow]
  ring

/-- Both endpoint conditions are used. Multiplying the two subinterval
Cauchy--Schwarz estimates avoids division at either endpoint. -/
theorem dirichlet_pointwise {f fD : ℝ → ℝ} {L t : ℝ}
    (hf : ContinuousOn f (Icc 0 L))
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivWithinAt f (fD x) (Ioi x) x)
    (hfD : IntervalIntegrable fD volume 0 L)
    (hfD2 : IntervalIntegrable (fun x => fD x ^ 2) volume 0 L)
    (hzero : f 0 = 0) (hend : f L = 0) (ht : t ∈ Icc 0 L) :
    L * f t ^ 2 ≤ t * (L - t) * ∫ x in (0 : ℝ)..L, fD x ^ 2 := by
  have htL : t ∈ uIcc 0 L := Icc_subset_uIcc ht
  have hleft := uIcc_subset_uIcc left_mem_uIcc htL
  have hright := uIcc_subset_uIcc htL right_mem_uIcc
  have h1 := square_integral_le_length_mul_integral_square ht.1
    (hfD.mono_set hleft) (hfD2.mono_set hleft)
  have h2 := square_integral_le_length_mul_integral_square ht.2
    (hfD.mono_set hright) (hfD2.mono_set hright)
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
    (hf.mono (Icc_subset_Icc le_rfl ht.2)) (fun x hx => hderiv x ⟨hx.1, hx.2.trans_le ht.2⟩)
    (hfD.mono_set hleft), hzero] at h1
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.2
    (hf.mono (Icc_subset_Icc ht.1 le_rfl)) (fun x hx => hderiv x ⟨ht.1.trans_lt hx.1, hx.2⟩)
    (hfD.mono_set hright), hend] at h2
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hfD2.mono_set hleft) (hfD2.mono_set hright)]
  linarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr ht.2), mul_le_mul_of_nonneg_left h2 ht.1]

/-- A square-integrable derivative and zero traces imply a quantitative
Dirichlet bound. Only a right derivative is needed at interior points. -/
theorem dirichlet_integral_square_le {f fD : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (hf : ContinuousOn f (Icc 0 L))
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivWithinAt f (fD x) (Ioi x) x)
    (hfD : IntervalIntegrable fD volume 0 L)
    (hfD2 : IntervalIntegrable (fun x => fD x ^ 2) volume 0 L)
    (hzero : f 0 = 0) (hend : f L = 0) :
    (∫ x in (0 : ℝ)..L, f x ^ 2) ≤ L ^ 2 / 6 * ∫ x in (0 : ℝ)..L, fD x ^ 2 := by
  have hbound := intervalIntegral.integral_mono_on hL.le
    ((ContinuousOn.intervalIntegrable_of_Icc hL.le (hf.pow 2)).const_mul L)
    (Continuous.intervalIntegrable (μ := volume) (by fun_prop) 0 L)
    (fun t ht => dirichlet_pointwise hf hderiv hfD hfD2 hzero hend ht)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
    integral_dirichlet_weight] at hbound
  exact le_of_mul_le_mul_left (hbound.trans_eq (by ring)) hL

theorem quarter_dirichlet_integral_square_le {f fD : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 (Real.pi / 2)))
    (hderiv : ∀ x ∈ Ioo 0 (Real.pi / 2), HasDerivWithinAt f (fD x) (Ioi x) x)
    (hfD : IntervalIntegrable fD volume 0 (Real.pi / 2))
    (hfD2 : IntervalIntegrable (fun x => fD x ^ 2) volume 0 (Real.pi / 2))
    (hzero : f 0 = 0) (hend : f (Real.pi / 2) = 0) :
    (∫ x in (0 : ℝ)..(Real.pi / 2), f x ^ 2) ≤
      5 / 12 * ∫ x in (0 : ℝ)..(Real.pi / 2), fD x ^ 2 := by
  have hL : 0 < Real.pi / 2 := by positivity
  refine (dirichlet_integral_square_le hL hf hderiv hfD hfD2 hzero hend).trans
    (mul_le_mul_of_nonneg_right ?_ (intervalIntegral.integral_nonneg hL.le fun x _ => sq_nonneg _))
  -- the elementary coefficient is below `5 / 12` by Mathlib's bound `π < 3.15`
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

/-- For a continuous function, vanishing square integral gives literal
pointwise equality, including the two endpoints. -/
theorem eqOn_zero_of_integral_square_eq_zero {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hzero : (∫ x in a..b, f x ^ 2) = 0) : EqOn f (fun _ => 0) (Icc a b) := by
  have hae := (integral_eq_zero_iff_of_nonneg (μ := volume.restrict (Icc a b))
    (fun x => sq_nonneg (f x))
    ((hf.pow 2).integrableOn_compact isCompact_Icc)).mp
    (by rwa [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le])
  exact Measure.eqOn_Icc_of_ae_eq volume hab.ne (hae.mono fun x hx => by simpa using hx) hf
    continuousOn_const

end AmbidextrousSofa.Analysis
