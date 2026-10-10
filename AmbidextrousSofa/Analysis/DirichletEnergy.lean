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
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp
  let L := b - a
  let I := ∫ x in a..b, f x
  have hL : 0 < L := sub_pos.mpr hab
  have hnonneg : 0 ≤ ∫ x in a..b, (L * f x - I) ^ 2 :=
    intervalIntegral.integral_nonneg hab.le (fun x _ => sq_nonneg _)
  have hexpand : (fun x => (L * f x - I) ^ 2) =
      (fun x => L ^ 2 * f x ^ 2 - (2 * L * I) * f x + I ^ 2) := by
    funext x
    ring
  rw [hexpand, intervalIntegral.integral_add
    ((hf2.const_mul (L ^ 2)).sub (hf.const_mul (2 * L * I))) intervalIntegrable_const,
    intervalIntegral.integral_sub (hf2.const_mul (L ^ 2)) (hf.const_mul (2 * L * I)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul] at hnonneg
  have hfactor : 0 ≤ L * (L * (∫ x in a..b, f x ^ 2) - I ^ 2) := by
    change 0 ≤ L ^ 2 * (∫ x in a..b, f x ^ 2) - 2 * L * I * I + L * I ^ 2 at hnonneg
    nlinarith
  have h := nonneg_of_mul_nonneg_right hfactor hL
  change I ^ 2 ≤ L * (∫ x in a..b, f x ^ 2)
  linarith

/-- The exact polynomial weight appearing in the two-endpoint estimate. -/
theorem integral_dirichlet_weight (L : ℝ) :
    (∫ t in (0 : ℝ)..L, t * (L - t)) = L ^ 3 / 6 := by
  have hfunction : (fun t : ℝ => t * (L - t)) = (fun t => L * t - t ^ 2) := by
    funext t
    ring
  rw [hfunction, intervalIntegral.integral_sub
    ((continuous_id.const_mul L).intervalIntegrable 0 L)
    ((continuous_id.pow 2).intervalIntegrable 0 L),
    intervalIntegral.integral_const_mul, integral_id, integral_pow]
  norm_num
  ring

/-- Both endpoint conditions are used. Multiplying the two subinterval
Cauchy--Schwarz estimates avoids division at either endpoint. -/
theorem dirichlet_pointwise {f fD : ℝ → ℝ} {L t : ℝ}
    (hL : 0 < L) (hf : ContinuousOn f (Icc 0 L))
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivWithinAt f (fD x) (Ioi x) x)
    (hfD : IntervalIntegrable fD volume 0 L)
    (hfD2 : IntervalIntegrable (fun x => fD x ^ 2) volume 0 L)
    (hzero : f 0 = 0) (hend : f L = 0) (ht : t ∈ Icc 0 L) :
    L * f t ^ 2 ≤ t * (L - t) * ∫ x in (0 : ℝ)..L, fD x ^ 2 := by
  have hleft : uIcc 0 t ⊆ uIcc 0 L := by
    rw [uIcc_of_le ht.1, uIcc_of_le hL.le]
    exact Icc_subset_Icc le_rfl ht.2
  have hright : uIcc t L ⊆ uIcc 0 L := by
    rw [uIcc_of_le ht.2, uIcc_of_le hL.le]
    exact Icc_subset_Icc ht.1 le_rfl
  have hleft_int : (∫ x in (0 : ℝ)..t, fD x) = f t := by
    have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
      (hf.mono (Icc_subset_Icc le_rfl ht.2))
      (fun x hx => hderiv x ⟨hx.1, hx.2.trans_le ht.2⟩)
      (hfD.mono_set hleft)
    simpa only [hzero, sub_zero] using h
  have hright_int : (∫ x in t..L, fD x) = -f t := by
    have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.2
      (hf.mono (Icc_subset_Icc ht.1 le_rfl))
      (fun x hx => hderiv x ⟨ht.1.trans_lt hx.1, hx.2⟩)
      (hfD.mono_set hright)
    simpa only [hend, zero_sub] using h
  have hleft_sq := square_integral_le_length_mul_integral_square ht.1
    (hfD.mono_set hleft) (hfD2.mono_set hleft)
  have hright_sq := square_integral_le_length_mul_integral_square ht.2
    (hfD.mono_set hright) (hfD2.mono_set hright)
  rw [hleft_int, sub_zero] at hleft_sq
  rw [hright_int, neg_sq] at hright_sq
  have hl := mul_le_mul_of_nonneg_left hleft_sq (sub_nonneg.mpr ht.2)
  have hr := mul_le_mul_of_nonneg_left hright_sq ht.1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hfD2.mono_set hleft) (hfD2.mono_set hright)]
  nlinarith

/-- A square-integrable derivative and zero traces imply a quantitative
Dirichlet bound. Only a right derivative is needed at interior points. -/
theorem dirichlet_integral_square_le {f fD : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (hf : ContinuousOn f (Icc 0 L))
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivWithinAt f (fD x) (Ioi x) x)
    (hfD : IntervalIntegrable fD volume 0 L)
    (hfD2 : IntervalIntegrable (fun x => fD x ^ 2) volume 0 L)
    (hzero : f 0 = 0) (hend : f L = 0) :
    (∫ x in (0 : ℝ)..L, f x ^ 2) ≤ L ^ 2 / 6 * ∫ x in (0 : ℝ)..L, fD x ^ 2 := by
  let E := ∫ x in (0 : ℝ)..L, fD x ^ 2
  have hfi : IntervalIntegrable (fun x => f x ^ 2) volume 0 L :=
    ContinuousOn.intervalIntegrable_of_Icc hL.le (hf.pow 2)
  have hweight : Continuous (fun t : ℝ => t * (L - t) * E) := by fun_prop
  have hbound := intervalIntegral.integral_mono_on hL.le (hfi.const_mul L)
    (hweight.intervalIntegrable 0 L)
    (fun t ht => dirichlet_pointwise hL hf hderiv hfD hfD2 hzero hend ht)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
    integral_dirichlet_weight] at hbound
  have hfactor : 0 ≤ L * (L ^ 2 / 6 * E - ∫ x in (0 : ℝ)..L, f x ^ 2) := by
    nlinarith
  have h := nonneg_of_mul_nonneg_right hfactor hL
  exact sub_nonneg.mp h

/-- On the quarter interval, the elementary coefficient is strictly below
`5 / 12`. The rational comparison uses Mathlib's proved bound for π. -/
theorem quarter_dirichlet_coefficient_lt : (Real.pi / 2) ^ 2 / 6 < (5 / 12 : ℝ) := by
  have hπ := Real.pi_lt_d2
  have hπpos := Real.pi_pos
  have hprod := mul_pos (sub_pos.mpr hπ)
    (show 0 < (3.15 : ℝ) + Real.pi by linarith)
  nlinarith

theorem quarter_dirichlet_integral_square_le {f fD : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 (Real.pi / 2)))
    (hderiv : ∀ x ∈ Ioo 0 (Real.pi / 2), HasDerivWithinAt f (fD x) (Ioi x) x)
    (hfD : IntervalIntegrable fD volume 0 (Real.pi / 2))
    (hfD2 : IntervalIntegrable (fun x => fD x ^ 2) volume 0 (Real.pi / 2))
    (hzero : f 0 = 0) (hend : f (Real.pi / 2) = 0) :
    (∫ x in (0 : ℝ)..(Real.pi / 2), f x ^ 2) ≤
      5 / 12 * ∫ x in (0 : ℝ)..(Real.pi / 2), fD x ^ 2 := by
  have hL : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  have h := dirichlet_integral_square_le hL hf hderiv hfD hfD2 hzero hend
  have hE : 0 ≤ ∫ x in (0 : ℝ)..(Real.pi / 2), fD x ^ 2 :=
    intervalIntegral.integral_nonneg hL.le (fun x _ => sq_nonneg _)
  exact h.trans (mul_le_mul_of_nonneg_right quarter_dirichlet_coefficient_lt.le hE)

/-- For a continuous function, vanishing square integral gives literal
pointwise equality, including the two endpoints. -/
theorem eqOn_zero_of_integral_square_eq_zero {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hzero : (∫ x in a..b, f x ^ 2) = 0) : EqOn f (fun _ => 0) (Icc a b) := by
  have hi : IntegrableOn (fun x => f x ^ 2) (Icc a b) :=
    (hf.pow 2).integrableOn_compact isCompact_Icc
  have hzero' : (∫ x in Icc a b, f x ^ 2) = 0 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
    exact hzero
  have hae : (fun x => f x ^ 2) =ᵐ[volume.restrict (Icc a b)] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall (fun x => sq_nonneg (f x))) hi).mp hzero'
  have hfunction : f =ᵐ[volume.restrict (Icc a b)] (fun _ => 0) := by
    filter_upwards [hae] with x hx
    have hx' : f x ^ 2 = 0 := hx
    exact sq_eq_zero_iff.mp hx'
  exact Measure.eqOn_Icc_of_ae_eq volume hab.ne hfunction hf continuousOn_const

end AmbidextrousSofa.Analysis
