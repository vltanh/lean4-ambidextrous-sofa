module

public import AmbidextrousSofa.Analysis.TiltedEndpointLeakage
public import AmbidextrousSofa.Analysis.HorizontalLeakageIntegral
public import AmbidextrousSofa.Analysis.TerminalCompanionMoment
public import AmbidextrousSofa.Analysis.OneTurnArea

@[expose] public section

/-!
# The excess moment and the actual outer niche area

The sine-weighted positive curvature excess bounds the displacement of
every first inner wall beyond the literal top endpoint. Thus the actual
niche vanishes after that endpoint plus the excess moment. Convexity on
the right wing then bounds its area by a triangle. The last result
integrates the compact quadratic excess envelope with exact rational
constants; it makes no assumption about an active wall being attained.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

def firstExcessMoment (ρ : ℝ → ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..(Real.pi / 2), max (ρ s - 1) 0 * Real.sin s

theorem firstExcessMoment_integrable {ρ : ℝ → ℝ} {K a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K) :
    IntervalIntegrable (fun s => max (ρ s - 1) 0 * Real.sin s) volume a b :=
  (intervalIntegrable_terminal_positive_excess
    (intervalIntegrable_bounded_real_density hρ hρ0 hρK a b)).mul_continuousOn
      Real.continuous_sin.continuousOn

theorem firstExcessMoment_nonneg (ρ : ℝ → ℝ) : 0 ≤ firstExcessMoment ρ := by
  apply intervalIntegral.integral_nonneg (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
  intro s hs
  exact mul_nonneg (le_max_right _ _)
    (Real.sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith only [hs.2, Real.pi_pos]))

theorem first_density_kernel_le_excess_moment
    {ρ : ℝ → ℝ} {K t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    (∫ s in t..(Real.pi / 2), Real.sin (s - t) * (ρ s - 1)) ≤
      Real.cos t * firstExcessMoment ρ := by
  have hki : IntervalIntegrable (fun s => Real.sin (s - t) * (ρ s - 1))
      volume t (Real.pi / 2) :=
    ((intervalIntegrable_bounded_real_density hρ hρ0 hρK _ _).sub
      intervalIntegrable_const).continuousOn_mul
        ((Real.continuous_sin.comp (continuous_id.sub_const t)).continuousOn)
  have hei := firstExcessMoment_integrable (a := t) (b := Real.pi / 2) hρ hρ0 hρK
  have hc : 0 ≤ Real.cos t := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩).le
  have hs : 0 ≤ Real.sin t := (Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])).le
  have hlocal := intervalIntegral.integral_mono_on ht.2.le hki (hei.const_mul (Real.cos t))
    (show ∀ s ∈ Icc t (Real.pi / 2), Real.sin (s - t) * (ρ s - 1) ≤
      Real.cos t * (max (ρ s - 1) 0 * Real.sin s) from by
        intro s hst
        have hsin : 0 ≤ Real.sin (s - t) := Real.sin_nonneg_of_nonneg_of_le_pi
          (sub_nonneg.mpr hst.1) (by linarith only [hst.2, ht.1, Real.pi_pos])
        have hcos : 0 ≤ Real.cos s := Real.cos_nonneg_of_mem_Icc
          ⟨by linarith only [hst.1, ht.1, Real.pi_pos], hst.2⟩
        calc
          _ ≤ Real.sin (s - t) * max (ρ s - 1) 0 :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) hsin
          _ ≤ (Real.sin s * Real.cos t) * max (ρ s - 1) 0 := by
            apply mul_le_mul_of_nonneg_right _ (le_max_right _ _)
            rw [Real.sin_sub]
            exact sub_le_self _ (mul_nonneg hcos hs)
          _ = _ := by ring)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) (Real.pi / 2))]
      (fun s => max (ρ s - 1) 0 * Real.sin s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hst
    exact mul_nonneg (le_max_right _ _)
      (Real.sin_nonneg_of_nonneg_of_le_pi hst.1.le
        (by linarith only [hst.2, Real.pi_pos]))
  have hextend := intervalIntegral.integral_mono_interval
    (a := t) (b := Real.pi / 2) (c := 0) (d := Real.pi / 2)
    ht.1.le ht.2.le le_rfl hnonneg (firstExcessMoment_integrable hρ hρ0 hρK)
  rw [intervalIntegral.integral_const_mul] at hlocal
  exact hlocal.trans (mul_le_mul_of_nonneg_left hextend hc)

theorem IsDownwardCap.firstWall_nonpos_after_excess_moment
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K b t x : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ S)
    (htop : MovingSofaOptimality.vminus U (Real.pi / 2) = (b, 1))
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hx : b + firstExcessMoment ρ ≤ x) :
    firstWall U t x ≤ 0 := by
  have hkernel := first_density_kernel_le_excess_moment hρ hρ0 hρK ht
  have hc : 0 ≤ Real.cos t := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩).le
  have hs : 0 ≤ Real.sin t := (Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])).le
  rw [hU.firstWall_eq_density_kernel_at hρ hρ0 hρK heq ht
    ((Ioo_subset_Ioo ht.1.le le_rfl).trans hsub) htop x, ← add_div]
  apply div_nonpos_of_nonpos_of_nonneg _ hs
  have hprod := mul_nonpos_of_nonpos_of_nonneg
    (show b - x + firstExcessMoment ρ ≤ 0 by linarith only [hx]) hc
  nlinarith only [hkernel, hprod]

theorem IsDownwardCap.sweptNiche_zero_after_excess_moment
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K b x : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ S)
    (htop : MovingSofaOptimality.vminus U (Real.pi / 2) = (b, 1))
    (hx : b + firstExcessMoment ρ ≤ x) :
    sweptNiche U (Real.pi / 2) x = 0 := by
  apply le_antisymm _ (sweptNiche_nonneg _ _ _)
  apply sweptNiche_le_of_forall (by linarith only [Real.pi_pos]) le_rfl
  intro t ht
  exact (min_le_left (firstWall U t x) (secondWall U t x)).trans
    (hU.firstWall_nonpos_after_excess_moment hρ hρ0 hρK heq hsub htop ht hx)

/-- A nonnegative convex tail which has already vanished at `X` is
bounded by the triangle from `(a, f a)` to `(X, 0)`, even if the requested
integration endpoint lies on either side of `X`. -/
theorem ConvexOn.integral_tail_le_triangle {f : ℝ → ℝ} {a b X : ℝ}
    (hf : ConvexOn ℝ (Ici a) f) (hc : Continuous f) (hn : ∀ x, 0 ≤ f x)
    (hab : a ≤ b) (haX : a ≤ X) (hz : ∀ x, X ≤ x → f x = 0) :
    (∫ x in a..b, f x) ≤ (X - a) * f a / 2 := by
  by_cases heq : a = X
  · have hzero : (∫ x in a..b, f x) = 0 := by
      calc
        _ = ∫ x in a..b, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le hab] at hx
          exact hz x (heq ▸ hx.1)
        _ = 0 := intervalIntegral.integral_zero
    rw [hzero, ← heq, sub_self, zero_mul, zero_div]
  have haX' : a < X := lt_of_le_of_ne haX heq
  have htr := (hf.subset (fun _ hx => hx.1) (convex_Icc a X)).integral_le_trapezoid
    haX' (hc.intervalIntegrable a X)
  rw [hz X le_rfl, add_zero] at htr
  by_cases hXb : X ≤ b
  · have hzero : (∫ x in X..b, f x) = 0 := by
      calc
        _ = ∫ x in X..b, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le hXb] at hx
          exact hz x hx.1
        _ = 0 := intervalIntegral.integral_zero
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable a X) (hc.intervalIntegrable X b)
    rw [hzero, add_zero] at hsplit
    exact hsplit ▸ htr
  · exact (intervalIntegral.integral_mono_interval le_rfl hab (le_of_not_ge hXb)
      (Eventually.of_forall hn) (hc.intervalIntegrable a X)).trans htr

theorem IsDownwardCap.right_niche_integral_le_excess_triangle
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K C b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ S)
    (htop : MovingSofaOptimality.vminus U (Real.pi / 2) = (b, 1))
    (hC0 : 0 ≤ C) (hCb : C ≤ b)
    (hcorner : ∀ t ∈ Ioo (0 : ℝ) (Real.pi / 2), (attachedCorner U t).1 ≤ C) :
    (∫ x in C..(2 * C), sweptNiche U (Real.pi / 2) x) ≤
      (b - C + firstExcessMoment ρ) * sweptNiche U (Real.pi / 2) C / 2 := by
  have h := (hU.convexOn_sweptNiche_right_of_corners hcorner).integral_tail_le_triangle
    hU.continuous_sweptNiche_pi_div_two (sweptNiche_nonneg U (Real.pi / 2))
    (show C ≤ 2 * C by linarith only [hC0])
    (show C ≤ b + firstExcessMoment ρ by linarith only [hCb, firstExcessMoment_nonneg ρ])
    (fun x hx => hU.sweptNiche_zero_after_excess_moment hρ hρ0 hρK heq hsub htop hx)
  convert h using 1 <;> ring

theorem integrable_horizontalLeakageEnvelope (A h : ℝ) :
    Integrable (horizontalLeakageEnvelope A h) := by
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  exact (show Continuous (fun s : ℝ => horizontalLeakageQuadratic h (s - A)) by
    unfold horizontalLeakageQuadratic
    fun_prop).integrableOn_Icc

theorem integral_horizontalLeakageEnvelope {A h : ℝ} (hh : 0 ≤ h) :
    (∫ s, horizontalLeakageEnvelope A h s) = horizontalLeakageA0 h := by
  rw [horizontalLeakageEnvelope, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show A ≤ A + h by linarith only [hh])]
  have hshift := intervalIntegral.integral_comp_sub_right
    (a := A) (b := A + h) (horizontalLeakageQuadratic h) A
  simp only [sub_self, add_sub_cancel_left] at hshift
  rw [hshift, integral_horizontalLeakageQuadratic]

theorem firstExcessMoment_le_envelope_mass
    {ρ : ℝ → ℝ} {K A h B : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (hh : 0 ≤ h) (hB : 0 ≤ B) (hend : A + h ≤ B)
    (hbound : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      ρ s - 1 ≤ horizontalLeakageEnvelope A h s) :
    firstExcessMoment ρ ≤ B * horizontalLeakageA0 h := by
  classical
  have hM := (integrable_horizontalLeakageEnvelope A h).const_mul B
  have hpoint : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      max (ρ s - 1) 0 * Real.sin s ≤ B * horizontalLeakageEnvelope A h s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hbound] with s hs hρs
    have he := horizontalLeakageEnvelope_nonneg A h s
    have hmax : max (ρ s - 1) 0 ≤ horizontalLeakageEnvelope A h s := max_le hρs he
    have hsin : 0 ≤ Real.sin s := (Real.sin_pos_of_pos_of_lt_pi hs.1
      (by linarith only [hs.2, Real.pi_pos])).le
    apply (mul_le_mul_of_nonneg_right hmax hsin).trans
    by_cases hmem : s ∈ Icc A (A + h)
    · have hsB := (Real.sin_le hs.1.le).trans (hmem.2.trans hend)
      nlinarith only [mul_le_mul_of_nonneg_left hsB he]
    · simp only [horizontalLeakageEnvelope, indicator_of_notMem hmem, zero_mul, mul_zero,
        le_refl]
  have hlocal := integral_mono_ae
    ((firstExcessMoment_integrable (a := 0) (b := Real.pi / 2) hρ hρ0 hρK).1.mono_set
      Ioo_subset_Ioc_self) hM.integrableOn hpoint
  have hglobal := setIntegral_le_integral (s := Ioo (0 : ℝ) (Real.pi / 2)) hM
    (Eventually.of_forall (fun s => mul_nonneg hB (horizontalLeakageEnvelope_nonneg A h s)))
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ Real.pi / 2 by positivity)] at hlocal
  have htotal : (∫ s, B * horizontalLeakageEnvelope A h s) = B * horizontalLeakageA0 h := by
    rw [integral_const_mul, integral_horizontalLeakageEnvelope hh]
  exact (hlocal.trans hglobal).trans_eq htotal

/-- The uniform ET moment margin is exact: `121/4860 < 1/40`. -/
theorem firstExcessMoment_lt_one_fortieth_of_short_envelope
    {ρ : ℝ → ℝ} {K A h : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (hh : 0 ≤ h) (hh1 : h ≤ 1 / 3) (hend : A + h ≤ 11 / 15)
    (hbound : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      ρ s - 1 ≤ horizontalLeakageEnvelope A h s) :
    firstExcessMoment ρ < 1 / 40 := by
  have hfirst := firstExcessMoment_le_envelope_mass hρ hρ0 hρK hh
    (show (0 : ℝ) ≤ 11 / 15 by norm_num) hend hbound
  have hmass := mul_le_mul_of_nonneg_left (horizontalLeakageA0_mono hh hh1)
    (show (0 : ℝ) ≤ 11 / 15 by norm_num)
  exact (hfirst.trans hmass).trans_lt (by norm_num [horizontalLeakageA0])

end AmbidextrousSofa
