import AmbidextrousSofa.Analysis.TiltedFirstUnitEnergy

/-!
# Actual moment bounds for the first-unit energy

The remainders here are literal iterated sine integrals. Their bounds
use integrable curvature densities and almost-everywhere inequalities;
no continuous density or assumed remainder value is needed.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa.Analysis

def forwardSineConvolution (u : ℝ → ℝ) (a t : ℝ) : ℝ :=
  ∫ s in a..t, u s * Real.sin (t - s)

def backwardSineConvolution (v : ℝ → ℝ) (b t : ℝ) : ℝ :=
  ∫ s in t..b, v s * Real.sin (s - t)

def firstUnitLeftRemainder (r u : ℝ → ℝ) (γ : ℝ) : ℝ :=
  ∫ t in 0..γ, r t * forwardSineConvolution u 0 t

def firstUnitRightRemainder (r v : ℝ → ℝ) (β L : ℝ) : ℝ :=
  ∫ t in β..L, r t * backwardSineConvolution v L t

theorem absolutelyContinuousOnInterval_integral_left
    {r : ℝ → ℝ} {a b : ℝ} (hr : IntervalIntegrable r volume a b) :
    AbsolutelyContinuousOnInterval (fun t => ∫ s in t..b, r s) a b := by
  apply (hr.absolutelyContinuousOnInterval_intervalIntegral (show b ∈ uIcc a b by simp)).neg.congr
  intro t ht
  exact (intervalIntegral.integral_symm b t).symm

theorem backwardSineConvolution_eq_moments
    {v : ℝ → ℝ} {b t : ℝ} (hv : IntervalIntegrable v volume t b) :
    backwardSineConvolution v b t =
      Real.cos t * (∫ s in t..b, v s * Real.sin s) -
        Real.sin t * (∫ s in t..b, v s * Real.cos s) := by
  have hsin := hv.mul_continuousOn Real.continuous_sin.continuousOn
  have hcos := hv.mul_continuousOn Real.continuous_cos.continuousOn
  unfold backwardSineConvolution
  calc
    _ = ∫ s in t..b,
        Real.cos t * (v s * Real.sin s) - Real.sin t * (v s * Real.cos s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Real.sin_sub]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub (hsin.const_mul _) (hcos.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem absolutelyContinuousOnInterval_backwardSineConvolution
    {v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hv : IntervalIntegrable v volume a b) :
    AbsolutelyContinuousOnInterval (backwardSineConvolution v b) a b := by
  have hsin := hv.mul_continuousOn Real.continuous_sin.continuousOn
  have hcos := hv.mul_continuousOn Real.continuous_cos.continuousOn
  have hc : AbsolutelyContinuousOnInterval Real.cos a b :=
    (show ContDiff ℝ 1 Real.cos by fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have hs : AbsolutelyContinuousOnInterval Real.sin a b :=
    (show ContDiff ℝ 1 Real.sin by fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have hA := absolutelyContinuousOnInterval_integral_left hsin
  have hB := absolutelyContinuousOnInterval_integral_left hcos
  apply ((hc.mul hA).sub (hs.mul hB)).congr
  intro t ht
  have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
  have hvt := hv.mono_set (show uIcc t b ⊆ uIcc a b by
    simpa only [uIcc_of_le ht'.2, uIcc_of_le hab] using
      (Icc_subset_Icc ht'.1 (le_refl b)))
  exact (backwardSineConvolution_eq_moments hvt).symm

theorem backwardSineConvolution_le_five_fourths
    {v : ℝ → ℝ} {β t : ℝ}
    (hβ0 : 0 ≤ β) (ht : t ∈ Icc β (Real.pi / 2))
    (hv : IntervalIntegrable v volume β (Real.pi / 2))
    (hvbound : ∀ᵐ s ∂volume.restrict (Icc β (Real.pi / 2)), v s ≤ 5 / 4) :
    backwardSineConvolution v (Real.pi / 2) t ≤ 5 / 4 * (1 - Real.sin t) := by
  have hβL : β ≤ Real.pi / 2 := ht.1.trans ht.2
  have hvt := hv.mono_set (show uIcc t (Real.pi / 2) ⊆ uIcc β (Real.pi / 2) by
    simpa only [uIcc_of_le ht.2, uIcc_of_le hβL] using
      (Icc_subset_Icc ht.1 (le_refl (Real.pi / 2))))
  have hkernel : Continuous (fun s : ℝ => Real.sin (s - t)) := by fun_prop
  have hpoint : (fun s => v s * Real.sin (s - t)) ≤ᵐ[
      volume.restrict (Icc t (Real.pi / 2))] (fun s => 5 / 4 * Real.sin (s - t)) := by
    filter_upwards [ae_restrict_Icc_subinterval ht.1 le_rfl hvbound,
      ae_restrict_mem measurableSet_Icc] with s hvs hs
    apply mul_le_mul_of_nonneg_right hvs
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hs.1]
    · linarith [hs.2, Real.pi_pos]
  unfold backwardSineConvolution
  calc
    _ ≤ ∫ s in t..(Real.pi / 2), 5 / 4 * Real.sin (s - t) :=
      intervalIntegral.integral_mono_ae_restrict ht.2
        (hvt.mul_continuousOn hkernel.continuousOn)
        ((hkernel.const_mul (5 / 4)).intervalIntegrable _ _) hpoint
    _ = 5 / 4 * (1 - Real.sin t) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right,
        integral_sin]
      simp only [sub_self, Real.cos_zero, Real.cos_pi_div_two_sub]

theorem cos_le_four_fifths_of_sin_ge {t : ℝ} (hs : 3 / 5 ≤ Real.sin t) :
    Real.cos t ≤ 4 / 5 := by
  have hsin2 : 9 / 25 ≤ Real.sin t ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ Real.sin t - 3 / 5 by linarith)
      (show 0 ≤ Real.sin t + 3 / 5 by linarith)]
  by_contra hnle
  have hgt := lt_of_not_ge hnle
  have hprod := mul_pos (sub_pos.mpr hgt)
    (show 0 < Real.cos t + 4 / 5 by linarith)
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- The sine moment pays both the ordinary mass and the cosine moment
of the actual right-window deficit density. -/
theorem firstUnit_right_window_moment_bounds
    {r : ℝ → ℝ} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβL : β ≤ Real.pi / 2) (hβsin : 3 / 5 ≤ Real.sin β)
    (hr : IntervalIntegrable r volume β (Real.pi / 2))
    (hr0 : ∀ᵐ t ∂volume.restrict (Icc β (Real.pi / 2)), 0 ≤ r t) :
    0 ≤ (∫ t in β..(Real.pi / 2), r t * Real.sin t) ∧
      (∫ t in β..(Real.pi / 2), r t) ≤
        5 / 3 * (∫ t in β..(Real.pi / 2), r t * Real.sin t) ∧
      (∫ t in β..(Real.pi / 2), r t * Real.cos t) ≤
        4 / 3 * (∫ t in β..(Real.pi / 2), r t * Real.sin t) := by
  have hsin := hr.mul_continuousOn Real.continuous_sin.continuousOn
  have hcos := hr.mul_continuousOn Real.continuous_cos.continuousOn
  have hpoint : ∀ᵐ t ∂volume.restrict (Icc β (Real.pi / 2)),
      0 ≤ r t * Real.sin t ∧ r t ≤ 5 / 3 * (r t * Real.sin t) ∧
        r t * Real.cos t ≤ 4 / 3 * (r t * Real.sin t) := by
    filter_upwards [hr0, ae_restrict_mem measurableSet_Icc] with t hrt ht
    have hst : 3 / 5 ≤ Real.sin t := hβsin.trans
      (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) ht.2 ht.1)
    have hct := cos_le_four_fifths_of_sin_ge hst
    refine ⟨mul_nonneg hrt (by linarith), ?_, ?_⟩
    · nlinarith [mul_nonneg hrt (show 0 ≤ Real.sin t - 3 / 5 by linarith)]
    · nlinarith [mul_le_mul_of_nonneg_left
        (show Real.cos t ≤ 4 / 3 * Real.sin t by linarith) hrt]
  refine ⟨intervalIntegral.integral_nonneg_of_ae_restrict hβL (hpoint.mono fun t ht => ht.1), ?_, ?_⟩
  · have hi := intervalIntegral.integral_mono_ae_restrict hβL hr (hsin.const_mul (5 / 3))
      (hpoint.mono fun t ht => ht.2.1)
    simpa only [intervalIntegral.integral_const_mul] using hi
  · have hi := intervalIntegral.integral_mono_ae_restrict hβL hcos (hsin.const_mul (4 / 3))
      (hpoint.mono fun t ht => ht.2.2)
    simpa only [intervalIntegral.integral_const_mul] using hi

/-- This bounds the literal companion convolution remainder by the
actual sine moment, even when the companion density exceeds one. -/
theorem firstUnitRightRemainder_le
    {r v : ℝ → ℝ} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβL : β ≤ Real.pi / 2) (hβsin : 3 / 5 ≤ Real.sin β)
    (hr : IntervalIntegrable r volume β (Real.pi / 2))
    (hv : IntervalIntegrable v volume β (Real.pi / 2))
    (hr0 : ∀ᵐ t ∂volume.restrict (Icc β (Real.pi / 2)), 0 ≤ r t)
    (hvbound : ∀ᵐ t ∂volume.restrict (Icc β (Real.pi / 2)), v t ≤ 5 / 4) :
    firstUnitRightRemainder r v β (Real.pi / 2) ≤
      5 / 6 * (∫ t in β..(Real.pi / 2), r t * Real.sin t) := by
  have hconv := absolutelyContinuousOnInterval_backwardSineConvolution hβL hv
  have hpoint : (fun t => r t * backwardSineConvolution v (Real.pi / 2) t) ≤ᵐ[
      volume.restrict (Icc β (Real.pi / 2))] (fun t => (1 / 2) * r t) := by
    filter_upwards [hr0, ae_restrict_mem measurableSet_Icc] with t hrt ht
    have hst : 3 / 5 ≤ Real.sin t := hβsin.trans
      (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) ht.2 ht.1)
    have hc := backwardSineConvolution_le_five_fourths hβ0 ht hv hvbound
    have hch : backwardSineConvolution v (Real.pi / 2) t ≤ 1 / 2 := by linarith
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hch hrt
  have hi := intervalIntegral.integral_mono_ae_restrict hβL
    (hr.mul_continuousOn hconv.continuousOn) (hr.const_mul (1 / 2)) hpoint
  rw [intervalIntegral.integral_const_mul] at hi
  have hmass := (firstUnit_right_window_moment_bounds hβ0 hβL hβsin hr hr0).2.1
  unfold firstUnitRightRemainder
  linarith

theorem firstUnitLeftRemainder_nonneg
    {r u : ℝ → ℝ} {γ : ℝ} (hγ0 : 0 ≤ γ) (hγL : γ ≤ Real.pi / 2)
    (hr0 : ∀ᵐ t ∂volume.restrict (Icc 0 γ), 0 ≤ r t)
    (hu0 : ∀ᵐ t ∂volume.restrict (Icc 0 γ), 0 ≤ u t) :
    0 ≤ firstUnitLeftRemainder r u γ := by
  unfold firstUnitLeftRemainder
  apply intervalIntegral.integral_nonneg_of_ae_restrict hγ0
  filter_upwards [hr0, ae_restrict_mem measurableSet_Icc] with t hrt ht
  apply mul_nonneg hrt
  unfold forwardSineConvolution
  apply intervalIntegral.integral_nonneg_of_ae_restrict ht.1
  filter_upwards [ae_restrict_Icc_subinterval le_rfl ht.2 hu0,
    ae_restrict_mem measurableSet_Icc] with s hus hs
  apply mul_nonneg hus
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · linarith [hs.2]
  · linarith [hs.1, ht.2, Real.pi_pos]

end AmbidextrousSofa.Analysis
