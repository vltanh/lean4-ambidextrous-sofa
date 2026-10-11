module

public import AmbidextrousSofa.Analysis.TiltedFirstUnitEnergy

@[expose] public section

/-!
# Actual moment bounds for the first-unit energy

The remainders here are literal iterated sine integrals. A sine
convolution is a trigonometric combination of two moments with a moving
endpoint, so it is continuous for every integrable density, and the
backward convolution is the forward one based at the right endpoint. The
bounds use integrable curvature densities and almost-everywhere
inequalities; no continuous density or assumed remainder value is needed.
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

/-- The backward sine convolution is the forward one based at the right endpoint. -/
theorem backwardSineConvolution_eq_forward (v : ℝ → ℝ) (b : ℝ) :
    backwardSineConvolution v b = forwardSineConvolution v b := by
  ext t
  rw [backwardSineConvolution, forwardSineConvolution, intervalIntegral.integral_symm,
    ← intervalIntegral.integral_neg]
  congr 1 with s
  rw [← neg_sub t s, Real.sin_neg]; ring

theorem forwardSineConvolution_eq_moments
    {u : ℝ → ℝ} {a t : ℝ} (hu : IntervalIntegrable u volume a t) :
    forwardSineConvolution u a t =
      Real.sin t * (∫ s in a..t, u s * Real.cos s) -
        Real.cos t * (∫ s in a..t, u s * Real.sin s) := by
  rw [forwardSineConvolution, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      ((hu.mul_continuousOn Real.continuous_cos.continuousOn).const_mul _)
      ((hu.mul_continuousOn Real.continuous_sin.continuousOn).const_mul _)]
  congr 1 with s
  rw [Real.sin_sub]; ring

theorem continuousOn_forwardSineConvolution {u : ℝ → ℝ} {a b c : ℝ}
    (hu : IntervalIntegrable u volume a b) (hc : c ∈ uIcc a b) :
    ContinuousOn (forwardSineConvolution u c) (uIcc a b) :=
  ((Real.continuous_sin.continuousOn.mul (intervalIntegral.continuousOn_primitive_interval'
    (hu.mul_continuousOn Real.continuous_cos.continuousOn) hc)).sub
    (Real.continuous_cos.continuousOn.mul (intervalIntegral.continuousOn_primitive_interval'
      (hu.mul_continuousOn Real.continuous_sin.continuousOn) hc))).congr fun _ ht =>
    forwardSineConvolution_eq_moments (hu.mono_set (uIcc_subset_uIcc hc ht))

theorem backwardSineConvolution_le_five_fourths
    {v : ℝ → ℝ} {β t : ℝ}
    (hβ0 : 0 ≤ β) (ht : t ∈ Icc β (Real.pi / 2))
    (hv : IntervalIntegrable v volume β (Real.pi / 2))
    (hvbound : ∀ᵐ s ∂volume.restrict (Icc β (Real.pi / 2)), v s ≤ 5 / 4) :
    backwardSineConvolution v (Real.pi / 2) t ≤ 5 / 4 * (1 - Real.sin t) := by
  have hk : Continuous fun s : ℝ => Real.sin (s - t) := by fun_prop
  calc
    _ ≤ ∫ s in t..(Real.pi / 2), 5 / 4 * Real.sin (s - t) := by
      refine intervalIntegral.integral_mono_ae_restrict ht.2 ((hv.mono_set
        (uIcc_subset_uIcc_right (Icc_subset_uIcc ht))).mul_continuousOn hk.continuousOn)
        ((hk.const_mul _).intervalIntegrable _ _) ?_
      filter_upwards [ae_restrict_Icc_subinterval ht.1 le_rfl hvbound,
        ae_restrict_mem measurableSet_Icc] with s hvs hs
      exact mul_le_mul_of_nonneg_right hvs
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hs.1])
          (by linarith [hs.2, ht.1, Real.pi_pos]))
    _ = 5 / 4 * (1 - Real.sin t) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right,
        integral_sin]
      simp only [sub_self, Real.cos_zero, Real.cos_pi_div_two_sub]

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
  have hpoint : ∀ᵐ t ∂volume.restrict (Icc β (Real.pi / 2)),
      0 ≤ r t * Real.sin t ∧ r t ≤ 5 / 3 * (r t * Real.sin t) ∧
        r t * Real.cos t ≤ 4 / 3 * (r t * Real.sin t) := by
    filter_upwards [hr0, ae_restrict_mem measurableSet_Icc] with t hrt ht
    have hst : 3 / 5 ≤ Real.sin t := hβsin.trans
      (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) ht.2 ht.1)
    have hct : Real.cos t ≤ 4 / 5 := by
      nlinarith [Real.sin_sq_add_cos_sq t,
        mul_nonneg (sub_nonneg.2 hst) (by linarith : 0 ≤ Real.sin t + 3 / 5)]
    refine ⟨mul_nonneg hrt (by linarith), ?_, ?_⟩
    · linarith [mul_nonneg hrt (sub_nonneg.2 hst)]
    · linarith [mul_nonneg hrt (by linarith : 0 ≤ 4 / 3 * Real.sin t - Real.cos t)]
  refine ⟨intervalIntegral.integral_nonneg_of_ae_restrict hβL (hpoint.mono fun t ht => ht.1), ?_,
    ?_⟩ <;> rw [← intervalIntegral.integral_const_mul]
  · exact intervalIntegral.integral_mono_ae_restrict hβL hr (hsin.const_mul _)
      (hpoint.mono fun t ht => ht.2.1)
  · exact intervalIntegral.integral_mono_ae_restrict hβL
      (hr.mul_continuousOn Real.continuous_cos.continuousOn) (hsin.const_mul _)
      (hpoint.mono fun t ht => ht.2.2)

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
  have hi := intervalIntegral.integral_mono_ae_restrict hβL (hr.mul_continuousOn
    ((backwardSineConvolution_eq_forward v _).symm ▸
      continuousOn_forwardSineConvolution hv right_mem_uIcc)) (hr.const_mul (1 / 2)) <| by
      filter_upwards [hr0, ae_restrict_mem measurableSet_Icc] with t hrt ht
      have hst : 3 / 5 ≤ Real.sin t := hβsin.trans
        (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) ht.2 ht.1)
      have hc := backwardSineConvolution_le_five_fourths hβ0 ht hv hvbound
      exact (mul_le_mul_of_nonneg_left (by linarith) hrt).trans_eq (mul_comm _ _)
  rw [intervalIntegral.integral_const_mul] at hi
  unfold firstUnitRightRemainder
  linarith [(firstUnit_right_window_moment_bounds hβ0 hβL hβsin hr hr0).2.1]

theorem firstUnitLeftRemainder_nonneg
    {r u : ℝ → ℝ} {γ : ℝ} (hγ0 : 0 ≤ γ) (hγL : γ ≤ Real.pi / 2)
    (hr0 : ∀ᵐ t ∂volume.restrict (Icc 0 γ), 0 ≤ r t)
    (hu0 : ∀ᵐ t ∂volume.restrict (Icc 0 γ), 0 ≤ u t) :
    0 ≤ firstUnitLeftRemainder r u γ := by
  refine intervalIntegral.integral_nonneg_of_ae_restrict hγ0 ?_
  filter_upwards [hr0, ae_restrict_mem measurableSet_Icc] with t hrt ht
  refine mul_nonneg hrt (intervalIntegral.integral_nonneg_of_ae_restrict ht.1 ?_)
  filter_upwards [ae_restrict_Icc_subinterval le_rfl ht.2 hu0,
    ae_restrict_mem measurableSet_Icc] with s hus hs
  exact mul_nonneg hus (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hs.2])
    (by linarith [hs.1, ht.2, Real.pi_pos]))

end AmbidextrousSofa.Analysis
