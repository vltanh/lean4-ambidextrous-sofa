module

public import AmbidextrousSofa.Analysis.HorizontalEndpointKernel
public import AmbidextrousSofa.Analysis.HorizontalLeakageScalar

@[expose] public section

/-!
# Exact integration of the horizontal curvature-excess envelope

The quadratic envelope has literal compact support. Its two moments are
the exact polynomials in the rational leakage rows. The kernel comparison
allows the crossing to precede the box angle and allows the support of
the envelope to extend beyond the angular integration interval.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

def horizontalLeakageQuadratic (h τ : ℝ) : ℝ :=
  (h ^ 2 + 2 * h) / 4 - τ / 2 - τ ^ 2 / 4

def horizontalLeakageEnvelope (A h s : ℝ) : ℝ :=
  (Icc A (A + h)).indicator (fun s => horizontalLeakageQuadratic h (s - A)) s

def horizontalLeakageMajorant (A h b s : ℝ) : ℝ :=
  (Icc A (A + h)).indicator
    (fun s => (max (A - b) 0 + (s - A)) * horizontalLeakageQuadratic h (s - A)) s

theorem horizontalLeakageQuadratic_nonneg {h τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) h) :
    0 ≤ horizontalLeakageQuadratic h τ := by
  have hprod := mul_nonneg (sub_nonneg.mpr hτ.2)
    (show 0 ≤ h + τ + 2 by linarith [hτ.1])
  unfold horizontalLeakageQuadratic
  nlinarith

theorem horizontalLeakageEnvelope_nonneg (A h s : ℝ) :
    0 ≤ horizontalLeakageEnvelope A h s := by
  classical
  by_cases hs : s ∈ Icc A (A + h)
  · rw [horizontalLeakageEnvelope, indicator_of_mem hs]
    apply horizontalLeakageQuadratic_nonneg
    constructor <;> linarith [hs.1, hs.2]
  · simp only [horizontalLeakageEnvelope, indicator_of_notMem hs, le_refl]

theorem horizontalLeakageMajorant_nonneg (A h b s : ℝ) :
    0 ≤ horizontalLeakageMajorant A h b s := by
  classical
  by_cases hs : s ∈ Icc A (A + h)
  · rw [horizontalLeakageMajorant, indicator_of_mem hs]
    exact mul_nonneg (add_nonneg (le_max_right _ _) (sub_nonneg.mpr hs.1))
      (horizontalLeakageQuadratic_nonneg ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  · simp only [horizontalLeakageMajorant, indicator_of_notMem hs, le_refl]

theorem integrable_horizontalLeakageMajorant (A h b : ℝ) :
    Integrable (horizontalLeakageMajorant A h b) := by
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  exact (show Continuous (fun s : ℝ =>
    (max (A - b) 0 + (s - A)) * horizontalLeakageQuadratic h (s - A)) by
      unfold horizontalLeakageQuadratic
      fun_prop).integrableOn_Icc

theorem integral_horizontalLeakageQuadratic (h : ℝ) :
    (∫ τ in (0 : ℝ)..h, horizontalLeakageQuadratic h τ) = horizontalLeakageA0 h := by
  unfold horizontalLeakageQuadratic horizontalLeakageA0
  rw [intervalIntegral.integral_sub
      ((intervalIntegrable_const (c := (h ^ 2 + 2 * h) / 4)).sub
        ((continuous_id.div_const 2).intervalIntegrable _ _))
      (((continuous_id.pow 2).div_const 4).intervalIntegrable _ _),
    intervalIntegral.integral_sub intervalIntegrable_const
      ((continuous_id.div_const 2).intervalIntegrable _ _),
    intervalIntegral.integral_div, intervalIntegral.integral_div,
    intervalIntegral.integral_const, integral_id, integral_pow]
  simp only [smul_eq_mul]
  ring

theorem integral_mul_horizontalLeakageQuadratic (h : ℝ) :
    (∫ τ in (0 : ℝ)..h, τ * horizontalLeakageQuadratic h τ) = horizontalLeakageA1 h := by
  have hfun (τ : ℝ) : τ * horizontalLeakageQuadratic h τ =
      ((h ^ 2 + 2 * h) / 4) * τ - τ ^ 2 / 2 - τ ^ 3 / 4 := by
    unfold horizontalLeakageQuadratic
    ring
  simp_rw [hfun]
  rw [intervalIntegral.integral_sub
      (((continuous_const.mul continuous_id).intervalIntegrable _ _).sub
        (((continuous_id.pow 2).div_const 2).intervalIntegrable _ _))
      (((continuous_id.pow 3).div_const 4).intervalIntegrable _ _),
    intervalIntegral.integral_sub ((continuous_const.mul continuous_id).intervalIntegrable _ _)
      (((continuous_id.pow 2).div_const 2).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
    intervalIntegral.integral_div, integral_id, integral_pow, integral_pow]
  unfold horizontalLeakageA1
  ring

theorem integral_horizontalLeakageMajorant {A h b : ℝ} (hh : 0 ≤ h) :
    (∫ s, horizontalLeakageMajorant A h b s) =
      horizontalLeakageA0 h * max (A - b) 0 + horizontalLeakageA1 h := by
  rw [horizontalLeakageMajorant, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show A ≤ A + h by linarith)]
  have hshift := intervalIntegral.integral_comp_sub_right
    (a := A) (b := A + h)
    (fun τ : ℝ => (max (A - b) 0 + τ) * horizontalLeakageQuadratic h τ) A
  simp only [sub_self, add_sub_cancel_left] at hshift
  rw [hshift]
  have hfun (τ : ℝ) : (max (A - b) 0 + τ) * horizontalLeakageQuadratic h τ =
      max (A - b) 0 * horizontalLeakageQuadratic h τ +
        τ * horizontalLeakageQuadratic h τ := by ring
  simp_rw [hfun]
  have hcont : Continuous (horizontalLeakageQuadratic h) := by
    unfold horizontalLeakageQuadratic
    fun_prop
  rw [intervalIntegral.integral_add
      ((continuous_const.mul hcont).intervalIntegrable _ _)
      ((continuous_id.mul hcont).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_horizontalLeakageQuadratic,
    integral_mul_horizontalLeakageQuadratic]
  ring

/-- The additional factor is valid even when the crossing lies before
the box angle. Only the part of the envelope inside the kernel interval
contributes, so no endpoint-containment hypothesis is needed. -/
theorem horizontal_density_kernel_le_envelope_moments
    {ρ : ℝ → ℝ} {K A h b t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (hh : 0 ≤ h) (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hbt : b ≤ t)
    (hbound : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      ρ s - 1 ≤ horizontalLeakageEnvelope A h s) :
    (∫ s in t..(Real.pi / 2), Real.sin (s - t) * (ρ s - 1)) ≤
      horizontalLeakageA0 h * max (A - b) 0 + horizontalLeakageA1 h := by
  classical
  have hρi := intervalIntegrable_bounded_real_density hρ hρ0 hρK t (Real.pi / 2)
  have hki : IntervalIntegrable (fun s => Real.sin (s - t) * (ρ s - 1))
      volume t (Real.pi / 2) := by
    simpa only [mul_comm] using
      (hρi.sub intervalIntegrable_const).mul_continuousOn
        (Real.continuous_sin.comp (continuous_id.sub_const t)).continuousOn
  have hM := integrable_horizontalLeakageMajorant A h b
  have hpoint : ∀ᵐ s ∂volume.restrict (Ioo t (Real.pi / 2)),
      Real.sin (s - t) * (ρ s - 1) ≤ horizontalLeakageMajorant A h b s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset
        (Ioo_subset_Ioo ht.1.le le_rfl) hbound] with s hs hρs
    have hsin0 : 0 ≤ Real.sin (s - t) := Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hs.1], by linarith [hs.2, ht.1, Real.pi_pos]⟩
    have hfirst := mul_le_mul_of_nonneg_left hρs hsin0
    apply hfirst.trans
    by_cases hmem : s ∈ Icc A (A + h)
    · rw [horizontalLeakageEnvelope, indicator_of_mem hmem,
        horizontalLeakageMajorant, indicator_of_mem hmem]
      apply mul_le_mul_of_nonneg_right _
        (horizontalLeakageQuadratic_nonneg ⟨by linarith [hmem.1], by linarith [hmem.2]⟩)
      have hsin := Real.sin_le (show 0 ≤ s - t by linarith [hs.1])
      have hmax : A - b ≤ max (A - b) 0 := le_max_left _ _
      linarith
    · simp only [horizontalLeakageEnvelope, horizontalLeakageMajorant,
        indicator_of_notMem hmem, mul_zero, le_refl]
  have hlocal : (∫ s in Ioo t (Real.pi / 2), Real.sin (s - t) * (ρ s - 1)) ≤
      ∫ s in Ioo t (Real.pi / 2), horizontalLeakageMajorant A h b s := by
    apply integral_mono_ae
      (hki.1.mono_set Ioo_subset_Ioc_self) hM.integrableOn hpoint
  have hglobal := setIntegral_le_integral (s := Ioo t (Real.pi / 2)) hM
    (Eventually.of_forall (horizontalLeakageMajorant_nonneg A h b))
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.2.le] at hlocal
  exact (hlocal.trans hglobal).trans_eq (integral_horizontalLeakageMajorant hh)

end AmbidextrousSofa
