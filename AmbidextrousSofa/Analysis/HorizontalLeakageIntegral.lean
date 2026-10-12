module

public import AmbidextrousSofa.Analysis.HorizontalEndpointKernel
public import AmbidextrousSofa.Analysis.HorizontalLeakageScalar

@[expose] public section

/-!
# Exact integration of the horizontal curvature-excess envelope

The quadratic envelope has literal compact support. Its two moments are
simple polynomials obtained by direct integration. The kernel comparison
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
  rw [horizontalLeakageQuadratic]
  nlinarith [mul_nonneg (sub_nonneg.mpr hτ.2) (show 0 ≤ h + τ + 2 by linarith [hτ.1, hτ.2])]

theorem horizontalLeakageEnvelope_nonneg (A h s : ℝ) :
    0 ≤ horizontalLeakageEnvelope A h s :=
  indicator_nonneg (fun _ hs => horizontalLeakageQuadratic_nonneg
    ⟨by linarith [hs.1], by linarith [hs.2]⟩) s

theorem horizontalLeakageMajorant_nonneg (A h b s : ℝ) :
    0 ≤ horizontalLeakageMajorant A h b s :=
  indicator_nonneg (fun _ hs => mul_nonneg (add_nonneg (le_max_right _ _) (sub_nonneg.mpr hs.1))
    (horizontalLeakageQuadratic_nonneg ⟨by linarith [hs.1], by linarith [hs.2]⟩)) s

theorem integral_horizontalLeakageQuadratic (h : ℝ) :
    (∫ τ in (0 : ℝ)..h, horizontalLeakageQuadratic h τ) = horizontalLeakageA0 h := by
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) [horizontalLeakageQuadratic,
    horizontalLeakageA0, intervalIntegral.integral_sub, integral_pow]
  ring

theorem integral_horizontalLeakageMajorant {A h b : ℝ} (hh : 0 ≤ h) :
    (∫ s, horizontalLeakageMajorant A h b s) =
      horizontalLeakageA0 h * max (A - b) 0 + horizontalLeakageA1 h := by
  unfold horizontalLeakageMajorant
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_comp_sub_right
      (fun τ => (max (A - b) 0 + τ) * horizontalLeakageQuadratic h τ), sub_self,
    add_sub_cancel_left]
  -- the linear term is written `τ ^ 1` so that `integral_pow` integrates it
  have hfun (τ : ℝ) : (max (A - b) 0 + τ) * horizontalLeakageQuadratic h τ =
      max (A - b) 0 * ((h ^ 2 + 2 * h) / 4) + ((h ^ 2 + 2 * h) / 4 - max (A - b) 0 / 2) * τ ^ 1 -
        (1 / 2 + max (A - b) 0 / 4) * τ ^ 2 - τ ^ 3 / 4 := by
    rw [horizontalLeakageQuadratic]; ring
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only [hfun,
    intervalIntegral.integral_sub, intervalIntegral.integral_add, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_div, integral_pow, smul_eq_mul]
  rw [horizontalLeakageA0, horizontalLeakageA1]
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
  have hki : IntervalIntegrable (fun s => Real.sin (s - t) * (ρ s - 1)) volume t (Real.pi / 2) :=
    ((intervalIntegrable_bounded_real_density hρ hρ0 hρK t (Real.pi / 2)).sub
      intervalIntegrable_const).continuousOn_mul (by fun_prop)
  have hM : Integrable (horizontalLeakageMajorant A h b) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (Continuous.integrableOn_Icc (by
      unfold horizontalLeakageQuadratic; fun_prop))
  have hpoint : ∀ᵐ s ∂volume.restrict (Ioo t (Real.pi / 2)),
      Real.sin (s - t) * (ρ s - 1) ≤ horizontalLeakageMajorant A h b s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae_restrict_of_subset
      (Ioo_subset_Ioo ht.1.le le_rfl) hbound] with s hs hρs
    refine (mul_le_mul_of_nonneg_left hρs (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hs.1], by linarith [hs.2, ht.1, Real.pi_pos]⟩)).trans ?_
    by_cases hmem : s ∈ Icc A (A + h)
    · rw [horizontalLeakageEnvelope, indicator_of_mem hmem, horizontalLeakageMajorant,
        indicator_of_mem hmem]
      have := Real.sin_le (show 0 ≤ s - t by linarith [hs.1])
      exact mul_le_mul_of_nonneg_right (by linarith [le_max_left (A - b) 0])
        (horizontalLeakageQuadratic_nonneg ⟨by linarith [hmem.1], by linarith [hmem.2]⟩)
    · simp [horizontalLeakageEnvelope, horizontalLeakageMajorant, hmem]
  calc (∫ s in t..(Real.pi / 2), Real.sin (s - t) * (ρ s - 1))
      = ∫ s in Ioo t (Real.pi / 2), Real.sin (s - t) * (ρ s - 1) := by
        rw [intervalIntegral.integral_of_le ht.2.le, integral_Ioc_eq_integral_Ioo]
    _ ≤ ∫ s in Ioo t (Real.pi / 2), horizontalLeakageMajorant A h b s :=
        integral_mono_ae (hki.1.mono_set Ioo_subset_Ioc_self) hM.integrableOn hpoint
    _ ≤ ∫ s, horizontalLeakageMajorant A h b s :=
        setIntegral_le_integral hM (Eventually.of_forall (horizontalLeakageMajorant_nonneg A h b))
    _ = _ := integral_horizontalLeakageMajorant hh

end AmbidextrousSofa
