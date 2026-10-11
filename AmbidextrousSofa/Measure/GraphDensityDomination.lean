module

public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

/-!
# Density bounds from a dominated graph projection

If a weighted parameter measure maps into Lebesgue measure, its density is
at most the absolute derivative of the coordinate map almost everywhere.
The coordinate map need not be injective. On each measurable test set, the
upper area inequality bounds the length of its image by the integral of
the absolute derivative, while projection domination bounds the weighted
mass by that image length.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal

namespace AmbidextrousSofa

/-- Real-valued graph weights are bounded by any almost everywhere
derivative representative of the coordinate map. -/
theorem ae_weight_le_abs_hasDerivAt_of_map_le_volume
    {S : Set ℝ} {w X XD : ℝ → ℝ} (hS : MeasurableSet S) (hw : AEMeasurable w (volume.restrict S))
    (hX : AEMeasurable X ((volume.restrict S).withDensity (fun t => ENNReal.ofReal (w t))))
    (hD : ∀ᵐ t ∂volume.restrict S, HasDerivAt X (XD t) t)
    (hmap : ((volume.restrict S).withDensity (fun t => ENNReal.ofReal (w t))).map X ≤ volume) :
    ∀ᵐ t ∂volume.restrict S, w t ≤ |XD t| := by
  let μ : Measure ℝ := (volume.restrict S).withDensity (fun t => ENNReal.ofReal (w t))
  have hμac : μ ≪ volume.restrict S := withDensity_absolutelyContinuous _ _
  have hμS : μ Sᶜ = 0 := hμac (ae_iff.mp (ae_restrict_mem hS))
  have hμD : μ {t | DifferentiableAt ℝ X t}ᶜ = 0 :=
    hμac (ae_iff.mp (hD.mono fun _ ht => ht.differentiableAt))
  -- Projection domination controls the extended density, with no injectivity premise.
  have hbound : ∀ᵐ t ∂volume.restrict S, ENNReal.ofReal (w t) ≤ ENNReal.ofReal |deriv X t| := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hw.ennreal_ofReal fun A hA _ => ?_
    have hT := (hA.inter hS).inter (measurableSet_of_differentiableAt ℝ X)
    calc (∫⁻ t in A, ENNReal.ofReal (w t) ∂volume.restrict S) = μ A := (withDensity_apply _ hA).symm
      _ = μ (A ∩ S ∩ {t | DifferentiableAt ℝ X t}) := by
          rw [measure_inter_conull hμD, measure_inter_conull hμS]
      _ ≤ μ.map X (X '' _) := Measure.le_map_apply_image hX _
      _ ≤ volume (X '' _) := hmap _
      _ ≤ ∫⁻ t in A ∩ S ∩ {t | DifferentiableAt ℝ X t}, ENNReal.ofReal |deriv X t| := by
          simpa only [ContinuousLinearMap.det_toSpanSingleton] using
            addHaar_image_le_lintegral_abs_det_fderiv volume hT fun t ht =>
              (show DifferentiableAt ℝ X t from ht.2).hasDerivAt.hasFDerivAt.hasFDerivWithinAt
      _ ≤ ∫⁻ t in A, ENNReal.ofReal |deriv X t| ∂volume.restrict S := by
          rw [Measure.restrict_restrict hA]
          exact lintegral_mono_set inter_subset_left
  filter_upwards [hD, hbound] with t ht hle
  rwa [ht.deriv, ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)] at hle

end AmbidextrousSofa
