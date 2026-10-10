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

/-- Projection domination controls an extended nonnegative density. No
integrability or injectivity premise is needed. -/
theorem ae_density_le_abs_deriv_of_map_le_volume
    {S : Set ℝ} {w : ℝ → ℝ≥0∞} {X : ℝ → ℝ}
    (hS : MeasurableSet S) (hw : AEMeasurable w (volume.restrict S))
    (hX : AEMeasurable X ((volume.restrict S).withDensity w))
    (hD : ∀ᵐ t ∂volume.restrict S, DifferentiableAt ℝ X t)
    (hmap : ((volume.restrict S).withDensity w).map X ≤ volume) :
    ∀ᵐ t ∂volume.restrict S, w t ≤ ENNReal.ofReal |deriv X t| := by
  let μ : Measure ℝ := (volume.restrict S).withDensity w
  let D : Set ℝ := {t | DifferentiableAt ℝ X t}
  have hDm : MeasurableSet D := measurableSet_of_differentiableAt ℝ X
  have hμac : μ ≪ volume.restrict S := withDensity_absolutelyContinuous _ _
  have hμS : μ Sᶜ = 0 := hμac (by
    rw [Measure.restrict_apply hS.compl, compl_inter_self, measure_empty])
  have hμD : μ Dᶜ = 0 := hμac (ae_iff.mp hD)
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hw
  intro A hA _
  let T : Set ℝ := (A ∩ S) ∩ D
  have hT : MeasurableSet T := (hA.inter hS).inter hDm
  have hmass : μ T = μ A := by
    change μ ((A ∩ S) ∩ D) = μ A
    rw [measure_inter_conull hμD, measure_inter_conull hμS]
  have harea : volume (X '' T) ≤ ∫⁻ t in T, ENNReal.ofReal |deriv X t| := by
    simpa only [ContinuousLinearMap.det_toSpanSingleton] using
      (addHaar_image_le_lintegral_abs_det_fderiv
        (f := X) (f' := fun t => ContinuousLinearMap.toSpanSingleton ℝ (deriv X t))
        volume hT (fun t ht =>
          (show DifferentiableAt ℝ X t from ht.2).hasDerivAt.hasFDerivAt.hasFDerivWithinAt))
  calc
    (∫⁻ t in A, w t ∂volume.restrict S) = μ A := (withDensity_apply w hA).symm
    _ = μ T := hmass.symm
    _ ≤ μ.map X (X '' T) := Measure.le_map_apply_image hX T
    _ ≤ volume (X '' T) := hmap (X '' T)
    _ ≤ ∫⁻ t in T, ENNReal.ofReal |deriv X t| := harea
    _ ≤ ∫⁻ t in A, ENNReal.ofReal |deriv X t| ∂volume.restrict S := by
      rw [Measure.restrict_restrict hA]
      exact lintegral_mono_set inter_subset_left

/-- Real-valued graph weights are bounded by any almost everywhere
derivative representative of the coordinate map. -/
theorem ae_weight_le_abs_hasDerivAt_of_map_le_volume
    {S : Set ℝ} {w X XD : ℝ → ℝ}
    (hS : MeasurableSet S) (hw : AEMeasurable w (volume.restrict S))
    (hX : AEMeasurable X
      ((volume.restrict S).withDensity (fun t => ENNReal.ofReal (w t))))
    (hD : ∀ᵐ t ∂volume.restrict S, HasDerivAt X (XD t) t)
    (hmap : ((volume.restrict S).withDensity (fun t => ENNReal.ofReal (w t))).map X ≤
      volume) :
    ∀ᵐ t ∂volume.restrict S, w t ≤ |XD t| := by
  have hbound := ae_density_le_abs_deriv_of_map_le_volume hS hw.ennreal_ofReal hX
    (hD.mono (fun _ ht => ht.differentiableAt)) hmap
  filter_upwards [hD, hbound] with t ht hle
  rw [ht.deriv] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (abs_nonneg (XD t))).mp hle

end AmbidextrousSofa
