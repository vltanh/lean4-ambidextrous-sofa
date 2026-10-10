module

public import AmbidextrousSofa.Measure.GraphMeasureTransfer
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Function.JacobianOneDim

@[expose] public section

/-!
# Exact angular density from a saturated injective graph

On an injective differentiable parameter set, the absolute derivative
measure maps exactly to length on the image. If another graph measure
has this same spatial restriction on the image of a measurable subset,
its density equals the absolute derivative almost everywhere there.
Continuity is needed only on the common parameter support, and is
derived from the stated derivatives in the saturation theorem.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal

namespace AmbidextrousSofa

theorem map_abs_deriv_density_eq_volume_image
    {S : Set ℝ} {X XD : ℝ → ℝ}
    (hS : MeasurableSet S) (hD : ∀ t ∈ S, HasDerivAt X (XD t) t) (hinj : InjOn X S) :
    ((volume.restrict S).withDensity (fun t => ENNReal.ofReal |XD t|)).map X =
      volume.restrict (X '' S) := by
  simpa only [ContinuousLinearMap.det_toSpanSingleton] using
    (map_withDensity_abs_det_fderiv_eq_addHaar
      (f := X) (f' := fun t => ContinuousLinearMap.toSpanSingleton ℝ (XD t))
      volume hS.nullMeasurableSet
      (fun t ht => (hD t ht).hasFDerivAt.hasFDerivWithinAt) hinj)

/-- Measurability away from the common almost-everywhere support is
unnecessary when recovering a measure from its injective graph map. -/
theorem measure_eq_of_map_eq_of_continuousOn_injOn
    {μ ν : Measure ℝ} {S : Set ℝ} {X : ℝ → ℝ}
    (hS : MeasurableSet S) (hX : ContinuousOn X S) (hinj : InjOn X S)
    (hμS : ∀ᵐ t ∂μ, t ∈ S) (hνS : ∀ᵐ t ∂ν, t ∈ S)
    (hmap : μ.map X = ν.map X) : μ = ν := by
  have hXμ : AEMeasurable X μ := by
    simpa only [Measure.restrict_eq_self_of_ae_mem hμS] using
      hX.aemeasurable (μ := μ) hS
  have hXν : AEMeasurable X ν := by
    simpa only [Measure.restrict_eq_self_of_ae_mem hνS] using
      hX.aemeasurable (μ := ν) hS
  apply Measure.ext
  intro A hA
  let E : Set ℝ := X '' (A ∩ S)
  have hE : MeasurableSet E := (hA.inter hS).image_of_continuousOn_injOn
    (hX.mono inter_subset_right) (hinj.mono inter_subset_right)
  have hpre (κ : Measure ℝ) (hκS : ∀ᵐ t ∂κ, t ∈ S) : X ⁻¹' E =ᵐ[κ] A := by
    filter_upwards [hκS] with t ht
    apply propext
    constructor
    · rintro ⟨s, ⟨hsA, hsS⟩, hst⟩
      have hst' : s = t := hinj hsS ht hst
      simpa only [hst'] using hsA
    · intro htA
      exact ⟨t, ⟨htA, ht⟩, rfl⟩
  calc
    μ A = μ (X ⁻¹' E) := (measure_congr (hpre μ hμS)).symm
    _ = μ.map X E := (Measure.map_apply_of_aemeasurable hXμ hE).symm
    _ = ν.map X E := congrArg (fun κ : Measure ℝ => κ E) hmap
    _ = ν (X ⁻¹' E) := Measure.map_apply_of_aemeasurable hXν hE
    _ = ν A := measure_congr (hpre ν hνS)

theorem restrict_graph_map_eq_map_restrict_of_injOn
    {μ : Measure ℝ} {S T : Set ℝ} {X : ℝ → ℝ}
    (hS : MeasurableSet S) (hX : ContinuousOn X S) (hinj : InjOn X S)
    (hμS : ∀ᵐ t ∂μ, t ∈ S) (hT : MeasurableSet T) (hTS : T ⊆ S) :
    (μ.map X).restrict (X '' T) = (μ.restrict T).map X := by
  have hXμ : AEMeasurable X μ := by
    simpa only [Measure.restrict_eq_self_of_ae_mem hμS] using
      hX.aemeasurable (μ := μ) hS
  have hXT : MeasurableSet (X '' T) := hT.image_of_continuousOn_injOn
    (hX.mono hTS) (hinj.mono hTS)
  rw [Measure.restrict_map_of_aemeasurable hXμ hXT]
  apply congrArg (fun κ : Measure ℝ => κ.map X)
  apply Measure.restrict_congr_set
  filter_upwards [hμS] with t ht
  apply propext
  constructor
  · rintro ⟨s, hsT, hst⟩
    have hst' : s = t := hinj (hTS hsT) ht hst
    simpa only [hst'] using hsT
  · intro htT
    exact ⟨t, htT, rfl⟩

/-- A saturated spatial image determines the source weight on its
parameter preimage. The weight need only be measurable and nonnegative
on the subset where the equality is claimed. -/
theorem ae_weight_eq_abs_deriv_of_graph_saturated_on
    {S T : Set ℝ} {X XD w : ℝ → ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hTS : T ⊆ S)
    (hD : ∀ t ∈ S, HasDerivAt X (XD t) t) (hinj : InjOn X S)
    (hw : AEMeasurable w (volume.restrict T))
    (hw0 : ∀ᵐ t ∂volume.restrict T, 0 ≤ w t)
    (hsaturated :
      (((volume.restrict S).withDensity (fun t => ENNReal.ofReal (w t))).map X).restrict
          (X '' T) = volume.restrict (X '' T)) :
    ∀ᵐ t ∂volume.restrict T, w t = |XD t| := by
  let μ : Measure ℝ := (volume.restrict S).withDensity (fun t => ENNReal.ofReal (w t))
  have hX : ContinuousOn X S :=
    fun t ht => (hD t ht).continuousAt.continuousWithinAt
  have hμS : ∀ᵐ t ∂μ, t ∈ S :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hS)
  have hrestrict := restrict_graph_map_eq_map_restrict_of_injOn hS hX hinj hμS hT hTS
  have hμT : μ.restrict T =
      (volume.restrict T).withDensity (fun t => ENNReal.ofReal (w t)) := by
    rw [μ, restrict_withDensity hT, Measure.restrict_restrict_of_subset hTS]
  change (μ.map X).restrict (X '' T) = _ at hsaturated
  rw [hrestrict, hμT] at hsaturated
  have harea := map_abs_deriv_density_eq_volume_image hT
    (fun t ht => hD t (hTS ht)) (hinj.mono hTS)
  have hmap : ((volume.restrict T).withDensity (fun t => ENNReal.ofReal (w t))).map X =
      ((volume.restrict T).withDensity (fun t => ENNReal.ofReal |XD t|)).map X :=
    hsaturated.trans harea.symm
  have hmeasures := measure_eq_of_map_eq_of_continuousOn_injOn hT (hX.mono hTS)
    (hinj.mono hTS)
    ((withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hT))
    ((withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hT)) hmap
  have hXD : AEMeasurable (fun t => |XD t|) (volume.restrict T) := by
    apply (measurable_deriv X).abs.aemeasurable.congr
    filter_upwards [ae_restrict_mem hT] with t ht
    exact congrArg abs (hD t (hTS ht)).deriv
  have heq := (withDensity_eq_iff_of_sigmaFinite hw.ennreal_ofReal hXD.ennreal_ofReal).mp
    hmeasures
  filter_upwards [heq, hw0] with t ht ht0
  simpa only [ENNReal.toReal_ofReal ht0, ENNReal.toReal_ofReal (abs_nonneg (XD t))] using
    congrArg ENNReal.toReal ht

end AmbidextrousSofa
