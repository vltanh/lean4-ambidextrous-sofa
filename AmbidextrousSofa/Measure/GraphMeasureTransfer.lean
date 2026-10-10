module

public import AmbidextrousSofa.Measure.RealRadonNikodym
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# Transferring source measures along a graph

A measure supported on a literal graph has the expected spatial
projection, including every measurable angular weight. On an injective
part of the graph, spatial equality determines angular equality.
The signed version uses integrable real weights and all measurable
spatial tests, so it also applies to the two opposing normal fluxes.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal

namespace AmbidextrousSofa

theorem graph_map_eq
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {A Y : Ω → ℝ} {X : ℝ → ℝ} (hA : Measurable A) (hX : Measurable X)
    (hgraph : ∀ᵐ z ∂ν, Y z = X (A z)) :
    ν.map Y = (ν.map A).map X := by
  calc
    ν.map Y = ν.map (fun z => X (A z)) := Measure.map_congr hgraph
    _ = (ν.map A).map X := (Measure.map_map hX hA).symm

theorem graph_weighted_map_eq
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {A Y : Ω → ℝ} {X : ℝ → ℝ} {W : ℝ → ℝ≥0∞}
    (hA : Measurable A) (hX : Measurable X) (hW : Measurable W)
    (hgraph : ∀ᵐ z ∂ν, Y z = X (A z)) :
    (ν.withDensity (fun z => W (A z))).map Y =
      ((ν.map A).withDensity W).map X := by
  have hweighted : ∀ᵐ z ∂ν.withDensity (fun z => W (A z)), Y z = X (A z) :=
    (withDensity_absolutelyContinuous ν _).ae_le hgraph
  rw [graph_map_eq hA hX hweighted, map_withDensity_comp ν hA hW]

/-- Every measurable spatial test determines the signed angular sum
when the coordinate is injective on its almost everywhere support. -/
theorem ae_add_eq_zero_of_graph_setIntegral_eq_zero
    {μ : Measure ℝ} {S : Set ℝ} {X f g : ℝ → ℝ}
    (hS : MeasurableSet S) (hX : ContinuousOn X S) (hinj : InjOn X S)
    (hμS : ∀ᵐ t ∂μ, t ∈ S) (hf : Integrable f μ) (hg : Integrable g μ)
    (htest : ∀ E : Set ℝ, MeasurableSet E →
      (∫ t in X ⁻¹' E, f t ∂μ) + (∫ t in X ⁻¹' E, g t ∂μ) = 0) :
    ∀ᵐ t ∂μ, f t + g t = 0 := by
  apply (hf.add hg).ae_eq_zero_of_forall_setIntegral_eq_zero
  intro A hA _
  let E : Set ℝ := X '' (A ∩ S)
  have hE : MeasurableSet E := (hA.inter hS).image_of_continuousOn_injOn
    (hX.mono inter_subset_right) (hinj.mono inter_subset_right)
  have hpre : X ⁻¹' E =ᵐ[μ] A := by
    filter_upwards [hμS] with t ht
    apply propext
    constructor
    · rintro ⟨s, ⟨hsA, hsS⟩, hst⟩
      have hst' : s = t := hinj hsS ht hst
      simpa only [hst'] using hsA
    · intro htA
      exact ⟨t, ⟨htA, ht⟩, rfl⟩
  calc
    (∫ t in A, f t + g t ∂μ) = ∫ t in X ⁻¹' E, f t + g t ∂μ :=
      setIntegral_congr_set hpre.symm
    _ = (∫ t in X ⁻¹' E, f t ∂μ) + (∫ t in X ⁻¹' E, g t ∂μ) :=
      integral_add hf.integrableOn hg.integrableOn
    _ = 0 := htest E hE

/-- Version for integrable weights on one measurable parameter set. -/
theorem ae_add_eq_zero_on_of_graph_setIntegral_eq_zero
    {S : Set ℝ} {X f g : ℝ → ℝ}
    (hS : MeasurableSet S) (hX : ContinuousOn X S) (hinj : InjOn X S)
    (hf : IntegrableOn f S) (hg : IntegrableOn g S)
    (htest : ∀ E : Set ℝ, MeasurableSet E →
      (∫ t in S ∩ X ⁻¹' E, f t) + (∫ t in S ∩ X ⁻¹' E, g t) = 0) :
    ∀ᵐ t ∂volume.restrict S, f t + g t = 0 := by
  apply ae_add_eq_zero_of_graph_setIntegral_eq_zero hS hX hinj
    (ae_restrict_mem hS) hf hg
  intro E hE
  simpa only [Measure.restrict_restrict' hS, inter_comm] using htest E hE

end AmbidextrousSofa
