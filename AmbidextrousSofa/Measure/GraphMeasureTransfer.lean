import AmbidextrousSofa.Measure.RealRadonNikodym
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

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

theorem graph_spatial_map_eq
    {ν : Measure (ℝ × ℝ)} {X : ℝ → ℝ} (hX : Measurable X)
    (hgraph : ∀ᵐ z ∂ν, z.2 = X z.1) :
    ν.map Prod.snd = (ν.map Prod.fst).map X :=
  graph_map_eq measurable_fst hX hgraph

theorem graph_weighted_spatial_map_eq
    {ν : Measure (ℝ × ℝ)} {X : ℝ → ℝ} {W : ℝ → ℝ≥0∞}
    (hX : Measurable X) (hW : Measurable W)
    (hgraph : ∀ᵐ z ∂ν, z.2 = X z.1) :
    (ν.withDensity (fun z => W z.1)).map Prod.snd =
      ((ν.map Prod.fst).withDensity W).map X :=
  graph_weighted_map_eq measurable_fst hX hW hgraph

/-- The coordinate map only needs to be injective on the common
almost everywhere support of the two measures. -/
theorem measure_eq_of_map_eq_of_injOn
    {μ ν : Measure ℝ} {S : Set ℝ} {X : ℝ → ℝ}
    (hS : MeasurableSet S) (hX : Measurable X) (hinj : InjOn X S)
    (hμS : ∀ᵐ t ∂μ, t ∈ S) (hνS : ∀ᵐ t ∂ν, t ∈ S)
    (hmap : μ.map X = ν.map X) : μ = ν := by
  apply Measure.ext
  intro A hA
  let E : Set ℝ := X '' (A ∩ S)
  have hE : MeasurableSet E :=
    (hA.inter hS).image_of_measurable_injOn hX (hinj.mono inter_subset_right)
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
    _ = μ.map X E := (Measure.map_apply hX hE).symm
    _ = ν.map X E := congrArg (fun κ : Measure ℝ => κ E) hmap
    _ = ν (X ⁻¹' E) := Measure.map_apply hX hE
    _ = ν A := measure_congr (hpre ν hνS)

theorem ae_density_eq_of_map_eq_of_injOn
    {μ : Measure ℝ} [SigmaFinite μ] {S : Set ℝ} {X : ℝ → ℝ}
    {f g : ℝ → ℝ≥0∞}
    (hS : MeasurableSet S) (hX : Measurable X) (hinj : InjOn X S)
    (hμS : ∀ᵐ t ∂μ, t ∈ S) (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hmap : (μ.withDensity f).map X = (μ.withDensity g).map X) : f =ᵐ[μ] g := by
  have heq := measure_eq_of_map_eq_of_injOn hS hX hinj
    ((withDensity_absolutelyContinuous μ f).ae_le hμS)
    ((withDensity_absolutelyContinuous μ g).ae_le hμS) hmap
  exact (withDensity_eq_iff_of_sigmaFinite hf hg).mp heq

theorem ae_real_density_eq_of_map_eq_of_injOn
    {μ : Measure ℝ} [SigmaFinite μ] {S : Set ℝ} {X f g : ℝ → ℝ}
    (hS : MeasurableSet S) (hX : Measurable X) (hinj : InjOn X S)
    (hμS : ∀ᵐ t ∂μ, t ∈ S) (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hf0 : ∀ᵐ t ∂μ, 0 ≤ f t) (hg0 : ∀ᵐ t ∂μ, 0 ≤ g t)
    (hmap : (μ.withDensity (fun t => ENNReal.ofReal (f t))).map X =
      (μ.withDensity (fun t => ENNReal.ofReal (g t))).map X) : f =ᵐ[μ] g := by
  have heq := ae_density_eq_of_map_eq_of_injOn hS hX hinj hμS
    hf.ennreal_ofReal hg.ennreal_ofReal hmap
  filter_upwards [heq, hf0, hg0] with t ht hft hgt
  simpa only [ENNReal.toReal_ofReal hft, ENNReal.toReal_ofReal hgt] using
    congrArg ENNReal.toReal ht

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
