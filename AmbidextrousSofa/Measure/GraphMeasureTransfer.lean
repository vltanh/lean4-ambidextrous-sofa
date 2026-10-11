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

theorem graph_weighted_map_eq
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {A Y : Ω → ℝ} {X : ℝ → ℝ} {W : ℝ → ℝ≥0∞}
    (hA : Measurable A) (hX : Measurable X) (hW : Measurable W)
    (hgraph : ∀ᵐ z ∂ν, Y z = X (A z)) :
    (ν.withDensity (fun z => W (A z))).map Y =
      ((ν.map A).withDensity W).map X := by
  rw [Measure.map_congr ((withDensity_absolutelyContinuous ν _).ae_le hgraph),
    ← map_withDensity_comp ν hA hW, Measure.map_map hX hA]
  rfl

/-- Every measurable spatial test determines the signed angular sum, for
integrable weights on one measurable parameter set on which the coordinate
is injective. -/
theorem ae_add_eq_zero_on_of_graph_setIntegral_eq_zero
    {S : Set ℝ} {X f g : ℝ → ℝ}
    (hS : MeasurableSet S) (hX : ContinuousOn X S) (hinj : InjOn X S)
    (hf : IntegrableOn f S) (hg : IntegrableOn g S)
    (htest : ∀ E : Set ℝ, MeasurableSet E →
      (∫ t in S ∩ X ⁻¹' E, f t) + (∫ t in S ∩ X ⁻¹' E, g t) = 0) :
    ∀ᵐ t ∂volume.restrict S, f t + g t = 0 := by
  refine (hf.add hg).ae_eq_zero_of_forall_setIntegral_eq_zero fun A hA _ => ?_
  have hpre : X ⁻¹' (X '' (A ∩ S)) =ᵐ[volume.restrict S] A := by
    filter_upwards [ae_restrict_mem hS] with t ht
    exact propext ⟨fun ⟨s, ⟨hsA, hsS⟩, hst⟩ => hinj hsS ht hst ▸ hsA, fun h => ⟨t, ⟨h, ht⟩, rfl⟩⟩
  rw [setIntegral_congr_set hpre.symm, integral_add' hf.integrableOn hg.integrableOn]
  simpa only [Measure.restrict_restrict' hS, inter_comm] using htest _
    ((hA.inter hS).image_of_continuousOn_injOn (hX.mono inter_subset_right)
      (hinj.mono inter_subset_right))

end AmbidextrousSofa
