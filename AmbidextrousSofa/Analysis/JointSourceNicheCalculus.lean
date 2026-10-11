module

public import AmbidextrousSofa.Analysis.JointBranchDensity
public import AmbidextrousSofa.Analysis.JointSourceAffine
public import AmbidextrousSofa.Analysis.JointNicheDerivative
public import AmbidextrousSofa.Analysis.ContactGraphSlope

@[expose] public section

/-!
# The common niche derivative on every actual source branch

The actual first-unit geometry identifies one open positive niche
interval. The joint measure is concentrated on that interval, so the
spatial graph residual cancels against every measurable spatial test.
At both strict tangent branches the residual vanishes separately.
Consequently the two corner restrictions carry exactly opposite
residual fluxes.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b C h m c K : ℝ} {ρ : ℝ → ℝ}
  (J : SelectedJointSourceLimit target a b)

def sourceGraphResidual (z : Plane) : ℝ :=
  J.nicheDerivative z.2 * Real.sin z.1 + Real.cos z.1

theorem integrable_sourceGraphResidual :
    Integrable J.sourceGraphResidual (J.measure : Measure Plane) :=
  (J.integrable_spatial_sine J.integrable_nicheDerivative).add
    (sourceCosineFunction.integrable _)

section ActualPair

variable (H : IsTiltedFirstUnitTarget target a b C h m c ρ K)
include H

theorem ae_hasDerivAt_niche_on_source :
    ∀ᵐ z ∂(J.measure : Measure Plane),
      HasDerivAt (sweptNiche target (Real.pi / 2)) (J.nicheDerivative z.2) z.2 := by
  have hd := (ae_restrict_iff' measurableSet_Ioo).mp
    (J.ae_hasDerivAt_niche H.hU.isCap H.Ioo_subset_box H.middle_eq.ge)
  filter_upwards [J.ae_spatial_mem_open_middle H.hU.isCap, ae_of_ae_map measurable_snd.aemeasurable
    (J.spatial_marginal_absolutelyContinuous.ae_le hd)] with z hz hd
  exact hd (H.middle_eq ▸ hz)

theorem setIntegral_sourceGraphResidual_eq_zero {E : Set ℝ} (hE : MeasurableSet E) :
    (∫ z in univ ×ˢ E, J.sourceGraphResidual z ∂(J.measure : Measure Plane)) = 0 := by
  have hP := H.positive_middle_eq
  have hs : univ ×ˢ E =ᵐ[(J.measure : Measure Plane)]
      univ ×ˢ (E ∩ firstUnitPositiveInterval target C) := by
    filter_upwards [J.ae_spatial_mem_open_middle H.hU.isCap, J.ae_niche_pos H] with z hz hp
    have : z.2 ∈ firstUnitPositiveInterval target C := hP.le ⟨H.middle_eq ▸ hz, hp⟩
    simp [this]
  rw [setIntegral_congr_set hs]
  exact J.setIntegral_graph_residual_eq_zero H.hU.isCap
    (fun x hx => H.Ioo_subset_box (hP.ge hx).1) (fun x hx => H.middle_eq.ge (hP.ge hx).1)
    (fun x hx => (hP.ge hx).2) (hE.inter measurableSet_Ioo) inter_subset_right

theorem setIntegral_corner_residuals_add_eq_zero {E : Set ℝ} (hE : MeasurableSet E) :
    (∫ z in univ ×ˢ E, J.sourceGraphResidual z
      ∂J.sourceBranchMeasure (firstCornerSource target)) +
      (∫ z in univ ×ˢ E, J.sourceGraphResidual z
        ∂J.sourceBranchMeasure (secondCornerSource target)) = 0 := by
  have hd := J.ae_hasDerivAt_niche_on_source H
  have hz₁ : ∀ᵐ z ∂J.sourceBranchMeasure (firstTangentSource target),
      J.sourceGraphResidual z = 0 := by
    filter_upwards [ae_restrict_mem (measurableSet_firstTangentSource H.hU.isCap.isCompact),
      ae_restrict_of_ae (J.ae_first_wall_contact H.hU.isCap), ae_restrict_of_ae hd]
      with z hz hc hd
    rw [sourceGraphResidual, H.hU.isCap.niche_derivative_at_strict_first_contact hz.1 hd
      (hc hz.1).1 hz.2, div_mul_cancel₀ _ (sin_cos_pos_of_mem_quarter hz.1).1.ne', neg_add_cancel]
  have hz₂ : ∀ᵐ z ∂J.sourceBranchMeasure (secondTangentSource target),
      J.sourceGraphResidual z = 0 := by
    filter_upwards [ae_restrict_mem (measurableSet_secondTangentSource H.hU.isCap.isCompact),
      ae_restrict_of_ae (J.ae_second_wall_contact H.hU.isCap), ae_restrict_of_ae hd]
      with z hz hc hd
    have hg := H.hU.isCap.niche_derivative_at_strict_second_contact
      ⟨by linarith only [hz.1.1], by linarith only [hz.1.2]⟩ hd (hc hz.1).1 hz.2
    rw [Real.sin_sub_pi_div_two, Real.cos_sub_pi_div_two] at hg
    rw [sourceGraphResidual, hg, div_mul_cancel₀ _ (Real.sin_pos_of_pos_of_lt_pi
      (by linarith only [hz.1.1, Real.pi_pos]) hz.1.2).ne', neg_add_cancel]
  have hi (S : Set Plane) : IntegrableOn J.sourceGraphResidual (univ ×ˢ E)
      (J.sourceBranchMeasure S) :=
    (J.integrable_sourceGraphResidual.mono_measure (J.sourceBranchMeasure_le S)).integrableOn
  have hz := J.setIntegral_sourceGraphResidual_eq_zero H hE
  rw [← J.source_four_branch_partition H, Measure.restrict_add, Measure.restrict_add,
    Measure.restrict_add, integral_add_measure (integrable_add_measure.mpr ⟨hi _, hi _⟩)
      (integrable_add_measure.mpr ⟨hi _, hi _⟩),
    integral_add_measure (hi _) (hi _), integral_add_measure (hi _) (hi _),
    integral_eq_zero_of_ae (ae_restrict_of_ae hz₁), integral_eq_zero_of_ae (ae_restrict_of_ae hz₂),
    zero_add, zero_add] at hz
  exact hz

end ActualPair
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
