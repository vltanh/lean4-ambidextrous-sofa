module

public import AmbidextrousSofa.Analysis.JointBranchProjection
public import AmbidextrousSofa.Analysis.JointCoreFlux

@[expose] public section

/-!
# One horizontal budget for the two corner source branches

The two corner restrictions are disjoint parts of the same source
measure. Their common sine-weighted horizontal projection, the core
projection, is the transport along the core graph of the weighted sum of
their angular densities, which vanish off the core phase. Horizontal
domination then bounds that sum by the actual strictly negative core
velocity.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa
namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b C h m c K : ℝ} {ρ : ℝ → ℝ}
  (J : SelectedJointSourceLimit target a b) (H : IsTiltedFirstUnitTarget target a b C h m c ρ K)

/-- The two corner branches are disjoint parts of the same source measure. -/
theorem sourceBranchMeasure_corner_union (hT : IsCompact target) :
    J.sourceBranchMeasure (firstCornerSource target ∪ secondCornerSource target) =
      J.sourceBranchMeasure (firstCornerSource target) +
        J.sourceBranchMeasure (secondCornerSource target) :=
  Measure.restrict_union (disjoint_sourceSlices.mono inter_subset_left inter_subset_left)
    (measurableSet_secondCornerSource hT)

def coreSourceProjection : Measure ℝ :=
  ((J.sourceBranchMeasure (firstCornerSource target ∪ secondCornerSource target)).withDensity
    (fun z => ENNReal.ofReal (Real.sin z.1))).map Prod.snd

set_option quotPrecheck false
local notation "F" => fullTiltedSupportQuarterPair H.hU H.hm.le H.haffine H.hρ H.hρ0 H.hρK H.heq
local notation "Z" => innerCornerPoint (F).f (F).g
local notation "p" => supportP (F).fD (F).g
local notation "q" => supportQ (F).gD (F).f
local notation "X" => (fun t => (Z t).1)
local notation "XD" => (fun t => p t * Real.cos t - q t * Real.sin t)
local notation "aZ" => J.sourceBranchDensity (firstCornerSource target) 0
local notation "aW" => J.sourceBranchDensity (secondCornerSource target) (Real.pi / 2)
local notation "w" => (fun t => aZ t * Real.sin t + aW t * Real.cos t)

theorem coreSourceProjection_eq_density_graph {α η : ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    J.coreSourceProjection =
      ((volume.restrict (Ioo α η)).withDensity (fun t => ENNReal.ofReal (w t))).map X := by
  have hac := J.angularMeasure_absolutelyContinuous H
  have hX := H.core_continuous.1.measurable
  obtain ⟨hgeom₁, hgeom₂⟩ := J.ae_corner_core_geometry H hphase
  have hw : Measurable fun t => ENNReal.ofReal (aZ t * Real.sin (t + 0)) :=
    ((J.measurable_sourceBranchDensity _ _).mul
      (Real.measurable_sin.comp (measurable_id.add_const 0))).ennreal_ofReal
  have hz := J.ae_corner_density_zero_off_core H hphase
  -- Both densities vanish off the core, where both weights are nonnegative.
  have hdens : (volume.restrict (Ioo α η)).withDensity (fun t => ENNReal.ofReal (w t)) =
      volume.withDensity (fun t => ENNReal.ofReal (aZ t * Real.sin (t + 0))) +
        volume.withDensity (fun t => ENNReal.ofReal (aW t * Real.sin (t + Real.pi / 2))) := by
    rw [← withDensity_indicator measurableSet_Ioo, ← withDensity_add_left hw]
    refine withDensity_congr_ae ?_
    filter_upwards [hz] with t ht
    by_cases hc : t ∈ Ioo α η
    · obtain ⟨hs, hcos⟩ := sin_cos_pos_of_mem_quarter
        ⟨hphase.first_mem.1.trans hc.1, hc.2.trans hphase.second_mem.2⟩
      simp only [indicator_of_mem hc, Pi.add_apply, add_zero, Real.sin_add_pi_div_two]
      exact ENNReal.ofReal_add (mul_nonneg (J.sourceBranchDensity_nonneg _ _ _) hs.le)
        (mul_nonneg (J.sourceBranchDensity_nonneg _ _ _) hcos.le)
    · simp [indicator_of_notMem hc, (ht hc).1, (ht hc).2]
  rw [coreSourceProjection, J.sourceBranchMeasure_corner_union H.hU.isCap.isCompact,
    withDensity_add_measure, Measure.map_add _ _ measurable_snd,
    ← J.sourceBranch_graph_map hac hX (d := 0) (hgeom₁.mono fun z hz => by
      simpa only [sub_zero] using hz.2.1),
    ← J.sourceBranch_graph_map hac hX (hgeom₂.mono fun z hz => hz.2.1), ← Measure.map_add _ _ hX,
    hdens]


theorem ae_corner_source_weighted_sum_le_core_speed {α η : ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    ∀ᵐ t ∂volume.restrict (Ioo α η),
      aZ t * Real.sin t + aW t * Real.cos t ≤
        q t * Real.sin t - p t * Real.cos t := by
  have hX : Measurable X := H.core_continuous.1.measurable
  have hsub : Ioo α η ⊆ Ioo 0 (Real.pi / 2) := fun t ht =>
    ⟨hphase.first_mem.1.trans ht.1, ht.2.trans hphase.second_mem.2⟩
  -- The two disjoint corner branches share one horizontal budget.
  have hmap : ((volume.restrict (Ioo α η)).withDensity fun t =>
      ENNReal.ofReal (w t)).map X ≤ volume := by
    rw [← J.coreSourceProjection_eq_density_graph H hphase]
    exact J.sourceBranch_sine_spatial_le ((measurableSet_firstCornerSource
      H.hU.isCap.isCompact).union (measurableSet_secondCornerSource H.hU.isCap.isCompact))
  have hD : ∀ᵐ t ∂volume.restrict (Ioo α η), HasDerivAt X (XD t) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht using
      (fullTiltedSupportQuarterPair_core_hasDerivAt H.hU H.hm.le H.haffine H.hρ H.hρ0 H.hρK H.heq
        (hsub ht)).1
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_weight_le_abs_hasDerivAt_of_map_le_volume measurableSet_Ioo
      (((J.measurable_sourceBranchDensity _ _).fun_mul Real.measurable_sin).fun_add
        ((J.measurable_sourceBranchDensity _ _).fun_mul Real.measurable_cos)).aemeasurable
      hX.aemeasurable hD hmap] with t ht hb
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter (hsub ht)
  have hneg : XD t < 0 := sub_neg.mpr
    ((mul_neg_of_neg_of_pos (hphase.core_signs t ht).1 hc).trans
      (mul_pos (hphase.core_signs t ht).2 hs))
  simpa only [abs_of_nonpos hneg.le, neg_sub] using hb

end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
