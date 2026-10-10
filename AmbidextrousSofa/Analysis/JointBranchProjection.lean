module

public import AmbidextrousSofa.Analysis.JointBranchDensity
public import AmbidextrousSofa.Measure.GraphMeasureTransfer
public import AmbidextrousSofa.Measure.GraphDensityDomination

@[expose] public section

/-!
# Horizontal domination for each literal source branch

Restricting the common source measure preserves its sine-weighted
horizontal bound. When a branch lies on an actual graph, the same bound
passes to its angular marginal and then to its real Radon--Nikodym
density. The area inequality bounds that weighted density by the
absolute horizontal velocity without requiring the graph to be injective.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa
namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

theorem source_sine_spatial_le :
    (((J.measure : Measure Plane).withDensity
      (fun z => ENNReal.ofReal (Real.sin z.1))).map Prod.snd) ≤ volume := by
  have h := J.horizontalProjection_le_volume
  rw [horizontalProjection, sourceHorizontalProjection, FiniteMeasure.toMeasure_map,
    weightedFiniteMeasure_toMeasure] at h
  exact h

theorem sourceBranch_sine_spatial_le {S : Set Plane} (hS : MeasurableSet S) :
    ((J.sourceBranchMeasure S).withDensity
      (fun z => ENNReal.ofReal (Real.sin z.1))).map Prod.snd ≤ volume := by
  unfold sourceBranchMeasure
  rw [← restrict_withDensity hS]
  exact (Measure.map_mono Measure.restrict_le_self measurable_snd).trans
    J.source_sine_spatial_le

theorem sourceBranch_sine_graph_le {S : Set Plane} (hS : MeasurableSet S)
    (d : ℝ) {X : ℝ → ℝ} (hX : Measurable X)
    (hgraph : ∀ᵐ z ∂J.sourceBranchMeasure S, z.2 = X (z.1 - d)) :
    ((J.sourceBranchAngular S d).withDensity
      (fun t => ENNReal.ofReal (Real.sin (t + d)))).map X ≤ volume := by
  calc
    _ = ((J.sourceBranchMeasure S).withDensity
        (fun z => ENNReal.ofReal (Real.sin z.1))).map Prod.snd := by
      simpa only [sourceBranchAngular, sub_add_cancel] using
        (graph_weighted_map_eq (measurable_fst.sub_const d) hX
          (Real.measurable_sin.comp (measurable_id.add_const d)).ennreal_ofReal hgraph).symm
    _ ≤ volume := J.sourceBranch_sine_spatial_le hS

section ActualDensity

variable (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
  {m c : ℝ} {ρ : ℝ → ℝ}
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
    capRoof target x = m * x + c)
  (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
  (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
  (heq : (upperCurvature target).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

theorem sourceBranch_density_sine_graph_le {S : Set Plane} (hS : MeasurableSet S)
    (d : ℝ) {X : ℝ → ℝ} (hX : Measurable X)
    (hgraph : ∀ᵐ z ∂J.sourceBranchMeasure S, z.2 = X (z.1 - d)) :
    (volume.withDensity (fun t => ENNReal.ofReal
      (J.sourceBranchDensity S d t * Real.sin (t + d)))).map X ≤ volume := by
  have hmap := J.sourceBranch_sine_graph_le hS d hX hgraph
  rw [J.sourceBranchAngular_eq_density hTarget hheight haffine hTargetBox hleft hright heq,
    ← withDensity_mul volume (J.measurable_sourceBranchDensity S d).ennreal_ofReal
      (Real.measurable_sin.comp (measurable_id.add_const d)).ennreal_ofReal] at hmap
  have hprod : (fun t => ENNReal.ofReal
      (J.sourceBranchDensity S d t * Real.sin (t + d))) =
      (fun t => ENNReal.ofReal (J.sourceBranchDensity S d t)) *
        (fun t => ENNReal.ofReal (Real.sin (t + d))) := by
    funext t
    exact ENNReal.ofReal_mul (J.sourceBranchDensity_nonneg S d t)
  rw [hprod]
  exact hmap

theorem ae_sourceBranchDensity_mul_sin_le_abs_deriv_on
    {S : Set Plane} (hS : MeasurableSet S) (d : ℝ)
    {X XD : ℝ → ℝ} (hX : Measurable X)
    (hgraph : ∀ᵐ z ∂J.sourceBranchMeasure S, z.2 = X (z.1 - d))
    {E : Set ℝ} (hE : MeasurableSet E)
    (hD : ∀ᵐ t ∂volume.restrict E, HasDerivAt X (XD t) t) :
    ∀ᵐ t ∂volume.restrict E,
      J.sourceBranchDensity S d t * Real.sin (t + d) ≤ |XD t| := by
  have hfull := J.sourceBranch_density_sine_graph_le hTarget hheight haffine hTargetBox
    hleft hright heq hS d hX hgraph
  have hrestricted :
      ((volume.restrict E).withDensity (fun t => ENNReal.ofReal
        (J.sourceBranchDensity S d t * Real.sin (t + d)))).map X ≤ volume := by
    rw [← restrict_withDensity hE]
    exact (Measure.map_mono Measure.restrict_le_self hX).trans hfull
  exact ae_weight_le_abs_hasDerivAt_of_map_le_volume hE
    ((J.measurable_sourceBranchDensity S d).mul
      (Real.measurable_sin.comp (measurable_id.add_const d))).aemeasurable
    hX.aemeasurable hD hrestricted

end ActualDensity
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
