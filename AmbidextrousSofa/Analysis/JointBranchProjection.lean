module

public import AmbidextrousSofa.Analysis.JointBranchDensity
public import AmbidextrousSofa.Measure.GraphMeasureTransfer
public import AmbidextrousSofa.Measure.GraphDensityDomination

@[expose] public section

/-!
# Horizontal domination for each literal source branch

Restricting the common source measure preserves its sine-weighted
horizontal bound. When a branch lies on an actual graph, its sine-weighted
angular density pushes forward to that horizontal projection, so the same
bound passes to its real Radon--Nikodym density. The area inequality
bounds that weighted density by the absolute horizontal velocity without
requiring the graph to be injective.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa
namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

theorem sourceBranch_sine_spatial_le {S : Set Plane} (hS : MeasurableSet S) :
    ((J.sourceBranchMeasure S).withDensity
      (fun z => ENNReal.ofReal (Real.sin z.1))).map Prod.snd ≤ volume := by
  rw [sourceBranchMeasure, ← restrict_withDensity hS]
  exact (Measure.map_mono Measure.restrict_le_self measurable_snd).trans
    J.horizontalProjection_le_volume

variable (hac : J.angularMeasure ≪ volume)
include hac

theorem sourceBranch_density_sine_eq (S : Set Plane) (d : ℝ) :
    (J.sourceBranchAngular S d).withDensity (fun t => ENNReal.ofReal (Real.sin (t + d))) =
      volume.withDensity (fun t => ENNReal.ofReal
        (J.sourceBranchDensity S d t * Real.sin (t + d))) := by
  rw [J.sourceBranchAngular_eq_density hac,
    ← withDensity_mul volume (g := fun t => ENNReal.ofReal (Real.sin (t + d)))
      (J.measurable_sourceBranchDensity S d).ennreal_ofReal
      (Real.measurable_sin.comp (measurable_id.add_const d)).ennreal_ofReal]
  exact congrArg _ (funext fun t => (ENNReal.ofReal_mul (J.sourceBranchDensity_nonneg S d t)).symm)

/-- Along a graph `z.2 = X (z.1 - d)` of a branch, its weighted angular density pushes forward to
its sine-weighted horizontal projection. -/
theorem sourceBranch_graph_map {S : Set Plane} {d : ℝ} {X : ℝ → ℝ} (hX : Measurable X)
    (hgraph : ∀ᵐ z ∂J.sourceBranchMeasure S, z.2 = X (z.1 - d)) :
    (volume.withDensity fun t =>
      ENNReal.ofReal (J.sourceBranchDensity S d t * Real.sin (t + d))).map X =
      ((J.sourceBranchMeasure S).withDensity fun z =>
        ENNReal.ofReal (Real.sin z.1)).map Prod.snd := by
  rw [← J.sourceBranch_density_sine_eq hac]
  simpa only [sourceBranchAngular, sub_add_cancel] using (graph_weighted_map_eq
    (W := fun t => ENNReal.ofReal (Real.sin (t + d))) (measurable_fst.sub_const d) hX
    (Real.measurable_sin.comp (measurable_id.add_const d)).ennreal_ofReal hgraph).symm

theorem ae_sourceBranchDensity_mul_sin_le_abs_deriv_on
    {S : Set Plane} (hS : MeasurableSet S) (d : ℝ)
    {X XD : ℝ → ℝ} (hX : Measurable X)
    (hgraph : ∀ᵐ z ∂J.sourceBranchMeasure S, z.2 = X (z.1 - d))
    {E : Set ℝ} (hE : MeasurableSet E)
    (hD : ∀ᵐ t ∂volume.restrict E, HasDerivAt X (XD t) t) :
    ∀ᵐ t ∂volume.restrict E,
      J.sourceBranchDensity S d t * Real.sin (t + d) ≤ |XD t| := by
  refine ae_weight_le_abs_hasDerivAt_of_map_le_volume hE ((J.measurable_sourceBranchDensity S d).mul
    (Real.measurable_sin.comp (measurable_id.add_const d))).aemeasurable hX.aemeasurable hD ?_
  rw [← restrict_withDensity hE]
  exact (Measure.map_mono Measure.restrict_le_self hX).trans
    ((J.sourceBranch_graph_map hac hX hgraph).trans_le (J.sourceBranch_sine_spatial_le hS))

end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
