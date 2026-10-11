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

theorem sourceBranch_sine_spatial_le {S : Set Plane} (hS : MeasurableSet S) :
    ((J.sourceBranchMeasure S).withDensity
      (fun z => ENNReal.ofReal (Real.sin z.1))).map Prod.snd ≤ volume := by
  rw [sourceBranchMeasure, ← restrict_withDensity hS]
  exact (Measure.map_mono Measure.restrict_le_self measurable_snd).trans
    J.horizontalProjection_le_volume

section ActualDensity

variable (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
  {m c : ℝ} {ρ : ℝ → ℝ}
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
    capRoof target x = m * x + c)
  (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
  (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
  (heq : (upperCurvature target).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

include hTarget hheight haffine hTargetBox hleft hright heq in
theorem ae_sourceBranchDensity_mul_sin_le_abs_deriv_on
    {S : Set Plane} (hS : MeasurableSet S) (d : ℝ)
    {X XD : ℝ → ℝ} (hX : Measurable X)
    (hgraph : ∀ᵐ z ∂J.sourceBranchMeasure S, z.2 = X (z.1 - d))
    {E : Set ℝ} (hE : MeasurableSet E)
    (hD : ∀ᵐ t ∂volume.restrict E, HasDerivAt X (XD t) t) :
    ∀ᵐ t ∂volume.restrict E,
      J.sourceBranchDensity S d t * Real.sin (t + d) ≤ |XD t| := by
  have hsin : Measurable fun t => Real.sin (t + d) :=
    Real.measurable_sin.comp (measurable_id.add_const d)
  have hmap := graph_weighted_map_eq (W := fun t => ENNReal.ofReal (Real.sin (t + d)))
    (measurable_fst.sub_const d) hX hsin.ennreal_ofReal hgraph
  rw [← sourceBranchAngular, J.sourceBranchAngular_eq_density hTarget hheight haffine hTargetBox
    hleft hright heq, ← withDensity_mul volume (J.measurable_sourceBranchDensity S d).ennreal_ofReal
    hsin.ennreal_ofReal] at hmap
  simp only [sub_add_cancel] at hmap
  refine ae_weight_le_abs_hasDerivAt_of_map_le_volume hE
    ((J.measurable_sourceBranchDensity S d).mul hsin).aemeasurable hX.aemeasurable hD ?_
  rw [← restrict_withDensity hE]
  refine (Measure.map_mono Measure.restrict_le_self hX).trans ?_
  simp_rw [ENNReal.ofReal_mul (J.sourceBranchDensity_nonneg S d _)]
  exact hmap.symm.trans_le (J.sourceBranch_sine_spatial_le hS)

end ActualDensity
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
