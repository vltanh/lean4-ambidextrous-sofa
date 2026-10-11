module

public import AmbidextrousSofa.Analysis.TangencyLoci

@[expose] public section

/-!
# Measurability of the actual tangency coordinates

The support-point formulas give globally measurable coordinate maps.
This permits transport of the literal branch measures without extending
a closed-interval parametrization or selecting a separate graph.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsDownwardCap.measurable_tangency_coordinates {U : Set Plane} (hU : IsDownwardCap U) :
    Measurable (fun t => (firstTangency U t).1) ∧ Measurable (fun t => (secondTangency U t).1) ∧
      Measurable (fun t => (secondTangency U t).2) := by
  have : Measurable (supportTangent U) := hU.measurable_supportTangent
  have := (continuous_angleSupport hU.isCompact).measurable
  simp only [firstTangency_fst_eq_support, secondTangency_fst_eq_support,
    secondTangency_snd_eq_support]
  refine ⟨?_, ?_, ?_⟩ <;> fun_prop

end AmbidextrousSofa
