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

theorem IsDownwardCap.measurable_firstTangency_fst
    {U : Set Plane} (hU : IsDownwardCap U) :
    Measurable (fun t => (firstTangency U t).1) := by
  rw [funext (firstTangency_fst_eq_support U)]
  exact (((continuous_angleSupport hU.isCompact).measurable.sub_const 1).mul
    Real.measurable_cos).sub (hU.measurable_supportTangent.mul Real.measurable_sin)

theorem IsDownwardCap.measurable_firstTangency_snd
    {U : Set Plane} (hU : IsDownwardCap U) :
    Measurable (fun t => (firstTangency U t).2) := by
  rw [funext (firstTangency_snd_eq_support U)]
  exact (((continuous_angleSupport hU.isCompact).measurable.sub_const 1).mul
    Real.measurable_sin).add (hU.measurable_supportTangent.mul Real.measurable_cos)

theorem IsDownwardCap.measurable_secondTangency_fst
    {U : Set Plane} (hU : IsDownwardCap U) :
    Measurable (fun t => (secondTangency U t).1) := by
  rw [funext (secondTangency_fst_eq_support U)]
  exact (((hU.measurable_supportTangent.comp (measurable_id.add_const
    (Real.pi / 2))).neg).mul Real.measurable_cos).sub
      ((((continuous_angleSupport hU.isCompact).measurable.comp
        (measurable_id.add_const (Real.pi / 2))).sub_const 1).mul Real.measurable_sin)

theorem IsDownwardCap.measurable_secondTangency_snd
    {U : Set Plane} (hU : IsDownwardCap U) :
    Measurable (fun t => (secondTangency U t).2) := by
  rw [funext (secondTangency_snd_eq_support U)]
  exact (((hU.measurable_supportTangent.comp (measurable_id.add_const
    (Real.pi / 2))).neg).mul Real.measurable_sin).add
      ((((continuous_angleSupport hU.isCompact).measurable.comp
        (measurable_id.add_const (Real.pi / 2))).sub_const 1).mul Real.measurable_cos)

end AmbidextrousSofa
