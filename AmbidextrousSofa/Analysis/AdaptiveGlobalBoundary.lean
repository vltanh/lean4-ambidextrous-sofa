module

public import AmbidextrousSofa.Analysis.EulerFlux

@[expose] public section

/-!
# Width variations for the adaptive functional

`QuarterPair.WidthTraces u a` prescribes the four endpoint values of a pair
whose common horizontal endpoint `a`, the width, is allowed to vary.
-/

namespace AmbidextrousSofa.Analysis

def QuarterPair.WidthTraces (u : QuarterPair) (a : ℝ) : Prop :=
  u.f 0 = a ∧ u.g 0 = 1 ∧ u.f (Real.pi / 2) = 1 ∧ u.g (Real.pi / 2) = a

end AmbidextrousSofa.Analysis
