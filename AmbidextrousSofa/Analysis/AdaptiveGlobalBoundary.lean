module

public import AmbidextrousSofa.Analysis.EulerFlux

@[expose] public section

/-!
# Width variations for the adaptive functional

This file proves the actual natural boundary condition for a local maximum
when the common horizontal endpoint is allowed to vary. The proof uses the
exact Taylor identity and a quadratic bound for both contact remainders;
it does not presume differentiability of an optimized value function.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace AmbidextrousSofa.Analysis

def QuarterPair.WidthTraces (u : QuarterPair) (a : ℝ) : Prop :=
  u.f 0 = a ∧ u.g 0 = 1 ∧ u.f (Real.pi / 2) = 1 ∧ u.g (Real.pi / 2) = a

end AmbidextrousSofa.Analysis
