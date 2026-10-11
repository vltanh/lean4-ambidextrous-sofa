module

public import AmbidextrousSofa.Analysis.PartialGridPolygon
public import AmbidextrousSofa.Analysis.GridScore

@[expose] public section

/-!
# Uniform finite recovery of the proper-angle spatial score

The finite history keeps the whole terminal first wall. Its only error is
the integral of the omitted historical barrier over the actual moving
middle window. The rescaled angular approximation controls this error
uniformly on the complete boxed cap domain.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace AmbidextrousSofa

namespace PartialGrid

open FinitePolygon

def score (U : Set Plane) (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset AngularGrid.QuarterAngle) : ℝ :=
  finiteSpatialScore U (normal α grid) (pairList α grid)
    (some (terminalIndex α hαL grid))

theorem eventually_score_error_le {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2) :
    ∀ᶠ n in atTop, ∀ U : Set Plane, IsDownwardCap U →
      U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 →
        0 ≤ score U α hαL (AngularGrid.dyadic n) - capScore U α ∧
          score U α hαL (AngularGrid.dyadic n) - capScore U α ≤ ε := by
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_dyadic_box
    (isCompact_Icc.prod isCompact_Icc) a b) (ε / (b - a + 1)) (by positivity)] with n hn U hU hUB
  have hG := (continuous_barrier (AngularGrid.dyadic n)).comp
    (Continuous.prodMk_right (hU.toCompactCap, α))
  rw [score, finiteSpatialScore_eq_integrals hU, funext (finiteBarrier_eq_barrier U α hαL _)]
  exact hU.score_error_le hUB hε (integrableOn_partialBarrier_Icc hU.isCompact (TerminalAngle.pos α)
    α.property.2 _ _) (capScore_eq_integrals U α) hG
    (barrier_le_partialBarrier hU.toCompactCap α _) fun x hx => hn ((hU.toCompactCap, α), x)
      ⟨⟨hUB, mem_univ _⟩, hx⟩

theorem exists_level_score_error_le {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2) (m : ℕ) :
    ∃ n ≥ m, ∀ U : Set Plane, IsDownwardCap U →
      U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 →
        0 ≤ score U α hαL (AngularGrid.dyadic n) - capScore U α ∧
          score U α hαL (AngularGrid.dyadic n) - capScore U α ≤ ε :=
  ((eventually_ge_atTop m).and (eventually_score_error_le hab hε α hαL)).exists

end PartialGrid

end AmbidextrousSofa
