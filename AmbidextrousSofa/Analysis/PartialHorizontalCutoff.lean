module

public import AmbidextrousSofa.Analysis.PartialSourceBalance
public import AmbidextrousSofa.Analysis.PartialSourceCounting
public import AmbidextrousSofa.Analysis.HorizontalCutoff

@[expose] public section

/-!
# Actual proper horizontal source moment away from the top

The full terminal wall contributes its ordinary literal source. A fixed
proper angle is separated from a sufficiently small neighborhood of the
top normal, where the sampled neighboring-wall estimate controls all
remaining inner mass. Outer source envelopes use the physical outer grid.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa
namespace PartialGrid

open FinitePolygon AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

theorem normal_snd_mul_innerSourceMass {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (j : SourceIndex α grid) :
    (normal α grid j).2 * innerSourceMass U α hαL grid j =
      (barrierExpr (pairList α grid) (some (terminalIndex α hαL grid))).sourceMass
        (wallSlope (normal α grid)) (barrierIntercept (normal α grid)
          (fun i => support U (normal α grid i)))
        (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) (some j) := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  rw [innerSourceMass, innerDensity, integral_sourceDensity_outward _ _ _ _
    (by unfold capWidth; linarith), mul_div_cancel₀ _ (normal_snd_pos α grid j).ne']
  rfl

theorem sum_sin_innerSourceMass_eq_positiveLength {U : Set Plane}
    (hU : IsDownwardCap U) (grid : Finset QuarterAngle) :
    (∑ j : SourceIndex α grid, (normal α grid j).2 * innerSourceMass U α hαL grid j) =
      finitePositiveLength U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid))
        (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  rw [finitePositiveLength_eq_sum _ _ _ _ (wallSlopes_injective α grid) (by
    unfold capWidth; linarith)]
  exact Finset.sum_congr rfl fun j _ => normal_snd_mul_innerSourceMass hU grid j

theorem normal_snd_mul_innerSourceMass_eq {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (j : SourceIndex α grid) :
    (normal α grid j).2 * innerSourceMass U α hαL grid j =
      finiteWingMass U (normal α grid) (some j) +
        (normal α grid j).2 * normalizedExposureDefect U α hαL grid j := by
  rw [normal_snd_mul_innerSourceMass hU, normalizedExposureDefect,
    mul_div_cancel₀ _ (normal_snd_pos α grid j).ne']
  unfold finiteExposureDefect finiteWingMass capWidth
  ring

theorem finitePositiveLength_le_horizontalOuterMass_away_top {U : Set Plane}
    (hU : IsDownwardCap U) {R η : ℝ} (hR : 0 ≤ R)
    (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1) (level : ℕ)
    (hη : η ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hterminal : η < Real.pi / 2 - α) :
    finitePositiveLength U (normal α (dyadic level)) (pairList α (dyadic level))
        (some (terminalIndex α hαL (dyadic level)))
        (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) ≤
      AngularGrid.horizontalOuterMass U (outerGrid α (dyadic level))
        (Ioo (0 : ℝ) Real.pi \ Icc (Real.pi / 2 - η) (Real.pi / 2 + η)) +
        (∑ j : SourceIndex α (dyadic level), |(normal α (dyadic level) j).1| *
          |normalizedExposureDefect U α hαL (dyadic level) j|) / Real.sin η +
        (8 * R + 24) * (2 * η + mesh α level) := by
  rw [← sum_sin_innerSourceMass_eq_positiveLength hU]
  exact sum_le_horizontalOuterMass_away_top (innerSourceMass_nonneg hU α hαL _)
    (normal_snd_mul_innerSourceMass_eq hU _) hη ((innerSourceMass_sum_interval_le hU α hαL hR hbox
      level (by linarith [hη.1]) fun ht => by linarith [ht.1]).trans_eq (by ring))

end PartialGrid
end AmbidextrousSofa
