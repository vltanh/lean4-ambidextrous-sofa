module

public import AmbidextrousSofa.Analysis.PartialPressureLimit
public import AmbidextrousSofa.Analysis.SelectedErosionMoments

@[expose] public section

/-!
# Actual proper-angle selected erosion moments

The selected exposure inequality bounds each normalized physical source
balance from below by its persistent support error. With the general
selected erosion limits, this gives the erosion moments of the proper-angle
selected polygons; both barriers include the whole terminal first wall.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa
namespace PartialGrid

open FinitePolygon AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

theorem finiteExposureDefect_div_eq_integrals {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (j : SourceIndex α grid) :
    finiteExposureDefect U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) j /
        (normal α grid j).2 =
      (∫ x in (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)..
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4),
        innerDensity U α hαL grid j x) -
      (∫ x in (horizontalLeft U)..
        (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4),
        outerDensity U α grid j x) -
      (∫ x in (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)..
        (horizontalRight U), outerDensity U α grid j x) := by
  classical
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  unfold innerDensity outerDensity finiteExposureDefect WallExpr.sourceMass
  repeat rw [integral_sourceDensity_outward _ _ _ _ (by linarith)]
  ring

/-- Actual curvature and the retained middle facet give the outward
derivative bound even when the selected outer facet has zero length. -/
theorem IsSelectedPolygon.exposure_defect_div_ge {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U) (hc : 0 ≤ coefficient)
    (j : SourceIndex α (dyadic level)) :
    -selectionDefect target U α level coefficient j ≤
      finiteExposureDefect U (normal α (dyadic level)) (pairList α (dyadic level))
          (some (terminalIndex α hαL (dyadic level))) j / (normal α (dyadic level) j).2 := by
  rw [finiteExposureDefect_div_eq_integrals hU.isCap]
  exact neg_le_exposure_of_atom_le (intervalIntegrable_outerDensity U α _ j)
    (hU.curvature_atom_le hc j) (integral_outerSource_eq_curvature_atom hU.isCap _
      (normal_snd_pos α _) (wallSlopes_injective α _) hU.polygon_eq j (normal_eq_unitNormal α _ j))

end PartialGrid
end AmbidextrousSofa
