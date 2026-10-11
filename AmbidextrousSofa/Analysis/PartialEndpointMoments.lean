module

public import AmbidextrousSofa.Analysis.SelectedEndpointMoments
public import AmbidextrousSofa.Analysis.PartialSelectedCurvature

@[expose] public section

/-!
# Proper-angle selected polygons are selected polygons

The physical finite source system retains every visited corner and the
whole terminal first wall. Aggregated support weights preserve the original
selection penalty, so the proper-angle selected polygons are selected
polygons in the general sense and inherit all their endpoint estimates.
-/

noncomputable section

namespace AmbidextrousSofa
namespace PartialGrid

open FinitePolygon AngularGrid

theorem IsSelectedPolygon.isSelected {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}
    {target U : Set Plane} {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U) (hc : 0 ≤ coefficient) :
    IsSelected (normal α (dyadic level)) (pairList α (dyadic level))
      (some (terminalIndex α hαL (dyadic level))) (fun i => coefficient * stageWeight α level i)
      target a b coefficient U where
  normal_unit i := ⟨_, normal_eq_unitNormal α _ i⟩
  normal_snd_pos := normal_snd_pos α _
  slope_injective := wallSlopes_injective α _
  weight_nonneg i := mul_nonneg hc (stageWeight_nonneg α level i)
  sum_weight_le := by
    rw [← Finset.mul_sum]; exact mul_le_of_le_one_right hc (sum_stageWeight_le_one α level)
  isCap := hU.isCap
  inBox := hU.inBox
  polygon_eq := hU.polygon_eq
  maximizes V hV hVB := by
    simpa only [score, sampledPenalty_mul, sampledPenalty_eq_stagePenalty] using
      hU.maximizes V hV hVB

end PartialGrid
end AmbidextrousSofa
