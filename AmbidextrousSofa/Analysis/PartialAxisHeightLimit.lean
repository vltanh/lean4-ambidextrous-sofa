module

public import AmbidextrousSofa.Analysis.PartialAxisCurvature
public import AmbidextrousSofa.Analysis.PartialPressureLimit
public import AmbidextrousSofa.Analysis.AxisHeightLimit

@[expose] public section

/-!
# Actual proper endpoint heights in the selected limit

The punctured-axis curvature estimates rule out a hidden limiting atom
next to either vertical face. Their rescaled mesh contribution tends to
zero. Hausdorff convergence at non-atomic interior angles consequently
identifies the independently constructed pressure limits with the actual
target endpoint heights.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa
namespace PartialGrid

open AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2} {target : Set Plane}
  {U : ℕ → Set Plane} {a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}

/-- The mesh term of the axis bounds tends to zero together with the selection defects. -/
private theorem axis_error_tendsto (C : ℝ) (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsDownwardCap (U n)) (hHausdorff : CapHausdorffTendsto U target)
    (hlevel : Tendsto level atTop atTop) (hc : ∀ n, 0 ≤ coefficient n)
    (hrate : Tendsto coefficient atTop (𝓝 0)) :
    Tendsto (fun n => C * mesh α (level n) +
      ∑ j, selectionDefect target (U n) α (level n) (coefficient n) j) atTop (𝓝 0) := by
  simpa only [Function.comp_apply, mul_zero, add_zero] using
    (((mesh_tendsto α).comp hlevel).const_mul C).add
      (selectionDefect_sum_tendsto hTarget hU hc hrate hHausdorff)

theorem selected_right_height_tendsto_actual
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : horizontalRight target < b) :
    Tendsto (fun n => capRoof (U n) (horizontalRight (U n))) atTop
      (𝓝 (capRoof target (horizontalRight target))) := by
  have hS := selectedLimit hTarget hTargetBox hU hHausdorff hlevel hc hrate hwidth
  have hheight := hS.right_height_tendsto hslack
  rwa [hHausdorff.right_height_eq_of_axis_bound hS.isCap hTarget (partialAxisCutoff_pos α one_pos)
    (axis_error_tendsto _ hTarget hS.isCap hHausdorff hlevel hc hrate)
    (fun ε hε hεδ => hS.eventually_one_le_capWidth.mono fun n hW =>
        ((hU n).curvature_right_axis_bound (hc n) (by positivity)
          (subset_symmetricBox_of_horizontalBox (hU n).inBox) one_pos hW hε hεδ).trans_eq
          (by rw [mul_add, add_assoc])) hheight] at hheight

theorem selected_left_height_tendsto_actual
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hwidth : 1 < capWidth target) (hslack : a < horizontalLeft target) :
    Tendsto (fun n => capRoof (U n) (horizontalLeft (U n))) atTop
      (𝓝 (capRoof target (horizontalLeft target))) := by
  have hS := selectedLimit hTarget hTargetBox hU hHausdorff hlevel hc hrate hwidth
  have hheight := hS.left_height_tendsto hslack
  rwa [hHausdorff.left_height_eq_of_axis_bound hS.isCap hTarget (partialAxisCutoff_pos α one_pos)
    (axis_error_tendsto _ hTarget hS.isCap hHausdorff hlevel hc hrate)
    (fun ε hε hεδ => hS.eventually_one_le_capWidth.mono fun n hW =>
        ((hU n).curvature_left_axis_bound (hc n) (by positivity)
          (subset_symmetricBox_of_horizontalBox (hU n).inBox) one_pos hW hε hεδ).trans_eq
          (by rw [mul_add, add_assoc])) hheight] at hheight

end PartialGrid
end AmbidextrousSofa
