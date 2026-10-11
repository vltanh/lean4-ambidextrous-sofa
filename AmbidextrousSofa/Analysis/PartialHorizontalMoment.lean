module

public import AmbidextrousSofa.Analysis.PositivePartialBarrierLimit
public import AmbidextrousSofa.Analysis.SelectedHorizontalMoment

@[expose] public section

/-!
# The actual proper horizontal source inequality

For each fixed top cutoff, selected source errors and the mesh vanish.
The cutoff then shrinks while remaining disjoint from the fixed terminal
normal. Thus positive proper-barrier length is bounded by the charged
outer windows outside any actual height-one top segment. The theorem
constructs the actual selected polygons itself.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- The actual positive proper-barrier length is bounded by the charged
exterior windows outside any actual top segment. Every selected polygon
and source-limit input is constructed from this joint maximum. -/
theorem IsJointCapMaximizer.positive_partial_middle_measure_le_outer_without_top
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval
      (horizontalLeft U) (horizontalRight U), capRoof U x = m * x + c)
    {a b : ℝ} (ha : (a, 1) ∈ U) (hb : (b, 1) ∈ U) :
    volume.real (middleHalfInterval (horizontalLeft U) (horizontalRight U) ∩
      {x : ℝ | 0 < partialBarrier U α x}) ≤
    volume.real (Icc (horizontalLeft U) (horizontalLeft U + capWidth U / 4) \ Ioo a b) +
      volume.real (Icc (horizontalRight U - capWidth U / 4) (horizontalRight U) \ Ioo a b) := by
  let β : TerminalAngle := ⟨α, hU.angle_mem⟩
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, hH⟩ := hU.exists_selected_polygons hproper
  have hcap n := (hV n).isCap
  exact AngularGrid.limit_le_outer_without_top
    (grid := fun n => PartialGrid.outerGrid β (AngularGrid.dyadic (level n)))
    hH hcap hU.isCap (fun n => (hV n).polygon_eq)
    (fun n => (hV n).inBox) ha hb hheight (lt_min (sub_pos.2 hproper) Real.pi_div_two_pos)
    (min_le_right _ _) (PartialGrid.integral_positiveBarrierOverlap_tendsto (α := β)
      (hαL := hproper) hU.isCap hU.isCap.subset_slack_box hcap (fun n => (hV n).inBox) hH hlevel)
    (PartialGrid.sum_cos_abs_normalizedExposureDefect_tendsto_zero_of_canonical_maximum hU
      hheight haffine hU.isCap.subset_slack_box hV hH hlevel hc hrate (sub_one_lt _)
      (lt_add_one _)) ((PartialGrid.mesh_tendsto β).comp hlevel) fun η hη n =>
    (PartialGrid.integral_positiveBarrierOverlap_le hU.isCap _).trans
      (PartialGrid.finitePositiveLength_le_horizontalOuterMass_away_top (hcap n) (by positivity)
        (subset_symmetricBox_of_horizontalBox (hV n).inBox) (level n)
        ⟨hη.1, hη.2.trans_le (min_le_right _ _)⟩ (hη.2.trans_le (min_le_left _ _)))

end AmbidextrousSofa
