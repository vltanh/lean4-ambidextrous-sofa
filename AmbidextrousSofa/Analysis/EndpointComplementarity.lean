module

public import AmbidextrousSofa.Analysis.AxisHeightLimit

@[expose] public section

/-!
# Endpoint complementarity for every actual full cap maximum

The actual selected sequence exists in a box with strict slack at both
axes. Its finite inward and outward variations determine the pressure
limit, while the neighboring-wall curvature estimate identifies the
limiting axis heights. The resulting law includes zero-height faces and
uses no regularity or endpoint complementarity certificate.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AmbidextrousSofa

theorem IsFullCapMaximizer.endpoint_complementarity {U : Set Plane}
    (hU : IsFullCapMaximizer U) :
    capRoof U (horizontalRight U) = max (capRightEndpointPressure U) 0 ∧
      capRoof U (horizontalLeft U) = max (capLeftEndpointPressure U) 0 := by
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, hH⟩ := hU.exists_selected_polygons
  have hwidth : 1 < capWidth U := one_lt_M.trans_le hU.width_bounds.1
  have hS := AngularGrid.selectedLimit hU.isCap hU.isCap.subset_slack_box hV hH hlevel hc hrate
    hwidth
  exact ⟨tendsto_nhds_unique (AngularGrid.selected_right_height_tendsto_actual hU.isCap
      hU.isCap.subset_slack_box hV hH hlevel hc hrate hwidth (lt_add_one _))
      (hS.right_height_tendsto (lt_add_one _)),
    tendsto_nhds_unique (AngularGrid.selected_left_height_tendsto_actual hU.isCap
      hU.isCap.subset_slack_box hV hH hlevel hc hrate hwidth (sub_one_lt _))
      (hS.left_height_tendsto (sub_one_lt _))⟩

end AmbidextrousSofa
