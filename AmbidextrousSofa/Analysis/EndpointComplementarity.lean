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
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hbox : U ⊆ Icc (horizontalLeft U - 1) (horizontalRight U + 1) ×ˢ Icc (0 : ℝ) 1 :=
    fun p hp => ⟨⟨by linarith [(hU.isCap.fst_mem_Icc hp).1],
      by linarith [(hU.isCap.fst_mem_Icc hp).2]⟩, hU.isCap.inStrip hp⟩
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, _, hHausdorff⟩ :=
    AngularGrid.exists_selected_sequence hU (by linarith) hbox
  have hlevelTop : Tendsto level atTop atTop := tendsto_atTop_mono hlevel tendsto_id
  have hc0 : ∀ n, 0 ≤ coefficient n := fun n => (hc n).le
  have hwidth : 1 < capWidth U := one_lt_M.trans_le hU.width_bounds.1
  exact ⟨AngularGrid.right_complementarity_of_height_tendsto hU.isCap hbox hV hHausdorff
      hlevelTop hc0 hrate hwidth (lt_add_one _) (AngularGrid.selected_right_height_tendsto_actual
        hU.isCap hbox hV hHausdorff hlevelTop hc0 hrate hwidth (lt_add_one _)),
    AngularGrid.left_complementarity_of_height_tendsto hU.isCap hbox hV hHausdorff
      hlevelTop hc0 hrate hwidth (sub_one_lt _) (AngularGrid.selected_left_height_tendsto_actual
        hU.isCap hbox hV hHausdorff hlevelTop hc0 hrate hwidth (sub_one_lt _))⟩

theorem IsFullCapMaximizer.right_endpoint_complementarity {U : Set Plane}
    (hU : IsFullCapMaximizer U) :
    capRoof U (horizontalRight U) = max (capRightEndpointPressure U) 0 :=
  hU.endpoint_complementarity.1

theorem IsFullCapMaximizer.left_endpoint_complementarity {U : Set Plane}
    (hU : IsFullCapMaximizer U) :
    capRoof U (horizontalLeft U) = max (capLeftEndpointPressure U) 0 :=
  hU.endpoint_complementarity.2

end AmbidextrousSofa
