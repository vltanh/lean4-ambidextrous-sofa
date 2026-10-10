import AmbidextrousSofa.Analysis.AxisHeightLimit

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
  let a := horizontalLeft U - 1
  let b := horizontalRight U + 1
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hbox : U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 := by
    intro p hp
    have hx : p.1 ∈ Icc (horizontalLeft U) (horizontalRight U) := by
      rw [← horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex]
      exact ⟨p, hp, rfl⟩
    refine ⟨⟨?_, ?_⟩, hU.isCap.inStrip hp⟩
    · dsimp [a]
      linarith [hx.1]
    · dsimp [b]
      linarith [hx.2]
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, _, hHausdorff⟩ :=
    AngularGrid.exists_selected_sequence hU hab hbox
  have hlevelTop : Tendsto level atTop atTop := tendsto_atTop_mono hlevel tendsto_id
  have hc0 : ∀ n, 0 ≤ coefficient n := fun n => (hc n).le
  have hwidth : 1 < capWidth U := one_lt_M.trans_le hU.width_bounds.1
  have hright : horizontalRight U < b := by dsimp [b]; linarith
  have hleft : a < horizontalLeft U := by dsimp [a]; linarith
  have hR := AngularGrid.selected_right_height_tendsto_actual hU.isCap hbox hV hHausdorff
    hlevelTop hc0 hrate hwidth hright
  have hL := AngularGrid.selected_left_height_tendsto_actual hU.isCap hbox hV hHausdorff
    hlevelTop hc0 hrate hwidth hleft
  exact ⟨AngularGrid.right_complementarity_of_height_tendsto hU.isCap hbox hV hHausdorff
      hlevelTop hc0 hrate hwidth hright hR,
    AngularGrid.left_complementarity_of_height_tendsto hU.isCap hbox hV hHausdorff
      hlevelTop hc0 hrate hwidth hleft hL⟩

theorem IsFullCapMaximizer.right_endpoint_complementarity {U : Set Plane}
    (hU : IsFullCapMaximizer U) :
    capRoof U (horizontalRight U) = max (capRightEndpointPressure U) 0 :=
  hU.endpoint_complementarity.1

theorem IsFullCapMaximizer.left_endpoint_complementarity {U : Set Plane}
    (hU : IsFullCapMaximizer U) :
    capRoof U (horizontalLeft U) = max (capLeftEndpointPressure U) 0 :=
  hU.endpoint_complementarity.2

end AmbidextrousSofa
