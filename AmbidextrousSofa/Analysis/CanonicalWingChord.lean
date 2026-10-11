module

public import AmbidextrousSofa.Analysis.FiniteGraphLength
public import AmbidextrousSofa.Analysis.SelectedGreenLimit
public import AmbidextrousSofa.Analysis.CanonicalOneTurn

@[expose] public section

/-!
# The wing chord comparison for every canonical full maximum

The exact finite Green limit and the actual endpoint-height limits pass
the two finite chord inequalities to the prescribed maximizer. The
approximating polygons are constructed in the final theorem. A Euclidean
triangle inequality gives the compressed chord bound, which combines
with the actual one-turn survivor to give the stronger CG area constraint.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- The endpoint chord comparison has no approximation hypothesis: the
actual selected sequence is constructed from this full maximizer. -/
theorem IsFullCapMaximizer.wing_chords_le_twice_score_of_affine
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    Real.sqrt (((horizontalRight U - horizontalLeft U) / 4) ^ 2 +
      (capRoof U (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) -
        capRoof U (horizontalLeft U)) ^ 2) +
    Real.sqrt (((horizontalRight U - horizontalLeft U) / 4) ^ 2 +
      (capRoof U (horizontalRight U) -
        capRoof U (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)) ^ 2) ≤
      2 * capScore U (Real.pi / 2) := by
  have hwidth : 1 < capWidth U := one_lt_M.trans_le hU.width_bounds.1
  have hlr : horizontalLeft U < horizontalRight U := by unfold capWidth at hwidth; linarith
  have hbox : U ⊆ Icc (horizontalLeft U - 1) (horizontalRight U + 1) ×ˢ Icc (0 : ℝ) 1 :=
    fun p hp => by
      have hx : p.1 ∈ Icc (horizontalLeft U) (horizontalRight U) := by
        rw [← hU.isCap.horizontalProjection_eq_Icc]
        exact ⟨p, hp, rfl⟩
      exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, hU.isCap.inStrip hp⟩
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, -, hHausdorff⟩ :=
    AngularGrid.exists_selected_sequence hU (by linarith) hbox
  replace hlevel := tendsto_atTop_mono hlevel tendsto_id
  replace hc := fun n => (hc n).le
  have hcap : ∀ n, IsDownwardCap (V n) := fun n => (hV n).isCap
  have hw := (hHausdorff.capWidth_tendsto hcap hU.isCap).div_const 4
  have hAu := hHausdorff.middleLeft_roof_tendsto hcap hU.isCap hlr
  have hAv := hHausdorff.middleRight_roof_tendsto hcap hU.isCap hlr
  have heL := AngularGrid.selected_left_height_tendsto_actual hU.isCap hbox hV hHausdorff
    hlevel hc hrate hwidth (by linarith)
  have heR := AngularGrid.selected_right_height_tendsto_actual hU.isCap hbox hV hHausdorff
    hlevel hc hrate hwidth (by linarith)
  exact le_of_tendsto_of_tendsto (((hw.pow 2).add ((hAu.sub heL).pow 2)).sqrt.add
      ((hw.pow 2).add ((heR.sub hAv).pow 2)).sqrt)
    (AngularGrid.finiteWingLength_tendsto_twice_score_of_canonical_maximum hU hheight haffine
      hbox hV hHausdorff hlevel hc hrate (by linarith) (by linarith))
    (Eventually.of_forall fun n => FinitePolygon.wing_chords_le_finiteWingLength (hcap n) _
      (AngularGrid.normal_unit _) (AngularGrid.normal_snd_pos _)
      (AngularGrid.wallSlopes_injective _) (hV n).polygon_eq)

/-- The stronger CG constraint follows from the actual survivor, actual
endpoint stationarity, and the proved wing chord comparison. -/
theorem IsFullCapMaximizer.ordinary_area_chord_necessary_of_canonical_range
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hleft : capRoof U (-C) = 1 - h) (hright : capRoof U C = 1)
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 37 / 50) (hh0 : 0 ≤ h) (hh1 : h ≤ 17 / 50)
    (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    Real.sqrt (C ^ 2 + (1 - h / 2 -
      (capRoof U (horizontalRight U) + capRoof U (horizontalLeft U)) / 2) ^ 2) +
      C * (3 - (capRoof U (horizontalRight U) + capRoof U (horizontalLeft U)) - 3 * h / 2) ≤
      (22199 : ℝ) / 10000 := by
  have hfit := hU.sweptNiche_le_roof_of_canonical_range
    hl hr hleft hright hC0 hC1 hh0 hh1 hheight haffine
  have hconv := hU.isCap.convexOn_sweptNiche_wings_of_roof_endpoints
    hl hr hleft hright hC0 hC1 hh1
  have harea := hU.isCap.volumeReal_oneTurnSurvivor_ge_score_of_affine (by linarith) hl hr
    hleft hright ((centered_quarter_points hl hr).2.2 ▸ haffine) hconv.1 hconv.2 hfit
  have hordinary := hU.isCap.volumeReal_oneTurnSurvivor_le hfit
  have hw : (horizontalRight U - horizontalLeft U) / 4 = C := by rw [hl, hr]; ring
  obtain ⟨hminus, hplus, -⟩ := centered_quarter_points hl hr
  have hsum := hU.endpoint_height_sum_of_affine hheight haffine
  rw [hminus, hplus, hleft, hright] at hsum
  have hchord := hU.wing_chords_le_twice_score_of_affine hheight haffine
  rw [hminus, hplus, hw, hleft, hright] at hchord
  have htriangle : 2 * Real.sqrt (C ^ 2 + (1 - h / 2 -
      (capRoof U (horizontalRight U) + capRoof U (horizontalLeft U)) / 2) ^ 2) ≤
      Real.sqrt (C ^ 2 + (1 - h - capRoof U (horizontalLeft U)) ^ 2) +
        Real.sqrt (C ^ 2 + (capRoof U (horizontalRight U) - 1) ^ 2) := by
    convert two_mul_sqrt_half_sum_le_chord_sum C (1 - h - capRoof U (horizontalLeft U))
      (1 - capRoof U (horizontalRight U)) using 3 <;> ring
  linarith [congrArg (C * ·) hsum]

end AmbidextrousSofa
