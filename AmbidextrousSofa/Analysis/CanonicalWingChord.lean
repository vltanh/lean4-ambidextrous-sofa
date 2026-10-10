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

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace AngularGrid

theorem wing_chords_le_twice_score_of_selected_sequence
    {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval
      (horizontalLeft target) (horizontalRight target), capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b) :
    Real.sqrt (((horizontalRight target - horizontalLeft target) / 4) ^ 2 +
      (capRoof target (horizontalLeft target +
          (horizontalRight target - horizontalLeft target) / 4) -
        capRoof target (horizontalLeft target)) ^ 2) +
    Real.sqrt (((horizontalRight target - horizontalLeft target) / 4) ^ 2 +
      (capRoof target (horizontalRight target) -
        capRoof target (horizontalRight target -
          (horizontalRight target - horizontalLeft target) / 4)) ^ 2) ≤
      2 * capScore target (Real.pi / 2) := by
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hwidth : 1 < capWidth target := one_lt_M.trans_le hTarget.width_bounds.1
  have hlr : horizontalLeft target < horizontalRight target := by
    unfold capWidth at hwidth
    linarith
  have hw := (hHausdorff.capWidth_tendsto hcap hTarget.isCap).div_const 4
  have hAu := hHausdorff.middleLeft_roof_tendsto hcap hTarget.isCap hlr
  have hAv := hHausdorff.middleRight_roof_tendsto hcap hTarget.isCap hlr
  have heL := selected_left_height_tendsto_actual hTarget.isCap hTargetBox hU hHausdorff
    hlevel hc hrate hwidth hleft
  have heR := selected_right_height_tendsto_actual hTarget.isCap hTargetBox hU hHausdorff
    hlevel hc hrate hwidth hright
  have hchord := ((hw.pow 2).add ((hAu.sub heL).pow 2)).sqrt.add
    (((hw.pow 2).add ((heR.sub hAv).pow 2)).sqrt)
  have hlength := finiteWingLength_tendsto_twice_score_of_canonical_maximum
    hTarget hheight haffine hTargetBox hU hHausdorff hlevel hc hrate hleft hright
  exact le_of_tendsto_of_tendsto hchord hlength
    (Eventually.of_forall (fun n => FinitePolygon.wing_chords_le_finiteWingLength
      (hcap n) (normal (dyadic (level n))) (normal_unit (dyadic (level n)))
      (normal_snd_pos (dyadic (level n))) (wallSlopes_injective (dyadic (level n)))
      (hU n).polygon_eq))

end AngularGrid

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
  exact AngularGrid.wing_chords_le_twice_score_of_selected_sequence hU hheight haffine hbox
    hV hHausdorff (tendsto_atTop_mono hlevel tendsto_id) (fun n => (hc n).le) hrate
    (by dsimp [a]; linarith) (by dsimp [b]; linarith)

theorem IsFullCapMaximizer.sqrt_chord_le_score_of_canonical
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hleft : capRoof U (-C) = 1 - h) (hright : capRoof U C = 1)
    (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    Real.sqrt (C ^ 2 + (1 - h / 2 -
      (capRoof U (horizontalRight U) + capRoof U (horizontalLeft U)) / 2) ^ 2) ≤
      capScore U (Real.pi / 2) := by
  have hwidth : (horizontalRight U - horizontalLeft U) / 4 = C := by rw [hl, hr]; ring
  have hminus : horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 = -C := by
    rw [hl, hr]; ring
  have hplus : horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 = C := by
    rw [hl, hr]; ring
  have hchord := hU.wing_chords_le_twice_score_of_affine hheight haffine
  rw [hminus, hplus, hwidth, hleft, hright] at hchord
  have htriangle := two_mul_sqrt_half_sum_le_chord_sum C
    (1 - h - capRoof U (horizontalLeft U)) (1 - capRoof U (horizontalRight U))
  have hsquare : (1 - capRoof U (horizontalRight U)) ^ 2 =
      (capRoof U (horizontalRight U) - 1) ^ 2 := by ring
  have hmid : ((1 - h - capRoof U (horizontalLeft U)) +
      (1 - capRoof U (horizontalRight U))) / 2 =
      1 - h / 2 - (capRoof U (horizontalRight U) + capRoof U (horizontalLeft U)) / 2 := by ring
  rw [hsquare, hmid] at htriangle
  linarith

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
  have haffine' : ∃ m c : ℝ, ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c := by
    simpa only [middleHalfInterval_eq_centered hl hr] using haffine
  have harea := hU.isCap.volumeReal_oneTurnSurvivor_ge_score_of_affine
    (by linarith) hl hr hleft hright haffine' hconv.1 hconv.2 hfit
  have hordinary := hU.isCap.volumeReal_oneTurnSurvivor_le hfit
  have hminus : horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 = -C := by
    rw [hl, hr]; ring
  have hplus : horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 = C := by
    rw [hl, hr]; ring
  have hsum := hU.endpoint_height_sum_of_affine hheight haffine
  rw [hminus, hplus, hleft, hright] at hsum
  have hsumC := congrArg (fun t : ℝ => C * t) hsum
  have hchord := hU.sqrt_chord_le_score_of_canonical hl hr hleft hright hheight haffine
  nlinarith

end AmbidextrousSofa
