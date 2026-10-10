import AmbidextrousSofa.Analysis.CanonicalWingChord

/-!
# The actual top segment and the two remaining wing chords

Split the selected polygon's right graph at a moving abscissa converging
to an actual height-one point. Three finite chord inequalities pass to
the exact Green length limit. This retains the top segment's full
horizontal length without assuming convergence of polygon top faces or
identifying limiting graph length with a weak measure.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace WallExpr

theorem finiteGraphLength_add {ι : Type*} [Fintype ι] (e : WallExpr ι)
    (a b : ι → ℝ) {l x r : ℝ} (hlx : l ≤ x) (hxr : x ≤ r) :
    e.finiteGraphLength a b l x + e.finiteGraphLength a b x r =
      e.finiteGraphLength a b l r := by
  let w : ι → ℝ := fun i => Real.sqrt (1 + a i ^ 2)
  change (∑ i, e.sourceMass a b l x i * w i) +
    (∑ i, e.sourceMass a b x r i * w i) = ∑ i, e.sourceMass a b l r i * w i
  rw [← e.integral_sourceDensity_eq_sum a b w hlx,
    ← e.integral_sourceDensity_eq_sum a b w hxr,
    ← e.integral_sourceDensity_eq_sum a b w (hlx.trans hxr)]
  exact intervalIntegral.integral_add_adjacent_intervals
    (e.intervalIntegrable_sourceDensity a b w l x) (e.intervalIntegrable_sourceDensity a b w x r)

end WallExpr

namespace FinitePolygon

theorem right_split_chords_le_finiteWingLength {ι : Type*} [Fintype ι] {U : Set Plane}
    (hU : IsDownwardCap U) (normal : ι → Plane)
    (hunit : ∀ i, coordDot (normal i) (normal i) = 1)
    (hpositive : ∀ i, 0 < (normal i).2)
    (hslope : Function.Injective (wallSlope normal)) (hpoly : U = circumscription U normal)
    {x : ℝ} (hx : x ∈ Icc
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) (horizontalRight U)) :
    Real.sqrt (((horizontalRight U - horizontalLeft U) / 4) ^ 2 +
      (capRoof U (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) -
        capRoof U (horizontalLeft U)) ^ 2) +
      (Real.sqrt ((x - (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)) ^ 2 +
          (capRoof U x - capRoof U
            (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)) ^ 2) +
        Real.sqrt ((horizontalRight U - x) ^ 2 + (capRoof U (horizontalRight U) - capRoof U x) ^ 2)) ≤
      finiteWingLength U normal := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  let l := horizontalLeft U
  let r := horizontalRight U
  let u := l + (r - l) / 4
  let v := r - (r - l) / 4
  have hlu : l ≤ u := by dsimp [u]; linarith only [hlr]
  have hvr : v ≤ r := by dsimp [v]; linarith only [hlr]
  have hu : u ∈ Icc l r := ⟨hlu, by dsimp [u]; linarith only [hlr]⟩
  have hv : v ∈ Icc l r := ⟨by dsimp [v]; linarith only [hlr], hvr⟩
  have hx' : x ∈ Icc l r := ⟨hv.1.trans hx.1, hx.2⟩
  have hroof := eqOn_roofEnvelope_of_circumscription hU normal hpositive hpoly
  have hgraph (y : ℝ) (hy : y ∈ Icc l r) :
      (roofExpr (ι := ι)).affineGraph (wallSlope normal)
        (roofIntercept normal (fun i => support U (normal i))) y = capRoof U y := hroof hy
  have hleft := (roofExpr (ι := ι)).chord_le_finiteGraphLength (wallSlope normal)
    (roofIntercept normal (fun i => support U (normal i))) hslope hlu
  have hmiddle := (roofExpr (ι := ι)).chord_le_finiteGraphLength (wallSlope normal)
    (roofIntercept normal (fun i => support U (normal i))) hslope hx.1
  have hright := (roofExpr (ι := ι)).chord_le_finiteGraphLength (wallSlope normal)
    (roofIntercept normal (fun i => support U (normal i))) hslope hx.2
  rw [hgraph u hu, hgraph l ⟨le_rfl, hlr⟩,
    show u - l = (r - l) / 4 by dsimp [u]; ring] at hleft
  rw [hgraph x hx', hgraph v hv] at hmiddle
  rw [hgraph r ⟨hlr, le_rfl⟩, hgraph x hx'] at hright
  have hsplit := (roofExpr (ι := ι)).finiteGraphLength_add (wallSlope normal)
    (roofIntercept normal (fun i => support U (normal i))) hx.1 hx.2
  have hsum := add_le_add hleft (add_le_add hmiddle hright)
  rw [hsplit, ← finiteWingLength_eq_graphLengths U normal hunit hpositive] at hsum
  exact hsum

end FinitePolygon

namespace AngularGrid

theorem split_wing_chords_le_twice_score_of_selected_sequence
    {target : Set Plane} {U : ℕ → Set Plane} {a b C T h : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval
      (horizontalLeft target) (horizontalRight target), capRoof target x = m * x + c)
    (hl : horizontalLeft target = -2 * C) (hr : horizontalRight target = 2 * C)
    (hC : 0 < C) (hT0 : 0 ≤ T) (hTC : T < C)
    (hleftRoof : capRoof target (-C) = 1 - h)
    (hrightRoof : capRoof target C = 1) (htop : capRoof target (C + T) = 1)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b) :
    T + Real.sqrt ((C - T) ^ 2 + (1 - capRoof target (horizontalRight target)) ^ 2) +
      Real.sqrt (C ^ 2 + (1 - h - capRoof target (horizontalLeft target)) ^ 2) ≤
        2 * capScore target (Real.pi / 2) := by
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hwidth : 1 < capWidth target := one_lt_M.trans_le hTarget.width_bounds.1
  have hlr : horizontalLeft target < horizontalRight target := by rw [hl, hr]; linarith only [hC]
  have hquarter : capWidth target / 4 = C := by unfold capWidth; rw [hl, hr]; ring
  have hmiddleL : horizontalLeft target + (horizontalRight target - horizontalLeft target) / 4 = -C := by
    rw [hl, hr]; ring
  have hmiddleR : horizontalRight target - (horizontalRight target - horizontalLeft target) / 4 = C := by
    rw [hl, hr]; ring
  let q : ℕ → ℝ := fun n => (horizontalRight (U n) - horizontalLeft (U n)) / 4
  let x : ℕ → ℝ := fun n => horizontalRight (U n) - q n + (T / C) * q n
  have hλ0 : 0 ≤ T / C := div_nonneg hT0 hC.le
  have hλ1 : T / C ≤ 1 := (div_le_iff₀ hC).mpr (by linarith only [hTC])
  have hxmem (n : ℕ) : x n ∈ Icc (horizontalRight (U n) - q n) (horizontalRight (U n)) := by
    have hq0 : 0 ≤ q n := div_nonneg (sub_nonneg.mpr
      (horizontalLeft_le_horizontalRight (hcap n).nonempty (hcap n).isCompact)) (by norm_num)
    have hprod := mul_nonneg hλ0 hq0
    have hle := mul_le_mul_of_nonneg_right hλ1 hq0
    dsimp only [x]
    constructor <;> linarith only [hprod, hle]
  have hxproj (n : ℕ) : x n ∈ horizontalProjection (U n) := by
    rw [horizontalProjection_eq_Icc (hcap n).nonempty (hcap n).isCompact (hcap n).convex]
    have horder := horizontalLeft_le_horizontalRight (hcap n).nonempty (hcap n).isCompact
    have hx := hxmem n
    dsimp only [q] at hx
    exact ⟨by linarith only [hx.1, horder], hx.2⟩
  have hq := (hHausdorff.capWidth_tendsto hcap hTarget.isCap).div_const 4
  rw [hquarter] at hq
  change Tendsto q atTop (𝓝 C) at hq
  have hR := hHausdorff.horizontalRight_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hTarget.isCap.isCompact hTarget.isCap.nonempty
  have hxlim : Tendsto x atTop (𝓝 (C + T)) := by
    have hlim := (hR.sub hq).add (hq.const_mul (T / C))
    rw [hr, div_mul_cancel₀ _ hC.ne'] at hlim
    simpa only [x, show 2 * C - C + T = C + T by ring] using hlim
  have hroofX := hHausdorff.capRoof_tendsto_of_interior hcap hTarget.isCap
    (show C + T ∈ Ioo (horizontalLeft target) (horizontalRight target) by
      rw [hl, hr]
      constructor <;> linarith only [hC, hT0, hTC]) hxproj hxlim
  rw [htop] at hroofX
  have hAu := hHausdorff.middleLeft_roof_tendsto hcap hTarget.isCap hlr
  have hAv := hHausdorff.middleRight_roof_tendsto hcap hTarget.isCap hlr
  rw [hmiddleL, hleftRoof] at hAu
  rw [hmiddleR, hrightRoof] at hAv
  have heL := selected_left_height_tendsto_actual hTarget.isCap hTargetBox hU hHausdorff
    hlevel hc hrate hwidth hleft
  have heR := selected_right_height_tendsto_actual hTarget.isCap hTargetBox hU hHausdorff
    hlevel hc hrate hwidth hright
  have hchord := (((hq.pow 2).add ((hAu.sub heL).pow 2)).sqrt).add
    ((((hxlim.sub (hR.sub hq)).pow 2).add ((hroofX.sub hAv).pow 2)).sqrt.add
      ((((hR.sub hxlim).pow 2).add ((heR.sub hroofX).pow 2)).sqrt))
  have hlength := finiteWingLength_tendsto_twice_score_of_canonical_maximum
    hTarget hheight haffine hTargetBox hU hHausdorff hlevel hc hrate hleft hright
  have hle := le_of_tendsto_of_tendsto hchord hlength
    (Eventually.of_forall (fun n => FinitePolygon.right_split_chords_le_finiteWingLength
      (hcap n) (normal (dyadic (level n))) (normal_unit (dyadic (level n)))
      (normal_snd_pos (dyadic (level n))) (wallSlopes_injective (dyadic (level n)))
      (hU n).polygon_eq (hxmem n)))
  rw [show C + T - (horizontalRight target - C) = T by rw [hr]; ring,
    show horizontalRight target - (C + T) = C - T by rw [hr]; ring,
    sub_self, zero_pow (by norm_num), add_zero,
    Real.sqrt_sq hT0,
    show (capRoof target (horizontalRight target) - 1) ^ 2 =
      (1 - capRoof target (horizontalRight target)) ^ 2 by ring] at hle
  linarith only [hle]

end AngularGrid

/-- The actual prescribed maximum constructs its own approximating
polygons. The splitting point is any actual height-one point on the
right wing, including the left endpoint of a nontrivial top segment. -/
theorem IsFullCapMaximizer.split_wing_chords_le_twice_score
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C T h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 0 < C) (hT0 : 0 ≤ T) (hTC : T < C)
    (hleftRoof : capRoof U (-C) = 1 - h) (hrightRoof : capRoof U C = 1)
    (htop : capRoof U (C + T) = 1) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    T + Real.sqrt ((C - T) ^ 2 + (1 - capRoof U (horizontalRight U)) ^ 2) +
      Real.sqrt (C ^ 2 + (1 - h - capRoof U (horizontalLeft U)) ^ 2) ≤
        2 * capScore U (Real.pi / 2) := by
  let a := horizontalLeft U - 1
  let b := horizontalRight U + 1
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hab : a ≤ b := by dsimp [a, b]; linarith only [hlr]
  have hbox : U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 := by
    intro p hp
    have hx := hU.isCap.fst_mem_Icc hp
    refine ⟨⟨?_, ?_⟩, hU.isCap.inStrip hp⟩
    · dsimp [a]; linarith only [hx.1]
    · dsimp [b]; linarith only [hx.2]
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, _, hHausdorff⟩ :=
    AngularGrid.exists_selected_sequence hU hab hbox
  exact AngularGrid.split_wing_chords_le_twice_score_of_selected_sequence
    hU hheight haffine hl hr hC hT0 hTC hleftRoof hrightRoof htop hbox hV hHausdorff
    (tendsto_atTop_mono hlevel tendsto_id) (fun n => (hc n).le) hrate
    (by dsimp [a]; linarith) (by dsimp [b]; linarith)

end AmbidextrousSofa
