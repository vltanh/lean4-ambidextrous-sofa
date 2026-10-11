module

public import AmbidextrousSofa.Analysis.CanonicalWingChord

@[expose] public section

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
  rw [finiteGraphLength, finiteGraphLength, finiteGraphLength,
    ← e.integral_sourceDensity_eq_sum a b _ hlx, ← e.integral_sourceDensity_eq_sum a b _ hxr,
    ← e.integral_sourceDensity_eq_sum a b _ (hlx.trans hxr)]
  exact intervalIntegral.integral_add_adjacent_intervals
    (e.intervalIntegrable_sourceDensity a b _ l x) (e.intervalIntegrable_sourceDensity a b _ x r)

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
  have hroof := eqOn_roofEnvelope_of_circumscription hU normal hpositive hpoly
  rw [finiteWingLength_eq_graphLengths U normal hunit hpositive,
    ← (roofExpr (ι := ι)).finiteGraphLength_add _ _ hx.1 hx.2]
  set l := horizontalLeft U
  set r := horizontalRight U
  have key {p q : ℝ} (hp : p ∈ Icc l r) (hq : q ∈ Icc l r) (hpq : p ≤ q) :
      √((q - p) ^ 2 + (capRoof U q - capRoof U p) ^ 2) ≤
        (roofExpr (ι := ι)).finiteGraphLength (wallSlope normal)
          (roofIntercept normal (fun i => support U (normal i))) p q := by
    rw [← hroof hp, ← hroof hq]
    exact (roofExpr (ι := ι)).chord_le_finiteGraphLength _ _ hslope hpq
  have hv : r - (r - l) / 4 ∈ Icc l r := ⟨by linarith, by linarith⟩
  have hx' : x ∈ Icc l r := ⟨hv.1.trans hx.1, hx.2⟩
  refine add_le_add ?_ (add_le_add (key hv hx' hx.1) (key hx' ⟨hlr, le_rfl⟩ hx.2))
  convert key ⟨le_rfl, hlr⟩ (⟨by linarith, by linarith⟩ : l + (r - l) / 4 ∈ Icc l r)
    (by linarith) using 3
  ring

end FinitePolygon

open AngularGrid in
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
  have hbox : U ⊆ Icc (horizontalLeft U - 1) (horizontalRight U + 1) ×ˢ Icc (0 : ℝ) 1 :=
    fun p hp => ⟨⟨by linarith [(hU.isCap.fst_mem_Icc hp).1],
      by linarith [(hU.isCap.fst_mem_Icc hp).2]⟩, hU.isCap.inStrip hp⟩
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, -, hHausdorff⟩ :=
    exists_selected_sequence hU (by linarith) hbox
  have hcap (n : ℕ) : IsDownwardCap (V n) := (hV n).isCap
  have hlevel' := tendsto_atTop_mono hlevel tendsto_id
  have hc' (n : ℕ) := (hc n).le
  have hwidth : 1 < capWidth U := one_lt_M.trans_le hU.width_bounds.1
  have hlr : horizontalLeft U < horizontalRight U := by linarith
  -- Split the right charged window of `V n` at `x n`, which tends to `C + T`.
  let q : ℕ → ℝ := fun n => (horizontalRight (V n) - horizontalLeft (V n)) / 4
  let x : ℕ → ℝ := fun n => horizontalRight (V n) - q n + (T / C) * q n
  have hxmem (n : ℕ) : x n ∈ Icc (horizontalRight (V n) - q n) (horizontalRight (V n)) := by
    have hq0 : 0 ≤ q n := div_nonneg (sub_nonneg.2
      (horizontalLeft_le_horizontalRight (hcap n).nonempty (hcap n).isCompact)) zero_le_four
    dsimp only [x]
    exact ⟨by linarith [mul_nonneg (div_nonneg hT0 hC.le) hq0],
      by linarith [mul_le_of_le_one_left hq0 ((div_le_one hC).2 hTC.le)]⟩
  have hxproj (n : ℕ) : x n ∈ horizontalProjection (V n) := by
    rw [horizontalProjection_eq_Icc (hcap n).nonempty (hcap n).isCompact (hcap n).convex]
    have h := hxmem n
    have := horizontalLeft_le_horizontalRight (hcap n).nonempty (hcap n).isCompact
    dsimp only [q] at h
    exact ⟨by linarith [h.1], h.2⟩
  have hq : Tendsto q atTop (𝓝 C) := by
    have := (hHausdorff.capWidth_tendsto hcap hU.isCap).div_const 4
    rwa [show capWidth U / 4 = C by rw [capWidth, hl, hr]; ring] at this
  have hR := hHausdorff.horizontalRight_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hU.isCap.isCompact hU.isCap.nonempty
  have hxlim : Tendsto x atTop (𝓝 (C + T)) := by
    have := (hR.sub hq).add (hq.const_mul (T / C))
    rwa [hr, div_mul_cancel₀ _ hC.ne', show 2 * C - C + T = C + T by ring] at this
  have hroofX := hHausdorff.capRoof_tendsto_of_interior hcap hU.isCap
    (show C + T ∈ Ioo (horizontalLeft U) (horizontalRight U) by
      rw [hl, hr]; constructor <;> linarith) hxproj hxlim
  have hAu := hHausdorff.middleLeft_roof_tendsto hcap hU.isCap hlr
  have hAv := hHausdorff.middleRight_roof_tendsto hcap hU.isCap hlr
  rw [htop] at hroofX
  rw [show horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 = -C by
    rw [hl, hr]; ring, hleftRoof] at hAu
  rw [show horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 = C by
    rw [hl, hr]; ring, hrightRoof] at hAv
  have heL := selected_left_height_tendsto_actual hU.isCap hbox hV hHausdorff
    hlevel' hc' hrate hwidth (by linarith)
  have heR := selected_right_height_tendsto_actual hU.isCap hbox hV hHausdorff
    hlevel' hc' hrate hwidth (by linarith)
  have hle := le_of_tendsto_of_tendsto ((((hq.pow 2).add ((hAu.sub heL).pow 2)).sqrt).add
    ((((hxlim.sub (hR.sub hq)).pow 2).add ((hroofX.sub hAv).pow 2)).sqrt.add
      ((((hR.sub hxlim).pow 2).add ((heR.sub hroofX).pow 2)).sqrt)))
    (finiteWingLength_tendsto_twice_score_of_canonical_maximum hU hheight haffine
      hbox hV hHausdorff hlevel' hc' hrate (by linarith) (by linarith))
    (Eventually.of_forall fun n => FinitePolygon.right_split_chords_le_finiteWingLength
      (hcap n) (normal (dyadic (level n))) (normal_unit (dyadic (level n)))
      (normal_snd_pos (dyadic (level n))) (wallSlopes_injective (dyadic (level n)))
      (hV n).polygon_eq (hxmem n))
  rw [show C + T - (horizontalRight U - C) = T by rw [hr]; ring,
    show horizontalRight U - (C + T) = C - T by rw [hr]; ring,
    sub_self, zero_pow two_ne_zero, add_zero, Real.sqrt_sq hT0,
    show (capRoof U (horizontalRight U) - 1) ^ 2 = (1 - capRoof U (horizontalRight U)) ^ 2 by
      ring] at hle
  linarith

end AmbidextrousSofa
