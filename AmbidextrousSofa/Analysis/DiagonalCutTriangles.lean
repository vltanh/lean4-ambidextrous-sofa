module

public import AmbidextrousSofa.Analysis.NearDiagonalGeometry
public import AmbidextrousSofa.Analysis.AsymmetricTent

@[expose] public section

/-!
# The actual exterior deficit pays for both near-diagonal cuts

Each support cut removes an ordinary triangle between a flat ceiling and
its diagonal continuation. The cuts are integrated in the actual charged
wings. A smaller complete cut rules out clipping at the outer endpoint
under the proved short-width deficit bound.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def affineCutTriangle (k δ p x : ℝ) : ℝ :=
  max (min (δ + k * (x - p)) (δ - (1 - k) * (x - p))) 0

theorem continuous_affineCutTriangle (k δ p : ℝ) : Continuous (affineCutTriangle k δ p) := by
  unfold affineCutTriangle
  fun_prop

theorem integral_affineCutTriangle_full {k δ p A B : ℝ}
    (hk : 0 < k) (hk1 : k < 1) (hδ : 0 ≤ δ)
    (hleft : δ ≤ k * (p - A)) (hright : δ ≤ (1 - k) * (B - p)) :
    (∫ x in A..B, affineCutTriangle k δ p x) = δ ^ 2 / (2 * k * (1 - k)) := by
  have hj : 0 < 1 - k := sub_pos.mpr hk1
  have hfun (x : ℝ) : affineCutTriangle k δ p x =
      max (min (k * (x - (p - δ / k))) ((1 - k) * ((p + δ / (1 - k)) - x))) 0 := by
    unfold affineCutTriangle
    congr 2 <;> field_simp <;> ring
  simp_rw [hfun]
  rw [integral_positive_asymmetric_tent_full hk hj
    (by linarith [(div_le_iff₀' hk).mpr hleft]) (by linarith [(div_le_iff₀' hj).mpr hright]),
    max_eq_left (by linarith [div_nonneg hδ hk.le, div_nonneg hδ hj.le])]
  field_simp
  ring

theorem affineCutTriangle_le_roof_gap {k δ p H x y : ℝ}
    (hbase : y ≤ min H (H + p - x))
    (hcut : y ≤ H + k * p - δ - k * x) :
    affineCutTriangle k δ p x ≤ min H (H + p - x) - y :=
  max_le ((min_le_min (by linarith : _ ≤ H - y) (by linarith : _ ≤ H + p - x - y)).trans_eq
    (min_sub_sub_right _ _ _)) (sub_nonneg.mpr hbase)

/-- Both literal roof gaps pay for any two weaker complete support
cuts. In particular, the zero cut on the opposite wing is allowed. -/
theorem IsDownwardCap.diagonalRoofDeficit_ge_near_cuts {U : Set Plane}
    (hU : IsDownwardCap U) {a h k u v δL δR : ℝ} (ha : 0 < a) (hh : 0 ≤ h)
    (hk : 0 < k) (hk1 : k < 1)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (hu : diagonalRight U = 1 + u) (hv : diagonalLeft U = 1 - h + v)
    (hδL0 : 0 ≤ δL) (hδR0 : 0 ≤ δR)
    (hδL : δL ≤ nearDiagonalLeftDeficit U h k v)
    (hδR : δR ≤ nearDiagonalRightDeficit U k u)
    (hLin : δL ≤ k * (v - a / 2)) (hLout : δL ≤ (1 - k) * (a - v))
    (hRin : δR ≤ k * (u - a / 2)) (hRout : δR ≤ (1 - k) * (a - u)) :
    (δL ^ 2 + δR ^ 2) / (2 * k * (1 - k)) ≤ diagonalRoofDeficit U a h u v := by
  have hproj : horizontalProjection U = Icc (-a) a := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
  have hL : δL ^ 2 / (2 * k * (1 - k)) ≤
      ∫ x in (-a)..(-a / 2), min (1 - h) (1 - h + v + x) - capRoof U x := by
    have hint : (∫ x in (-a)..(-a / 2), affineCutTriangle k δL v (-x)) =
        δL ^ 2 / (2 * k * (1 - k)) := by
      rw [intervalIntegral.integral_comp_neg]
      simpa only [neg_div, neg_neg] using integral_affineCutTriangle_full hk hk1 hδL0 hLin hLout
    rw [← hint]
    refine intervalIntegral.integral_mono_on (by linarith)
      (((continuous_affineCutTriangle k δL v).comp continuous_neg).intervalIntegrable _ _)
      ((Continuous.intervalIntegrable (by fun_prop) _ _).sub (hU.intervalIntegrable_capRoof _ _))
      fun x hx => ?_
    have hxU : x ∈ horizontalProjection U := hproj ▸ ⟨hx.1, by linarith [hx.2]⟩
    have h1 := hU.capRoof_le_nearDiagonalLeft h k v hxU
    have h2 := hU.capRoof_le_diagonalLeft hxU
    simpa only [sub_neg_eq_add, Function.comp_apply] using affineCutTriangle_le_roof_gap
      (k := k) (δ := δL) (p := v) (H := 1 - h) (x := -x)
      (le_min (hU.left_roof_le_middle_height ha hh hl hr hleft hright x hx) (by linarith))
      (by linarith)
  have hR : δR ^ 2 / (2 * k * (1 - k)) ≤
      ∫ x in (a / 2)..a, min 1 (1 + u - x) - capRoof U x := by
    rw [← integral_affineCutTriangle_full hk hk1 hδR0 hRin hRout]
    refine intervalIntegral.integral_mono_on (by linarith)
      ((continuous_affineCutTriangle k δR u).intervalIntegrable _ _)
      ((Continuous.intervalIntegrable (by fun_prop) _ _).sub (hU.intervalIntegrable_capRoof _ _))
      fun x hx => ?_
    have hxU : x ∈ horizontalProjection U := hproj ▸ ⟨by linarith [hx.1], hx.2⟩
    have h1 := hU.capRoof_le_nearDiagonalRight k u hxU
    have h2 := hU.capRoof_le_diagonalRight hxU
    exact affineCutTriangle_le_roof_gap
      (le_min (capRoof_le_one hU.isCompact hU.inStrip x) (by linarith)) (by linarith)
  exact (add_div _ _ _).trans_le (add_le_add hL hR)

theorem short_outer_cut_area_gt {k z : ℝ} (hk0 : 2 / 5 < k) (hk1 : k < 1)
    (hksq : k ^ 2 + 2 * k = 1) (hz : 23 / 200 < z) :
    (9 / 1000 : ℝ) < ((1 - k) * z) ^ 2 / (2 * k * (1 - k)) := by
  have hk : 0 < k := by linarith
  have hj : 0 < 1 - k := sub_pos.mpr hk1
  rw [show ((1 - k) * z) ^ 2 / (2 * k * (1 - k)) = (1 + k) / 2 * z ^ 2 by
    field_simp
    linear_combination -hksq]
  linarith [mul_nonneg (sub_nonneg.mpr hk0.le) (sq_nonneg z),
    pow_lt_pow_left₀ hz (by norm_num) two_ne_zero]

/-- The small actual exterior deficit rules out outer clipping on either
wing. The two complete literal triangles then add without overlap. -/
theorem IsDownwardCap.short_diagonal_cut_payment {U : Set Plane}
    (hU : IsDownwardCap U) {a h k u v : ℝ} (ha : 0 < a) (hh : 0 ≤ h)
    (hk0 : 2 / 5 < k) (hk1 : k < 1) (hksq : k ^ 2 + 2 * k = 1)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (hu : diagonalRight U = 1 + u) (hv : diagonalLeft U = 1 - h + v)
    (hL : nearDiagonalLeftDeficit U h k v ∈ Icc 0 (k * (v - a / 2)))
    (hR : nearDiagonalRightDeficit U k u ∈ Icc 0 (k * (u - a / 2)))
    (hvu : 23 / 200 < a - v) (huu : 23 / 200 < a - u)
    (hD : diagonalRoofDeficit U a h u v < 9 / 1000) :
    nearDiagonalLeftDeficit U h k v ≤ (1 - k) * (a - v) ∧
      nearDiagonalRightDeficit U k u ≤ (1 - k) * (a - u) ∧
      (nearDiagonalLeftDeficit U h k v ^ 2 + nearDiagonalRightDeficit U k u ^ 2) /
        (2 * k * (1 - k)) ≤ diagonalRoofDeficit U a h u v := by
  have hk : 0 < k := by linarith
  have hL0 : 0 ≤ (1 - k) * (a - v) := mul_nonneg (by linarith) (by linarith)
  have hR0 : 0 ≤ (1 - k) * (a - u) := mul_nonneg (by linarith) (by linarith)
  have hLout : nearDiagonalLeftDeficit U h k v ≤ (1 - k) * (a - v) := by
    by_contra! hbad
    have hcut := hU.diagonalRoofDeficit_ge_near_cuts ha hh hk hk1 hl hr hleft hright hu hv
      hL0 le_rfl hbad.le hR.1 (hbad.le.trans hL.2) le_rfl (hR.1.trans hR.2) hR0
    rw [zero_pow two_ne_zero, add_zero] at hcut
    linarith [short_outer_cut_area_gt hk0 hk1 hksq hvu]
  have hRout : nearDiagonalRightDeficit U k u ≤ (1 - k) * (a - u) := by
    by_contra! hbad
    have hcut := hU.diagonalRoofDeficit_ge_near_cuts ha hh hk hk1 hl hr hleft hright hu hv
      le_rfl hR0 hL.1 hbad.le (hL.1.trans hL.2) hL0 (hbad.le.trans hR.2) le_rfl
    rw [zero_pow two_ne_zero, zero_add] at hcut
    linarith [short_outer_cut_area_gt hk0 hk1 hksq huu]
  exact ⟨hLout, hRout, hU.diagonalRoofDeficit_ge_near_cuts ha hh hk hk1 hl hr hleft hright
    hu hv hL.1 hR.1 le_rfl le_rfl hL.2 hLout hR.2 hRout⟩

end AmbidextrousSofa
