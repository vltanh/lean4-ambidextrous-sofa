module

public import AmbidextrousSofa.Analysis.FullTriangleParameters
public import AmbidextrousSofa.Analysis.ThreeAngleNiche

@[expose] public section

/-!
# Actual exterior and niche area payments for three full triangles

The exterior payment uses only the inner half of each support cut. The
niche payment integrates the two complete signed triangles of the
three-angle barrier on opposite sides of the diagonal apex and subtracts
their entire floor correction. All supports and all integrals belong to
the original cap. What remains of the three-angle score is the
full-triangle relaxation and the two floor losses, bounded by the depths
of the two endpoints.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsDownwardCap.diagonalRoofDeficit_ge_inner_cuts {U : Set Plane}
    (hU : IsDownwardCap U) {a h k u v : ℝ} (ha : 0 < a) (hh : 0 ≤ h) (hk : 0 < k)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (hu : diagonalRight U = 1 + u) (hv : diagonalLeft U = 1 - h + v)
    (huv : u ∈ Icc (a / 2) a) (hvv : v ∈ Icc (a / 2) a)
    (hδR : nearDiagonalRightDeficit U k u ∈ Icc 0 (k * (u - a / 2)))
    (hδL : nearDiagonalLeftDeficit U h k v ∈ Icc 0 (k * (v - a / 2))) :
    (nearDiagonalRightDeficit U k u ^ 2 + nearDiagonalLeftDeficit U h k v ^ 2) / (2 * k) ≤
      diagonalRoofDeficit U a h u v := by
  have hx (x : ℝ) (h1 : -a ≤ x) (h2 : x ≤ a) : x ∈ horizontalProjection U :=
    (hl ▸ hr ▸ hU.horizontalProjection_eq_Icc) ▸ ⟨h1, h2⟩
  have hfitL := (div_le_iff₀' hk).mpr hδL.2
  have hR := hU.right_roof_gap_ge_cut ha hk hl hr hu huv hδR
  have hL := integral_gap_ge_right_ramp
    (f := fun x => min (1 - h) (1 - h + v + x) - capRoof U x)
    (fun l r => (Continuous.intervalIntegrable (by fun_prop) l r).sub
      (hU.intervalIntegrable_capRoof l r)) hk hδL.1
    (show -v ∈ Icc (-a) (-a / 2) from ⟨by linarith only [hvv.2], by linarith only [hvv.1]⟩)
    (by linarith only [hδL.2])
    (fun x hx' => sub_nonneg.mpr (le_min
      (hU.left_roof_le_middle_height ha hh hl hr hleft hright x hx')
      (by linarith only [hv, hU.capRoof_le_diagonalLeft (hx x hx'.1 (by linarith only [hx'.2,
        ha]))])))
    fun x hx' => by
      have := hU.capRoof_le_nearDiagonalLeft h k v
        (hx x (by linarith only [hx'.1, hvv.2]) (by linarith only [hx'.2, hfitL, ha]))
      rw [min_eq_left (by linarith only [hx'.1])]
      linarith only [this]
  rw [diagonalRoofDeficit, add_div]
  linarith only [hR, hL]

/-- The three-angle score of a canonical cap is at most the full-triangle relaxation plus the
floor losses of the two niche triangles. The losses are bounded by the depths `1 - capRoof U a`
and `1 - capRoof U (-a)` of the two endpoints. -/
theorem IsDownwardCap.threeAngleScore_le_full_triangles {U : Set Plane} (hU : IsDownwardCap U)
    {a h : ℝ} (hah : 3 / 4 ≤ a - 1 / 2 - h / 4) (ha1 : a ≤ 8 / 5) (hh0 : 0 ≤ h)
    (hh1 : h ≤ 1 / 3) (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hEP : 1 - h / 2 ≤ capRoof U a + capRoof U (-a)) :
    let k := Real.sqrt 2 - 1
    let u := diagonalRight U - 1
    let v := diagonalLeft U - 1 + h
    let t := 2 * fullTriangleCos k - (1 + k)
    0 ≤ (u + v - h) / 2 - k ∧
      intervalSpatialScore (capRoof U) (threeAngleBarrier U) (horizontalLeft U)
          (horizontalRight U) ≤ fullTriangleRelaxation a h k (fullTriangleCos k) u v +
        (1 - k) / 2 * ((max (1 - capRoof U a - t) 0) ^ 2 + (max (1 - capRoof U (-a) - t) 0) ^ 2) := by
  intro k u v t
  obtain ⟨hk0, hk1, hksq, hc0, hc1⟩ := fullTriangle_offset_bounds
  dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  have ha : 5 / 4 ≤ a := by linarith only [hah, hh0]
  have hk : 0 < k := by linarith only [hk0]
  have hu : diagonalRight U = 1 + u := by ring
  have hv : diagonalLeft U = 1 - h + v := by ring
  have huv : u ∈ Icc (a / 2) a ∧ v ∈ Icc (a / 2) a :=
    hU.tilted_diagonal_parameters_mem (by linarith only [ha]) hh0 (by linarith only [ha, hh1]) hl
      hr hleft hright
  have hproj := (hl ▸ hr ▸ hU.horizontalProjection_eq_Icc).superset
  have heR : capRoof U a ≤ 1 - (a - u) := by
    linarith only [hU.capRoof_le_diagonalRight (hproj ⟨by linarith only [ha], le_rfl⟩), hu]
  have heL : capRoof U (-a) ≤ 1 - (a - (v - h)) := by
    linarith only [hU.capRoof_le_diagonalLeft (hproj ⟨le_rfl, by linarith only [ha]⟩), hv]
  have hm0 : 3 / 4 ≤ (u + v - h) / 2 := by linarith only [hEP, heR, heL, hah]
  have hδR := hU.nearDiagonalRightDeficit_mem (by linarith only [ha]) hk.le (by linarith only [hk1])
    hl hr hright hu
  have hδL := hU.nearDiagonalLeftDeficit_mem (by linarith only [ha]) hh0 hk.le
    (by linarith only [hk1]) (by linarith only [mul_le_mul_of_nonneg_left ha hk.le, hk0, hh1])
    hl hr hleft hright haffine hv huv.2.1
  have hbR : wideNearRightIntercept U k =
      1 - nearDiagonalNorm k + k * v - h - nearDiagonalLeftDeficit U h k v := by
    rw [wideNearRightIntercept, nearDiagonalLeftDeficit]
    ring
  have hbL := wideNearLeftIntercept_eq U k u
  have hN := (wide_norm_rational_bounds hk0 hk1).1
  have hcR := wide_crossing_after_apex (u := u) (w := v - h) (b := wideNearRightIntercept U k) hk
    hk1 hN hh0 (by linarith only [hm0]) (by linarith only [hbR, hδL.1])
  have hcL := wide_crossing_after_apex (u := v - h) (w := u) (h := 0)
    (b := wideNearLeftIntercept U k) hk hk1 hN le_rfl (by linarith only [hm0])
    (by linarith only [hbL, hδR.1])
  have hcos : 1 + a - 2 * fullTriangleCos k ≤ a / 2 := by linarith only [ha1, hc0]
  have hd := tilted_diagonal_apex_mem (by linarith only [ha]) hh0 (by linarith only [ha, hh1])
    huv.1 huv.2
  have hN := hU.threeAngle_integral_ge_full_triangles hk hksq rfl hl hr hu
    (show diagonalLeft U = 1 + (v - h) by linarith only [hv])
    (by convert hd using 1; ring) (by linarith only [hcR]) (by linarith only [hcL])
    ((fullTriangle_outer_zero_le hk hksq heR).trans hcos)
    ((fullTriangle_outer_zero_le hk hksq heL).trans hcos)
  rw [show u + (v - h) = u + v - h by ring, fullTriangleNicheGain] at hN
  -- The floor losses are bounded by the endpoint depths.
  have hloss : fullTriangleNicheFloorLoss U a k u (v - h) ≤ (1 - k) / 2 *
      ((max (1 - capRoof U a - t) 0) ^ 2 + (max (1 - capRoof U (-a) - t) 0) ^ 2) := by
    rw [fullTriangleNicheFloorLoss, fullTriangleFloorCoefficient_eq hk hksq]
    exact mul_le_mul_of_nonneg_left (add_le_add
      (pow_le_pow_left₀ (le_max_right _ _) ((fullTriangle_floor_loss_le_endpoint hk hksq heR).trans
        (max_le_max (by linarith only [heR]) le_rfl)) 2)
      (pow_le_pow_left₀ (le_max_right _ _) ((fullTriangle_floor_loss_le_endpoint hk hksq heL).trans
        (max_le_max (by linarith only [heL]) le_rfl)) 2)) (by linarith only [hk1])
  have hcut := hU.diagonalRoofDeficit_ge_inner_cuts (by linarith only [ha]) hh0 hk hl hr hleft
    hright hu hv huv.1 huv.2 hδR hδL
  have hpay := fullTriangle_square_payment hk hδR.1 hδL.1
    (fullTriangle_gain_sum (a := a) hk hksq hbR hbL hEP)
  refine ⟨by linarith only [hm0, hk1], ?_⟩
  rw [hl, hr, intervalSpatialScore_centered, fullTriangleRelaxation, diagonalRelaxation]
  linarith only [hU.diagonalRoofDeficit_eq h huv.1 huv.2, hN, hpay, hcut, hloss]

end AmbidextrousSofa
