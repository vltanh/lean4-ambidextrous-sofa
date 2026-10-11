module

public import AmbidextrousSofa.Analysis.FullTriangleParameters
public import AmbidextrousSofa.Analysis.NicheBoxBounds

@[expose] public section

/-!
# Actual exterior and niche area payments for three full triangles

The exterior payment uses only the inner half of each support cut. The
niche payment integrates the two complete signed triangles on opposite
sides of the diagonal apex and subtracts their entire floor correction.
All supports and all integrals belong to the original cap.
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
  have hx (x : ℝ) (h1 : -a ≤ x) (h2 : x ≤ a) : x ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
    exact ⟨h1, h2⟩
  have hfitR := (div_le_iff₀' hk).mpr hδR.2
  have hfitL := (div_le_iff₀' hk).mpr hδL.2
  have hR := integral_gap_ge_left_ramp (f := fun x => min 1 (1 + u - x) - capRoof U x)
    (fun l r => (Continuous.intervalIntegrable (by fun_prop) l r).sub
      (hU.intervalIntegrable_capRoof l r)) hk hδR.1 huv hδR.2
    (fun x hx' => sub_nonneg.mpr (le_min (capRoof_le_one hU.isCompact hU.inStrip x)
      (by linarith only [hu, hU.capRoof_le_diagonalRight (hx x (by linarith only [hx'.1, ha])
        hx'.2)])))
    fun x hx' => by
      have := hU.capRoof_le_nearDiagonalRight k u
        (hx x (by linarith only [hx'.1, hfitR, ha]) (hx'.2.trans huv.2))
      rw [min_eq_left (by linarith only [hx'.2])]
      linarith only [this]
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

def fullTriangleNicheGain (U : Set Plane) (a k u v : ℝ) : ℝ :=
  ((max (wideGain k u (wideNearRightIntercept U k)
      (wideEndpointIntercept a (capRoof U a) k)) 0) ^ 2 +
    (max (wideGain k v (wideNearLeftIntercept U k)
      (wideEndpointIntercept a (capRoof U (-a)) k)) 0) ^ 2) / (1 + k)

def fullTriangleNicheFloorLoss (U : Set Plane) (a k u v : ℝ) : ℝ :=
  fullTriangleFloorCoefficient k *
    ((max (fullTriangleRightZero k u (wideEndpointIntercept a (capRoof U a) k) - (u - k)) 0) ^ 2 +
      (max (fullTriangleRightZero k v (wideEndpointIntercept a (capRoof U (-a)) k) - (v - k)) 0) ^ 2)

theorem IsDownwardCap.niche_integral_ge_full_triangles {U : Set Plane}
    (hU : IsDownwardCap U) {a k u v α : ℝ}
    (hk : 0 < k) (hk1 : k ≤ 1) (hksq : k ^ 2 + 2 * k = 1)
    (hkoffset : k = Real.sqrt 2 - 1)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hu : diagonalRight U = 1 + u) (hv : diagonalLeft U = 1 + v)
    (hα : Real.pi / 2 - Real.arctan k ≤ α) (hαL : α ≤ Real.pi / 2)
    (hd : (u - v) / 2 ∈ Icc (-a / 2) (a / 2))
    (hcR : (u - v) / 2 ≤ wideCrossing k u (wideNearRightIntercept U k))
    (hcL : -(u - v) / 2 ≤ wideCrossing k v (wideNearLeftIntercept U k))
    (hrR : fullTriangleRightZero k u (wideEndpointIntercept a (capRoof U a) k) ≤ a / 2)
    (hrL : fullTriangleRightZero k v (wideEndpointIntercept a (capRoof U (-a)) k) ≤ a / 2) :
    (max ((u + v) / 2 - k) 0) ^ 2 - (max (u - k - a / 2) 0) ^ 2 / 2 -
      (max (v - k - a / 2) 0) ^ 2 / 2 + fullTriangleNicheGain U a k u v -
        fullTriangleNicheFloorLoss U a k u v ≤
      ∫ x in (-a / 2)..(a / 2), partialBarrier U α x := by
  have hα45 : Real.pi / 4 ≤ α := by
    linarith only [hα, Real.arctan_one ▸ Real.arctan_mono hk1]
  have hn := hU.intervalIntegrable_partialBarrier
    ((sub_pos.mpr (Real.arctan_lt_pi_div_two k)).trans_le hα) hαL
  have hc : Continuous fun x : ℝ => max (min (u - k - x) (v - k + x)) 0 := by fun_prop
  have hfloor (x : ℝ) : max (min (u - k - x) (v - k + x)) 0 ≤ partialBarrier U α x := by
    simpa only [sub_zero, zero_add] using hU.tilted_diagonal_tent_le_partialBarrier
      (h := 0) hkoffset hu (by simpa only [sub_zero] using hv) hα45 hαL x
  have hright := fullTriangle_niche_gain_integral hk hksq hn hfloor
    (hU.wide_near_right_wall_le hk hk1 hr hα hαL) hd.2 hcR hrR
  have hleft := fullTriangle_niche_gain_integral (n := fun x => partialBarrier U α (-x)) hk hksq
    (fun l r => by simpa only [neg_neg] using (IntervalIntegrable.iff_comp_neg).mp (hn (-l) (-r)))
    (fun x => by simpa only [min_comm, sub_neg_eq_add, ← sub_eq_add_neg] using hfloor (-x))
    (hU.wide_near_left_wall_le hk hl hα hαL) (by linarith only [hd.1]) (by linarith only [hcL])
    hrL
  have hflip := intervalIntegral.integral_comp_neg (a := (v - u) / 2) (b := a / 2)
    fun x => partialBarrier U α x - max (min (u - k - x) (v - k + x)) 0
  simp only [sub_neg_eq_add, ← sub_eq_add_neg, min_comm (u - k + _), ← neg_div, neg_sub]
    at hflip
  rw [hflip] at hleft
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    ((hn (-a / 2) ((u - v) / 2)).sub (hc.intervalIntegrable _ _))
    ((hn _ (a / 2)).sub (hc.intervalIntegrable _ _))
  rw [intervalIntegral.integral_sub (hn (-a / 2) (a / 2)) (hc.intervalIntegrable _ _)] at hadd
  have hdiag := integral_tilted_diagonal_tent k (h := 0)
    (show (u - v + 0) / 2 ∈ Icc (-a / 2) (a / 2) by simpa only [add_zero] using hd)
  simp only [sub_zero] at hdiag
  rw [fullTriangleNicheGain, fullTriangleNicheFloorLoss, add_div _ _ (1 + k)]
  linarith only [hleft, hright, hadd, hdiag]

end AmbidextrousSofa
