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
  let δR := nearDiagonalRightDeficit U k u
  let δL := nearDiagonalLeftDeficit U h k v
  let fR : ℝ → ℝ := fun x => min 1 (1 + u - x) - capRoof U x
  let fL : ℝ → ℝ := fun x => min (1 - h) (1 - h + v + x) - capRoof U x
  have hfR : ∀ l r, IntervalIntegrable fR volume l r := fun l r =>
    ((show Continuous (fun x : ℝ => min 1 (1 + u - x)) by fun_prop).intervalIntegrable l r).sub
      (hU.intervalIntegrable_capRoof l r)
  have hfL : ∀ l r, IntervalIntegrable fL volume l r := fun l r =>
    ((show Continuous (fun x : ℝ => min (1 - h) (1 - h + v + x)) by
      fun_prop).intervalIntegrable l r).sub (hU.intervalIntegrable_capRoof l r)
  have hproj : horizontalProjection U = Icc (-a) a := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
  have hfR0 : ∀ x ∈ Icc (a / 2) a, 0 ≤ fR x := by
    intro x hx
    have hxU : x ∈ horizontalProjection U := by
      rw [hproj]; exact ⟨by linarith only [hx.1, ha], hx.2⟩
    apply sub_nonneg.mpr
    exact le_min (capRoof_le_one hU.isCompact hU.inStrip x)
      (by linarith only [hU.capRoof_le_diagonalRight hxU, hu])
  have hfL0 : ∀ x ∈ Icc (-a) (-a / 2), 0 ≤ fL x := by
    intro x hx
    have hxU : x ∈ horizontalProjection U := by
      rw [hproj]; exact ⟨hx.1, by linarith only [hx.2, ha]⟩
    apply sub_nonneg.mpr
    exact le_min (hU.left_roof_le_middle_height ha hh hl hr hleft hright x hx)
      (by linarith only [hU.capRoof_le_diagonalLeft hxU, hv])
  have hR : δR ^ 2 / (2 * k) ≤ ∫ x in (a / 2)..a, fR x := by
    apply integral_gap_ge_left_ramp hfR hk hδR.1 huv hδR.2 hfR0
    intro x hx
    have hfit : δR / k ≤ u - a / 2 := (div_le_iff₀ hk).mpr (by rw [mul_comm]; exact hδR.2)
    have hxU : x ∈ horizontalProjection U := by
      rw [hproj]
      exact ⟨by linarith only [hx.1, hfit, ha], hx.2.trans huv.2⟩
    have hcut := hU.capRoof_le_nearDiagonalRight k u hxU
    dsimp [fR]
    rw [min_eq_left (by linarith only [hx.2] : 1 ≤ 1 + u - x)]
    change capRoof U x ≤ 1 + k * u - δR - k * x at hcut
    nlinarith only [hcut]
  have hL : δL ^ 2 / (2 * k) ≤ ∫ x in (-a)..(-a / 2), fL x := by
    apply integral_gap_ge_right_ramp hfL hk hδL.1
      (show -v ∈ Icc (-a) (-a / 2) by constructor <;> linarith only [hvv.1, hvv.2])
      (show δL ≤ k * (-a / 2 - -v) by convert hδL.2 using 1 <;> ring) hfL0
    intro x hx
    have hfit : δL / k ≤ v - a / 2 := (div_le_iff₀ hk).mpr (by rw [mul_comm]; exact hδL.2)
    have hxU : x ∈ horizontalProjection U := by
      rw [hproj]
      exact ⟨by linarith only [hx.1, hvv.2], by linarith only [hx.2, hfit, ha]⟩
    have hcut := hU.capRoof_le_nearDiagonalLeft h k v hxU
    dsimp [fL]
    rw [min_eq_left (by linarith only [hx.1] : 1 - h ≤ 1 - h + v + x)]
    change capRoof U x ≤ 1 - h + k * v - δL + k * x at hcut
    nlinarith only [hcut]
  change (δR ^ 2 + δL ^ 2) / (2 * k) ≤
    (∫ x in (-a)..(-a / 2), fL x) + ∫ x in (a / 2)..a, fR x
  rw [add_div]
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
  have hα0 : 0 < α := (sub_pos.mpr (Real.arctan_lt_pi_div_two k)).trans_le hα
  have hα45 : Real.pi / 4 ≤ α := by
    have h := Real.arctan_strictMono.monotone hk1
    rw [Real.arctan_one] at h
    linarith only [h, hα]
  let n := partialBarrier U α
  let d := (u - v) / 2
  let f : ℝ → ℝ := fun x => n x - max (min (u - k - x) (v - k + x)) 0
  have hn : ∀ l r, IntervalIntegrable n volume l r :=
    hU.intervalIntegrable_partialBarrier hα0 hαL
  have hfloor (x : ℝ) : max (min (u - k - x) (v - k + x)) 0 ≤ n x := by
    simpa only [sub_zero, zero_add] using hU.tilted_diagonal_tent_le_partialBarrier
      (h := 0) hkoffset hu (by simpa only [sub_zero] using hv) hα45 hαL x
  have hright := fullTriangle_niche_gain_integral hk hksq hn hfloor
    (hU.wide_near_right_wall_le hk hk1 hr hα hαL) hd.2 hcR hrR
  have hnRef : ∀ l r, IntervalIntegrable (fun x => n (-x)) volume l r := by
    intro l r
    have h := (IntervalIntegrable.iff_comp_neg).mp (hn (-l) (-r))
    simpa only [neg_neg] using h
  have hfloorRef (x : ℝ) : max (min (v - k - x) (u - k + x)) 0 ≤ n (-x) := by
    have h := hfloor (-x)
    have hid : min (u - k - -x) (v - k + -x) = min (v - k - x) (u - k + x) := by
      rw [min_comm]
      congr 1 <;> ring
    rwa [hid] at h
  have hleft := fullTriangle_niche_gain_integral hk hksq hnRef hfloorRef
    (hU.wide_near_left_wall_le hk hl hα hαL)
    (show (v - u) / 2 ≤ a / 2 by linarith only [hd.1])
    (show (v - u) / 2 ≤ wideCrossing k v (wideNearLeftIntercept U k) by linarith only [hcL]) hrL
  have hleftInt :
      (∫ x in ((v - u) / 2)..(a / 2), n (-x) - max (min (v - k - x) (u - k + x)) 0) =
        ∫ x in (-a / 2)..d, f x := by
    have hfun (x : ℝ) : n (-x) - max (min (v - k - x) (u - k + x)) 0 = f (-x) := by
      dsimp [f]
      rw [min_comm]
      congr 3 <;> ring
    simp_rw [hfun]
    rw [intervalIntegral.integral_comp_neg]
    congr 1 <;> (try dsimp only [d]) <;> ring
  rw [hleftInt] at hleft
  change _ ≤ ∫ x in d..(a / 2), f x at hright
  have hf : ∀ l r, IntervalIntegrable f volume l r := fun l r =>
    (hn l r).sub ((show Continuous (fun x : ℝ => max (min (u - k - x) (v - k + x)) 0)
      by fun_prop).intervalIntegrable l r)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hf (-a / 2) d) (hf d (a / 2))
  have hdiag : (∫ x in (-a / 2)..(a / 2), max (min (u - k - x) (v - k + x)) 0) =
      (max ((u + v) / 2 - k) 0) ^ 2 - (max (u - k - a / 2) 0) ^ 2 / 2 -
        (max (v - k - a / 2) 0) ^ 2 / 2 := by
    simpa only [sub_zero] using integral_tilted_diagonal_tent k (h := 0)
      (show (u - v + 0) / 2 ∈ Icc (-a / 2) (a / 2) by simpa only [add_zero] using hd)
  have hwhole : (∫ x in (-a / 2)..(a / 2), f x) =
      (∫ x in (-a / 2)..(a / 2), n x) -
      ((max ((u + v) / 2 - k) 0) ^ 2 - (max (u - k - a / 2) 0) ^ 2 / 2 -
        (max (v - k - a / 2) 0) ^ 2 / 2) := by
    dsimp only [f]
    rw [intervalIntegral.integral_sub (hn _ _)
      ((show Continuous (fun x : ℝ => max (min (u - k - x) (v - k + x)) 0)
        by fun_prop).intervalIntegrable _ _), hdiag]
  rw [hwhole] at hadd
  unfold fullTriangleNicheGain fullTriangleNicheFloorLoss
  have hgainSum :
      ((max (wideGain k u (wideNearRightIntercept U k)
          (wideEndpointIntercept a (capRoof U a) k)) 0) ^ 2 +
       (max (wideGain k v (wideNearLeftIntercept U k)
          (wideEndpointIntercept a (capRoof U (-a)) k)) 0) ^ 2) / (1 + k) =
      (max (wideGain k u (wideNearRightIntercept U k)
          (wideEndpointIntercept a (capRoof U a) k)) 0) ^ 2 / (1 + k) +
      (max (wideGain k v (wideNearLeftIntercept U k)
          (wideEndpointIntercept a (capRoof U (-a)) k)) 0) ^ 2 / (1 + k) := add_div _ _ _
  rw [hgainSum]
  nlinarith only [hleft, hright, hadd]

end AmbidextrousSofa
