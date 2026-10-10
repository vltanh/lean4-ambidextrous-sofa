module

public import AmbidextrousSofa.Analysis.ThreeAngleComparison

@[expose] public section

/-!
# Actual niche payments using only the three displayed corners

The nearby support lines below belong to the original cap. Their corner
minima are bounded by the literal three-angle barrier. A common integral
splice adds the two disjoint contributions to the complete diagonal
floor, retaining every positive-floor and window correction.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsDownwardCap.threeAngle_diagonal_floor {U : Set Plane}
    (hU : IsDownwardCap U) {h k u v : ℝ} (hk : k = Real.sqrt 2 - 1)
    (hu : diagonalRight U = 1 + u) (hv : diagonalLeft U = 1 - h + v) (x : ℝ) :
    max (min (u - k - x) (v - h - k + x)) 0 ≤ threeAngleBarrier U x := by
  have hbound := diagonalBarrier_le_threeAngleBarrier U x
  rw [diagonalBarrier, cornerWall, firstWall_pi_div_four_eq_diagonal hU,
    secondWall_pi_div_four_eq_diagonal hU, hu, hv] at hbound
  have hsqrt : Real.sqrt 2 = k + 1 := by linarith only [hk]
  rw [hsqrt] at hbound
  convert hbound using 1 <;> congr 2 <;> ring

theorem IsDownwardCap.wide_near_right_corner_le {U : Set Plane}
    (hU : IsDownwardCap U) {a k : ℝ} (hk : 0 < k)
    (hr : horizontalRight U = a) (x : ℝ) :
    min (wideNearRightIntercept U k + k * x)
      (wideEndpointIntercept a (capRoof U a) k - x / k) ≤
        cornerWall U (Real.arctan k) x := by
  have hx : a ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hr]
    exact ⟨by rw [← hr]; exact horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact, le_rfl⟩
  have hs := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hx) (1, k)
  simp only [coordDot, mul_one] at hs
  have hcomp : wideEndpointIntercept a (capRoof U a) k - x / k ≤ firstWall U (Real.arctan k) x := by
    rw [hU.firstWall_arctan hk.ne']
    unfold wideEndpointIntercept
    apply (le_div_iff₀ hk).mpr
    have hmul : (capRoof U a + (a - nearDiagonalNorm k) / k - x / k) * k =
        a + capRoof U a * k - nearDiagonalNorm k - x := by field_simp [hk.ne'] <;> ring
    rw [hmul]
    linarith only [hs]
  have hsecond : wideNearRightIntercept U k + k * x = secondWall U (Real.arctan k) x := by
    rw [hU.secondWall_arctan]
    rfl
  rw [hsecond, cornerWall,
    min_comm (secondWall U (Real.arctan k) x) (wideEndpointIntercept a (capRoof U a) k - x / k)]
  exact min_le_min hcomp le_rfl

theorem IsDownwardCap.wide_near_left_corner_le {U : Set Plane}
    (hU : IsDownwardCap U) {a k : ℝ} (hk : 0 < k)
    (hl : horizontalLeft U = -a) (x : ℝ) :
    min (wideNearLeftIntercept U k + k * x)
      (wideEndpointIntercept a (capRoof U (-a)) k - x / k) ≤
        cornerWall U (Real.pi / 2 - Real.arctan k) (-x) := by
  have hx : -a ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl]
    exact ⟨le_rfl, by rw [← hl]; exact horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact⟩
  have hs := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hx) (-1, k)
  simp only [coordDot, mul_neg_one, neg_neg] at hs
  have hcomp : wideEndpointIntercept a (capRoof U (-a)) k - x / k ≤
      secondWall U (Real.pi / 2 - Real.arctan k) (-x) := by
    rw [hU.secondWall_complement_arctan hk.ne']
    unfold wideEndpointIntercept
    apply (le_div_iff₀ hk).mpr
    have hmul : (capRoof U (-a) + (a - nearDiagonalNorm k) / k - x / k) * k =
        a + capRoof U (-a) * k - nearDiagonalNorm k - x := by field_simp [hk.ne'] <;> ring
    rw [hmul]
    linarith only [hs]
  have hfirst : wideNearLeftIntercept U k + k * x =
      firstWall U (Real.pi / 2 - Real.arctan k) (-x) := by
    rw [hU.firstWall_complement_arctan]
    unfold wideNearLeftIntercept
    ring
  rw [hfirst, cornerWall]
  exact min_le_min le_rfl hcomp

theorem IsDownwardCap.wide_near_right_le_threeAngleBarrier {U : Set Plane}
    (hU : IsDownwardCap U) {a k : ℝ} (hk : 0 < k) (hkoffset : k = Real.sqrt 2 - 1)
    (hr : horizontalRight U = a) (x : ℝ) :
    min (wideNearRightIntercept U k + k * x)
      (wideEndpointIntercept a (capRoof U a) k - x / k) ≤ threeAngleBarrier U x :=
  (hU.wide_near_right_corner_le hk hr x).trans
    (by simpa only [hkoffset] using first_corner_le_threeAngleBarrier U x)

theorem IsDownwardCap.wide_near_left_le_threeAngleBarrier {U : Set Plane}
    (hU : IsDownwardCap U) {a k : ℝ} (hk : 0 < k) (hkoffset : k = Real.sqrt 2 - 1)
    (hl : horizontalLeft U = -a) (x : ℝ) :
    min (wideNearLeftIntercept U k + k * x)
      (wideEndpointIntercept a (capRoof U (-a)) k - x / k) ≤ threeAngleBarrier U (-x) :=
  (hU.wide_near_left_corner_le hk hl x).trans
    (by simpa only [hkoffset] using last_corner_le_threeAngleBarrier U (-x))

theorem symmetric_barrier_gain_integral {n : ℝ → ℝ} {a k u v gR gL : ℝ}
    (hn : ∀ l r, IntervalIntegrable n volume l r)
    (hd : (u - v) / 2 ∈ Icc (-a / 2) (a / 2))
    (hR : gR ≤ ∫ x in ((u - v) / 2)..(a / 2),
      n x - max (min (u - k - x) (v - k + x)) 0)
    (hL : gL ≤ ∫ x in ((v - u) / 2)..(a / 2),
      n (-x) - max (min (v - k - x) (u - k + x)) 0) :
    (max ((u + v) / 2 - k) 0) ^ 2 - (max (u - k - a / 2) 0) ^ 2 / 2 -
      (max (v - k - a / 2) 0) ^ 2 / 2 + gR + gL ≤
        ∫ x in (-a / 2)..(a / 2), n x := by
  let d := (u - v) / 2
  let f : ℝ → ℝ := fun x => n x - max (min (u - k - x) (v - k + x)) 0
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
  rw [hleftInt] at hL
  change gR ≤ ∫ x in d..(a / 2), f x at hR
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
  linarith only [hR, hL, hadd]

theorem IsDownwardCap.threeAngle_integral_ge_full_triangles {U : Set Plane}
    (hU : IsDownwardCap U) {a k u v : ℝ}
    (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1) (hkoffset : k = Real.sqrt 2 - 1)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hu : diagonalRight U = 1 + u) (hv : diagonalLeft U = 1 + v)
    (hd : (u - v) / 2 ∈ Icc (-a / 2) (a / 2))
    (hcR : (u - v) / 2 ≤ wideCrossing k u (wideNearRightIntercept U k))
    (hcL : -(u - v) / 2 ≤ wideCrossing k v (wideNearLeftIntercept U k))
    (hrR : fullTriangleRightZero k u (wideEndpointIntercept a (capRoof U a) k) ≤ a / 2)
    (hrL : fullTriangleRightZero k v (wideEndpointIntercept a (capRoof U (-a)) k) ≤ a / 2) :
    (max ((u + v) / 2 - k) 0) ^ 2 - (max (u - k - a / 2) 0) ^ 2 / 2 -
      (max (v - k - a / 2) 0) ^ 2 / 2 + fullTriangleNicheGain U a k u v -
        fullTriangleNicheFloorLoss U a k u v ≤
      ∫ x in (-a / 2)..(a / 2), threeAngleBarrier U x := by
  let n := threeAngleBarrier U
  have hn : ∀ l r, IntervalIntegrable n volume l r :=
    (continuous_threeAngleBarrier U).intervalIntegrable
  have hfloor (x : ℝ) : max (min (u - k - x) (v - k + x)) 0 ≤ n x := by
    simpa only [sub_zero] using hU.threeAngle_diagonal_floor (h := 0) hkoffset hu
      (by simpa only [sub_zero] using hv) x
  have hnRef : ∀ l r, IntervalIntegrable (fun x => n (-x)) volume l r :=
    ((continuous_threeAngleBarrier U).comp continuous_neg).intervalIntegrable
  have hfloorRef (x : ℝ) : max (min (v - k - x) (u - k + x)) 0 ≤ n (-x) := by
    have h := hfloor (-x)
    have hid : min (u - k - -x) (v - k + -x) = min (v - k - x) (u - k + x) := by
      rw [min_comm]
      congr 1 <;> ring
    rwa [hid] at h
  have hR := fullTriangle_niche_gain_integral hk hksq hn hfloor
    (hU.wide_near_right_le_threeAngleBarrier hk hkoffset hr) hd.2 hcR hrR
  have hL := fullTriangle_niche_gain_integral hk hksq hnRef hfloorRef
    (hU.wide_near_left_le_threeAngleBarrier hk hkoffset hl)
    (show (v - u) / 2 ≤ a / 2 by linarith only [hd.1])
    (show (v - u) / 2 ≤ wideCrossing k v (wideNearLeftIntercept U k) by linarith only [hcL]) hrL
  have h := symmetric_barrier_gain_integral hn hd hR hL
  convert h using 1 <;> dsimp only [n, fullTriangleNicheGain, fullTriangleNicheFloorLoss] <;> ring

theorem IsDownwardCap.threeAngle_integral_ge_wide_pieces {U : Set Plane}
    (hU : IsDownwardCap U) {a k u v : ℝ}
    (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1) (hkoffset : k = Real.sqrt 2 - 1)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hu : diagonalRight U = 1 + u) (hv : diagonalLeft U = 1 + v)
    (hd : (u - v) / 2 ∈ Icc (-a / 2) (a / 2))
    (hcR : (u - v) / 2 ≤ wideCrossing k u (wideNearRightIntercept U k))
    (hcL : -(u - v) / 2 ≤ wideCrossing k v (wideNearLeftIntercept U k))
    (hpR : widePeak k (wideNearRightIntercept U k) (wideEndpointIntercept a (capRoof U a) k) ≤ a / 2)
    (hpL : widePeak k (wideNearLeftIntercept U k) (wideEndpointIntercept a (capRoof U (-a)) k) ≤ a / 2) :
    (max ((u + v) / 2 - k) 0) ^ 2 - (max (u - k - a / 2) 0) ^ 2 / 2 -
      (max (v - k - a / 2) 0) ^ 2 / 2 +
      ((max (wideTruncatedGain k u (wideNearRightIntercept U k)
          (wideEndpointIntercept a (capRoof U a) k)) 0) ^ 2 +
       (max (wideTruncatedGain k v (wideNearLeftIntercept U k)
          (wideEndpointIntercept a (capRoof U (-a)) k)) 0) ^ 2) / (2 * (1 + k)) ≤
      ∫ x in (-a / 2)..(a / 2), threeAngleBarrier U x := by
  let n := threeAngleBarrier U
  have hn : ∀ l r, IntervalIntegrable n volume l r :=
    (continuous_threeAngleBarrier U).intervalIntegrable
  have hfloor (x : ℝ) : max (min (u - k - x) (v - k + x)) 0 ≤ n x := by
    simpa only [sub_zero] using hU.threeAngle_diagonal_floor (h := 0) hkoffset hu
      (by simpa only [sub_zero] using hv) x
  have hnRef : ∀ l r, IntervalIntegrable (fun x => n (-x)) volume l r :=
    ((continuous_threeAngleBarrier U).comp continuous_neg).intervalIntegrable
  have hfloorRef (x : ℝ) : max (min (v - k - x) (u - k + x)) 0 ≤ n (-x) := by
    have h := hfloor (-x)
    have hid : min (u - k - -x) (v - k + -x) = min (v - k - x) (u - k + x) := by
      rw [min_comm]
      congr 1 <;> ring
    rwa [hid] at h
  have hR := wide_rising_piece_integral hk hksq hn hfloor
    (hU.wide_near_right_le_threeAngleBarrier hk hkoffset hr) hd.2 hcR hpR
  have hL := wide_rising_piece_integral hk hksq hnRef hfloorRef
    (hU.wide_near_left_le_threeAngleBarrier hk hkoffset hl)
    (show (v - u) / 2 ≤ a / 2 by linarith only [hd.1])
    (show (v - u) / 2 ≤ wideCrossing k v (wideNearLeftIntercept U k) by linarith only [hcL]) hpL
  have h := symmetric_barrier_gain_integral hn hd hR hL
  convert h using 1
  ring

end AmbidextrousSofa
