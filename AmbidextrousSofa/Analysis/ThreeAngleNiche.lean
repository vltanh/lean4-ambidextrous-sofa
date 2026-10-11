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
  convert hbound using 3 <;> linarith

/-- The diagonal floor below the three-angle barrier, and its reflection. -/
private theorem IsDownwardCap.threeAngle_floors {U : Set Plane} (hU : IsDownwardCap U)
    {k u v : ℝ} (hkoffset : k = Real.sqrt 2 - 1) (hu : diagonalRight U = 1 + u)
    (hv : diagonalLeft U = 1 + v) (x : ℝ) :
    max (min (u - k - x) (v - k + x)) 0 ≤ threeAngleBarrier U x ∧
      max (min (v - k - x) (u - k + x)) 0 ≤ threeAngleBarrier U (-x) := by
  have h (y : ℝ) := hU.threeAngle_diagonal_floor (h := 0) hkoffset hu (by rwa [sub_zero]) y
  exact ⟨by simpa using h x, by simpa [min_comm, sub_eq_add_neg] using h (-x)⟩

theorem IsDownwardCap.wide_near_right_le_threeAngleBarrier {U : Set Plane}
    (hU : IsDownwardCap U) {a k : ℝ} (hk : 0 < k) (hkoffset : k = Real.sqrt 2 - 1)
    (hr : horizontalRight U = a) (x : ℝ) :
    min (wideNearRightIntercept U k + k * x)
      (wideEndpointIntercept a (capRoof U a) k - x / k) ≤ threeAngleBarrier U x := by
  have hs := coordDot_le_support hU.isCompact
    (capRoof_mem hU.isCompact (hr ▸ horizontalRight_mem hU.nonempty hU.isCompact)) (1, k)
  simp only [coordDot] at hs
  refine le_trans ?_ (hkoffset ▸ first_corner_le_threeAngleBarrier U x)
  rw [cornerWall, min_comm (firstWall _ _ _)]
  refine min_le_min (hU.secondWall_arctan k x).ge ?_
  rw [hU.firstWall_arctan hk.ne', wideEndpointIntercept, le_div_iff₀ hk, sub_mul, add_mul,
    div_mul_cancel₀ _ hk.ne', div_mul_cancel₀ _ hk.ne']
  linarith

theorem IsDownwardCap.wide_near_left_le_threeAngleBarrier {U : Set Plane}
    (hU : IsDownwardCap U) {a k : ℝ} (hk : 0 < k) (hkoffset : k = Real.sqrt 2 - 1)
    (hl : horizontalLeft U = -a) (x : ℝ) :
    min (wideNearLeftIntercept U k + k * x)
      (wideEndpointIntercept a (capRoof U (-a)) k - x / k) ≤ threeAngleBarrier U (-x) := by
  have hs := coordDot_le_support hU.isCompact
    (capRoof_mem hU.isCompact (hl ▸ horizontalLeft_mem hU.nonempty hU.isCompact)) (-1, k)
  simp only [coordDot] at hs
  refine le_trans ?_ (hkoffset ▸ last_corner_le_threeAngleBarrier U (-x))
  rw [cornerWall, hU.firstWall_complement_arctan, hU.secondWall_complement_arctan hk.ne']
  refine min_le_min (le_of_eq (by rw [wideNearLeftIntercept]; ring)) ?_
  rw [wideEndpointIntercept, le_div_iff₀ hk, sub_mul, add_mul, div_mul_cancel₀ _ hk.ne',
    div_mul_cancel₀ _ hk.ne']
  linarith

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
  have htent : Continuous fun x => max (min (u - k - x) (v - k + x)) 0 := by fun_prop
  have hrefl := intervalIntegral.integral_comp_neg (a := (v - u) / 2) (b := a / 2)
    (fun x => n x - max (min (u - k - x) (v - k + x)) 0)
  simp only [← neg_div, neg_sub, sub_neg_eq_add, ← sub_eq_add_neg] at hrefl
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    ((hn (-a / 2) ((u - v) / 2)).sub (htent.intervalIntegrable _ _))
    ((hn ((u - v) / 2) (a / 2)).sub (htent.intervalIntegrable _ _))
  have hdiag := integral_tilted_diagonal_tent k (h := 0) (a := a) (u := u) (v := v)
    (by rwa [add_zero])
  simp only [sub_zero] at hdiag
  rw [intervalIntegral.integral_sub (hn (-a / 2) (a / 2)) (htent.intervalIntegrable _ _),
    hdiag] at hadd
  simp only [min_comm] at hL
  linarith

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
  have hn := (continuous_threeAngleBarrier U).intervalIntegrable (μ := volume)
  have hR := fullTriangle_niche_gain_integral hk hksq hn
    (fun x => (hU.threeAngle_floors hkoffset hu hv x).1)
    (hU.wide_near_right_le_threeAngleBarrier hk hkoffset hr) hd.2 hcR hrR
  have hL := fullTriangle_niche_gain_integral (n := fun x => threeAngleBarrier U (-x)) hk hksq
    ((continuous_threeAngleBarrier U).comp continuous_neg).intervalIntegrable
    (fun x => (hU.threeAngle_floors hkoffset hu hv x).2)
    (hU.wide_near_left_le_threeAngleBarrier hk hkoffset hl) (by linarith only [hd.1])
    (by linarith only [hcL]) hrL
  convert symmetric_barrier_gain_integral hn hd hR hL using 1
  simp only [fullTriangleNicheGain, fullTriangleNicheFloorLoss]
  ring

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
  have hn := (continuous_threeAngleBarrier U).intervalIntegrable (μ := volume)
  have hR := wide_rising_piece_integral hk hksq hn
    (fun x => (hU.threeAngle_floors hkoffset hu hv x).1)
    (hU.wide_near_right_le_threeAngleBarrier hk hkoffset hr) hd.2 hcR hpR
  have hL := wide_rising_piece_integral (n := fun x => threeAngleBarrier U (-x)) hk hksq
    ((continuous_threeAngleBarrier U).comp continuous_neg).intervalIntegrable
    (fun x => (hU.threeAngle_floors hkoffset hu hv x).2)
    (hU.wide_near_left_le_threeAngleBarrier hk hkoffset hl) (by linarith only [hd.1])
    (by linarith only [hcL]) hpL
  convert symmetric_barrier_gain_integral hn hd hR hL using 1
  ring

end AmbidextrousSofa
