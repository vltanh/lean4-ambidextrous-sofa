module

public import AmbidextrousSofa.Analysis.ThreeAngleDeficit

@[expose] public section

/-!
# Both short-width tails in the literal three-angle barrier

The two nearby corners pay the same actual support-cut triangles as in
the short-width comparison. Their disjointness at the diagonal apex and
their outer-tip corrections are proved before integration.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsDownwardCap.threeAngle_left_competitor_le {U : Set Plane}
    (hU : IsDownwardCap U) {h k u v : ℝ} (hk : 0 < k)
    (hkoffset : k = Real.sqrt 2 - 1) (hcomp : u + k ≤ support U (1, k)) (x : ℝ) :
    min ((u + k - nearDiagonalNorm k - x) / k)
      (1 - h + k * v - nearDiagonalLeftDeficit U h k v - nearDiagonalNorm k + k * x) ≤
        threeAngleBarrier U x := by
  refine le_trans ?_ (hkoffset ▸ first_corner_le_threeAngleBarrier U x)
  rw [cornerWall, hU.firstWall_arctan hk.ne', hU.secondWall_arctan, nearDiagonalLeftDeficit]
  exact min_le_min (div_le_div_of_nonneg_right (by linarith only [hcomp]) hk.le) (by linarith)

theorem IsDownwardCap.threeAngle_right_competitor_le {U : Set Plane}
    (hU : IsDownwardCap U) {h k u v : ℝ} (hk : 0 < k)
    (hkoffset : k = Real.sqrt 2 - 1)
    (hcomp : v + k * (1 - h) ≤ support U (-1, k)) (x : ℝ) :
    min ((v + k * (1 - h) - nearDiagonalNorm k + x) / k)
      (1 + k * u - nearDiagonalRightDeficit U k u - nearDiagonalNorm k - k * x) ≤
        threeAngleBarrier U x := by
  refine le_trans ?_ (hkoffset ▸ last_corner_le_threeAngleBarrier U x)
  rw [cornerWall, hU.firstWall_complement_arctan, hU.secondWall_complement_arctan hk.ne',
    min_comm (support U (k, 1) - nearDiagonalNorm k - k * x), nearDiagonalRightDeficit]
  exact min_le_min (div_le_div_of_nonneg_right (by linarith only [hcomp]) hk.le) (by linarith)

theorem IsDownwardCap.threeAngle_integral_ge_diagonal_two_tails {U : Set Plane}
    (hU : IsDownwardCap U) {a h k u v L : ℝ}
    (ha : 0 < a) (hk : 0 < k) (hk1 : k < 1) (hksq : k ^ 2 + 2 * k = 1)
    (hkoffset : k = Real.sqrt 2 - 1)
    (hu : diagonalRight U = 1 + u) (hv : diagonalLeft U = 1 - h + v)
    (hcompR : u + k ≤ support U (1, k))
    (hcompL : v + k * (1 - h) ≤ support U (-1, k))
    (hη : (2 / 25 : ℝ) ≤ 1 - nearDiagonalNorm k + k ^ 2)
    (hd : (u - v + h) / 2 ∈ Icc (-a / 2) (a / 2))
    (hpL : k - v + h ∈ Icc (-a / 2) (a / 2))
    (hpR : k - u ∈ Icc (-a / 2) (a / 2))
    (hendL : k - v + h + shortLeftTailHeight k h (nearDiagonalLeftDeficit U h k v) /
      (1 - k) ≤ (u - v + h) / 2)
    (hendR : k - u + shortRightTailHeight (nearDiagonalRightDeficit U k u) /
      (1 - k) ≤ -(u - v + h) / 2)
    (hL : nearDiagonalNorm k + shortLeftTailHeight k h (nearDiagonalLeftDeficit U h k v) / k ≤
      u + v - h)
    (hR : nearDiagonalNorm k + shortRightTailHeight (nearDiagonalRightDeficit U k u) / k ≤
      u + v - k * h)
    (hL0 : 0 ≤ L)
    (hclipL : shortLeftTailHeight k h (nearDiagonalLeftDeficit U h k v) / k -
      (k - v + h + a / 2) ≤ L)
    (hclipR : shortRightTailHeight (nearDiagonalRightDeficit U k u) / k -
      (k - u + a / 2) ≤ L) :
    (max ((u + v - h) / 2 - k) 0) ^ 2 -
      (max (u - k - a / 2) 0) ^ 2 / 2 - (max (v - h - k - a / 2) 0) ^ 2 / 2 +
      nearTriangleCoefficient k *
        (shortLeftTailHeight k h (nearDiagonalLeftDeficit U h k v) ^ 2 +
          shortRightTailHeight (nearDiagonalRightDeficit U k u) ^ 2) - k * L ^ 2 ≤
      ∫ x in (-a / 2)..(a / 2), threeAngleBarrier U x := by
  set EL := shortLeftTailHeight k h (nearDiagonalLeftDeficit U h k v)
  set ER := shortRightTailHeight (nearDiagonalRightDeficit U k u)
  -- The two nearby support competitors add two disjoint triangles to the diagonal floor.
  have hpt (x : ℝ) : max (min (u - k - x) (v - h - k + x)) 0 +
      affineCutTriangle k EL (k - v + h) x + affineCutTriangle k ER (k - u) (-x) ≤
        threeAngleBarrier U x := by
    have hfloor := hU.threeAngle_diagonal_floor hkoffset hu hv x
    rcases le_or_gt x ((u - v + h) / 2) with hx | hx
    · rw [min_eq_right (by linarith only [hx]), show v - h - k + x = x - (k - v + h) by ring]
        at hfloor ⊢
      rw [affineCutTriangle_eq_zero_of_right hk1 (hendR.trans (by linarith only [hx])), add_zero]
      exact near_tail_add_floor_le hk hk1 hksq hfloor (by linarith only [hL])
        (shortLeftTailHeight_peak hη) (hU.threeAngle_left_competitor_le hk hkoffset hcompR x)
    · rw [min_eq_left (by linarith only [hx]), show u - k - x = -x - (k - u) by ring] at hfloor ⊢
      rw [affineCutTriangle_eq_zero_of_right hk1 (hendL.trans hx.le), add_zero]
      exact near_tail_add_floor_le (A := v + k * (1 - h) - nearDiagonalNorm k) hk hk1 hksq hfloor
        (by linarith only [hR]) (shortRightTailHeight_peak hη)
        (by simpa only [sub_neg_eq_add, mul_neg, ← sub_eq_add_neg] using
          hU.threeAngle_right_competitor_le hk hkoffset hcompL x)
  have hj : 0 < 1 - k := sub_pos.mpr hk1
  have hIL := integral_affineCutTriangle_ge_of_outer_tip_bound hk hk1
    (show 0 ≤ EL from le_max_right _ _) hpL.1 hpL.2
    ((div_le_iff₀' hj).mp (by linarith only [hendL, hd.2])) hL0 (by linarith only [hclipL])
  have hIR : ER ^ 2 / (2 * k * (1 - k)) - k / 2 * L ^ 2 ≤
      ∫ x in (-a / 2)..(a / 2), affineCutTriangle k ER (k - u) (-x) := by
    simpa only [intervalIntegral.integral_comp_neg, neg_div, neg_neg] using
      integral_affineCutTriangle_ge_of_outer_tip_bound hk hk1 (show 0 ≤ ER from le_max_right _ _)
        hpR.1 hpR.2 ((div_le_iff₀' hj).mp (by linarith only [hendR, hd.1])) hL0
        (by linarith only [hclipR])
  have hIB := (show Continuous (fun x : ℝ =>
    max (min (u - k - x) (v - h - k + x)) 0) by fun_prop).intervalIntegrable (μ := volume)
      (-a / 2) (a / 2)
  have hITL := (continuous_affineCutTriangle k EL (k - v + h)).intervalIntegrable
    (μ := volume) (-a / 2) (a / 2)
  have hITR := ((continuous_affineCutTriangle k ER (k - u)).comp continuous_neg).intervalIntegrable
    (μ := volume) (-a / 2) (a / 2)
  have hi := intervalIntegral.integral_mono (by linarith only [ha] : -a / 2 ≤ a / 2)
    ((hIB.add hITL).add hITR) ((continuous_threeAngleBarrier U).intervalIntegrable _ _) hpt
  rw [intervalIntegral.integral_add (hIB.add hITL) hITR,
    intervalIntegral.integral_add hIB hITL, integral_tilted_diagonal_tent k hd] at hi
  simp only [Function.comp_apply] at hi
  rw [nearTriangleCoefficient, one_div_mul_eq_div, add_div]
  linarith only [hi, hIL, hIR]

end AmbidextrousSofa
