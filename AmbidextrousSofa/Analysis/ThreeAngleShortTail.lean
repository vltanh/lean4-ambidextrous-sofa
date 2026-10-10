import AmbidextrousSofa.Analysis.ThreeAngleDeficit

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
  have hcorner : cornerWall U (Real.arctan k) x ≤ threeAngleBarrier U x := by
    simpa only [hkoffset] using first_corner_le_threeAngleBarrier U x
  apply le_trans _ hcorner
  rw [cornerWall, hU.firstWall_arctan hk.ne', hU.secondWall_arctan]
  apply min_le_min
  · exact div_le_div_of_nonneg_right (by linarith only [hcomp]) hk.le
  · unfold nearDiagonalLeftDeficit
    linarith

theorem IsDownwardCap.threeAngle_right_competitor_le {U : Set Plane}
    (hU : IsDownwardCap U) {h k u v : ℝ} (hk : 0 < k)
    (hkoffset : k = Real.sqrt 2 - 1)
    (hcomp : v + k * (1 - h) ≤ support U (-1, k)) (x : ℝ) :
    min ((v + k * (1 - h) - nearDiagonalNorm k + x) / k)
      (1 + k * u - nearDiagonalRightDeficit U k u - nearDiagonalNorm k - k * x) ≤
        threeAngleBarrier U x := by
  have hcorner : cornerWall U (Real.pi / 2 - Real.arctan k) x ≤ threeAngleBarrier U x := by
    simpa only [hkoffset] using last_corner_le_threeAngleBarrier U x
  apply le_trans _ hcorner
  rw [cornerWall, hU.firstWall_complement_arctan, hU.secondWall_complement_arctan hk.ne',
    min_comm (support U (k, 1) - nearDiagonalNorm k - k * x)]
  apply min_le_min
  · exact div_le_div_of_nonneg_right (by linarith only [hcomp]) hk.le
  · unfold nearDiagonalRightDeficit
    linarith

theorem IsDownwardCap.diagonal_two_tails_le_threeAngleBarrier {U : Set Plane}
    (hU : IsDownwardCap U) {h k u v : ℝ}
    (hk : 0 < k) (hk1 : k < 1) (hksq : k ^ 2 + 2 * k = 1)
    (hkoffset : k = Real.sqrt 2 - 1)
    (hu : diagonalRight U = 1 + u) (hv : diagonalLeft U = 1 - h + v)
    (hcompR : u + k ≤ support U (1, k))
    (hcompL : v + k * (1 - h) ≤ support U (-1, k))
    (hη : (2 / 25 : ℝ) ≤ 1 - nearDiagonalNorm k + k ^ 2)
    (hendL : k - v + h + shortLeftTailHeight k h (nearDiagonalLeftDeficit U h k v) /
      (1 - k) ≤ (u - v + h) / 2)
    (hendR : k - u + shortRightTailHeight (nearDiagonalRightDeficit U k u) /
      (1 - k) ≤ -(u - v + h) / 2)
    (hL : nearDiagonalNorm k + shortLeftTailHeight k h (nearDiagonalLeftDeficit U h k v) / k ≤
      u + v - h)
    (hR : nearDiagonalNorm k + shortRightTailHeight (nearDiagonalRightDeficit U k u) / k ≤
      u + v - k * h) (x : ℝ) :
    max (min (u - k - x) (v - h - k + x)) 0 +
      affineCutTriangle k (shortLeftTailHeight k h (nearDiagonalLeftDeficit U h k v))
        (k - v + h) x +
      affineCutTriangle k (shortRightTailHeight (nearDiagonalRightDeficit U k u))
        (k - u) (-x) ≤ threeAngleBarrier U x := by
  have hfloor := hU.threeAngle_diagonal_floor hkoffset hu hv x
  by_cases hx : x ≤ (u - v + h) / 2
  · have hzero : affineCutTriangle k (shortRightTailHeight (nearDiagonalRightDeficit U k u))
        (k - u) (-x) = 0 :=
      affineCutTriangle_eq_zero_of_right hk1 (by linarith only [hendR, hx])
    have hbase : max (min (u - k - x) (v - h - k + x)) 0 =
        max (x - (k - v + h)) 0 := by
      rw [min_eq_right (by linarith only [hx])]
      congr 1
      ring
    rw [hbase, hzero, add_zero]
    rw [hbase] at hfloor
    apply near_tail_add_floor_le hk hk1 hksq hfloor
      (A := u + k - nearDiagonalNorm k)
      (B := 1 - h + k * v - nearDiagonalLeftDeficit U h k v - nearDiagonalNorm k)
    · linarith only [hL]
    · exact shortLeftTailHeight_peak hη
    · exact hU.threeAngle_left_competitor_le hk hkoffset hcompR x
  · have hx' : (u - v + h) / 2 ≤ x := le_of_not_ge hx
    have hzero : affineCutTriangle k (shortLeftTailHeight k h (nearDiagonalLeftDeficit U h k v))
        (k - v + h) x = 0 :=
      affineCutTriangle_eq_zero_of_right hk1 (hendL.trans hx')
    have hbase : max (min (u - k - x) (v - h - k + x)) 0 =
        max (-x - (k - u)) 0 := by
      rw [min_eq_left (by linarith only [hx'])]
      congr 1
      ring
    rw [hbase, hzero, add_zero]
    rw [hbase] at hfloor
    apply near_tail_add_floor_le hk hk1 hksq hfloor
      (A := v + k * (1 - h) - nearDiagonalNorm k)
      (B := 1 + k * u - nearDiagonalRightDeficit U k u - nearDiagonalNorm k)
    · nlinarith only [hR]
    · exact shortRightTailHeight_peak hη
    · simpa only [sub_neg_eq_add, mul_neg] using
        hU.threeAngle_right_competitor_le hk hkoffset hcompL x

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
  let EL := shortLeftTailHeight k h (nearDiagonalLeftDeficit U h k v)
  let ER := shortRightTailHeight (nearDiagonalRightDeficit U k u)
  have hj : 0 < 1 - k := sub_pos.mpr hk1
  have hEL : EL ≤ (1 - k) * (a / 2 - (k - v + h)) := by
    have h := (div_le_iff₀ hj).mp
      (show EL / (1 - k) ≤ a / 2 - (k - v + h) by linarith only [hendL, hd.2])
    nlinarith only [h]
  have hER : ER ≤ (1 - k) * (a / 2 - (k - u)) := by
    have h := (div_le_iff₀ hj).mp
      (show ER / (1 - k) ≤ a / 2 - (k - u) by linarith only [hendR, hd.1])
    nlinarith only [h]
  have hIL := integral_affineCutTriangle_ge_of_outer_tip_bound hk hk1
    (show 0 ≤ EL from le_max_right _ _) hpL.1 hpL.2 hEL hL0
    (show EL / k - ((k - v + h) - (-a / 2)) ≤ L by linarith only [hclipL])
  have hIR₀ := integral_affineCutTriangle_ge_of_outer_tip_bound hk hk1
    (show 0 ≤ ER from le_max_right _ _) hpR.1 hpR.2 hER hL0
    (show ER / k - ((k - u) - (-a / 2)) ≤ L by linarith only [hclipR])
  have hIR : ER ^ 2 / (2 * k * (1 - k)) - k / 2 * L ^ 2 ≤
      ∫ x in (-a / 2)..(a / 2), affineCutTriangle k ER (k - u) (-x) := by
    rw [intervalIntegral.integral_comp_neg]
    simpa only [neg_div, neg_neg] using hIR₀
  have hIB := (show Continuous (fun x : ℝ =>
    max (min (u - k - x) (v - h - k + x)) 0) by fun_prop).intervalIntegrable (-a / 2) (a / 2)
  have hITL := (continuous_affineCutTriangle k EL (k - v + h)).intervalIntegrable (-a / 2) (a / 2)
  have hITR := ((continuous_affineCutTriangle k ER (k - u)).comp continuous_neg).intervalIntegrable
    (-a / 2) (a / 2)
  have hi := intervalIntegral.integral_mono_on (by linarith only [ha] : -a / 2 ≤ a / 2)
    ((hIB.add hITL).add hITR) ((continuous_threeAngleBarrier U).intervalIntegrable _ _)
    (fun x (_ : x ∈ Icc (-a / 2) (a / 2)) =>
      hU.diagonal_two_tails_le_threeAngleBarrier hk hk1 hksq hkoffset hu hv
        hcompR hcompL hη hendL hendR hL hR x)
  rw [intervalIntegral.integral_add (hIB.add hITL) hITR,
    intervalIntegral.integral_add hIB hITL, integral_tilted_diagonal_tent k hd] at hi
  have heq : nearTriangleCoefficient k * (EL ^ 2 + ER ^ 2) =
      EL ^ 2 / (2 * k * (1 - k)) + ER ^ 2 / (2 * k * (1 - k)) := by
    unfold nearTriangleCoefficient
    ring
  change _ + nearTriangleCoefficient k * (EL ^ 2 + ER ^ 2) - k * L ^ 2 ≤ _
  rw [heq]
  linarith only [hi, hIL, hIR]

end AmbidextrousSofa
