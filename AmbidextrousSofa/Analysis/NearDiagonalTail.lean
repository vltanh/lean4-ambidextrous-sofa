module

public import AmbidextrousSofa.Analysis.ShortTailGeometry
public import AmbidextrousSofa.Analysis.ClippedTailIntegral

@[expose] public section

/-!
# Two literal additional niche tails

The diagonal niche floor and two actual nearby two-wall competitors
produce disjoint extra triangles. Their inner tips lie on their own
side of the diagonal apex. Only the outer tips can leave the middle
window, and their omitted areas are retained in the integral bound.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem near_tail_add_floor_le {k E p A B x n : ℝ}
    (hk : 0 < k) (hk1 : k < 1) (hksq : k ^ 2 + 2 * k = 1)
    (hfloor : max (x - p) 0 ≤ n)
    (hcomp : E / k ≤ A - p) (hpeak : 0 < E → E - k * p ≤ B)
    (hwall : min ((A - x) / k) (B + k * x) ≤ n) :
    max (x - p) 0 + affineCutTriangle k E p x ≤ n := by
  rcases le_or_gt E 0 with hE | hE
  · rwa [affineCutTriangle_eq_zero_of_height_nonpos hk.le hk1.le hE, add_zero]
  rcases le_or_gt (p + E / (1 - k)) x with hx | hx
  · rwa [affineCutTriangle_eq_zero_of_right hk1 hx, add_zero]
  have hc := near_tail_companion_bound hk hk1 hksq hcomp
    (show x - p ≤ E / (1 - k) by linarith only [hx])
  rw [sub_sub_sub_cancel_right] at hc
  exact affineCutTriangle_add_floor_le hfloor
    ((le_min hc (by linarith only [hpeak hE])).trans hwall)

theorem shortLeftTailHeight_peak {h k v δ : ℝ}
    (hη : (2 / 25 : ℝ) ≤ 1 - nearDiagonalNorm k + k ^ 2)
    (hE : 0 < shortLeftTailHeight k h δ) :
    shortLeftTailHeight k h δ - k * (k - v + h) ≤
      1 - h + k * v - δ - nearDiagonalNorm k := by
  rw [shortLeftTailHeight, max_eq_left ((lt_max_iff.mp hE).resolve_right (lt_irrefl 0)).le]
  linarith only [hη]

theorem shortRightTailHeight_peak {k u δ : ℝ}
    (hη : (2 / 25 : ℝ) ≤ 1 - nearDiagonalNorm k + k ^ 2)
    (hE : 0 < shortRightTailHeight δ) :
    shortRightTailHeight δ - k * (k - u) ≤
      1 + k * u - δ - nearDiagonalNorm k := by
  rw [shortRightTailHeight, max_eq_left ((lt_max_iff.mp hE).resolve_right (lt_irrefl 0)).le]
  linarith only [hη]

theorem IsDownwardCap.tilted_diagonal_tent_le_partialBarrier
    {U : Set Plane} (hU : IsDownwardCap U) {h k u v α : ℝ}
    (hk : k = Real.sqrt 2 - 1)
    (hu : diagonalRight U = 1 + u) (hv : diagonalLeft U = 1 - h + v)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α ≤ Real.pi / 2) (x : ℝ) :
    max (min (u - k - x) (v - h - k + x)) 0 ≤ partialBarrier U α x := by
  have hbound := hU.diagonal_tent_le_partialBarrier hα0 hαL x
  rw [hu, hv, show Real.sqrt 2 = k + 1 by linarith only [hk], ← min_symmetric_lines] at hbound
  convert hbound using 4 <;> ring

/-- Exact integration of both actual extra tails, including the two
possible omitted outer tips. -/
theorem IsDownwardCap.partialBarrier_integral_ge_diagonal_two_tails
    {U : Set Plane} (hU : IsDownwardCap U) {a h k u v α L : ℝ}
    (ha : 0 < a) (hk : 0 < k) (hk1 : k < 1) (hksq : k ^ 2 + 2 * k = 1)
    (hkoffset : k = Real.sqrt 2 - 1)
    (hαnear : Real.pi / 2 - Real.arctan k ≤ α) (hαL : α ≤ Real.pi / 2)
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
      ∫ x in (-a / 2)..(a / 2), partialBarrier U α x := by
  set EL := shortLeftTailHeight k h (nearDiagonalLeftDeficit U h k v)
  set ER := shortRightTailHeight (nearDiagonalRightDeficit U k u)
  -- The actual nearby support competitors add two disjoint triangles to the diagonal niche floor.
  have hpt (x : ℝ) : max (min (u - k - x) (v - h - k + x)) 0 +
      affineCutTriangle k EL (k - v + h) x + affineCutTriangle k ER (k - u) (-x) ≤
        partialBarrier U α x := by
    have hfloor := hU.tilted_diagonal_tent_le_partialBarrier hkoffset hu hv
      (by linarith only [arctan_le_complement_arctan hk1.le, hαnear]) hαL x
    rcases le_or_gt x ((u - v + h) / 2) with hx | hx
    · rw [min_eq_right (by linarith only [hx]), show v - h - k + x = x - (k - v + h) by ring]
        at hfloor ⊢
      rw [affineCutTriangle_eq_zero_of_right hk1
        (hendR.trans (by linarith only [hx] : _ ≤ -x)), add_zero]
      exact near_tail_add_floor_le hk hk1 hksq hfloor (by linarith only [hL])
        (shortLeftTailHeight_peak hη)
        (hU.nearDiagonal_left_competitor_le hk hk1.le hαnear hαL hcompR x)
    · rw [min_eq_left (by linarith only [hx]), show u - k - x = -x - (k - u) by ring]
        at hfloor ⊢
      rw [affineCutTriangle_eq_zero_of_right hk1 (hendL.trans hx.le), add_zero]
      exact near_tail_add_floor_le (A := v + k * (1 - h) - nearDiagonalNorm k) hk hk1 hksq hfloor
        (by linarith only [hR]) (shortRightTailHeight_peak hη)
        (by simpa only [sub_neg_eq_add, mul_neg, ← sub_eq_add_neg] using
          hU.nearDiagonal_right_competitor_le hk hαnear hαL hcompL x)
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
    ((hIB.add hITL).add hITR)
    (hU.intervalIntegrable_partialBarrier
      ((sub_pos.mpr (Real.arctan_lt_pi_div_two k)).trans_le hαnear) hαL _ _)
    hpt
  rw [intervalIntegral.integral_add (hIB.add hITL) hITR,
    intervalIntegral.integral_add hIB hITL, integral_tilted_diagonal_tent k hd] at hi
  simp only [Function.comp_apply] at hi
  rw [nearTriangleCoefficient, one_div_mul_eq_div, add_div]
  linarith only [hi, hIL, hIR]

end AmbidextrousSofa
