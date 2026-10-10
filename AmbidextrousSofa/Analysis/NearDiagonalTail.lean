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
  by_cases hE : E ≤ 0
  · rw [affineCutTriangle_eq_zero_of_height_nonpos hk.le hk1.le hE, add_zero]
    exact hfloor
  · have hEpos : 0 < E := lt_of_not_ge hE
    by_cases hx : p + E / (1 - k) ≤ x
    · rw [affineCutTriangle_eq_zero_of_right hk1 hx, add_zero]
      exact hfloor
    · have hz : x - p ≤ E / (1 - k) := by linarith [le_of_not_ge hx]
      have hc := near_tail_companion_bound hk hk1 hksq hcomp hz
      have hfirst : E + k * (x - p) ≤ (A - x) / k := by
        convert hc using 1 <;> congr 1 <;> ring
      have hsecond : E + k * (x - p) ≤ B + k * x := by
        nlinarith only [hpeak hEpos]
      exact affineCutTriangle_add_floor_le hfloor ((le_min hfirst hsecond).trans hwall)

theorem shortLeftTailHeight_peak {h k v δ : ℝ}
    (hη : (2 / 25 : ℝ) ≤ 1 - nearDiagonalNorm k + k ^ 2)
    (hE : 0 < shortLeftTailHeight k h δ) :
    shortLeftTailHeight k h δ - k * (k - v + h) ≤
      1 - h + k * v - δ - nearDiagonalNorm k := by
  have harg : 0 < (2 / 25 : ℝ) - (1 - k) * h - δ := by
    simpa only [shortLeftTailHeight, lt_max_iff, lt_self_iff_false, or_false] using hE
  rw [shortLeftTailHeight, max_eq_left harg.le]
  nlinarith only [hη]

theorem shortRightTailHeight_peak {k u δ : ℝ}
    (hη : (2 / 25 : ℝ) ≤ 1 - nearDiagonalNorm k + k ^ 2)
    (hE : 0 < shortRightTailHeight δ) :
    shortRightTailHeight δ - k * (k - u) ≤
      1 + k * u - δ - nearDiagonalNorm k := by
  have harg : 0 < (2 / 25 : ℝ) - δ := by
    simpa only [shortRightTailHeight, lt_max_iff, lt_self_iff_false, or_false] using hE
  rw [shortRightTailHeight, max_eq_left harg.le]
  nlinarith only [hη]

theorem IsDownwardCap.tilted_diagonal_tent_le_partialBarrier
    {U : Set Plane} (hU : IsDownwardCap U) {h k u v α : ℝ}
    (hk : k = Real.sqrt 2 - 1)
    (hu : diagonalRight U = 1 + u) (hv : diagonalLeft U = 1 - h + v)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α ≤ Real.pi / 2) (x : ℝ) :
    max (min (u - k - x) (v - h - k + x)) 0 ≤ partialBarrier U α x := by
  have hbound := hU.diagonal_tent_le_partialBarrier hα0 hαL x
  rw [← cornerWall_pi_div_four_eq_tent hU, cornerWall,
    firstWall_pi_div_four_eq_diagonal hU, secondWall_pi_div_four_eq_diagonal hU,
    hu, hv] at hbound
  have hsqrt : Real.sqrt 2 = k + 1 := by linarith only [hk]
  rw [hsqrt] at hbound
  convert hbound using 1 <;> congr 2 <;> ring

/-- The actual nearby support competitors add two disjoint triangles
to the complete diagonal niche floor. -/
theorem IsDownwardCap.diagonal_two_tails_le_partialBarrier
    {U : Set Plane} (hU : IsDownwardCap U) {h k u v α : ℝ}
    (hk : 0 < k) (hk1 : k < 1) (hksq : k ^ 2 + 2 * k = 1)
    (hkoffset : k = Real.sqrt 2 - 1)
    (hαnear : Real.pi / 2 - Real.arctan k ≤ α) (hαL : α ≤ Real.pi / 2)
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
        (k - u) (-x) ≤ partialBarrier U α x := by
  have hatan := Real.arctan_strictMono.monotone hk1.le
  rw [Real.arctan_one] at hatan
  have hα0 : Real.pi / 4 ≤ α := by linarith only [hatan, hαnear]
  have hfloor := hU.tilted_diagonal_tent_le_partialBarrier hkoffset hu hv hα0 hαL x
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
    · exact hU.nearDiagonal_left_competitor_le hk hk1.le hαnear hαL hcompR x
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
    · simpa only [sub_neg_eq_add, mul_neg, ← sub_eq_add_neg] using
        hU.nearDiagonal_right_competitor_le hk hαnear hαL hcompL x

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
    max (min (u - k - x) (v - h - k + x)) 0) by fun_prop).intervalIntegrable (μ := volume)
      (-a / 2) (a / 2)
  have hITL := (continuous_affineCutTriangle k EL (k - v + h)).intervalIntegrable
    (μ := volume) (-a / 2) (a / 2)
  have hITR := ((continuous_affineCutTriangle k ER (k - u)).comp continuous_neg).intervalIntegrable
    (μ := volume) (-a / 2) (a / 2)
  have hi := intervalIntegral.integral_mono_on (by linarith : -a / 2 ≤ a / 2)
    ((hIB.add hITL).add hITR)
    (hU.intervalIntegrable_partialBarrier
      ((sub_pos.mpr (Real.arctan_lt_pi_div_two k)).trans_le hαnear) hαL _ _)
    (fun x (_ : x ∈ Icc (-a / 2) (a / 2)) =>
      hU.diagonal_two_tails_le_partialBarrier hk hk1 hksq hkoffset hαnear hαL hu hv
        hcompR hcompL hη hendL hendR hL hR x)
  rw [intervalIntegral.integral_add (hIB.add hITL) hITR,
    intervalIntegral.integral_add hIB hITL, integral_tilted_diagonal_tent k hd] at hi
  simp only [Function.comp_apply] at hi
  have heq : nearTriangleCoefficient k * (EL ^ 2 + ER ^ 2) =
      EL ^ 2 / (2 * k * (1 - k)) + ER ^ 2 / (2 * k * (1 - k)) := by
    unfold nearTriangleCoefficient
    ring
  change _ + nearTriangleCoefficient k * (EL ^ 2 + ER ^ 2) - k * L ^ 2 ≤ _
  rw [heq]
  linarith only [hi, hIL, hIR]

end AmbidextrousSofa
