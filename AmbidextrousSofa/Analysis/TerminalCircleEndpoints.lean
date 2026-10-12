module

public import AmbidextrousSofa.Analysis.CircleAverage

@[expose] public section

/-!
# Exact endpoint margins for the terminal circle comparison

Use the cosine of the established terminal-angle endpoint. Four unit-seed
Newton updates bound this root and its sine. The resulting gap is concave in
cap width, so two endpoint checks control the whole width interval.
The circle-height bounds at both endpoints use the same Newton formulas.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

/-- One Newton step gives an upper square-root bound; dividing the radicand
by that upper bound gives a lower bound. Both width endpoints use these same formulas. -/
def circleNewtonUpper (q x : ℝ) : ℝ := (x + q / x) / 2

def circleNewtonLower (q x : ℝ) : ℝ := q / circleNewtonUpper q x

/-- An upper bound for a circle average from rational bounds on its two endpoint heights. -/
theorem circleAverage_lt_of_heights {q y L R : ℝ} (hq : 0 < q)
    (hy : y ∈ Ioo (q / 2) (1 - q / 2)) (hL0 : 0 < L) (hL : 1 - (y - q / 2) ^ 2 < L ^ 2)
    (hR : R ^ 2 < 1 - (y + q / 2) ^ 2) :
    circleAverage q y < (L - R) / q := by
  rw [circleAverage_eq_height_difference hq hy, circleHeight, circleHeight]
  exact div_lt_div_of_pos_right
    (by linarith [(Real.sqrt_lt' hL0).2 hL, Real.lt_sqrt_of_sq_lt hR]) hq

/-- Use the unit circle's upper root bound as the starting value for every
endpoint root. All four updates are the same arithmetic operation. -/
def circleRootUpper (q : ℝ) : ℝ :=
  circleNewtonUpper q (circleNewtonUpper q (circleNewtonUpper q (circleNewtonUpper q 1)))

def circleRootLower (q : ℝ) : ℝ := q / circleRootUpper q

def terminalCircleCosine : ℝ := Real.sqrt (9 / 73)
def terminalCircleSine : ℝ := Real.sqrt (64 / 73)

/-- The common Newton procedure also supplies the sine price in the
cubic payment; no separate linear sine approximation is chosen. -/
def terminalCircleSineLower : ℝ := circleRootLower (64 / 73)

theorem terminalCircleSineLower_pos : 0 < terminalCircleSineLower := by
  norm_num [terminalCircleSineLower, circleRootLower, circleRootUpper, circleNewtonUpper]

theorem terminalCircleSineLower_le_of_slope {c s : ℝ}
    (hc : 0 ≤ c) (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1) (hcut : c ≤ 3 / 8 * s) :
    terminalCircleSineLower ≤ s := by
  have hq : terminalCircleSineLower ^ 2 ≤ (64 / 73 : ℝ) := by
    norm_num [terminalCircleSineLower, circleRootLower, circleRootUpper, circleNewtonUpper]
  nlinarith only [hq, hs, terminalCircleSineLower_pos,
    pow_le_pow_left₀ hc hcut 2, hcs]

/-- The actual circle gap at a cap width. Its minimum is forced to an
endpoint by concavity; it is not an independently chosen tolerance. -/
def terminalCircleEndpointGap (C : ℝ) : ℝ :=
  (2 * C - terminalCircleCosine) / terminalCircleSine -
    circleAverage terminalCircleCosine (C - terminalCircleCosine ^ 3 / 8)

def terminalCircleGap : ℝ :=
  min (terminalCircleEndpointGap (1 / 2)) (terminalCircleEndpointGap (37 / 50))

/-- The normalized price required by the angular overlap's cubic moment. -/
def terminalCubicPrice : ℝ :=
  ((4 / 5) * (2 / 3) ^ 3 * (3 / 8) ^ 2) / (6 * (2 / 3) * terminalCircleSineLower)

private def circleCosineUpper : ℝ := circleRootUpper (9 / 73)
private def circleCosineLower : ℝ := circleRootLower (9 / 73)
private def circleSineUpper : ℝ := circleRootUpper (64 / 73)

private theorem circleCosine_bounds {q : ℝ} (hq : 0 < q) (hq2 : q ^ 2 = 9 / 73) :
    circleCosineLower ≤ q ∧ q ≤ circleCosineUpper := by
  norm_num [circleCosineLower, circleCosineUpper, circleRootLower, circleRootUpper, circleNewtonUpper]
  constructor <;> nlinarith only [hq, hq2]

private theorem circle_gap_at_endpoint {C q S L R : ℝ}
    (hC0 : (1 / 2 : ℝ) ≤ C) (hC1 : C ≤ 37 / 50)
    (hq : 0 < q) (hq2 : q ^ 2 = 9 / 73) (hS : 0 < S) (hS2 : S ^ 2 = 64 / 73)
    (hL0 : 0 < L)
    (hL : 1 - (C - (1 / 2 + (9 / 73) / 8) * circleCosineUpper) ^ 2 < L ^ 2)
    (hR : R ^ 2 < 1 - (C + (1 / 2 - (9 / 73) / 8) * circleCosineUpper) ^ 2)
    (hdiff : 0 ≤ L - R)
    (hgap : terminalCubicPrice < (2 * C - circleCosineUpper) / circleSineUpper -
      (L - R) / circleCosineLower) :
    terminalCubicPrice < (2 * C - q) / S - circleAverage q (C - q ^ 3 / 8) := by
  obtain ⟨hql, hqu⟩ := circleCosine_bounds hq hq2
  have hqu1 : circleCosineUpper < 3 / 8 := by
    norm_num [circleCosineUpper, circleRootUpper, circleNewtonUpper]
  have hql0 : 0 < circleCosineLower := by
    norm_num [circleCosineLower, circleRootLower, circleRootUpper, circleNewtonUpper]
  have hsu0 : 0 < circleSineUpper := by norm_num [circleSineUpper, circleRootUpper, circleNewtonUpper]
  have hsu : S ≤ circleSineUpper := by
    have hsquare : (64 / 73 : ℝ) ≤ circleSineUpper ^ 2 := by
      norm_num [circleSineUpper, circleRootUpper, circleNewtonUpper]
    nlinarith only [hS, hS2, hsu0, hsquare]
  have hlinear : (2 * C - circleCosineUpper) / circleSineUpper ≤ (2 * C - q) / S := by
    apply (div_le_div_of_nonneg_left (by linarith only [hC0, hqu1]) hS hsu).trans
    exact div_le_div_of_nonneg_right (by linarith only [hqu]) hS.le
  have hqc : q ^ 3 / 8 = (9 / 73) * q / 8 := by linear_combination q / 8 * hq2
  have hy : C - q ^ 3 / 8 ∈ Ioo (q / 2) (1 - q / 2) := by
    rw [hqc]
    constructor <;> linarith only [hC0, hC1, hqu, hqu1, hq]
  have ha := circleAverage_lt_of_heights (q := q) (y := C - q ^ 3 / 8) (L := L) (R := R) hq hy hL0 (by
      rw [hqc]
      nlinarith only [hL, pow_le_pow_left₀ (by linarith only [hC0, hqu1] :
        0 ≤ C - (1 / 2 + (9 / 73) / 8) * circleCosineUpper)
        (by linarith only [hqu] : C - (1 / 2 + (9 / 73) / 8) * circleCosineUpper ≤
          C - (1 / 2 + (9 / 73) / 8) * q) 2]) (by
      rw [hqc]
      nlinarith only [hR, pow_le_pow_left₀ (by linarith only [hC0, hq] :
        0 ≤ C + (1 / 2 - (9 / 73) / 8) * q)
        (by linarith only [hqu] : C + (1 / 2 - (9 / 73) / 8) * q ≤
          C + (1 / 2 - (9 / 73) / 8) * circleCosineUpper) 2])
  have hdiv : (L - R) / q ≤ (L - R) / circleCosineLower := by
    rw [div_le_div_iff₀ hq hql0]
    nlinarith only [mul_nonneg hdiff (sub_nonneg.mpr hql)]
  linarith only [ha, hdiv, hgap, hlinear]

/-- The exact minimum circle gap pays the cubic overlap price. -/
theorem terminalCircleGap_gt_cubicPrice : terminalCubicPrice < terminalCircleGap := by
  have hq : 0 < terminalCircleCosine := Real.sqrt_pos.mpr (by norm_num)
  have hq2 : terminalCircleCosine ^ 2 = 9 / 73 := Real.sq_sqrt (by norm_num)
  have hS : 0 < terminalCircleSine := Real.sqrt_pos.mpr (by norm_num)
  have hS2 : terminalCircleSine ^ 2 = 64 / 73 := Real.sq_sqrt (by norm_num)
  have hends : ∀ C ∈ ({(1 / 2 : ℝ), 37 / 50} : Set ℝ), terminalCubicPrice < terminalCircleEndpointGap C := by
    intro C hC
    simp only [mem_insert_iff, mem_singleton_iff] at hC
    unfold terminalCircleEndpointGap
    rcases hC with hC | hC <;>
      apply circle_gap_at_endpoint (C := C)
        (L := circleRootUpper (1 - (C - (1 / 2 + (9 / 73) / 8) * circleCosineUpper) ^ 2))
        (R := circleRootLower (1 - (C + (1 / 2 - (9 / 73) / 8) * circleCosineUpper) ^ 2))
        (by rw [hC] <;> norm_num) (by rw [hC] <;> norm_num) hq hq2 hS hS2 <;>
      rw [hC] <;>
      norm_num [terminalCubicPrice, terminalCircleSineLower, circleCosineUpper, circleCosineLower,
        circleSineUpper, circleRootLower, circleRootUpper, circleNewtonUpper]
  exact lt_min (hends _ (by simp)) (hends _ (by simp))

theorem terminalCircleGap_pos : 0 < terminalCircleGap :=
  (by norm_num [terminalCubicPrice, terminalCircleSineLower, circleRootLower, circleRootUpper, circleNewtonUpper] : (0 : ℝ) < terminalCubicPrice).trans terminalCircleGap_gt_cubicPrice

/-- Concavity makes the actual minimum circle gap a bound throughout the width interval. -/
theorem terminal_circle_average_gap {q C : ℝ} (hq : 0 < q) (hq2 : q ^ 2 = 9 / 73)
    (hC0 : (1 / 2 : ℝ) ≤ C) (hC1 : C ≤ 37 / 50) :
    terminalCircleGap ≤ (2 * C - q) / terminalCircleSine - circleAverage q (C - q ^ 3 / 8) := by
  have hqeq : q = terminalCircleCosine := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 9 / 73)
    have hpos := Real.sqrt_nonneg (9 / 73 : ℝ)
    dsimp [terminalCircleCosine]
    nlinarith only [hq, hq2, hsq, hpos]
  have hq1 : q < 3 / 8 := by nlinarith only [hq, hq2]
  have hqc : q ^ 3 / 8 = (9 / 73) * q / 8 := by linear_combination q / 8 * hq2
  have h := (circleAverage_linear_gap_concave (q := q) (e := q ^ 3 / 8)
    (l := 1 / 2) (u := 37 / 50) (A := 2 / terminalCircleSine) (B := -q / terminalCircleSine)
    hq.le (by rw [hqc]; linarith only [hq1]) (by rw [hqc]; linarith only [hq1, hq])).min_le_of_mem_Icc
      (by norm_num) (by norm_num) ⟨hC0, hC1⟩
  rw [terminalCircleGap, terminalCircleEndpointGap, terminalCircleEndpointGap, ← hqeq]
  have hlin (x : ℝ) : (2 / terminalCircleSine) * x + (-q / terminalCircleSine) =
      (2 * x - q) / terminalCircleSine := by ring
  simpa only [hlin] using h

/-- The cotangent cut places the cosine below the same simple upper bound. -/
theorem terminal_cosine_lt_three_eighths {c : ℝ}
    (hc : 0 < c) (hcut : 73 * c ^ 2 ≤ 9) : c < (3 / 8 : ℝ) := by nlinarith

end AmbidextrousSofa
