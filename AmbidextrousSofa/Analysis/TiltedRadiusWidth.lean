module

public import AmbidextrousSofa.Analysis.TiltedBalanceHeight

@[expose] public section

/-!
# The width determined by the initial-circle radius

At the small-height boundary, a dry low endpoint gives the smallest
possible initial momentum. The squared-radius bound five then determines
the comparison width. Its Newton bounds serve both the floor-energy
test and the three-triangle exclusion; no separate width tolerance is chosen.
-/

noncomputable section

attribute [local simp]
  AmbidextrousSofa.Analysis.tiltedBalanceMomentum
  AmbidextrousSofa.Analysis.tiltedBalanceFloorOffset
  AmbidextrousSofa.Analysis.tiltedBalanceGap
  AmbidextrousSofa.Analysis.tiltedBalanceDerivative
  AmbidextrousSofa.Analysis.tiltedBalanceLowerStep
  AmbidextrousSofa.Analysis.tiltedBalanceUpperStep
  AmbidextrousSofa.Analysis.tiltedBalanceLower₁
  AmbidextrousSofa.Analysis.tiltedBalanceUpper₁
  AmbidextrousSofa.Analysis.tiltedBalanceLower₂
  AmbidextrousSofa.Analysis.tiltedBalanceUpper₂
  AmbidextrousSofa.Analysis.tiltedBalanceLower
  AmbidextrousSofa.Analysis.tiltedBalanceUpper

namespace AmbidextrousSofa.Analysis

def tiltedRadiusMomentum : ℝ := tiltedBalanceMomentum tiltedBalanceHeight
def tiltedRadiusSquare : ℝ := 5 - tiltedRadiusMomentum ^ 2
@[local simp] abbrev tiltedRadiusSquareLower : ℝ := 5 - tiltedBalanceMomentum tiltedBalanceLower ^ 2
@[local simp] abbrev tiltedRadiusSquareUpper : ℝ := 5 - tiltedBalanceMomentum tiltedBalanceUpper ^ 2
def tiltedRadiusSpanUpper : ℝ := squareRootNewton tiltedRadiusSquareUpper (squareRootNewton tiltedRadiusSquareUpper 2)
def tiltedRadiusSpanLower : ℝ := tiltedRadiusSquareLower / tiltedRadiusSpanUpper
def tiltedRadiusWidth : ℝ := Real.sqrt tiltedRadiusSquare / 3

/-- The pressure-derived radius increases throughout the balance bracket. -/
theorem tiltedRadius_square_bounds :
    tiltedRadiusSquareLower ≤ tiltedRadiusSquare ∧ tiltedRadiusSquare ≤ tiltedRadiusSquareUpper := by
  obtain ⟨hl, hu⟩ := tiltedBalanceHeight_bounds
  have hmono {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 3))
      (hy : y ∈ Set.Icc (0 : ℝ) (1 / 3)) (hxy : x ≤ y) :
      5 - tiltedBalanceMomentum x ^ 2 ≤ 5 - tiltedBalanceMomentum y ^ 2 := by
    have hdiff : 0 ≤ tiltedBalanceMomentum y - tiltedBalanceMomentum x := by
      dsimp [tiltedBalanceMomentum]; linarith only [hxy]
    have hsum : 0 ≤ -(tiltedBalanceMomentum y + tiltedBalanceMomentum x) := by
      dsimp [tiltedBalanceMomentum]; linarith only [hx.2, hy.2]
    nlinarith only [mul_nonneg hdiff hsum]
  have hL : tiltedBalanceLower ∈ Set.Icc (0 : ℝ) (1 / 3) := by
    norm_num [tiltedBalanceGap, tiltedBalanceFloorOffset, tiltedBalanceDerivative]
  have hU : tiltedBalanceUpper ∈ Set.Icc (0 : ℝ) (1 / 3) := by
    norm_num [tiltedBalanceGap, tiltedBalanceFloorOffset, tiltedBalanceDerivative]
  exact ⟨hmono hL tiltedBalanceHeight_mem hl, hmono tiltedBalanceHeight_mem hU hu⟩

private theorem sqrt_lt_two_Newton {q : ℝ} (hq4 : 4 < q) :
    Real.sqrt q < squareRootNewton q (squareRootNewton q 2) := by
  have hq : 0 ≤ q := by linarith only [hq4]
  have hs := Real.sq_sqrt hq
  have h1 := sqrt_lt_Newton_of_seed_ne hq (by norm_num : (0 : ℝ) < 2)
    (by norm_num; linarith only [hq4] : (2 : ℝ) ^ 2 ≠ q)
  have hp1 : 0 < squareRootNewton q 2 := (Real.sqrt_nonneg _).trans_lt h1
  have hn1 : (squareRootNewton q 2) ^ 2 ≠ q := by
    have hsum : 0 < squareRootNewton q 2 + Real.sqrt q := by
      linarith only [h1, Real.sqrt_nonneg q]
    nlinarith only [hs, mul_pos (sub_pos.mpr h1) hsum]
  exact sqrt_lt_Newton_of_seed_ne hq hp1 hn1

private theorem sqrt_between_radius_bounds {qL q qU R : ℝ}
    (hL : 0 < qL) (hl : qL ≤ q) (hu : q ≤ qU)
    (hR : Real.sqrt qU < R) : qL / R < Real.sqrt q ∧ Real.sqrt q < R := by
  have hp : 0 < R := (Real.sqrt_nonneg _).trans_lt hR
  have hU : 0 ≤ qU := by linarith only [hL, hl, hu]
  have hup : qU < R ^ 2 := by
    have hsum : 0 < R + Real.sqrt qU := by linarith only [hR, Real.sqrt_nonneg qU]
    nlinarith only [Real.sq_sqrt hU, mul_pos (sub_pos.mpr hR) hsum]
  have hlo : (qL / R) ^ 2 < q := by
    rw [div_pow, div_lt_iff₀ (sq_pos_of_pos hp)]
    have hless := mul_lt_mul_of_pos_right (hl.trans_lt (hu.trans_lt hup)) hL
    nlinarith only [hless, mul_le_mul_of_nonneg_right hl (sq_nonneg R)]
  exact ⟨Real.lt_sqrt_of_sq_lt hlo, (Real.sqrt_le_sqrt hu).trans_lt hR⟩

theorem tiltedRadius_root_bounds :
    tiltedRadiusSpanLower < Real.sqrt tiltedRadiusSquare ∧
      Real.sqrt tiltedRadiusSquare < tiltedRadiusSpanUpper := by
  exact sqrt_between_radius_bounds (by norm_num : (0 : ℝ) < tiltedRadiusSquareLower)
    tiltedRadius_square_bounds.1 tiltedRadius_square_bounds.2
    (sqrt_lt_two_Newton (by norm_num : (4 : ℝ) < tiltedRadiusSquareUpper))

theorem tiltedRadiusSquare_pos : 0 < tiltedRadiusSquare := by
  have h := tiltedRadius_square_bounds.1
  norm_num [tiltedBalanceLower, tiltedBalanceGap, tiltedBalanceFloorOffset, tiltedBalanceDerivative] at h
  linarith only [h]

theorem tiltedRadiusMomentum_neg : tiltedRadiusMomentum < 0 := by
  have h := tiltedBalanceHeight_mem.2
  unfold tiltedRadiusMomentum tiltedBalanceMomentum
  linarith only [h]

theorem tiltedRadiusWidth_sq :
    9 * tiltedRadiusWidth ^ 2 = 5 - tiltedRadiusMomentum ^ 2 := by
  have h := Real.sq_sqrt tiltedRadiusSquare_pos.le
  unfold tiltedRadiusWidth tiltedRadiusSquare at *
  nlinarith

theorem tiltedRadiusWidth_bounds :
    tiltedRadiusSpanLower / 3 < tiltedRadiusWidth ∧
      tiltedRadiusWidth < tiltedRadiusSpanUpper / 3 := by
  unfold tiltedRadiusWidth
  exact ⟨div_lt_div_of_pos_right tiltedRadius_root_bounds.1 (by norm_num),
    div_lt_div_of_pos_right tiltedRadius_root_bounds.2 (by norm_num)⟩

theorem tiltedRadiusWidth_pos : 0 < tiltedRadiusWidth := by
  have h := tiltedRadiusSquare_pos
  unfold tiltedRadiusWidth
  positivity

/-- Coarse brackets used only for the common triangle clipping checks. -/
theorem tiltedRadius_comparison_brackets :
    (73 / 50 : ℝ) ≤ 2 * tiltedRadiusSpanLower / 3 ∧
      2 * tiltedRadiusSpanLower / 3 ≤ (37 / 25 : ℝ) ∧
      tiltedRadiusSpanUpper / 3 < (37 / 50 : ℝ) := by
  norm_num [tiltedRadiusSpanLower, tiltedRadiusSpanUpper, tiltedBalanceLower, tiltedBalanceUpper,
    tiltedBalanceGap, tiltedBalanceFloorOffset, tiltedBalanceDerivative, squareRootNewton]

end AmbidextrousSofa.Analysis
