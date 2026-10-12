module

public import AmbidextrousSofa.Analysis.ExactEstimates

@[expose] public section

/-!
# The height where the two initial energy tests balance

The dry endpoint bounds momentum between `b` and `b + 1/4`. At radius
`√(5-b²)`, the upper floor test meets four at one height in the canonical
interval. Squaring that positive comparison gives a decreasing polynomial.
Newton brackets start from the already proved canonical height interval.
-/

noncomputable section

open Set

namespace AmbidextrousSofa.Analysis

abbrev tiltedBalanceMomentum (h : ℝ) : ℝ := -1 / 2 + 5 * h / 4

abbrev tiltedBalanceFloorOffset (h : ℝ) : ℝ :=
  (5 - tiltedBalanceMomentum h ^ 2) + (tiltedBalanceMomentum h + 1 / 4) ^ 2 +
    (tiltedBalanceMomentum h + 1 / 4) * (1 - h) - 4

abbrev tiltedBalanceGap (h : ℝ) : ℝ :=
  tiltedBalanceFloorOffset h ^ 2 - (5 - tiltedBalanceMomentum h ^ 2) * h * (2 - h)

abbrev tiltedBalanceDerivative (h : ℝ) : ℝ := (-455 + 686 * h - 180 * h ^ 2) / 64

private def balanceDifference (x y : ℝ) : ℝ :=
  -455 / 64 + 343 / 64 * (x + y) - 15 / 16 * (x ^ 2 + x * y + y ^ 2)

private theorem balance_difference (x y : ℝ) :
    tiltedBalanceGap x - tiltedBalanceGap y = (x - y) * balanceDifference x y := by
  unfold tiltedBalanceGap tiltedBalanceFloorOffset tiltedBalanceMomentum balanceDifference
  ring

theorem tiltedBalanceGap_strictAnti : StrictAntiOn tiltedBalanceGap (Icc 0 (1 / 3)) := by
  intro x hx y hy hxy
  have hneg : balanceDifference y x < 0 := by
    unfold balanceDifference
    nlinarith only [hx.2, hy.2, sq_nonneg x, sq_nonneg y, mul_nonneg hx.1 hy.1]
  have h := mul_neg_of_pos_of_neg (sub_pos.mpr hxy) hneg
  rw [← balance_difference] at h
  linarith only [h]

theorem exists_balance_height : ∃ h ∈ Icc (0 : ℝ) (1 / 3), tiltedBalanceGap h = 0 := by
  obtain ⟨h, hh, heq⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by unfold tiltedBalanceGap tiltedBalanceFloorOffset tiltedBalanceMomentum; fun_prop :
      Continuous tiltedBalanceGap).continuousOn
    (by norm_num [tiltedBalanceGap, tiltedBalanceFloorOffset, tiltedBalanceMomentum] :
      (0 : ℝ) ∈ Icc (tiltedBalanceGap (1 / 3)) (tiltedBalanceGap 0))
  exact ⟨h, hh, heq⟩

def tiltedBalanceHeight : ℝ := Classical.choose exists_balance_height

theorem tiltedBalanceHeight_mem : tiltedBalanceHeight ∈ Icc (0 : ℝ) (1 / 3) :=
  (Classical.choose_spec exists_balance_height).1

theorem tiltedBalanceHeight_gap : tiltedBalanceGap tiltedBalanceHeight = 0 :=
  (Classical.choose_spec exists_balance_height).2

theorem tiltedBalanceHeight_pos : 0 < tiltedBalanceHeight := by
  have h0 : tiltedBalanceGap 0 ≠ 0 := by
    norm_num [tiltedBalanceGap, tiltedBalanceFloorOffset, tiltedBalanceMomentum]
  exact lt_of_le_of_ne tiltedBalanceHeight_mem.1 (fun h => h0 (h ▸ tiltedBalanceHeight_gap))

private theorem balanceDerivative_neg {h : ℝ} (hh : h ∈ Icc (0 : ℝ) (1 / 3)) :
    tiltedBalanceDerivative h < 0 := by
  unfold tiltedBalanceDerivative
  nlinarith only [hh.2, sq_nonneg h]

private theorem balanceDifference_ge_derivative {l x y : ℝ}
    (hx : x ∈ Icc l (1 / 3)) (hy : y ∈ Icc l (1 / 3)) :
    tiltedBalanceDerivative l ≤ balanceDifference x y := by
  unfold tiltedBalanceDerivative balanceDifference
  nlinarith only [mul_nonneg (sub_nonneg.mpr hx.1)
      (by linarith only [hx.2, hy.2, hx.1] : 0 ≤ 343 / 64 - 15 / 16 * (x + y + l)),
    mul_nonneg (sub_nonneg.mpr hy.1)
      (by linarith only [hy.2, hx.2, hx.1] : 0 ≤ 343 / 64 - 15 / 16 * (y + 2 * l))]

abbrev tiltedBalanceLowerStep (l : ℝ) : ℝ := l - tiltedBalanceGap l / tiltedBalanceDerivative l
abbrev tiltedBalanceUpperStep (l u : ℝ) : ℝ := u - tiltedBalanceGap u / tiltedBalanceDerivative l

theorem tiltedBalance_bracket_step {l u : ℝ}
    (hl0 : 0 ≤ l) (hl : l ≤ tiltedBalanceHeight) (hu : tiltedBalanceHeight ≤ u) (hu1 : u ≤ 1 / 3) :
    tiltedBalanceLowerStep l ≤ tiltedBalanceHeight ∧
      tiltedBalanceHeight ≤ tiltedBalanceUpperStep l u := by
  have hd := balanceDerivative_neg ⟨hl0, hl.trans (hu.trans hu1)⟩
  have hdl := balanceDifference_ge_derivative ⟨le_rfl, hl.trans (hu.trans hu1)⟩
    ⟨hl, tiltedBalanceHeight_mem.2⟩
  have hdu := balanceDifference_ge_derivative ⟨hl.trans hu, hu1⟩
    ⟨hl, tiltedBalanceHeight_mem.2⟩
  have hfl := balance_difference l tiltedBalanceHeight
  have hfu := balance_difference u tiltedBalanceHeight
  rw [tiltedBalanceHeight_gap, sub_zero] at hfl hfu
  constructor
  · unfold tiltedBalanceLowerStep
    have hq : l - tiltedBalanceHeight ≤ tiltedBalanceGap l / tiltedBalanceDerivative l :=
      (le_div_iff_of_neg hd).mpr (by
        rw [hfl]
        exact mul_le_mul_of_nonpos_left hdl (sub_nonpos.mpr hl))
    linarith only [hq]
  · unfold tiltedBalanceUpperStep
    have hq : tiltedBalanceGap u / tiltedBalanceDerivative l ≤ u - tiltedBalanceHeight :=
      (div_le_iff_of_neg hd).mpr (by
        rw [hfu]
        exact mul_le_mul_of_nonneg_left hdu (sub_nonneg.mpr hu))
    linarith only [hq]

/-- Three common bracket updates from the canonical interval. -/
abbrev tiltedBalanceLower₁ : ℝ := tiltedBalanceLowerStep 0
abbrev tiltedBalanceUpper₁ : ℝ := tiltedBalanceUpperStep 0 (1 / 3)
abbrev tiltedBalanceLower₂ : ℝ := tiltedBalanceLowerStep tiltedBalanceLower₁
abbrev tiltedBalanceUpper₂ : ℝ := tiltedBalanceUpperStep tiltedBalanceLower₁ tiltedBalanceUpper₁
abbrev tiltedBalanceLower : ℝ := tiltedBalanceLowerStep tiltedBalanceLower₂
abbrev tiltedBalanceUpper : ℝ := tiltedBalanceUpperStep tiltedBalanceLower₂ tiltedBalanceUpper₂

theorem tiltedBalanceHeight_bounds : tiltedBalanceLower ≤ tiltedBalanceHeight ∧
    tiltedBalanceHeight ≤ tiltedBalanceUpper := by
  have h1 := tiltedBalance_bracket_step (by norm_num) tiltedBalanceHeight_mem.1
    tiltedBalanceHeight_mem.2 (by norm_num)
  have h2 := tiltedBalance_bracket_step
    (by norm_num [tiltedBalanceLower₁, tiltedBalanceLowerStep, tiltedBalanceGap,
      tiltedBalanceFloorOffset, tiltedBalanceMomentum, tiltedBalanceDerivative]) h1.1 h1.2
    (by norm_num [tiltedBalanceUpper₁, tiltedBalanceUpperStep, tiltedBalanceGap,
      tiltedBalanceFloorOffset, tiltedBalanceMomentum, tiltedBalanceDerivative])
  exact tiltedBalance_bracket_step
    (by norm_num [tiltedBalanceLower₂, tiltedBalanceLower₁, tiltedBalanceLowerStep,
      tiltedBalanceGap, tiltedBalanceFloorOffset, tiltedBalanceMomentum, tiltedBalanceDerivative])
    h2.1 h2.2
    (by norm_num [tiltedBalanceUpper₂, tiltedBalanceLower₁, tiltedBalanceUpper₁,
      tiltedBalanceUpperStep, tiltedBalanceLowerStep, tiltedBalanceGap,
      tiltedBalanceFloorOffset, tiltedBalanceMomentum, tiltedBalanceDerivative])

/-- A Newton square-root bound is strict unless the seed is already exact. -/
theorem sqrt_lt_Newton_of_seed_ne {q x : ℝ} (hq : 0 ≤ q) (hx : 0 < x) (hne : x ^ 2 ≠ q) :
    Real.sqrt q < squareRootNewton q x := by
  have hs := Real.sq_sqrt hq
  have hn : x - Real.sqrt q ≠ 0 := fun heq => hne (by rw [sub_eq_zero.mp heq, hs])
  have hdiff : squareRootNewton q x - Real.sqrt q = (x - Real.sqrt q) ^ 2 / (2 * x) := by
    unfold squareRootNewton
    field_simp [hx.ne']
    nlinarith only [hs]
  have hpos := div_pos (sq_pos_of_ne_zero hn) (by linarith only [hx] : 0 < 2 * x)
  rw [← hdiff] at hpos
  linarith only [hpos]

theorem tiltedBalanceHeight_energy_eq :
    (5 - tiltedBalanceMomentum tiltedBalanceHeight ^ 2) +
      (tiltedBalanceMomentum tiltedBalanceHeight + 1 / 4) ^ 2 +
      (tiltedBalanceMomentum tiltedBalanceHeight + 1 / 4) * (1 - tiltedBalanceHeight) -
      Real.sqrt (5 - tiltedBalanceMomentum tiltedBalanceHeight ^ 2) *
        Real.sqrt (tiltedBalanceHeight * (2 - tiltedBalanceHeight)) = 4 := by
  have hh := tiltedBalanceHeight_mem
  have hq : 0 ≤ tiltedBalanceHeight * (2 - tiltedBalanceHeight) :=
    mul_nonneg hh.1 (by linarith only [hh.2])
  have hr : 0 ≤ 5 - tiltedBalanceMomentum tiltedBalanceHeight ^ 2 := by
    unfold tiltedBalanceMomentum
    nlinarith only [hh.1, hh.2, mul_nonneg hh.1
      (by linarith only [hh.2] : 0 ≤ 1 - 5 * tiltedBalanceHeight / 4)]
  have hb : 0 ≤ tiltedBalanceFloorOffset tiltedBalanceHeight := by
    unfold tiltedBalanceFloorOffset tiltedBalanceMomentum
    nlinarith only [hh.1, mul_nonneg hh.1
      (by linarith only [hh.2] : 0 ≤ 17 / 8 - 5 * tiltedBalanceHeight / 4)]
  have hsq : (Real.sqrt (5 - tiltedBalanceMomentum tiltedBalanceHeight ^ 2) *
      Real.sqrt (tiltedBalanceHeight * (2 - tiltedBalanceHeight))) ^ 2 =
      (5 - tiltedBalanceMomentum tiltedBalanceHeight ^ 2) * tiltedBalanceHeight * (2 - tiltedBalanceHeight) := by
    rw [mul_pow, Real.sq_sqrt hr, Real.sq_sqrt hq]
    ring
  have heq := tiltedBalanceHeight_gap
  unfold tiltedBalanceGap at heq
  have hprod : Real.sqrt (5 - tiltedBalanceMomentum tiltedBalanceHeight ^ 2) *
      Real.sqrt (tiltedBalanceHeight * (2 - tiltedBalanceHeight)) =
      tiltedBalanceFloorOffset tiltedBalanceHeight := by
    nlinarith only [heq, hsq, hb, mul_nonneg (Real.sqrt_nonneg (5 - tiltedBalanceMomentum tiltedBalanceHeight ^ 2))
      (Real.sqrt_nonneg (tiltedBalanceHeight * (2 - tiltedBalanceHeight)))]
  rw [hprod]
  unfold tiltedBalanceFloorOffset
  ring

end AmbidextrousSofa.Analysis
