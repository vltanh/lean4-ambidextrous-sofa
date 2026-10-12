module

public import AmbidextrousSofa.ExactConstant

@[expose] public section

/-!
# Generated enclosures and exact cuts below the reference constant

These inequalities use a polynomial lower bound for arctangent and the exact
cubic equation. Newton brackets generate the sharper comparisons with the
reference area. The diagonal offset uses a common Newton enclosure and its
quadratic equation; no floating-point comparison is used.
-/

noncomputable section

namespace AmbidextrousSofa

/-- One Newton step enclosing a positive square root. -/
abbrev squareRootNewton (q x : ℝ) : ℝ := (x + q / x) / 2

/-- The diagonal offset enclosure, generated from the elementary seed `3/2`. -/
abbrev diagonalOffsetUpper : ℝ := squareRootNewton 2 (squareRootNewton 2 (3 / 2)) - 1

/-- The reciprocal of the square-root upper enclosure supplies a lower enclosure. -/
abbrev diagonalOffsetLower : ℝ := 2 / (diagonalOffsetUpper + 1) - 1

/-- A positive Newton seed always supplies a square-root upper bound. -/
theorem sqrt_le_squareRootNewton {q x : ℝ} (hq : 0 ≤ q) (hx : 0 < x) :
    Real.sqrt q ≤ squareRootNewton q x := by
  have h : 2 * Real.sqrt q - x ≤ q / x :=
    (le_div_iff₀ hx).2 (by nlinarith [Real.sq_sqrt hq, sq_nonneg (x - Real.sqrt q)])
  unfold squareRootNewton
  linarith only [h]

/-- The lower Newton enclosure uses the derivative at the lower endpoint. -/
def cubicBracketLower (l u : ℝ) : ℝ := u - cubic u / (3 + 12 * l ^ 2)

/-- The upper Newton enclosure uses the derivative at the upper endpoint. -/
def cubicBracketUpper (u : ℝ) : ℝ := u - cubic u / (3 + 12 * u ^ 2)

/-- Convexity of the reference cubic turns one bracket into a tighter bracket.
The proof uses its divided difference, rather than a chosen decimal enclosure. -/
theorem cubic_bracket_step {l u : ℝ} (hl0 : 0 ≤ l) (hl : l ≤ Y) (hu : Y ≤ u) :
    cubicBracketLower l u ≤ Y ∧ Y ≤ cubicBracketUpper u := by
  have hu0 : 0 ≤ u := Y_pos.le.trans hu
  have hfactor : cubic u = (u - Y) * (3 + 4 * (u ^ 2 + u * Y + Y ^ 2)) := by
    unfold cubic
    linear_combination Y_equation
  have hlo : 3 + 12 * l ^ 2 ≤ 3 + 4 * (u ^ 2 + u * Y + Y ^ 2) := by
    nlinarith [mul_nonneg (sub_nonneg.2 (hl.trans hu)) (by linarith : 0 ≤ u + l),
      mul_nonneg (sub_nonneg.2 hl) (by linarith [Y_pos] : 0 ≤ Y + l),
      mul_nonneg (sub_nonneg.2 (hl.trans hu)) Y_pos.le,
      mul_nonneg (sub_nonneg.2 hl) hl0]
  have hhi : 3 + 4 * (u ^ 2 + u * Y + Y ^ 2) ≤ 3 + 12 * u ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hu) (by linarith [Y_pos] : 0 ≤ u + Y),
      mul_nonneg (sub_nonneg.2 hu) hu0]
  have hlow : u - Y ≤ cubic u / (3 + 12 * l ^ 2) :=
    (le_div_iff₀ (by positivity)).2 (by
      rw [hfactor]
      exact mul_le_mul_of_nonneg_left hlo (sub_nonneg.2 hu))
  have hhigh : cubic u / (3 + 12 * u ^ 2) ≤ u - Y :=
    (div_le_iff₀ (by positivity)).2 (by
      rw [hfactor]
      exact mul_le_mul_of_nonneg_left hhi (sub_nonneg.2 hu))
  constructor
  · unfold cubicBracketLower; linarith
  · unfold cubicBracketUpper; linarith

/-- Two applications from the elementary bracket `[1/4, 1/3]`.
The endpoints remain formulas, so their otherwise long fractions never
become independent constants in the argument. -/
def referenceRootLower : ℝ :=
  cubicBracketLower (cubicBracketLower (1 / 4) (1 / 3)) (cubicBracketUpper (1 / 3))

theorem referenceRootLower_nonneg : 0 ≤ referenceRootLower := by
  norm_num [referenceRootLower, cubicBracketLower, cubicBracketUpper, cubic]

theorem referenceRootLower_le_Y : referenceRootLower ≤ Y := by
  have hl : (1 / 4 : ℝ) ≤ Y :=
    (cubic_strictMono.lt_iff_lt.mp (by rw [Y_cubic]; norm_num [cubic])).le
  have hu : Y ≤ (1 / 3 : ℝ) :=
    (cubic_strictMono.lt_iff_lt.mp (by rw [Y_cubic]; norm_num [cubic])).le
  have h := cubic_bracket_step (by norm_num : (0 : ℝ) ≤ 1 / 4)
    hl hu
  exact (cubic_bracket_step
    (by norm_num [cubicBracketLower, cubic]) h.1 h.2).1

theorem referenceRootLower_lt_Y : referenceRootLower < Y := by
  apply cubic_strictMono.lt_iff_lt.mp
  rw [Y_cubic]
  norm_num [referenceRootLower, cubicBracketLower, cubicBracketUpper, cubic]

theorem self_sub_cube_div_three_le_arctan {y : ℝ} (hy : 0 ≤ y) :
    y - y ^ 3 / 3 ≤ Real.arctan y := by
  have h := monotone_of_hasDerivAt_nonneg (fun x => (Real.hasDerivAt_arctan x).sub
    ((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 3))) fun x => by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + x ^ 2)).2
        (by nlinarith [sq_nonneg (x ^ 2)] : (1 - x ^ 2) * (1 + x ^ 2) ≤ 1)
      norm_num [← one_div]
      linarith
  simpa using h hy

/-- A formula-generated lower bound for the reference half-area. -/
def referenceHalfAreaLower : ℝ :=
  (1 + 4 * referenceRootLower ^ 2 + referenceRootLower - referenceRootLower ^ 3 / 3) / 2

theorem referenceHalfAreaLower_lt_half_M : referenceHalfAreaLower < M / 2 := by
  have hy := referenceRootLower_lt_Y
  have h0 := referenceRootLower_nonneg
  have hbeta : referenceRootLower - referenceRootLower ^ 3 / 3 < beta :=
    (self_sub_cube_div_three_le_arctan h0).trans_lt (Real.arctan_lt_arctan_iff.mpr hy)
  unfold referenceHalfAreaLower M
  nlinarith [mul_nonneg (sub_nonneg.2 hy.le) (by linarith [Y_pos] : 0 ≤ Y + referenceRootLower)]

theorem referenceHalfAreaLower_le_half_M : referenceHalfAreaLower ≤ M / 2 :=
  referenceHalfAreaLower_lt_half_M.le

/-- The cubic lower estimate is already strong enough to cross `8/5`. -/
theorem eight_fifths_lt_M : (8 / 5 : ℝ) < M := by
  unfold M
  linarith [show Y - Y ^ 3 / 3 ≤ beta from self_sub_cube_div_three_le_arctan Y_pos.le,
    Y_equation, two_sevenths_lt_Y,
    mul_pos (sub_pos.mpr two_sevenths_lt_Y) (by linarith [Y_pos] : (0 : ℝ) < Y + 2 / 7)]

theorem sqrt_two_lt_M : Real.sqrt 2 < M :=
  ((Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)).trans eight_fifths_lt_M

theorem sqrt_two_sub_one_bounds :
    (diagonalOffsetLower : ℝ) < Real.sqrt 2 - 1 ∧ Real.sqrt 2 - 1 < (diagonalOffsetUpper) ∧
      Real.sqrt 2 - 1 < 29 / 70 := by
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hroot := Real.sqrt_nonneg (2 : ℝ)
  have hupper : Real.sqrt (2 : ℝ) < (diagonalOffsetUpper + 1) :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  exact ⟨by norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton]; nlinarith,
    by linarith only [hupper], by nlinarith⟩

theorem sqrt_two_sub_one_quadratic :
    (Real.sqrt 2 - 1) ^ 2 + 2 * (Real.sqrt 2 - 1) = (1 : ℝ) := by
  linear_combination Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)

/-- The coarse scalar certificates also lie below the generated reference budget. -/
theorem forty_one_fiftieths_lt_referenceHalfAreaLower :
    (41 / 50 : ℝ) < referenceHalfAreaLower := by
  norm_num [referenceHalfAreaLower, referenceRootLower, cubicBracketLower, cubicBracketUpper, cubic]

/-- `41/50 < M/2`, retained for scalar certificates using the coarse comparison. -/
theorem forty_one_fiftieths_lt_half_M : (41 / 50 : ℝ) < M / 2 :=
  forty_one_fiftieths_lt_referenceHalfAreaLower.trans referenceHalfAreaLower_lt_half_M

end AmbidextrousSofa
