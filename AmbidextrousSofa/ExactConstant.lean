module

public import Mathlib

@[expose] public section

/-!
# The exact ambidextrous reference constant

This file begins the formalization of the constant used in the Gate 3 manuscript.
The polynomial has a unique real root, which is positive and lies strictly between
`2 / 7` and `3 / 10`. The definitions of `Y`, `beta`, and `M` use that proved
existence result; no area or optimality statement is assumed here.

This is an uncompiled draft. External declaration signatures were inspected in
Mathlib revision `c55e6e786f49471c72fbddbec5415808896aec1e`.
-/

noncomputable section

namespace AmbidextrousSofa

/-- The cubic polynomial determining the reference parameter. -/
def cubic (y : ℝ) : ℝ := 4 * y ^ 3 + 3 * y - 1

/-- The reference cubic is strictly increasing on the entire real line. -/
theorem cubic_strictMono : StrictMono cubic := fun x y hxy => by
  unfold cubic; nlinarith [sq_nonneg (x + y), sq_nonneg (x - y)]

/-- The intermediate value theorem supplies a positive root. -/
theorem exists_positive_root : ∃ y : ℝ, 0 < y ∧ cubic y = 0 := by
  obtain ⟨y, hy, heq⟩ := intermediate_value_Icc (by norm_num : (2 / 7 : ℝ) ≤ 3 / 10)
    (by unfold cubic; fun_prop : Continuous cubic).continuousOn
    (by norm_num [cubic] : (0 : ℝ) ∈ Set.Icc (cubic (2 / 7)) (cubic (3 / 10)))
  exact ⟨y, by linarith [hy.1], heq⟩

/-- The reference parameter, selected from the proved positive-root existence. -/
def Y : ℝ := Classical.choose exists_positive_root

/-- The selected parameter is positive. -/
theorem Y_pos : 0 < Y := (Classical.choose_spec exists_positive_root).1

/-- The selected parameter is a root of the cubic. -/
theorem Y_cubic : cubic Y = 0 := (Classical.choose_spec exists_positive_root).2

/-- The defining equation in the form used by the manuscript. -/
theorem Y_equation : 4 * Y ^ 3 + 3 * Y = 1 := sub_eq_zero.mp Y_cubic

/-- Every real solution of the cubic is the selected parameter. -/
theorem eq_Y_of_cubic_eq_zero {y : ℝ} (hy : cubic y = 0) : y = Y :=
  cubic_strictMono.injective (hy.trans Y_cubic.symm)

/-- The lower rational bound used in the geometric reference construction. -/
theorem two_sevenths_lt_Y : (2 / 7 : ℝ) < Y :=
  cubic_strictMono.lt_iff_lt.mp (by rw [Y_cubic]; norm_num [cubic])

/-- The upper rational bound used in the geometric reference construction. -/
theorem Y_lt_three_tenths : Y < (3 / 10 : ℝ) :=
  cubic_strictMono.lt_iff_lt.mp (by rw [Y_cubic]; norm_num [cubic])

/-- The parameter is nonzero, as needed for later reciprocal formulas. -/
theorem Y_ne_zero : Y ≠ 0 := Y_pos.ne'

/-- The reference switching angle. -/
def beta : ℝ := Real.arctan Y

/-- The reference switching angle is positive. -/
theorem beta_pos : 0 < beta := Real.arctan_pos.mpr Y_pos

/-- The switching angle is strictly less than a quarter turn. -/
theorem beta_lt_pi_div_two : beta < Real.pi / 2 := Real.arctan_lt_pi_div_two Y

/-- The reference switching angle lies before the midpoint of a quarter turn. -/
theorem beta_lt_pi_div_four : beta < Real.pi / 4 := by
  rw [beta, ← Real.arctan_one]
  exact Real.arctan_strictMono (by linarith [Y_lt_three_tenths])

/-- The trigonometric parameter recovers the cubic root exactly. -/
theorem tan_beta : Real.tan beta = Y := Real.tan_arctan Y

/-- The exact candidate area constant. This definition asserts no area bound. -/
def M : ℝ := 1 + 4 * Y ^ 2 + beta

/-- A first elementary lower bound on the reference constant. -/
theorem one_lt_M : 1 < M := by unfold M; linarith [sq_nonneg Y, beta_pos]

/-- A division-free form of the manuscript identity `M = 1 / Y - 2 + beta`. -/
theorem M_sub_beta_add_two_mul_Y : (M - beta + 2) * Y = 1 := by
  unfold M; linear_combination Y_equation

end AmbidextrousSofa
