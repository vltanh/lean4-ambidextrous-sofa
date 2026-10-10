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

/-- An exact factorization of the difference of two cubic values. -/
theorem cubic_sub_cubic (x y : ℝ) :
    cubic y - cubic x =
      (y - x) * (4 * (y ^ 2 + y * x + x ^ 2) + 3) := by
  unfold cubic
  ring

/-- The reference cubic is strictly increasing on the entire real line. -/
theorem cubic_strictMono : StrictMono cubic := by
  intro x y hxy
  have hfactor : 0 < 4 * (y ^ 2 + y * x + x ^ 2) + 3 := by
    nlinarith [sq_nonneg (x + y), sq_nonneg (x - y)]
  have hdiff : 0 < cubic y - cubic x := by
    rw [cubic_sub_cubic]
    exact mul_pos (sub_pos.mpr hxy) hfactor
  exact sub_pos.mp hdiff

/-- Continuity of the cubic, used in the intermediate value theorem. -/
theorem continuous_cubic : Continuous cubic := by
  unfold cubic
  fun_prop

/-- The intermediate value theorem supplies a positive root. -/
theorem exists_positive_root : ∃ y : ℝ, 0 < y ∧ cubic y = 0 := by
  have hab : (2 / 7 : ℝ) ≤ 3 / 10 := by norm_num
  have hzero : (0 : ℝ) ∈ Set.Icc (cubic (2 / 7)) (cubic (3 / 10)) := by
    norm_num [cubic]
  obtain ⟨y, hy, heq⟩ :=
    intermediate_value_Icc hab continuous_cubic.continuousOn hzero
  refine ⟨y, ?_, heq⟩
  linarith [hy.1]

/-- Any two real roots coincide; positivity is unnecessary for uniqueness. -/
theorem cubic_root_unique {x y : ℝ} (hx : cubic x = 0) (hy : cubic y = 0) :
    x = y :=
  cubic_strictMono.injective (hx.trans hy.symm)

/-- There is exactly one positive real root of the reference cubic. -/
theorem existsUnique_positive_root : ∃! y : ℝ, 0 < y ∧ cubic y = 0 := by
  obtain ⟨y, hy, heq⟩ := exists_positive_root
  refine ⟨y, ⟨hy, heq⟩, ?_⟩
  intro z hz
  exact cubic_root_unique hz.2 heq

/-- The reference parameter, selected from the proved positive-root existence. -/
def Y : ℝ := Classical.choose exists_positive_root

/-- The selected parameter is positive. -/
theorem Y_pos : 0 < Y :=
  (Classical.choose_spec exists_positive_root).1

/-- The selected parameter is a root of the cubic. -/
theorem Y_cubic : cubic Y = 0 :=
  (Classical.choose_spec exists_positive_root).2

/-- The defining equation in the form used by the manuscript. -/
theorem Y_equation : 4 * Y ^ 3 + 3 * Y = 1 := by
  have h := Y_cubic
  unfold cubic at h
  linarith

/-- Every real solution of the cubic is the selected parameter. -/
theorem eq_Y_of_cubic_eq_zero {y : ℝ} (hy : cubic y = 0) : y = Y :=
  cubic_root_unique hy Y_cubic

/-- A root characterization independent of the choice used to define `Y`. -/
theorem cubic_eq_zero_iff_eq_Y (y : ℝ) : cubic y = 0 ↔ y = Y := by
  constructor
  · exact eq_Y_of_cubic_eq_zero
  · intro h
    rw [h]
    exact Y_cubic

/-- The lower rational bound used in the geometric reference construction. -/
theorem two_sevenths_lt_Y : (2 / 7 : ℝ) < Y := by
  apply (cubic_strictMono.lt_iff_lt).mp
  rw [Y_cubic]
  norm_num [cubic]

/-- The upper rational bound used in the geometric reference construction. -/
theorem Y_lt_three_tenths : Y < (3 / 10 : ℝ) := by
  apply (cubic_strictMono.lt_iff_lt).mp
  rw [Y_cubic]
  norm_num [cubic]

/-- The parameter is nonzero, as needed for later reciprocal formulas. -/
theorem Y_ne_zero : Y ≠ 0 := ne_of_gt Y_pos

/-- A convenient consequence of the exact rational upper bound. -/
theorem Y_lt_one : Y < 1 := by
  linarith [Y_lt_three_tenths]

/-- The reference switching angle. -/
def beta : ℝ := Real.arctan Y

/-- The reference switching angle is positive. -/
theorem beta_pos : 0 < beta := by
  exact Real.arctan_pos.mpr Y_pos

/-- The switching angle is strictly less than a quarter turn. -/
theorem beta_lt_pi_div_two : beta < Real.pi / 2 := by
  exact Real.arctan_lt_pi_div_two Y

/-- The reference switching angle lies before the midpoint of a quarter turn. -/
theorem beta_lt_pi_div_four : beta < Real.pi / 4 := by
  change Real.arctan Y < Real.pi / 4
  rw [← Real.arctan_one]
  exact Real.arctan_lt_arctan_iff.mpr Y_lt_one

/-- The trigonometric parameter recovers the cubic root exactly. -/
theorem tan_beta : Real.tan beta = Y := by
  exact Real.tan_arctan Y

/-- The exact candidate area constant. This definition asserts no area bound. -/
def M : ℝ := 1 + 4 * Y ^ 2 + beta

/-- A first elementary lower bound on the reference constant. -/
theorem one_lt_M : 1 < M := by
  unfold M
  nlinarith [sq_nonneg Y, beta_pos]

/-- Positivity of the reference constant. -/
theorem M_pos : 0 < M := by
  linarith [one_lt_M]

/-- A division-free form of the manuscript identity `M = 1 / Y - 2 + beta`. -/
theorem M_sub_beta_add_two_mul_Y : (M - beta + 2) * Y = 1 := by
  calc
    (M - beta + 2) * Y = 4 * Y ^ 3 + 3 * Y := by
      unfold M
      ring
    _ = 1 := Y_equation

end AmbidextrousSofa
