module

public import AmbidextrousSofa.Analysis.ExactEstimates

@[expose] public section

/-!
# Exact rational bounds for the horizontal leakage exclusion

The seven rows below contain only explicit rational data and polynomial
inequalities. They bound the quadratic excess envelope, its first two
moments, the first crossing time and the box angle. The final scalar
inequality is incompatible with the ordinary one-turn area bound.
Every row is proved with exact rational arithmetic in its proof body.
-/

noncomputable section

namespace AmbidextrousSofa

def horizontalLeakageA0 (h : ℝ) : ℝ := h ^ 2 / 4 + h ^ 3 / 6

def horizontalLeakageA1 (h : ℝ) : ℝ := h ^ 3 / 12 + h ^ 4 / 16

def horizontalLeakageBoxSine (C : ℝ) : ℝ := (1 - C ^ 2) / (1 + C ^ 2)

theorem horizontalLeakageA0_nonneg {h : ℝ} (hh : 0 ≤ h) :
    0 ≤ horizontalLeakageA0 h := by unfold horizontalLeakageA0; positivity

theorem horizontalLeakageA1_nonneg {h : ℝ} (hh : 0 ≤ h) :
    0 ≤ horizontalLeakageA1 h := by unfold horizontalLeakageA1; positivity

theorem horizontalLeakageA0_mono {h k : ℝ} (hh : 0 ≤ h) (hhk : h ≤ k) :
    horizontalLeakageA0 h ≤ horizontalLeakageA0 k := by
  unfold horizontalLeakageA0
  gcongr

theorem horizontalLeakageA1_mono {h k : ℝ} (hh : 0 ≤ h) (hhk : h ≤ k) :
    horizontalLeakageA1 h ≤ horizontalLeakageA1 k := by
  unfold horizontalLeakageA1
  gcongr

theorem horizontalLeakageBoxSine_pos {C : ℝ} (hC0 : 0 ≤ C) (hC1 : C < 1) :
    0 < horizontalLeakageBoxSine C := by
  unfold horizontalLeakageBoxSine
  apply div_pos _ (by positivity)
  nlinarith [mul_pos (sub_pos.mpr hC1) (by linarith : 0 < 1 + C)]

theorem horizontalLeakageBoxSine_antitone {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    horizontalLeakageBoxSine b ≤ horizontalLeakageBoxSine a := by
  unfold horizontalLeakageBoxSine
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hsq := (sq_le_sq₀ ha (ha.trans hab)).2 hab
  nlinarith

/-- All fields are numerical inequalities for the displayed rational row;
none is a cap-area or curvature hypothesis. -/
structure HorizontalLeakageRow where
  a : ℝ
  b : ℝ
  H : ℝ
  h : ℝ
  T : ℝ
  t : ℝ
  B : ℝ
  a_pos : 0 < a
  a_le_b : a ≤ b
  b_lt_one : b < 1
  H_nonneg : 0 ≤ H
  H_le_one : H ≤ 1
  h_nonneg : 0 ≤ h
  h_lt_one : h < 1
  T_nonneg : 0 ≤ T
  t_nonneg : 0 ≤ t
  B_nonneg : 0 ≤ B
  B_le_one : B ≤ 1
  box : (1 - H) ^ 2 ≤ 1 - b ^ 2
  excess : 9 * b ^ 2 - 1 / 4 + 9 * H ^ 2 / 16 ≤
    (2 + (h ^ 2 + 2 * h) / 4) ^ 2
  crossing : 1 + 3 * H / 2 ≤ 6 * a * T - T ^ 2
  before_vertex : T < 3 * a
  angle : t ≤ 2 * ((1 - b) / (1 + b) - ((1 - b) / (1 + b)) ^ 3 / 3)
  leakage : horizontalLeakageA0 h * max (T - t) 0 + horizontalLeakageA1 h ≤
    B * horizontalLeakageBoxSine b
  residual_pos : 0 < (22199 : ℝ) / 10000 - a * (2 - B)
  contradiction : ((22199 : ℝ) / 10000 - a * (2 - B)) ^ 2 <
    a ^ 2 + (1 - B) ^ 2 / 4

def horizontalLeakageRow0 : HorizontalLeakageRow where
  a := 8571 / 12500
  b := 343 / 500
  H := 681 / 2500
  h := 27 / 2000
  T := 377 / 1000
  t := 46 / 125
  B := 1 / 400000
  a_pos := by norm_num
  a_le_b := by norm_num
  b_lt_one := by norm_num
  H_nonneg := by norm_num
  H_le_one := by norm_num
  h_nonneg := by norm_num
  h_lt_one := by norm_num
  T_nonneg := by norm_num
  t_nonneg := by norm_num
  B_nonneg := by norm_num
  B_le_one := by norm_num
  box := by norm_num
  excess := by norm_num
  crossing := by norm_num
  before_vertex := by norm_num
  angle := by norm_num
  leakage := by norm_num [horizontalLeakageA0, horizontalLeakageA1, horizontalLeakageBoxSine]
  residual_pos := by norm_num
  contradiction := by norm_num

def horizontalLeakageRow1 : HorizontalLeakageRow where
  a := 343 / 500
  b := 69 / 100
  H := 1381 / 5000
  h := 19 / 500
  T := 473 / 1250
  t := 3627 / 10000
  B := 1 / 30000
  a_pos := by norm_num
  a_le_b := by norm_num
  b_lt_one := by norm_num
  H_nonneg := by norm_num
  H_le_one := by norm_num
  h_nonneg := by norm_num
  h_lt_one := by norm_num
  T_nonneg := by norm_num
  t_nonneg := by norm_num
  B_nonneg := by norm_num
  B_le_one := by norm_num
  box := by norm_num
  excess := by norm_num
  crossing := by norm_num
  before_vertex := by norm_num
  angle := by norm_num
  leakage := by norm_num [horizontalLeakageA0, horizontalLeakageA1, horizontalLeakageBoxSine]
  residual_pos := by norm_num
  contradiction := by norm_num

def horizontalLeakageRow2 : HorizontalLeakageRow where
  a := 69 / 100
  b := 7 / 10
  H := 2859 / 10000
  h := 971 / 10000
  T := 3801 / 10000
  t := 873 / 2500
  B := 1 / 2000
  a_pos := by norm_num
  a_le_b := by norm_num
  b_lt_one := by norm_num
  H_nonneg := by norm_num
  H_le_one := by norm_num
  h_nonneg := by norm_num
  h_lt_one := by norm_num
  T_nonneg := by norm_num
  t_nonneg := by norm_num
  B_nonneg := by norm_num
  B_le_one := by norm_num
  box := by norm_num
  excess := by norm_num
  crossing := by norm_num
  before_vertex := by norm_num
  angle := by norm_num
  leakage := by norm_num [horizontalLeakageA0, horizontalLeakageA1, horizontalLeakageBoxSine]
  residual_pos := by norm_num
  contradiction := by norm_num

def horizontalLeakageRow3 : HorizontalLeakageRow where
  a := 7 / 10
  b := 29 / 40
  H := 3113 / 10000
  h := 2323 / 10000
  T := 769 / 2000
  t := 3161 / 10000
  B := 3 / 400
  a_pos := by norm_num
  a_le_b := by norm_num
  b_lt_one := by norm_num
  H_nonneg := by norm_num
  H_le_one := by norm_num
  h_nonneg := by norm_num
  h_lt_one := by norm_num
  T_nonneg := by norm_num
  t_nonneg := by norm_num
  B_nonneg := by norm_num
  B_le_one := by norm_num
  box := by norm_num
  excess := by norm_num
  crossing := by norm_num
  before_vertex := by norm_num
  angle := by norm_num
  leakage := by norm_num [horizontalLeakageA0, horizontalLeakageA1, horizontalLeakageBoxSine]
  residual_pos := by norm_num
  contradiction := by norm_num

def horizontalLeakageRow4 : HorizontalLeakageRow where
  a := 29 / 40
  b := 3 / 4
  H := 1693 / 5000
  h := 1771 / 5000
  T := 3799 / 10000
  t := 2837 / 10000
  B := 31 / 1000
  a_pos := by norm_num
  a_le_b := by norm_num
  b_lt_one := by norm_num
  H_nonneg := by norm_num
  H_le_one := by norm_num
  h_nonneg := by norm_num
  h_lt_one := by norm_num
  T_nonneg := by norm_num
  t_nonneg := by norm_num
  B_nonneg := by norm_num
  B_le_one := by norm_num
  box := by norm_num
  excess := by norm_num
  crossing := by norm_num
  before_vertex := by norm_num
  angle := by norm_num
  leakage := by norm_num [horizontalLeakageA0, horizontalLeakageA1, horizontalLeakageBoxSine]
  residual_pos := by norm_num
  contradiction := by norm_num

def horizontalLeakageRow5 : HorizontalLeakageRow where
  a := 3 / 4
  b := 31 / 40
  H := 3681 / 10000
  h := 2331 / 5000
  T := 753 / 2000
  t := 2521 / 10000
  B := 83 / 1000
  a_pos := by norm_num
  a_le_b := by norm_num
  b_lt_one := by norm_num
  H_nonneg := by norm_num
  H_le_one := by norm_num
  h_nonneg := by norm_num
  h_lt_one := by norm_num
  T_nonneg := by norm_num
  t_nonneg := by norm_num
  B_nonneg := by norm_num
  B_le_one := by norm_num
  box := by norm_num
  excess := by norm_num
  crossing := by norm_num
  before_vertex := by norm_num
  angle := by norm_num
  leakage := by norm_num [horizontalLeakageA0, horizontalLeakageA1, horizontalLeakageBoxSine]
  residual_pos := by norm_num
  contradiction := by norm_num

def horizontalLeakageRow6 : HorizontalLeakageRow where
  a := 31 / 40
  b := 4 / 5
  H := 2 / 5
  h := 5703 / 10000
  T := 1871 / 5000
  t := 2213 / 10000
  B := 9 / 50
  a_pos := by norm_num
  a_le_b := by norm_num
  b_lt_one := by norm_num
  H_nonneg := by norm_num
  H_le_one := by norm_num
  h_nonneg := by norm_num
  h_lt_one := by norm_num
  T_nonneg := by norm_num
  t_nonneg := by norm_num
  B_nonneg := by norm_num
  B_le_one := by norm_num
  box := by norm_num
  excess := by norm_num
  crossing := by norm_num
  before_vertex := by norm_num
  angle := by norm_num
  leakage := by norm_num [horizontalLeakageA0, horizontalLeakageA1, horizontalLeakageBoxSine]
  residual_pos := by norm_num
  contradiction := by norm_num

theorem exists_horizontalLeakageRow {C : ℝ}
    (hC0 : 8571 / 12500 ≤ C) (hC1 : C ≤ 4 / 5) :
    ∃ R : HorizontalLeakageRow, R.a ≤ C ∧ C ≤ R.b := by
  by_cases h0 : C ≤ 343 / 500
  · exact ⟨horizontalLeakageRow0, hC0, h0⟩
  by_cases h1 : C ≤ 69 / 100
  · exact ⟨horizontalLeakageRow1, (lt_of_not_ge h0).le, h1⟩
  by_cases h2 : C ≤ 7 / 10
  · exact ⟨horizontalLeakageRow2, (lt_of_not_ge h1).le, h2⟩
  by_cases h3 : C ≤ 29 / 40
  · exact ⟨horizontalLeakageRow3, (lt_of_not_ge h2).le, h3⟩
  by_cases h4 : C ≤ 3 / 4
  · exact ⟨horizontalLeakageRow4, (lt_of_not_ge h3).le, h4⟩
  by_cases h5 : C ≤ 31 / 40
  · exact ⟨horizontalLeakageRow5, (lt_of_not_ge h4).le, h5⟩
  exact ⟨horizontalLeakageRow6, (lt_of_not_ge h5).le, hC1⟩

theorem HorizontalLeakageRow.box_height_le (R : HorizontalLeakageRow) {C : ℝ}
    (hC0 : 0 ≤ C) (hCb : C ≤ R.b) :
    1 - Real.sqrt (1 - C ^ 2) ≤ R.H := by
  have hb0 : 0 ≤ R.b := R.a_pos.le.trans R.a_le_b
  have hsq := (sq_le_sq₀ hC0 hb0).2 hCb
  have hroot := Real.le_sqrt_of_sq_le
    (show (1 - R.H) ^ 2 ≤ 1 - C ^ 2 from R.box.trans (by linarith))
  linarith

theorem HorizontalLeakageRow.crossing_time_le (R : HorizontalLeakageRow) {C e : ℝ}
    (haC : R.a ≤ C) (he : e ≤ 1 / 2 + 3 * R.H / 4) :
    3 * C - Real.sqrt (9 * C ^ 2 - 2 * e) ≤ R.T := by
  have hmul := mul_nonneg (sub_nonneg.mpr haC) R.T_nonneg
  have hsq : (3 * C - R.T) ^ 2 ≤ 9 * C ^ 2 - 2 * e := by
    nlinarith [R.crossing]
  have hroot := Real.le_sqrt_of_sq_le hsq
  linarith

theorem HorizontalLeakageRow.excess_le (R : HorizontalLeakageRow) {C e : ℝ}
    (hC0 : 0 ≤ C) (hCb : C ≤ R.b)
    (he0 : 1 / 2 - R.H / 4 ≤ e) (he1 : e ≤ 1 / 2 + 3 * R.H / 4) :
    max (Real.sqrt (9 * C ^ 2 - e * (1 - e)) - 2) 0 ≤
      (R.h ^ 2 + 2 * R.h) / 4 := by
  have hsqC := (sq_le_sq₀ hC0 (R.a_pos.le.trans R.a_le_b)).2 hCb
  have he0' : 0 ≤ e - 1 / 2 + 3 * R.H / 4 := by linarith [R.H_nonneg]
  have he1' : 0 ≤ 3 * R.H / 4 - (e - 1 / 2) := by linarith
  have hsqe := mul_nonneg he0' he1'
  have hrad : 9 * C ^ 2 - e * (1 - e) ≤
      (2 + (R.h ^ 2 + 2 * R.h) / 4) ^ 2 := by nlinarith [R.excess]
  have hh0 := R.h_nonneg
  have hε : 0 ≤ (R.h ^ 2 + 2 * R.h) / 4 := by positivity
  have hroot := (Real.sqrt_le_left (by linarith :
    0 ≤ 2 + (R.h ^ 2 + 2 * R.h) / 4)).2 hrad
  exact max_le (by linarith) hε

theorem HorizontalLeakageRow.envelope_length_le (R : HorizontalLeakageRow) {ε : ℝ}
    (hε : ε ≤ (R.h ^ 2 + 2 * R.h) / 4) :
    Real.sqrt (1 + 4 * ε) - 1 ≤ R.h := by
  have hroot := (Real.sqrt_le_left (by linarith [R.h_nonneg] : 0 ≤ R.h + 1)).2
    (show 1 + 4 * ε ≤ (R.h + 1) ^ 2 by nlinarith)
  linarith

theorem HorizontalLeakageRow.box_angle_le (R : HorizontalLeakageRow) {C : ℝ}
    (hC0 : 0 ≤ C) (hCb : C ≤ R.b) :
    R.t ≤ 2 * Real.arctan ((1 - C) / (1 + C)) := by
  have hb0 := R.a_pos.le.trans R.a_le_b
  have hz : (1 - R.b) / (1 + R.b) ≤ (1 - C) / (1 + C) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).2
    nlinarith
  have hpoly := self_sub_cube_div_three_le_arctan
    (div_nonneg (sub_nonneg.mpr R.b_lt_one.le) (by linarith : 0 ≤ 1 + R.b))
  have hmono := Real.arctan_mono hz
  linarith [R.angle]

/-- At the lower row endpoint the energy criterion is already satisfied.
The rational lower bound for the square root avoids rounding the root of
the defining algebraic threshold. -/
theorem horizontal_energy_threshold_of_width_le {C : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 8571 / 12500) :
    9 * C ^ 2 ≤ 4 + (1 - (1 - Real.sqrt (1 - C ^ 2)) ^ 2) / 4 := by
  have hsq := (sq_le_sq₀ hC0 (by norm_num : (0 : ℝ) ≤ 8571 / 12500)).2 hC1
  have hrad : 0 ≤ 1 - C ^ 2 := by nlinarith
  have hlower : (3639 : ℝ) / 5000 ≤ Real.sqrt (1 - C ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  nlinarith [Real.sq_sqrt hrad]

/-- The final row inequality contradicts the monotone ordinary-area
obstruction at every width in the row. -/
theorem HorizontalLeakageRow.not_ordinary_area_bound (R : HorizontalLeakageRow) {C : ℝ}
    (haC : R.a ≤ C)
    (hbound : C * (2 - R.B) + Real.sqrt (C ^ 2 + (1 - R.B) ^ 2 / 4) ≤
      (22199 : ℝ) / 10000) : False := by
  have hC0 := R.a_pos.le.trans haC
  have hsqC := (sq_le_sq₀ R.a_pos.le hC0).2 haC
  have hsqroot := Real.sqrt_le_sqrt
    (show R.a ^ 2 + (1 - R.B) ^ 2 / 4 ≤ C ^ 2 + (1 - R.B) ^ 2 / 4 by linarith)
  have hlinear := mul_le_mul_of_nonneg_right haC (by linarith [R.B_le_one] : 0 ≤ 2 - R.B)
  have hs : Real.sqrt (R.a ^ 2 + (1 - R.B) ^ 2 / 4) ≤
      (22199 : ℝ) / 10000 - R.a * (2 - R.B) := by linarith
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) R.residual_pos.le).2 hs
  rw [Real.sq_sqrt (by positivity)] at hsq
  exact (not_lt_of_ge hsq) R.contradiction

end AmbidextrousSofa
