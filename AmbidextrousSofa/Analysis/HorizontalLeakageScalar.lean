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

theorem horizontalLeakageA0_mono {h k : ℝ} (hh : 0 ≤ h) (hhk : h ≤ k) :
    horizontalLeakageA0 h ≤ horizontalLeakageA0 k := by unfold horizontalLeakageA0; gcongr

theorem horizontalLeakageBoxSine_antitone {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    horizontalLeakageBoxSine b ≤ horizontalLeakageBoxSine a := by
  unfold horizontalLeakageBoxSine
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul hab hab ha (ha.trans hab)]

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

def horizontalLeakageRow0 : HorizontalLeakageRow := by
  apply HorizontalLeakageRow.mk (8571 / 12500) (343 / 500) (681 / 2500) (27 / 2000) (377 / 1000)
    (46 / 125) (1 / 400000) <;>
    norm_num [horizontalLeakageA0, horizontalLeakageA1, horizontalLeakageBoxSine]

def horizontalLeakageRow1 : HorizontalLeakageRow := by
  apply HorizontalLeakageRow.mk (343 / 500) (69 / 100) (1381 / 5000) (19 / 500) (473 / 1250)
    (3627 / 10000) (1 / 30000) <;>
    norm_num [horizontalLeakageA0, horizontalLeakageA1, horizontalLeakageBoxSine]

def horizontalLeakageRow2 : HorizontalLeakageRow := by
  apply HorizontalLeakageRow.mk (69 / 100) (7 / 10) (2859 / 10000) (971 / 10000) (3801 / 10000)
    (873 / 2500) (1 / 2000) <;>
    norm_num [horizontalLeakageA0, horizontalLeakageA1, horizontalLeakageBoxSine]

def horizontalLeakageRow3 : HorizontalLeakageRow := by
  apply HorizontalLeakageRow.mk (7 / 10) (29 / 40) (3113 / 10000) (2323 / 10000) (769 / 2000)
    (3161 / 10000) (3 / 400) <;>
    norm_num [horizontalLeakageA0, horizontalLeakageA1, horizontalLeakageBoxSine]

def horizontalLeakageRow4 : HorizontalLeakageRow := by
  apply HorizontalLeakageRow.mk (29 / 40) (3 / 4) (1693 / 5000) (1771 / 5000) (3799 / 10000)
    (2837 / 10000) (31 / 1000) <;>
    norm_num [horizontalLeakageA0, horizontalLeakageA1, horizontalLeakageBoxSine]

def horizontalLeakageRow5 : HorizontalLeakageRow := by
  apply HorizontalLeakageRow.mk (3 / 4) (31 / 40) (3681 / 10000) (2331 / 5000) (753 / 2000)
    (2521 / 10000) (83 / 1000) <;>
    norm_num [horizontalLeakageA0, horizontalLeakageA1, horizontalLeakageBoxSine]

def horizontalLeakageRow6 : HorizontalLeakageRow := by
  apply HorizontalLeakageRow.mk (31 / 40) (4 / 5) (2 / 5) (5703 / 10000) (1871 / 5000)
    (2213 / 10000) (9 / 50) <;>
    norm_num [horizontalLeakageA0, horizontalLeakageA1, horizontalLeakageBoxSine]

theorem exists_horizontalLeakageRow {C : ℝ}
    (hC0 : 8571 / 12500 ≤ C) (hC1 : C ≤ 4 / 5) :
    ∃ R : HorizontalLeakageRow, R.a ≤ C ∧ C ≤ R.b := by
  rcases le_or_gt C (343 / 500) with h0 | h0
  · exact ⟨horizontalLeakageRow0, hC0, h0⟩
  rcases le_or_gt C (69 / 100) with h1 | h1
  · exact ⟨horizontalLeakageRow1, h0.le, h1⟩
  rcases le_or_gt C (7 / 10) with h2 | h2
  · exact ⟨horizontalLeakageRow2, h1.le, h2⟩
  rcases le_or_gt C (29 / 40) with h3 | h3
  · exact ⟨horizontalLeakageRow3, h2.le, h3⟩
  rcases le_or_gt C (3 / 4) with h4 | h4
  · exact ⟨horizontalLeakageRow4, h3.le, h4⟩
  rcases le_or_gt C (31 / 40) with h5 | h5
  · exact ⟨horizontalLeakageRow5, h4.le, h5⟩
  exact ⟨horizontalLeakageRow6, h5.le, hC1⟩

theorem HorizontalLeakageRow.box_height_le (R : HorizontalLeakageRow) {C : ℝ}
    (hC0 : 0 ≤ C) (hCb : C ≤ R.b) :
    1 - Real.sqrt (1 - C ^ 2) ≤ R.H := by
  have := Real.le_sqrt_of_sq_le (R.box.trans (by nlinarith : 1 - R.b ^ 2 ≤ 1 - C ^ 2))
  linarith

theorem HorizontalLeakageRow.box_angle_le (R : HorizontalLeakageRow) {C : ℝ}
    (hC0 : 0 ≤ C) (hCb : C ≤ R.b) :
    R.t ≤ 2 * Real.arctan ((1 - C) / (1 + C)) := by
  have hb0 := R.a_pos.le.trans R.a_le_b
  have hz : (1 - R.b) / (1 + R.b) ≤ (1 - C) / (1 + C) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  linarith [R.angle, Real.arctan_mono hz, self_sub_cube_div_three_le_arctan
    (div_nonneg (sub_nonneg.mpr R.b_lt_one.le) (by linarith : 0 ≤ 1 + R.b))]

/-- At the lower row endpoint the energy criterion is already satisfied.
The rational lower bound for the square root avoids rounding the root of
the defining algebraic threshold. -/
theorem horizontal_energy_threshold_of_width_le {C : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 8571 / 12500) :
    9 * C ^ 2 ≤ 4 + (1 - (1 - Real.sqrt (1 - C ^ 2)) ^ 2) / 4 := by
  have hsq : C ^ 2 ≤ (8571 / 12500) ^ 2 := by gcongr
  have hlower : (3639 : ℝ) / 5000 ≤ Real.sqrt (1 - C ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  nlinarith [Real.sq_sqrt (by nlinarith : 0 ≤ 1 - C ^ 2)]

/-- The final row inequality contradicts the monotone ordinary-area
obstruction at every width in the row. -/
theorem HorizontalLeakageRow.not_ordinary_area_bound (R : HorizontalLeakageRow) {C : ℝ}
    (haC : R.a ≤ C)
    (hbound : C * (2 - R.B) + Real.sqrt (C ^ 2 + (1 - R.B) ^ 2 / 4) ≤
      (22199 : ℝ) / 10000) : False := by
  have hroot := Real.sqrt_le_sqrt (by nlinarith [R.a_pos] :
    R.a ^ 2 + (1 - R.B) ^ 2 / 4 ≤ C ^ 2 + (1 - R.B) ^ 2 / 4)
  linarith [Real.lt_sqrt_of_sq_lt R.contradiction,
    mul_le_mul_of_nonneg_right haC (by linarith [R.B_le_one] : 0 ≤ 2 - R.B)]

end AmbidextrousSofa
