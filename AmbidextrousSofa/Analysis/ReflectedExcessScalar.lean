module

public import AmbidextrousSofa.Analysis.TiltedLateExcessScalar

@[expose] public section

/-!
# The exact reflected excess end time

The actual reflected energy and first-zero inequalities reduce to two
rational ranges for the original low endpoint height. The resulting
quadratic excess envelope ends before `11/15` in both ranges. No sampled
angle estimate or differential inequality is added to the scalar input.
-/

noncomputable section

namespace AmbidextrousSofa.Analysis

theorem reflected_excess_stops_early {d e a ε : ℝ}
    (hd0 : 2 ≤ d) (hd1 : d ≤ 111 / 50)
    (he0 : 3 / 20 ≤ e) (he1 : e ≤ 3 / 4)
    (hε : 0 ≤ ε) (hradius : (2 + ε) ^ 2 ≤ d ^ 2 - e * (1 - e))
    (had : a ≤ d) (hquad : 0 ≤ e - d * a + a ^ 2 / 2) :
    ε < 1 / 5 ∧ quadraticExcessLength ε < 7 / 20 ∧
      a + quadraticExcessLength ε < 11 / 15 := by
  have hdsq : d ^ 2 ≤ (111 / 50) ^ 2 := by nlinarith
  rcases le_total e (2 / 3) with he | he
  · have hε1 : ε < 1 / 5 := by
      nlinarith [mul_nonneg (sub_nonneg.2 he0) (by linarith : (0 : ℝ) ≤ 17 / 20 - e)]
    have ha : a < 3 / 8 := first_zero_lt_of_quadratic had (by linarith) hquad (by linarith)
    have hell : quadraticExcessLength ε < 7 / 20 :=
      quadraticExcessLength_lt hε (by norm_num) (by linarith)
    exact ⟨hε1, hell, by linarith⟩
  · have hε1 : ε < 9 / 50 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ e - 1 / 4) (sub_nonneg.2 he1)]
    have ha : a < 21 / 50 := first_zero_lt_of_quadratic had (by linarith) hquad (by linarith)
    have hell : quadraticExcessLength ε < 5 / 16 :=
      quadraticExcessLength_lt hε (by norm_num) (by linarith)
    exact ⟨by linarith, by linarith, by linarith⟩

end AmbidextrousSofa.Analysis
