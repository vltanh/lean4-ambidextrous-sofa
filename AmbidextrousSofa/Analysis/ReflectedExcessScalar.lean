import AmbidextrousSofa.Analysis.TiltedLateExcessScalar

/-!
# The exact reflected excess end time

The actual reflected energy and first-zero inequalities reduce to two
rational ranges for the original low endpoint height. The resulting
quadratic excess envelope ends before `11/15` in both ranges. No sampled
angle estimate or differential inequality is added to the scalar input.
-/

noncomputable section

namespace AmbidextrousSofa.Analysis

theorem reflected_excess_low_endpoint_stops_early {d e a ε : ℝ}
    (hd0 : 2 ≤ d) (hd1 : d ≤ 111 / 50)
    (he0 : 3 / 20 ≤ e) (he1 : e ≤ 2 / 3)
    (hε : 0 ≤ ε) (hradius : (2 + ε) ^ 2 ≤ d ^ 2 - e * (1 - e))
    (had : a ≤ d) (hquad : 0 ≤ e - d * a + a ^ 2 / 2) :
    a < 3 / 8 ∧ ε < 1 / 5 ∧ quadraticExcessLength ε < 7 / 20 ∧
      a + quadraticExcessLength ε < 11 / 15 := by
  have heprod : 51 / 400 ≤ e * (1 - e) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr he0)
      (show 0 ≤ 17 / 20 - e by linarith only [he1])]
  have hdsq : d ^ 2 ≤ (111 / 50 : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hd1)
      (show 0 ≤ 111 / 50 + d by linarith only [hd0])]
  have hε1 : ε < 1 / 5 := by
    by_contra hbad
    have hprod := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hbad))
      (show 0 ≤ ε + 21 / 5 by linarith only [hε])
    nlinarith only [hprod, hradius, heprod, hdsq]
  have ha : a < 3 / 8 := first_zero_lt_of_quadratic had
    (by linarith only [hd0]) hquad (by linarith only [hd0, he1])
  have hell : quadraticExcessLength ε < 7 / 20 :=
    quadraticExcessLength_lt hε (by norm_num) (by linarith only [hε1])
  exact ⟨ha, hε1, hell, by linarith only [ha, hell]⟩

theorem reflected_excess_high_endpoint_stops_early {d e a ε : ℝ}
    (hd0 : 2 ≤ d) (hd1 : d ≤ 111 / 50)
    (he0 : 2 / 3 ≤ e) (he1 : e ≤ 3 / 4)
    (hε : 0 ≤ ε) (hradius : (2 + ε) ^ 2 ≤ d ^ 2 - e * (1 - e))
    (had : a ≤ d) (hquad : 0 ≤ e - d * a + a ^ 2 / 2) :
    a < 21 / 50 ∧ ε < 9 / 50 ∧ quadraticExcessLength ε < 5 / 16 ∧
      a + quadraticExcessLength ε < 11 / 15 := by
  have heprod : 3 / 16 ≤ e * (1 - e) := by
    nlinarith only [mul_nonneg (show 0 ≤ e - 1 / 4 by linarith only [he0])
      (sub_nonneg.mpr he1)]
  have hdsq : d ^ 2 ≤ (111 / 50 : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hd1)
      (show 0 ≤ 111 / 50 + d by linarith only [hd0])]
  have hε1 : ε < 9 / 50 := by
    by_contra hbad
    have hprod := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hbad))
      (show 0 ≤ ε + 209 / 50 by linarith only [hε])
    nlinarith only [hprod, hradius, heprod, hdsq]
  have ha : a < 21 / 50 := first_zero_lt_of_quadratic had
    (by linarith only [hd0]) hquad (by linarith only [hd0, he1])
  have hell : quadraticExcessLength ε < 5 / 16 :=
    quadraticExcessLength_lt hε (by norm_num) (by linarith only [hε1])
  exact ⟨ha, hε1, hell, by linarith only [ha, hell]⟩

theorem reflected_excess_stops_early {d e a ε : ℝ}
    (hd0 : 2 ≤ d) (hd1 : d ≤ 111 / 50)
    (he0 : 3 / 20 ≤ e) (he1 : e ≤ 3 / 4)
    (hε : 0 ≤ ε) (hradius : (2 + ε) ^ 2 ≤ d ^ 2 - e * (1 - e))
    (had : a ≤ d) (hquad : 0 ≤ e - d * a + a ^ 2 / 2) :
    ε < 1 / 5 ∧ quadraticExcessLength ε < 7 / 20 ∧
      a + quadraticExcessLength ε < 11 / 15 := by
  by_cases he : e ≤ 2 / 3
  · exact (reflected_excess_low_endpoint_stops_early hd0 hd1 he0 he hε hradius had hquad).2
  · have h := reflected_excess_high_endpoint_stops_early
      hd0 hd1 (le_of_not_ge he) he1 hε hradius had hquad
    exact ⟨by linarith only [h.2.1], by linarith only [h.2.2.1], h.2.2.2⟩

end AmbidextrousSofa.Analysis
