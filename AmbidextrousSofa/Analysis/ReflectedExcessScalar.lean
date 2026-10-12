module

public import AmbidextrousSofa.Analysis.TiltedLateExcessScalar

@[expose] public section

/-!
# The exact reflected excess end time

Compare the crossing and decay jointly, then increase width and height
to their common upper endpoint. This single comparison bounds the whole
reflected range without separating initial heights.
-/

noncomputable section

namespace AmbidextrousSofa.Analysis

theorem reflected_excess_stops_early {d e a ε : ℝ}
    (hd0 : 2 ≤ d) (hd1 : d ≤ 111 / 50)
    (he0 : 3 / 20 ≤ e) (he1 : e ≤ 3 / 4)
    (hε : 0 ≤ ε) (hradius : (2 + ε) ^ 2 ≤ d ^ 2 - e * (1 - e))
    (had : a ≤ d) (hquad : 0 ≤ e - d * a + a ^ 2 / 2) :
    ε < 1 / 5 ∧ quadraticExcessLength ε < 1 / 3 ∧
      a + quadraticExcessLength ε < 11 / 15 := by
  have hproduct : 1 / 8 ≤ e * (1 - e) := by
    nlinarith only [he0, he1, mul_nonneg (sub_nonneg.mpr he0)
      (by linarith : 0 ≤ 17 / 20 - e)]
  have heps : ε < 1 / 5 := by nlinarith only [hradius, hproduct, hd0, hd1, hε]
  refine ⟨heps, quadraticExcessLength_lt hε (by norm_num) (by nlinarith only [hradius, hproduct, hd0, hd1, hε]), ?_⟩
  have hsum := first_zero_add_quadratic_excess_le (δ := 0) had hquad
    (by simpa using hradius)
  refine hsum.trans_lt ?_
  exact zero_tilt_excess_stops_early hd0 hd1 (by linarith only [he0]) he1

end AmbidextrousSofa.Analysis
