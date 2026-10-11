module

public import AmbidextrousSofa.Analysis.InitialAngleRelaxation

@[expose] public section

/-!
# Exact clipping and integrals at the three-support critical point

The critical support parameters have explicitly ordered wall intersections.
Their delicate falling-wall versus terminal-floor comparison is derived
from the natural inset equation and the two preliminary width ranges.
These are local parameter identities, not an assumed optimization of the
finite-support relaxation.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def initialAngleCriticalB (K d : ℝ) : ℝ := (K + d) / 2

def initialAngleCriticalU (K C k d : ℝ) : ℝ :=
  (1 - k) * C + K / 2 + k * d / 2

def initialAngleCriticalV (K C k d : ℝ) : ℝ :=
  (1 + k) * C + K / 2 - k * d / 2

/-- The inset of a cotangent in `(0, 1)` lies strictly between `0` and `√2 - 1`. -/
theorem initialAngle_inset_bounds {k d s : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hs0 : 0 ≤ s)
    (hs2 : s ^ 2 = 1 + k ^ 2) (hkd : k * d = s - 1) : 0 < d ∧ d < Real.sqrt 2 - 1 := by
  have hd : 0 < d := pos_of_mul_pos_right (by nlinarith : 0 < k * d) hk0.le
  have hparam : k * (1 - d ^ 2) = 2 * d :=
    mul_left_cancel₀ hk0.ne' (by linear_combination -hs2 - (k * d + 1 + s) * hkd)
  have hK0 := sqrt_two_sub_one_bounds.1
  have hK := sqrt_two_sub_one_quadratic
  have hden : 0 < 1 - d ^ 2 := by nlinarith
  exact ⟨hd, by nlinarith [mul_pos (sub_pos.2 hk1) hden]⟩

end AmbidextrousSofa
