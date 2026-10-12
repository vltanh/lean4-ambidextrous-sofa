module

public import AmbidextrousSofa.Analysis.InitialAngleRelaxation

@[expose] public section

/-!
# Algebraic centers for the three-support calibration

The balanced support parameters center two quadratic identities. Their
realizability and the ordering of their wall intersections are unnecessary:
the calibration bounds the actual clipped integrals directly. The inset
bounds follow from the unit-circle identity.
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
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  have hK := sqrt_two_sub_one_quadratic
  have hden : 0 < 1 - d ^ 2 := by nlinarith
  exact ⟨hd, by nlinarith [mul_pos (sub_pos.2 hk1) hden]⟩

end AmbidextrousSofa
