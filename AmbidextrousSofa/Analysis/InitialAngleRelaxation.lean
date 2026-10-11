module

public import AmbidextrousSofa.Analysis.PositiveTent
public import AmbidextrousSofa.Analysis.InitialAngleScalar
public import AmbidextrousSofa.Analysis.TerminalThreeSupports

@[expose] public section

/-!
# The actual three-support integral relaxation

The four functions below retain every positive-part, wall-switch, and
window-endpoint clipping in the relaxation. Actual cap scores are
bounded by this function through the three genuine support lines.

The right-wall integral is reduced to two clipped ramps. Dropping its
extra terminal charge gives the diagonal relaxation, whose fully exposed
tent has an exact integral. This proves the complementary-region estimate
directly from the support compatibility inequalities. The calibration
regions require a further comparison with the stationary value.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def initialAngleRampLoss (C z : ℝ) : ℝ :=
  ∫ x in C..(2 * C), max (x - z) 0

def initialAngleRightLoss (C k u b : ℝ) : ℝ :=
  ∫ x in C..(2 * C), max (max 0 (x - u)) (k * (x - b))

def initialAngleNicheLoss (K C k d u v b : ℝ) : ℝ :=
  ∫ x in (-C)..C, max (max 0 (min (u - K - x) (v - K + x)))
    (k * (b - d - x))

def initialAngleRelaxation (K C k d u v b : ℝ) : ℝ :=
  2 * C - initialAngleRampLoss C v - initialAngleRightLoss C k u b -
    initialAngleNicheLoss K C k d u v b

theorem initialAngleRampLoss_eq_positive_squares (C z : ℝ) :
    initialAngleRampLoss C z =
      ((max (2 * C - z) 0) ^ 2 - (max (C - z) 0) ^ 2) / 2 := by
  simp only [initialAngleRampLoss, sub_eq_neg_add, integral_positive_ramp_add]

theorem initialAngleRampLoss_eq_affine {C z : ℝ}
    (hC : 0 ≤ C) (hz : z ≤ C) :
    initialAngleRampLoss C z = 3 * C ^ 2 / 2 - C * z := by
  rw [initialAngleRampLoss_eq_positive_squares, max_eq_left (show 0 ≤ 2 * C - z by linarith),
    max_eq_left (show 0 ≤ C - z by linarith)]
  ring

theorem initialAngleRampLoss_eq_square {C z : ℝ}
    (hz0 : C ≤ z) (hz1 : z ≤ 2 * C) :
    initialAngleRampLoss C z = (2 * C - z) ^ 2 / 2 := by
  rw [initialAngleRampLoss_eq_positive_squares,
    max_eq_left (sub_nonneg.mpr hz1), max_eq_right (sub_nonpos.mpr hz0)]
  ring

theorem initialAngleNicheLoss_nonneg {C : ℝ} (hC : 0 ≤ C) (K k d u v b : ℝ) :
    0 ≤ initialAngleNicheLoss K C k d u v b :=
  intervalIntegral.integral_nonneg_of_forall (by linarith)
    fun _ => (le_max_left _ _).trans (le_max_left _ _)

theorem initialAngleRampLoss_le_rightLoss {C : ℝ} (hC : 0 ≤ C) (k u b : ℝ) :
    initialAngleRampLoss C u ≤ initialAngleRightLoss C k u b :=
  intervalIntegral.integral_mono (by linarith) (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    fun x => (max_comm _ _).trans_le (le_max_left _ _)

theorem initialAngleRelaxation_le_twice_width {C : ℝ} (hC : 0 ≤ C)
    (K k d u v b : ℝ) : initialAngleRelaxation K C k d u v b ≤ 2 * C := by
  have hramp (z : ℝ) : 0 ≤ initialAngleRampLoss C z :=
    intervalIntegral.integral_nonneg_of_forall (by linarith) fun _ => le_max_right _ _
  unfold initialAngleRelaxation
  linarith [hramp v, (hramp u).trans (initialAngleRampLoss_le_rightLoss hC k u b),
    initialAngleNicheLoss_nonneg hC K k d u v b]

/-- The relaxation bound holds with every ramp tail retained, even when a wall switch
lies outside the exterior integration interval. -/
theorem initialAngleRightLoss_eq_ramps {C k u b : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) (hbu : b ≤ u) :
    initialAngleRightLoss C k u b = k * initialAngleRampLoss C b +
      (1 - k) * initialAngleRampLoss C ((u - k * b) / (1 - k)) := by
  set z := (u - k * b) / (1 - k)
  have hsplit : (1 - k) * z = u - k * b := mul_div_cancel₀ _ (by linarith)
  have hbz : b ≤ z := by nlinarith
  have huz : u ≤ z := by nlinarith
  unfold initialAngleRightLoss initialAngleRampLoss
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rcases le_total x b with hxb | hbx
  · rw [max_eq_left (show x - u ≤ 0 by linarith), max_eq_left (mul_nonpos_of_nonneg_of_nonpos hk0
      (sub_nonpos.mpr hxb)), max_eq_right (sub_nonpos.mpr hxb),
      max_eq_right (show x - z ≤ 0 by linarith)]
    ring
  rcases le_total x z with hxz | hzx
  · rw [max_eq_right (max_le (mul_nonneg hk0 (sub_nonneg.mpr hbx)) (by nlinarith)),
      max_eq_left (sub_nonneg.mpr hbx), max_eq_right (sub_nonpos.mpr hxz)]
    ring
  · rw [max_eq_right (show 0 ≤ x - u by linarith), max_eq_left (by nlinarith),
      max_eq_left (sub_nonneg.mpr hbx), max_eq_left (sub_nonneg.mpr hzx)]
    linear_combination hsplit

theorem initialAngle_diagonal_integral_le_nicheLoss {C : ℝ} (hC : 0 ≤ C)
    (K k d u v b : ℝ) :
    (∫ x in (-C)..C, max 0 (min (u - K - x) (v - K + x))) ≤
      initialAngleNicheLoss K C k d u v b :=
  intervalIntegral.integral_mono (by linarith) (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _) fun _ => le_max_left _ _

/-- If both ends of the diagonal tent are nonnegative, all its clipped
terms have known signs and its full integral is an explicit quadratic. -/
theorem initialAngle_diagonal_integral_full {K C u v : ℝ}
    (hK : 0 ≤ K) (hu0 : C + K ≤ u) (hu1 : u ≤ 2 * C) (hv0 : C + K ≤ v) (hv1 : v ≤ 2 * C) :
    (∫ x in (-C)..C, max 0 (min (u - K - x) (v - K + x))) =
      ((u + v) / 2 - K) ^ 2 - (v - K - C) ^ 2 / 2 - (u - K - C) ^ 2 / 2 := by
  have hp : (u - v) / 2 ∈ Icc (-C) C := by constructor <;> linarith
  rw [intervalIntegral.integral_congr (g := fun x => max (((u + v) / 2 - K) - |x - (u - v) / 2|) 0)
    fun x _ => by dsimp only; rw [← min_symmetric_lines, max_comm]; ring_nf]
  rw [integral_positive_tent_centered hp, max_eq_left (by linarith : 0 ≤ (u + v) / 2 - K),
    max_eq_left (by linarith : 0 ≤ (u + v) / 2 - K - C - (u - v) / 2),
    max_eq_left (by linarith : 0 ≤ (u + v) / 2 - K - C + (u - v) / 2)]
  ring

/-- Outside both calibration regions, the actual finite-support
relaxation has the strict complementary margin. -/
theorem initialAngleRelaxation_complement_lt {C k d s u v b : ℝ}
    (hC : 0 ≤ C) (hk0 : 3 / 8 ≤ k) (hk1 : k ≤ 4 / 5)
    (hs0 : 0 ≤ s) (hs2 : s ^ 2 = 1 + k ^ 2) (hkd : k * d = s - 1)
    (hu1 : u ≤ 2 * C) (hv1 : v ≤ 2 * C)
    (hcompat : u ≤ 2 * (1 - k) * C + k * b)
    (hu : C + (Real.sqrt 2 - 1) < u)
    (hY : (1 + k) * C + (Real.sqrt 2 - 1) - v + k * (b - d) < 0) :
    initialAngleRelaxation (Real.sqrt 2 - 1) C k d u v b < (319 / 400 : ℝ) := by
  have hK0 := initialAngle_offset_bounds.1
  have hs : s < 13 / 10 := by nlinarith
  have hCk := mul_nonneg (by linarith : 0 ≤ 3 * k - 1) hC
  have hv : C + (Real.sqrt 2 - 1) < v := by linarith
  unfold initialAngleRelaxation
  linarith [initialAngleRampLoss_le_rightLoss hC k u b,
    initialAngle_diagonal_integral_le_nicheLoss hC (Real.sqrt 2 - 1) k d u v b,
    initialAngleRampLoss_eq_square (show C ≤ u by linarith) hu1,
    initialAngleRampLoss_eq_square (show C ≤ v by linarith) hv1,
    initialAngle_diagonal_integral_full (by linarith) hu.le hu1 hv.le hv1,
    initialAngle_complement_bound (h := (u + v) / 2) (C := C) initialAngle_offset_sq
      (by linarith)]

/-- The scalar relaxation is bounded from the actual cap roof and partial
barrier, with its own centered middle-half window. -/
theorem IsDownwardCap.capScore_le_initialAngleRelaxation {U : Set Plane}
    (hU : IsDownwardCap U) {C α : ℝ} (hC : 0 ≤ C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α < Real.pi / 2) :
    capScore U α ≤ initialAngleRelaxation (Real.sqrt 2 - 1) C (terminalSlope α)
      (terminalInset α) (diagonalRight U - 1) (diagonalLeft U - 1)
      (terminalSupportPosition U α) :=
  hU.capScore_le_three_support_integrals_centered hC hleft hright hα0 hαL

end AmbidextrousSofa
