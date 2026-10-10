module

public import AmbidextrousSofa.Analysis.PositiveTent
public import AmbidextrousSofa.Analysis.InitialAngleScalar
public import AmbidextrousSofa.Analysis.TerminalThreeSupports

@[expose] public section

/-!
# The actual three-support integral relaxation

The four functions below retain every positive-part, wall-switch, and
window-endpoint clipping in the AT relaxation. Actual cap scores are
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
  have hfun : (fun x : ℝ => max (x - z) 0) =
      (fun x : ℝ => max (-z + x) 0) := by
    funext x
    congr 1
    ring
  unfold initialAngleRampLoss
  rw [hfun, integral_positive_ramp_add,
    show -z + 2 * C = 2 * C - z by ring,
    show -z + C = C - z by ring]

theorem initialAngleRampLoss_eq_affine {C z : ℝ}
    (hC : 0 ≤ C) (hz : z ≤ C) :
    initialAngleRampLoss C z = 3 * C ^ 2 / 2 - C * z := by
  rw [initialAngleRampLoss_eq_positive_squares,
    max_eq_left (show 0 ≤ 2 * C - z by linarith),
    max_eq_left (show 0 ≤ C - z by linarith)]
  ring

theorem initialAngleRampLoss_eq_square {C z : ℝ}
    (hz0 : C ≤ z) (hz1 : z ≤ 2 * C) :
    initialAngleRampLoss C z = (2 * C - z) ^ 2 / 2 := by
  rw [initialAngleRampLoss_eq_positive_squares,
    max_eq_left (sub_nonneg.mpr hz1), max_eq_right (sub_nonpos.mpr hz0)]
  ring

theorem initialAngleRampLoss_nonneg {C : ℝ} (hC : 0 ≤ C) (z : ℝ) :
    0 ≤ initialAngleRampLoss C z := by
  exact intervalIntegral.integral_nonneg_of_forall (by linarith)
    (fun x => le_max_right (x - z) 0)

theorem initialAngleRightLoss_nonneg {C : ℝ} (hC : 0 ≤ C) (k u b : ℝ) :
    0 ≤ initialAngleRightLoss C k u b := by
  exact intervalIntegral.integral_nonneg_of_forall (by linarith)
    (fun x => (le_max_left 0 (x - u)).trans (le_max_left _ _))

theorem initialAngleNicheLoss_nonneg {C : ℝ} (hC : 0 ≤ C) (K k d u v b : ℝ) :
    0 ≤ initialAngleNicheLoss K C k d u v b := by
  exact intervalIntegral.integral_nonneg_of_forall (by linarith)
    (fun x => (le_max_left 0 (min (u - K - x) (v - K + x))).trans
      (le_max_left _ _))

theorem initialAngleRelaxation_le_twice_width {C : ℝ} (hC : 0 ≤ C)
    (K k d u v b : ℝ) : initialAngleRelaxation K C k d u v b ≤ 2 * C := by
  unfold initialAngleRelaxation
  linarith [initialAngleRampLoss_nonneg hC v, initialAngleRightLoss_nonneg hC k u b,
    initialAngleNicheLoss_nonneg hC K k d u v b]

/-- The zero, terminal, and diagonal pieces are exactly two positive ramps. -/
theorem initialAngle_right_integrand_ramps {k u b z : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) (hbz : b ≤ z)
    (hsplit : (1 - k) * z = u - k * b) (x : ℝ) :
    max (max 0 (x - u)) (k * (x - b)) =
      k * max (x - b) 0 + (1 - k) * max (x - z) 0 := by
  have hbu : b ≤ u := by
    nlinarith only [hsplit, mul_nonneg (show 0 ≤ 1 - k by linarith)
      (sub_nonneg.mpr hbz)]
  have huz : u ≤ z := by
    nlinarith only [hsplit, mul_nonneg hk0 (sub_nonneg.mpr hbz)]
  by_cases hxb : x ≤ b
  · have hcharge : k * (x - b) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hk0 (sub_nonpos.mpr hxb)
    simp only [max_eq_left (show x - u ≤ 0 by linarith),
      max_eq_left hcharge, max_eq_right (sub_nonpos.mpr hxb),
      max_eq_right (show x - z ≤ 0 by linarith), mul_zero, add_zero]
  · have hbx : b ≤ x := le_of_not_ge hxb
    by_cases hxz : x ≤ z
    · have hcharge : 0 ≤ k * (x - b) := mul_nonneg hk0 (sub_nonneg.mpr hbx)
      have hdiag : x - u ≤ k * (x - b) := by
        nlinarith only [hsplit, mul_nonneg (show 0 ≤ 1 - k by linarith)
          (sub_nonneg.mpr hxz)]
      rw [max_eq_right (max_le hcharge hdiag), max_eq_left (sub_nonneg.mpr hbx),
        max_eq_right (sub_nonpos.mpr hxz), mul_zero, add_zero]
    · have hzx : z ≤ x := le_of_not_ge hxz
      have hdiag : k * (x - b) ≤ x - u := by
        nlinarith only [hsplit, mul_nonneg (show 0 ≤ 1 - k by linarith)
          (sub_nonneg.mpr hzx)]
      rw [max_eq_right (show 0 ≤ x - u by linarith), max_eq_left hdiag,
        max_eq_left (sub_nonneg.mpr hbx), max_eq_left (sub_nonneg.mpr hzx)]
      nlinarith only [hsplit]

/-- AT.14 holds with every ramp tail retained, even when a wall switch
lies outside the exterior integration interval. -/
theorem initialAngleRightLoss_eq_ramps {C k u b : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) (hbu : b ≤ u) :
    initialAngleRightLoss C k u b = k * initialAngleRampLoss C b +
      (1 - k) * initialAngleRampLoss C ((u - k * b) / (1 - k)) := by
  let z := (u - k * b) / (1 - k)
  have hm : 0 < 1 - k := by linarith
  have hbz : b ≤ z := by
    apply (le_div_iff₀ hm).mpr
    nlinarith only [hbu]
  have hsplit : (1 - k) * z = u - k * b := by
    exact mul_div_cancel₀ _ (ne_of_gt hm)
  have hcfirst : Continuous (fun x : ℝ => k * max (x - b) 0) := by fun_prop
  have hcsecond : Continuous (fun x : ℝ => (1 - k) * max (x - z) 0) := by fun_prop
  unfold initialAngleRightLoss
  calc
    _ = ∫ x in C..(2 * C), k * max (x - b) 0 + (1 - k) * max (x - z) 0 := by
      apply intervalIntegral.integral_congr
      intro x _
      exact initialAngle_right_integrand_ramps hk0 hk1 hbz hsplit x
    _ = _ := by
      rw [intervalIntegral.integral_add (hcfirst.intervalIntegrable C (2 * C))
        (hcsecond.intervalIntegrable C (2 * C)), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      rfl

theorem initialAngleRampLoss_le_rightLoss {C : ℝ} (hC : 0 ≤ C) (k u b : ℝ) :
    initialAngleRampLoss C u ≤ initialAngleRightLoss C k u b := by
  have hcfirst : Continuous (fun x : ℝ => max (x - u) 0) := by fun_prop
  have hcsecond : Continuous (fun x : ℝ => max (max 0 (x - u)) (k * (x - b))) := by
    fun_prop
  apply intervalIntegral.integral_mono (by linarith)
    (hcfirst.intervalIntegrable C (2 * C)) (hcsecond.intervalIntegrable C (2 * C))
  intro x
  calc
    max (x - u) 0 = max 0 (x - u) := max_comm _ _
    _ ≤ _ := le_max_left _ _

theorem initialAngle_diagonal_integral_le_nicheLoss {C : ℝ} (hC : 0 ≤ C)
    (K k d u v b : ℝ) :
    (∫ x in (-C)..C, max 0 (min (u - K - x) (v - K + x))) ≤
      initialAngleNicheLoss K C k d u v b := by
  have hcfirst : Continuous (fun x : ℝ => max 0 (min (u - K - x) (v - K + x))) := by
    fun_prop
  have hcsecond : Continuous (fun x : ℝ =>
      max (max 0 (min (u - K - x) (v - K + x))) (k * (b - d - x))) := by
    fun_prop
  exact intervalIntegral.integral_mono (by linarith)
    (hcfirst.intervalIntegrable (-C) C) (hcsecond.intervalIntegrable (-C) C)
    (fun x => le_max_left _ _)

/-- If both ends of the diagonal tent are nonnegative, all its clipped
terms have known signs and its full integral is an explicit quadratic. -/
theorem initialAngle_diagonal_integral_full {K C u v : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hu0 : C + K ≤ u) (hu1 : u ≤ 2 * C)
    (hv0 : C + K ≤ v) (hv1 : v ≤ 2 * C) :
    (∫ x in (-C)..C, max 0 (min (u - K - x) (v - K + x))) =
      ((u + v) / 2 - K) ^ 2 - (v - K - C) ^ 2 / 2 - (u - K - C) ^ 2 / 2 := by
  have hp : (u - v) / 2 ∈ Icc (-C) C := by constructor <;> linarith
  have hh : 0 ≤ (u + v) / 2 - K := by linarith
  calc
    _ = ∫ x in (-C)..C, max (((u + v) / 2 - K) - |x - (u - v) / 2|) 0 := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [show u - K - x = ((u + v) / 2 - K) + (u - v) / 2 - x by ring,
        show v - K + x = ((u + v) / 2 - K) - (u - v) / 2 + x by ring,
        min_symmetric_lines, max_comm]
    _ = _ := by
      rw [integral_positive_tent_centered hp,
        show (u + v) / 2 - K - C - (u - v) / 2 = v - K - C by ring,
        show (u + v) / 2 - K - C + (u - v) / 2 = u - K - C by ring,
        max_eq_left hh, max_eq_left (show 0 ≤ v - K - C by linarith),
        max_eq_left (show 0 ≤ u - K - C by linarith)]

theorem initialAngleRelaxation_le_complement_quadratic {K C k d u v b : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hu0 : C + K ≤ u) (hu1 : u ≤ 2 * C)
    (hv0 : C + K ≤ v) (hv1 : v ≤ 2 * C) :
    initialAngleRelaxation K C k d u v b ≤
      2 * C - 2 * C ^ 2 + 2 * K * C - ((u + v) / 2 - C) ^ 2 := by
  have hright := initialAngleRampLoss_le_rightLoss hC k u b
  have hniche := initialAngle_diagonal_integral_le_nicheLoss hC K k d u v b
  have hgu := initialAngleRampLoss_eq_square (show C ≤ u by linarith) hu1
  have hgv := initialAngleRampLoss_eq_square (show C ≤ v by linarith) hv1
  have hdiag := initialAngle_diagonal_integral_full hC hK hu0 hu1 hv0 hv1
  unfold initialAngleRelaxation
  nlinarith only [hright, hniche, hgu, hgv, hdiag]

/-- Outside both AT calibration regions, the actual finite-support
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
  have hk2 : k ^ 2 ≤ 16 / 25 := by
    nlinarith [mul_nonneg (show 0 ≤ 4 / 5 - k by linarith)
      (show 0 ≤ 4 / 5 + k by linarith)]
  have hs : s < 13 / 10 := by
    apply (sq_lt_sq₀ hs0 (by norm_num : (0 : ℝ) ≤ 13 / 10)).mp
    nlinarith only [hs2, hk2]
  have hkdBound : k * d < 3 / 10 := by linarith
  have hCterm : 0 ≤ (3 * k - 1) * C :=
    mul_nonneg (by linarith) hC
  have hvu : u < v := by nlinarith
  have hv : C + (Real.sqrt 2 - 1) < v := hu.trans hvu
  have hgap : 9 / 20 < (u + v) / 2 - C := by nlinarith
  exact (initialAngleRelaxation_le_complement_quadratic hC (by linarith)
    hu.le hu1 hv.le hv1).trans_lt
    (initialAngle_complement_bound initialAngle_offset_sq hgap)

/-- The scalar relaxation is bounded from the actual cap roof and partial
barrier, with its own centered middle-half window. -/
theorem IsDownwardCap.capScore_le_initialAngleRelaxation {U : Set Plane}
    (hU : IsDownwardCap U) {C α : ℝ} (hC : 0 ≤ C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α < Real.pi / 2) :
    capScore U α ≤ initialAngleRelaxation (Real.sqrt 2 - 1) C (terminalSlope α)
      (terminalInset α) (diagonalRight U - 1) (diagonalLeft U - 1)
      (terminalSupportPosition U α) := by
  exact hU.capScore_le_three_support_integrals_centered hC hleft hright hα0 hαL

end AmbidextrousSofa
