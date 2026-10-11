module

public import AmbidextrousSofa.Analysis.AsymmetricTent
public import AmbidextrousSofa.Analysis.InitialAngleCalibration

@[expose] public section

/-!
# The high-right finite-support comparison

Subtracting the terminal wall from the two diagonal lines produces a
positive asymmetric tent. Its complete area bounds the increment of the
actual floored niche on the smaller window. The final exposed length
then bounds every finite increase of the left support parameter. In the
high-right alternative this cost is paid by the charged left exterior,
so the scalar relaxation can be increased to `v = C`.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-- The complete area of the diagonal tent above the terminal line. -/
theorem integral_positive_wall_difference_full {A B K k d u v b : ℝ}
    (hk0 : -1 < k) (hk1 : k < 1)
    (hAl : A ≤ (k * (b - d) - (v - K)) / (1 + k))
    (hrB : (u - K - k * (b - d)) / (1 - k) ≤ B) :
    (∫ x in A..B, max (min (u - K - x - k * (b - d - x)) (v - K + x - k * (b - d - x))) 0) =
      (max ((1 + k) * u + (1 - k) * v - 2 * K - 2 * k * (b - d)) 0) ^ 2 /
        (4 * (1 - k ^ 2)) := by
  have hp : 0 < 1 + k := by linarith
  have hm : 0 < 1 - k := by linarith
  have hden : 0 < 1 - k ^ 2 := by nlinarith
  generalize hl : (k * (b - d) - (v - K)) / (1 + k) = l at hAl
  generalize hr : (u - K - k * (b - d)) / (1 - k) = r at hrB
  rw [div_eq_iff hp.ne'] at hl
  rw [div_eq_iff hm.ne'] at hr
  rw [intervalIntegral.integral_congr (g := fun x => max (min ((1 + k) * (x - l))
      ((1 - k) * (r - x))) 0) fun x _ => by
        dsimp only
        rw [min_comm,
          show v - K + x - k * (b - d - x) = (1 + k) * (x - l) by linear_combination -hl,
          show u - K - x - k * (b - d - x) = (1 - k) * (r - x) by linear_combination hr],
    integral_positive_asymmetric_tent_full hp hm hAl hrB,
    show (1 + k) * u + (1 - k) * v - 2 * K - 2 * k * (b - d) = (1 - k ^ 2) * (r - l) by
      linear_combination (1 + k) * hr - (1 - k) * hl,
    show max ((1 - k ^ 2) * (r - l)) 0 = (1 - k ^ 2) * max (r - l) 0 by
      rw [mul_max_of_nonneg _ _ hden.le, mul_zero]]
  field_simp
  ring

/-- A finite niche increase is no larger than the complete-area increase
of the positive tent above the terminal line, which the final exposed
rising-wall length times the support increment bounds. The integral itself
remains on the original middle window, with all three clipping mechanisms. -/
theorem initialAngleNicheLoss_increment_le {K C k d u v₀ v₁ b : ℝ}
    (hC : 0 ≤ C) (hk0 : -1 < k) (hk1 : k < 1) (hv : v₀ ≤ v₁) :
    initialAngleNicheLoss K C k d u v₁ b - initialAngleNicheLoss K C k d u v₀ b ≤
      max ((1 + k) * u + (1 - k) * v₁ - 2 * K - 2 * k * (b - d)) 0 *
        (v₁ - v₀) / (2 * (1 + k)) := by
  have hp : 0 < 1 + k := by linarith
  have hm : 0 < 1 - k := by linarith
  set A := min (-C) ((k * (b - d) - (v₁ - K)) / (1 + k))
  set B := max C ((u - K - k * (b - d)) / (1 - k))
  have hT (v : ℝ) : Continuous fun x : ℝ =>
      max (min (u - K - x - k * (b - d - x)) (v - K + x - k * (b - d - x))) 0 := by fun_prop
  have hN (v : ℝ) : Continuous fun x : ℝ =>
      max (max 0 (min (u - K - x) (v - K + x))) (k * (b - d - x)) := by fun_prop
  have h1 := intervalIntegral.integral_mono (μ := volume) (by linarith : -C ≤ C)
    (((hN v₁).fun_sub (hN v₀)).intervalIntegrable _ _)
    (((hT v₁).fun_sub (hT v₀)).intervalIntegrable _ _)
    fun x => wall_increment_le_shifted_tent (by linarith)
  have h2 := intervalIntegral.integral_mono_interval (μ := volume) (min_le_left _ _)
    (by linarith : -C ≤ C) (le_max_left _ _)
    (ae_of_all _ fun x => sub_nonneg.2 (max_le_max (min_le_min le_rfl (by linarith)) le_rfl))
    (((hT v₁).fun_sub (hT v₀)).intervalIntegrable A B)
  rw [initialAngleNicheLoss, initialAngleNicheLoss, ← intervalIntegral.integral_sub
    ((hN v₁).intervalIntegrable _ _) ((hN v₀).intervalIntegrable _ _)]
  refine (h1.trans h2).trans ?_
  rw [intervalIntegral.integral_sub ((hT v₁).intervalIntegrable _ _)
      ((hT v₀).intervalIntegrable _ _),
    integral_positive_wall_difference_full hk0 hk1 (min_le_right _ _) (le_max_right _ _),
    integral_positive_wall_difference_full hk0 hk1
      ((min_le_right _ _).trans (div_le_div_of_nonneg_right (by linarith) hp.le))
      (le_max_right _ _), ← sub_div, div_le_div_iff₀ (by nlinarith) (by linarith)]
  have hP : (1 + k) * u + (1 - k) * v₀ - 2 * K - 2 * k * (b - d) ≤
      (1 + k) * u + (1 - k) * v₁ - 2 * K - 2 * k * (b - d) := by
    linarith [mul_le_mul_of_nonneg_left hv hm.le]
  linarith [mul_le_mul_of_nonneg_right (positivePart_square_increment_le hP)
    (by linarith : (0 : ℝ) ≤ 2 * (1 + k))]

/-- In the high-right alternative, raising `v` to `C` costs no more niche
area than the exact charged-exterior reward it creates. -/
theorem initialAngleRelaxation_le_raise_left {K C k d u v b : ℝ}
    (hC : 0 ≤ C) (hk0 : 1 / 3 ≤ k) (hk1 : k < 1) (hkd : k * d ≤ K)
    (hu : u ≤ 2 * C) (hv : v ≤ C) (hb : C ≤ b) :
    initialAngleRelaxation K C k d u v b ≤ initialAngleRelaxation K C k d u C b := by
  have hp : 0 < 1 + k := by linarith
  have hmax : max ((1 + k) * u + (1 - k) * C - 2 * K - 2 * k * (b - d)) 0 ≤
      2 * (1 + k) * C :=
    max_le (by linarith [mul_le_mul_of_nonneg_left hu hp.le,
      mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ k), hkd,
      mul_nonneg (show 0 ≤ 3 * k - 1 by linarith) hC]) (by positivity)
  have hprod := mul_le_mul_of_nonneg_right hmax (sub_nonneg.mpr hv)
  have hpaid := (initialAngleNicheLoss_increment_le hC (by linarith) hk1 hv).trans
    ((div_le_iff₀ (by linarith)).2 (by linarith) : _ ≤ C * (C - v))
  unfold initialAngleRelaxation
  linarith [initialAngleRampLoss_eq_affine hC hv, initialAngleRampLoss_eq_affine hC (le_refl C)]

end AmbidextrousSofa
