import AmbidextrousSofa.Analysis.AsymmetricTent
import AmbidextrousSofa.Analysis.InitialAngleCalibration

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
theorem integral_positive_wall_difference_full {A B k a c e : ℝ}
    (hk0 : -1 < k) (hk1 : k < 1)
    (hAl : A ≤ (k * e - c) / (1 + k))
    (hrB : (a - k * e) / (1 - k) ≤ B) :
    (∫ x in A..B,
      max (min ((a - x) - k * (e - x)) ((c + x) - k * (e - x))) 0) =
        (max ((1 + k) * a + (1 - k) * c - 2 * k * e) 0) ^ 2 /
          (4 * (1 - k ^ 2)) := by
  let l := (k * e - c) / (1 + k)
  let r := (a - k * e) / (1 - k)
  have hp : 0 < 1 + k := by linarith
  have hm : 0 < 1 - k := by linarith
  have hden : 0 < 1 - k ^ 2 := by nlinarith only [mul_pos hp hm]
  have hl : (1 + k) * l = k * e - c := mul_div_cancel₀ _ (ne_of_gt hp)
  have hr : (1 - k) * r = a - k * e := mul_div_cancel₀ _ (ne_of_gt hm)
  have hfun : (fun x : ℝ =>
      max (min ((a - x) - k * (e - x)) ((c + x) - k * (e - x))) 0) =
      (fun x : ℝ => max (min ((1 + k) * (x - l)) ((1 - k) * (r - x))) 0) := by
    funext x
    rw [show (a - x) - k * (e - x) = (1 - k) * (r - x) by nlinarith only [hr],
      show (c + x) - k * (e - x) = (1 + k) * (x - l) by nlinarith only [hl],
      min_comm]
  have hnum : (1 - k ^ 2) * (r - l) =
      (1 + k) * a + (1 - k) * c - 2 * k * e := by
    calc
      _ = (1 + k) * ((1 - k) * r) - (1 - k) * ((1 + k) * l) := by ring
      _ = _ := by rw [hr, hl]; ring
  have hmax : max ((1 + k) * a + (1 - k) * c - 2 * k * e) 0 =
      (1 - k ^ 2) * max (r - l) 0 := by
    rw [← hnum]
    simpa only [mul_zero] using (mul_max_of_nonneg (r - l) 0 hden.le).symm
  rw [hfun, integral_positive_asymmetric_tent_full hp hm hAl hrB,
    show (1 + k) + (1 - k) = (2 : ℝ) by ring, hmax]
  field_simp [ne_of_gt hden] <;> ring

/-- A finite niche increase is no larger than the complete-area increase
of the positive tent above the terminal line. The integral itself remains
on the original middle window, with all three clipping mechanisms. -/
theorem initialAngleNicheLoss_increment_le_area {K C k d u v₀ v₁ b : ℝ}
    (hC : 0 ≤ C) (hk0 : -1 < k) (hk1 : k < 1) (hv : v₀ ≤ v₁) :
    initialAngleNicheLoss K C k d u v₁ b - initialAngleNicheLoss K C k d u v₀ b ≤
      ((max ((1 + k) * u + (1 - k) * v₁ - 2 * K - 2 * k * (b - d)) 0) ^ 2 -
        (max ((1 + k) * u + (1 - k) * v₀ - 2 * K - 2 * k * (b - d)) 0) ^ 2) /
          (4 * (1 - k ^ 2)) := by
  let l₀ := (k * (b - d) - (v₀ - K)) / (1 + k)
  let l₁ := (k * (b - d) - (v₁ - K)) / (1 + k)
  let r := ((u - K) - k * (b - d)) / (1 - k)
  let A := min (-C) l₁
  let B := max C r
  let T (v x : ℝ) :=
    max (min ((u - K - x) - k * (b - d - x))
      ((v - K + x) - k * (b - d - x))) 0
  let N (v x : ℝ) :=
    max (max 0 (min (u - K - x) (v - K + x))) (k * (b - d - x))
  have hp : 0 < 1 + k := by linarith
  have hl : l₁ ≤ l₀ := by
    apply (div_le_div_iff₀ hp hp).2
    nlinarith only [mul_nonneg hp.le (sub_nonneg.mpr hv)]
  have hAC : A ≤ -C := min_le_left _ _
  have hCB : C ≤ B := le_max_left _ _
  have hAl₁ : A ≤ l₁ := min_le_right _ _
  have hAl₀ : A ≤ l₀ := hAl₁.trans hl
  have hrB : r ≤ B := le_max_right _ _
  have hT (v : ℝ) : Continuous (T v) := by dsimp [T]; fun_prop
  have hN (v : ℝ) : Continuous (N v) := by dsimp [N]; fun_prop
  have hTmono (x : ℝ) : T v₀ x ≤ T v₁ x := by
    apply max_le_max _ le_rfl
    exact min_le_min le_rfl (by linarith only [hv])
  have hpoint (x : ℝ) : N v₁ x - N v₀ x ≤ T v₁ x - T v₀ x :=
    wall_increment_le_shifted_tent (by linarith only [hv])
  have hmono : (∫ x in (-C)..C, N v₁ x - N v₀ x) ≤
      ∫ x in (-C)..C, T v₁ x - T v₀ x :=
    intervalIntegral.integral_mono (by linarith)
      (((hN v₁).sub (hN v₀)).intervalIntegrable (-C) C)
      (((hT v₁).sub (hT v₀)).intervalIntegrable (-C) C) hpoint
  have hext : (∫ x in (-C)..C, T v₁ x - T v₀ x) ≤
      ∫ x in A..B, T v₁ x - T v₀ x :=
    intervalIntegral.integral_mono_interval hAC (by linarith) hCB
      (ae_of_all _ fun x => sub_nonneg.mpr (hTmono x))
      (((hT v₁).sub (hT v₀)).intervalIntegrable A B)
  have harea₁ : (∫ x in A..B, T v₁ x) =
      (max ((1 + k) * u + (1 - k) * v₁ - 2 * K - 2 * k * (b - d)) 0) ^ 2 /
        (4 * (1 - k ^ 2)) := by
    have h := integral_positive_wall_difference_full (a := u - K) (c := v₁ - K)
      (e := b - d) hk0 hk1 hAl₁ hrB
    rw [show (1 + k) * (u - K) + (1 - k) * (v₁ - K) - 2 * k * (b - d) =
      (1 + k) * u + (1 - k) * v₁ - 2 * K - 2 * k * (b - d) by ring] at h
    exact h
  have harea₀ : (∫ x in A..B, T v₀ x) =
      (max ((1 + k) * u + (1 - k) * v₀ - 2 * K - 2 * k * (b - d)) 0) ^ 2 /
        (4 * (1 - k ^ 2)) := by
    have h := integral_positive_wall_difference_full (a := u - K) (c := v₀ - K)
      (e := b - d) hk0 hk1 hAl₀ hrB
    rw [show (1 + k) * (u - K) + (1 - k) * (v₀ - K) - 2 * k * (b - d) =
      (1 + k) * u + (1 - k) * v₀ - 2 * K - 2 * k * (b - d) by ring] at h
    exact h
  rw [intervalIntegral.integral_sub ((hN v₁).intervalIntegrable (-C) C)
    ((hN v₀).intervalIntegrable (-C) C)] at hmono
  rw [intervalIntegral.integral_sub ((hT v₁).intervalIntegrable A B)
    ((hT v₀).intervalIntegrable A B), harea₁, harea₀] at hext
  change initialAngleNicheLoss K C k d u v₁ b - initialAngleNicheLoss K C k d u v₀ b ≤ _
    at hmono
  exact (hmono.trans hext).trans_eq (by ring)

/-- The complete tent-area secant is bounded by its final exposed
rising-wall length times the support increment. -/
theorem initialAngleNicheLoss_increment_le {K C k d u v₀ v₁ b : ℝ}
    (hC : 0 ≤ C) (hk0 : -1 < k) (hk1 : k < 1) (hv : v₀ ≤ v₁) :
    initialAngleNicheLoss K C k d u v₁ b - initialAngleNicheLoss K C k d u v₀ b ≤
      max ((1 + k) * u + (1 - k) * v₁ - 2 * K - 2 * k * (b - d)) 0 *
        (v₁ - v₀) / (2 * (1 + k)) := by
  let P₀ := (1 + k) * u + (1 - k) * v₀ - 2 * K - 2 * k * (b - d)
  let P₁ := (1 + k) * u + (1 - k) * v₁ - 2 * K - 2 * k * (b - d)
  have hp : 0 < 1 + k := by linarith
  have hm : 0 < 1 - k := by linarith
  have hden : 0 < 1 - k ^ 2 := by nlinarith only [mul_pos hp hm]
  have hP : P₀ ≤ P₁ := by
    dsimp [P₀, P₁]
    nlinarith only [mul_nonneg hm.le (sub_nonneg.mpr hv)]
  have hsec : ((max P₁ 0) ^ 2 - (max P₀ 0) ^ 2) / (4 * (1 - k ^ 2)) ≤
      max P₁ 0 * (v₁ - v₀) / (2 * (1 + k)) := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hden)).2
    calc
      _ ≤ 2 * max P₁ 0 * (P₁ - P₀) := positivePart_square_increment_le hP
      _ = (max P₁ 0 * (v₁ - v₀) / (2 * (1 + k))) * (4 * (1 - k ^ 2)) := by
        dsimp [P₀, P₁]
        field_simp [ne_of_gt hp] <;> ring
  exact (initialAngleNicheLoss_increment_le_area hC hk0 hk1 hv).trans hsec

/-- In the high-right alternative, raising `v` to `C` costs no more niche
area than the exact charged-exterior reward it creates. -/
theorem initialAngleRelaxation_le_raise_left {K C k d u v b : ℝ}
    (hC : 0 ≤ C) (hk0 : 1 / 3 ≤ k) (hk1 : k < 1) (hkd : k * d ≤ K)
    (hu : u ≤ 2 * C) (hv : v ≤ C) (hb : C ≤ b) :
    initialAngleRelaxation K C k d u v b ≤ initialAngleRelaxation K C k d u C b := by
  have hk : 0 ≤ k := by linarith
  have hkneg : -1 < k := by linarith
  have hp : 0 < 1 + k := by linarith
  have hnum : (1 + k) * u + (1 - k) * C - 2 * K - 2 * k * (b - d) ≤
      2 * (1 + k) * C := by
    nlinarith only [mul_le_mul_of_nonneg_left hu hp.le,
      mul_le_mul_of_nonneg_left hb hk, hkd,
      mul_nonneg (show 0 ≤ 3 * k - 1 by linarith) hC]
  have hmax : max ((1 + k) * u + (1 - k) * C - 2 * K - 2 * k * (b - d)) 0 ≤
      2 * (1 + k) * C :=
    max_le hnum (mul_nonneg (mul_nonneg (by norm_num) hp.le) hC)
  have hpaid : initialAngleNicheLoss K C k d u C b - initialAngleNicheLoss K C k d u v b ≤
      C * (C - v) := by
    apply (initialAngleNicheLoss_increment_le hC hkneg hk1 hv).trans
    apply (div_le_iff₀ (mul_pos (by norm_num) hp)).2
    nlinarith only [mul_le_mul_of_nonneg_right hmax (sub_nonneg.mpr hv)]
  have hgv := initialAngleRampLoss_eq_affine hC hv
  have hgC := initialAngleRampLoss_eq_affine hC (le_refl C)
  unfold initialAngleRelaxation
  nlinarith only [hpaid, hgv, hgC]

end AmbidextrousSofa
