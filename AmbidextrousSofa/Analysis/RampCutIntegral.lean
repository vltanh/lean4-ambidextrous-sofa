import AmbidextrousSofa.Analysis.AsymmetricTent

/-!
# Ordinary one-sided triangular area payments

A nonnegative integrable gap on a charged interval pays the entire area
of a fitted affine triangle on either side of its peak. The surrounding
gap is retained by integral monotonicity.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem integral_affine_scalar (s t p k δ : ℝ) :
    (∫ x in s..t, δ + k * (x - p)) =
      δ * (t - s) + k * ((t ^ 2 - s ^ 2) / 2 - p * (t - s)) := by
  have hfun (x : ℝ) : δ + k * (x - p) = k * x + (δ - k * p) := by ring
  simp_rw [hfun]
  rw [intervalIntegral.integral_add
      ((continuous_const.mul continuous_id).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem integral_gap_ge_left_ramp {f : ℝ → ℝ} {A B p k δ : ℝ}
    (hf : ∀ l r, IntervalIntegrable f volume l r)
    (hk : 0 < k) (hδ : 0 ≤ δ) (hp : p ∈ Icc A B)
    (hfit : δ ≤ k * (p - A))
    (hf0 : ∀ x ∈ Icc A B, 0 ≤ f x)
    (hcut : ∀ x ∈ Icc (p - δ / k) p, δ + k * (x - p) ≤ f x) :
    δ ^ 2 / (2 * k) ≤ ∫ x in A..B, f x := by
  have hδk : 0 ≤ δ / k := div_nonneg hδ hk.le
  have hA : A ≤ p - δ / k := by
    have h := (div_le_iff₀ hk).mpr hfit
    linarith only [h]
  have hlocal := intervalIntegral.integral_mono_on
    (show p - δ / k ≤ p by linarith only [hδk])
    ((show Continuous (fun x : ℝ => δ + k * (x - p)) by fun_prop).intervalIntegrable _ _)
    (hf _ _) hcut
  have harea : (∫ x in (p - δ / k)..p, δ + k * (x - p)) = δ ^ 2 / (2 * k) := by
    rw [integral_affine_scalar]
    field_simp [hk.ne'] <;> ring
  rw [harea] at hlocal
  apply hlocal.trans
  apply intervalIntegral.integral_mono_interval hA
    (show p - δ / k ≤ p by linarith only [hδk]) hp.2 _ (hf A B)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hf0 x (Ioc_subset_Icc_self hx)

theorem integral_gap_ge_right_ramp {f : ℝ → ℝ} {A B p k δ : ℝ}
    (hf : ∀ l r, IntervalIntegrable f volume l r)
    (hk : 0 < k) (hδ : 0 ≤ δ) (hp : p ∈ Icc A B)
    (hfit : δ ≤ k * (B - p))
    (hf0 : ∀ x ∈ Icc A B, 0 ≤ f x)
    (hcut : ∀ x ∈ Icc p (p + δ / k), δ - k * (x - p) ≤ f x) :
    δ ^ 2 / (2 * k) ≤ ∫ x in A..B, f x := by
  have hδk : 0 ≤ δ / k := div_nonneg hδ hk.le
  have hB : p + δ / k ≤ B := by
    have h := (div_le_iff₀ hk).mpr hfit
    linarith only [h]
  have hlocal := intervalIntegral.integral_mono_on
    (show p ≤ p + δ / k by linarith only [hδk])
    ((show Continuous (fun x : ℝ => δ - k * (x - p)) by fun_prop).intervalIntegrable _ _)
    (hf _ _) hcut
  have harea : (∫ x in p..(p + δ / k), δ - k * (x - p)) = δ ^ 2 / (2 * k) := by
    have hfun (x : ℝ) : δ - k * (x - p) = δ + (-k) * (x - p) := by ring
    simp_rw [hfun]
    rw [integral_affine_scalar]
    field_simp [hk.ne'] <;> ring
  rw [harea] at hlocal
  apply hlocal.trans
  apply intervalIntegral.integral_mono_interval hp.1
    (show p ≤ p + δ / k by linarith only [hδk]) hB _ (hf A B)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hf0 x (Ioc_subset_Icc_self hx)

end AmbidextrousSofa
