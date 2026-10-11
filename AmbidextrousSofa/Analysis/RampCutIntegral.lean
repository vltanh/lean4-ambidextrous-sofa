module

public import AmbidextrousSofa.Analysis.AsymmetricTent

@[expose] public section

/-!
# Ordinary one-sided triangular area payments

A nonnegative integrable gap on a charged interval pays the entire area
of a fitted affine triangle on either side of its peak. The surrounding
gap is retained by integral monotonicity.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem integral_gap_ge_left_ramp {f : ℝ → ℝ} {A B p k δ : ℝ}
    (hf : ∀ l r, IntervalIntegrable f volume l r)
    (hk : 0 < k) (hδ : 0 ≤ δ) (hp : p ∈ Icc A B)
    (hfit : δ ≤ k * (p - A))
    (hf0 : ∀ x ∈ Icc A B, 0 ≤ f x)
    (hcut : ∀ x ∈ Icc (p - δ / k) p, δ + k * (x - p) ≤ f x) :
    δ ^ 2 / (2 * k) ≤ ∫ x in A..B, f x := by
  have hδk : 0 ≤ δ / k := div_nonneg hδ hk.le
  calc δ ^ 2 / (2 * k) = ∫ x in (p - δ / k)..p, δ + k * (x - p) := by
        simp_rw [show ∀ x, δ + k * (x - p) = k * x + (δ - k * p) from fun x => by ring]
        rw [integral_affine]; field_simp; ring
    _ ≤ ∫ x in (p - δ / k)..p, f x := intervalIntegral.integral_mono_on (by linarith)
        (Continuous.intervalIntegrable (by fun_prop) _ _) (hf _ _) hcut
    _ ≤ ∫ x in A..B, f x := intervalIntegral.integral_mono_interval
        (by linarith [(div_le_iff₀' hk).mpr hfit]) (by linarith) hp.2
        ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => hf0 x (Ioc_subset_Icc_self hx))
        (hf A B)

theorem integral_gap_ge_right_ramp {f : ℝ → ℝ} {A B p k δ : ℝ}
    (hf : ∀ l r, IntervalIntegrable f volume l r)
    (hk : 0 < k) (hδ : 0 ≤ δ) (hp : p ∈ Icc A B)
    (hfit : δ ≤ k * (B - p))
    (hf0 : ∀ x ∈ Icc A B, 0 ≤ f x)
    (hcut : ∀ x ∈ Icc p (p + δ / k), δ - k * (x - p) ≤ f x) :
    δ ^ 2 / (2 * k) ≤ ∫ x in A..B, f x := by
  -- Reflect `x ↦ -x` and apply the left ramp.
  have h := integral_gap_ge_left_ramp (f := fun x => f (-x)) (A := -B) (B := -A) (p := -p)
    (fun l r => by simpa using (IntervalIntegrable.iff_comp_neg).mp (hf (-l) (-r))) hk hδ
    ⟨neg_le_neg hp.2, neg_le_neg hp.1⟩ (by linarith)
    (fun x hx => hf0 _ ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    (fun x hx => by linarith [hcut (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩])
  simpa [intervalIntegral.integral_comp_neg] using h

end AmbidextrousSofa
