module

public import AmbidextrousSofa.Analysis.LocalSourceDensity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

@[expose] public section

/-!
# Sharp densities from local interval bounds

The Lebesgue differentiation theorem identifies the limiting average of a
bounded density over small positive intervals with the density itself.
Thus a local interval bound, at the points where it is proved, bounds the
actual Radon–Nikodym density there; the coefficient need not be
continuous. Applied on an open interval where the measure is dominated by
a multiple of Lebesgue measure, local bounds at almost every point give
domination by the pointwise coefficient.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem measureReal_eq_integral_of_restrict_withDensity
    {μ : Measure ℝ} {ρ : ℝ → ℝ} {S s : Set ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (heq : μ.restrict S = (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hs : MeasurableSet s) (hsub : s ⊆ S) :
    μ.real s = ∫ t in s, ρ t := by
  have h : μ s = μ.restrict S s := by rw [Measure.restrict_apply hs, inter_eq_left.mpr hsub]
  rw [measureReal_def, h, heq, withDensity_apply _ hs, Measure.restrict_restrict_of_subset hsub,
    integral_eq_lintegral_of_nonneg_ae (.of_forall hρ0) hρ.aestronglyMeasurable]

/-- A local interval bound at the points of an open set where it is proved bounds a bounded
density of the measure at almost every such point. -/
theorem ae_density_le_of_local_bound
    {μ : Measure ℝ} {ρ f : ℝ → ℝ} {S : Set ℝ} {P : ℝ → Prop} {C : ℝ}
    (hS : IsOpen S) (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : μ.restrict S = (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hlocal : ∀ t ∈ S, P t → ∀ ε > 0,
      ∃ δ > 0, ∀ d : ℝ, 0 < d → d < δ → μ.real (Ioc t (t + d)) ≤ (f t + ε) * d) :
    ∀ᵐ t : ℝ ∂volume, t ∈ S → P t → ρ t ≤ f t := by
  have hint : LocallyIntegrable ρ volume := locallyIntegrable_iff.mpr fun K hK =>
    IntegrableOn.of_bound hK.measure_lt_top hρ.aestronglyMeasurable C (Eventually.of_forall
      fun t => (Real.norm_eq_abs _).trans_le ((abs_of_nonneg (hρ0 t)).trans_le (hρC t)))
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hint] with t hdt ht hP
  obtain ⟨a, b, htIoo, hIoo⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hS.mem_nhds ht)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ, hδ, hbound⟩ := hlocal t ht hP ε hε
  refine le_of_tendsto (hdt t).tendsto_slope_zero_right ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδ (sub_pos.mpr htIoo.2))] with d ⟨hd0, hd⟩
  rw [lt_min_iff] at hd
  rw [intervalIntegral.integral_same, sub_zero, smul_eq_mul, inv_mul_le_iff₀ hd0,
    intervalIntegral.integral_of_le (by linarith), ← measureReal_eq_integral_of_restrict_withDensity
      hρ hρ0 heq measurableSet_Ioc fun s hs => hIoo ⟨htIoo.1.trans hs.1, by linarith [hs.2]⟩]
  exact (hbound d hd0 hd.1).trans_eq (mul_comm _ _)

/-- A measure dominated by `C` times Lebesgue measure on `(A, B)`, with local interval bounds
`κ t + ε` around almost every point of `(A, B)`, is dominated there by the density `κ`. -/
theorem restrict_Ioo_le_withDensity_of_local_bound {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    {A B C : ℝ} {κ : ℝ → ℝ} (hC : 0 ≤ C)
    (hcoarse : μ.restrict (Ioo A B) ≤ ENNReal.ofReal C • volume.restrict (Ioo A B))
    (hlocal : ∀ᵐ t, t ∈ Ioo A B → ∀ ε > 0, ∃ δ > 0, ∀ a b : ℝ, t - δ < a → a ≤ b →
      b < t + δ → μ.real (Ioc a b) ≤ (κ t + ε) * (b - a)) :
    μ.restrict (Ioo A B) ≤
      (volume.restrict (Ioo A B)).withDensity (fun t => ENNReal.ofReal (κ t)) := by
  have : IsFiniteMeasure (μ.restrict (Ioo A B)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  obtain ⟨ρ, hρ, hρbounds, heq⟩ := exists_bounded_real_density_of_le_smul hC hcoarse
  have hle := ae_density_le_of_local_bound isOpen_Ioo hρ (fun t => (hρbounds t).1)
    (fun t => (hρbounds t).2) heq (f := κ) (P := fun t => ∀ ε > 0, ∃ δ > 0, ∀ a b : ℝ,
      t - δ < a → a ≤ b → b < t + δ → μ.real (Ioc a b) ≤ (κ t + ε) * (b - a))
    fun t _ hP ε hε => by
      obtain ⟨δ, hδ, h⟩ := hP ε hε
      refine ⟨δ, hδ, fun d hd hdδ => ?_⟩
      simpa only [add_sub_cancel_left] using h t (t + d) (by linarith) (by linarith) (by linarith)
  rw [heq]
  refine withDensity_mono ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hlocal,
    ae_restrict_of_ae hle] with t ht hlocal hle
  exact ENNReal.ofReal_le_ofReal (hle ht (hlocal ht))

end AmbidextrousSofa
