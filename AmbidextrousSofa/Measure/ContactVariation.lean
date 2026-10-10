module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-!
# One-sided contact and strict-gap integral variations

The quotients are bounded between zero and one. Consequently dominated
convergence converts a literal clipped linear displacement into the
measure of its contact set or its strict positive-gap set. These generic
lemmas make no geometric differentiability or source-selection assumption.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem contactRamp_quotient_bounds {ε d : ℝ} (hε : 0 < ε) (hd : 0 ≤ d) :
    0 ≤ max (ε - d) 0 / ε ∧ max (ε - d) 0 / ε ≤ 1 := by
  refine ⟨div_nonneg (le_max_right _ _) hε.le, ?_⟩
  apply (div_le_one hε).mpr
  exact max_le (sub_le_self _ hd) hε.le

theorem strictGapRamp_quotient_bounds {ε d : ℝ} (hε : 0 < ε) :
    0 ≤ min ε (max d 0) / ε ∧ min ε (max d 0) / ε ≤ 1 := by
  refine ⟨div_nonneg (le_min hε.le (le_max_right _ _)) hε.le, ?_⟩
  exact (div_le_one hε).mpr (min_le_left _ _)

theorem tendsto_contactRamp_quotient {d : ℝ} (hd : 0 ≤ d) :
    Tendsto (fun ε : ℝ => max (ε - d) 0 / ε) (𝓝[>] 0)
      (𝓝 (if d = 0 then 1 else 0)) := by
  by_cases hd0 : d = 0
  · rw [if_pos hd0]
    apply tendsto_const_nhds.congr'
    filter_upwards [show ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε from self_mem_nhdsWithin]
      with ε hε
    simp only [hd0, sub_zero, max_eq_left hε.le, div_self hε.ne']
  · rw [if_neg hd0]
    have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT hdpos] with ε hε
    rw [max_eq_right (sub_nonpos.mpr hε.2.le), zero_div]

theorem tendsto_strictGapRamp_quotient (d : ℝ) :
    Tendsto (fun ε : ℝ => min ε (max d 0) / ε) (𝓝[>] 0)
      (𝓝 (if 0 < d then 1 else 0)) := by
  by_cases hd : 0 < d
  · rw [if_pos hd]
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT hd] with ε hε
    rw [max_eq_left hd.le, min_eq_left hε.2.le, div_self hε.1.ne']
  · rw [if_neg hd]
    apply tendsto_const_nhds.congr'
    filter_upwards [show ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε from self_mem_nhdsWithin]
      with ε hε
    rw [max_eq_right (le_of_not_gt hd), min_eq_right hε.le, zero_div]

theorem tendsto_integral_contactRamp_quotient {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {d : X → ℝ} (hd : Measurable d)
    (hd0 : ∀ᵐ x ∂μ, 0 ≤ d x) :
    Tendsto (fun ε : ℝ => ∫ x, max (ε - d x) 0 / ε ∂μ) (𝓝[>] 0)
      (𝓝 (μ.real {x | d x = 0})) := by
  let E : Set X := {x | d x = 0}
  have hE : MeasurableSet E := measurableSet_eq_fun hd measurable_const
  have hmeas : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable (fun x => max (ε - d x) 0 / ε) μ :=
    Eventually.of_forall (fun ε =>
      (((measurable_const.sub hd).max measurable_const).div_const ε).aestronglyMeasurable)
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∀ᵐ x ∂μ, ‖max (ε - d x) 0 / ε‖ ≤ (1 : ℝ) := by
    filter_upwards [show ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε from self_mem_nhdsWithin]
      with ε hε
    filter_upwards [hd0] with x hx
    have h := contactRamp_quotient_bounds hε hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun ε : ℝ => max (ε - d x) 0 / ε) (𝓝[>] 0)
        (𝓝 (E.indicator (fun _ => (1 : ℝ)) x)) := by
    filter_upwards [hd0] with x hx
    simpa only [E, indicator, mem_setOf_eq] using tendsto_contactRamp_quotient hx
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun _ : X => (1 : ℝ)) hmeas hbound (integrable_const 1) hlim
  simpa only [integral_indicator_const 1 hE, smul_eq_mul, mul_one, E] using h

theorem tendsto_integral_strictGapRamp_quotient {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {d : X → ℝ} (hd : Measurable d) :
    Tendsto (fun ε : ℝ => ∫ x, min ε (max (d x) 0) / ε ∂μ) (𝓝[>] 0)
      (𝓝 (μ.real {x | 0 < d x})) := by
  let E : Set X := {x | 0 < d x}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hd
  have hmeas : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable (fun x => min ε (max (d x) 0) / ε) μ :=
    Eventually.of_forall (fun ε =>
      ((measurable_const.min (hd.max measurable_const)).div_const ε).aestronglyMeasurable)
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∀ᵐ x ∂μ, ‖min ε (max (d x) 0) / ε‖ ≤ (1 : ℝ) := by
    filter_upwards [show ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε from self_mem_nhdsWithin]
      with ε hε
    exact Eventually.of_forall (fun x => by
      have h := strictGapRamp_quotient_bounds (d := d x) hε
      simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2)
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun ε : ℝ => min ε (max (d x) 0) / ε) (𝓝[>] 0)
        (𝓝 (E.indicator (fun _ => (1 : ℝ)) x)) :=
    Eventually.of_forall (fun x => by
      simpa only [E, indicator, mem_setOf_eq] using tendsto_strictGapRamp_quotient (d x))
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun _ : X => (1 : ℝ)) hmeas hbound (integrable_const 1) hlim
  simpa only [integral_indicator_const 1 hE, smul_eq_mul, mul_one, E] using h

end AmbidextrousSofa
