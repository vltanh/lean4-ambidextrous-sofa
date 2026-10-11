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

theorem tendsto_contactRamp_quotient {d : ℝ} (hd : 0 ≤ d) :
    Tendsto (fun ε : ℝ => max (ε - d) 0 / ε) (𝓝[>] 0) (𝓝 (if d = 0 then 1 else 0)) := by
  rcases hd.eq_or_lt with rfl | hd
  · refine tendsto_const_nhds.congr' (eventually_mem_nhdsWithin.mono fun ε (hε : 0 < ε) => ?_)
    simp [max_eq_left hε.le, hε.ne']
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hd] with ε hε
    simp [hd.ne', max_eq_right (sub_nonpos.2 hε.2.le)]

theorem tendsto_strictGapRamp_quotient (d : ℝ) :
    Tendsto (fun ε : ℝ => min ε (max d 0) / ε) (𝓝[>] 0) (𝓝 (if 0 < d then 1 else 0)) := by
  by_cases hd : 0 < d
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hd] with ε hε
    simp [hd, max_eq_left hd.le, min_eq_left hε.2.le, hε.1.ne']
  · refine tendsto_const_nhds.congr' (eventually_mem_nhdsWithin.mono fun ε (hε : 0 < ε) => ?_)
    simp [hd, max_eq_right (not_lt.1 hd), min_eq_right hε.le]

/-- Dominated convergence for quotients between zero and one: their integrals converge
to the measure of the set where their pointwise limit is one. -/
theorem tendsto_integral_of_quotient_bounds {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] {F : ℝ → X → ℝ} {E : Set X} (hE : MeasurableSet E)
    (hF : ∀ ε, Measurable (F ε)) (hF01 : ∀ ε > 0, ∀ᵐ x ∂μ, 0 ≤ F ε x ∧ F ε x ≤ 1)
    (hlim : ∀ᵐ x ∂μ, Tendsto (F · x) (𝓝[>] 0) (𝓝 (E.indicator 1 x))) :
    Tendsto (fun ε => ∫ x, F ε x ∂μ) (𝓝[>] 0) (𝓝 (μ.real E)) := by
  have h := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] 0) 1
    (Eventually.of_forall fun ε => (hF ε).aestronglyMeasurable)
    (eventually_mem_nhdsWithin.mono fun ε hε => (hF01 ε hε).mono fun x hx => by
      simpa [abs_of_nonneg hx.1] using hx.2)
    (integrable_const 1) hlim
  rwa [integral_indicator_one hE] at h

theorem tendsto_integral_contactRamp_quotient {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {d : X → ℝ} (hd : Measurable d)
    (hd0 : ∀ᵐ x ∂μ, 0 ≤ d x) :
    Tendsto (fun ε : ℝ => ∫ x, max (ε - d x) 0 / ε ∂μ) (𝓝[>] 0)
      (𝓝 (μ.real {x | d x = 0})) :=
  tendsto_integral_of_quotient_bounds μ (measurableSet_eq_fun hd measurable_const)
    (fun ε => ((measurable_const.sub hd).max measurable_const).div_const ε)
    (fun ε hε => hd0.mono fun x hx =>
      ⟨div_nonneg (le_max_right _ _) hε.le, (div_le_one hε).2 (max_le (sub_le_self _ hx) hε.le)⟩)
    (hd0.mono fun x hx => by simpa [indicator_apply] using tendsto_contactRamp_quotient hx)

theorem tendsto_integral_strictGapRamp_quotient {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {d : X → ℝ} (hd : Measurable d) :
    Tendsto (fun ε : ℝ => ∫ x, min ε (max (d x) 0) / ε ∂μ) (𝓝[>] 0)
      (𝓝 (μ.real {x | 0 < d x})) :=
  tendsto_integral_of_quotient_bounds μ (measurableSet_lt measurable_const hd)
    (fun ε => (measurable_const.min (hd.max measurable_const)).div_const ε)
    (fun ε hε => .of_forall fun x =>
      ⟨div_nonneg (le_min hε.le (le_max_right _ _)) hε.le, (div_le_one hε).2 (min_le_left _ _)⟩)
    (.of_forall fun x => by simpa [indicator_apply] using tendsto_strictGapRamp_quotient (d x))

end AmbidextrousSofa
