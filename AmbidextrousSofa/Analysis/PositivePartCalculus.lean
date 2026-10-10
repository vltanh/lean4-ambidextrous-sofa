module

public import AmbidextrousSofa.Analysis.LevelSetDerivative
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

/-!
# Absolutely continuous barriers with a clipped variable

Taking the maximum with a constant preserves absolute continuity. At
the clipping level the derivative vanishes almost everywhere, by the
actual level-set derivative theorem. This supplies a barrier principle
which only needs a derivative sign above the barrier; no differentiable
selection at a zero crossing is assumed.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem absolutelyContinuousOnInterval_max_const
    {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) (c : ℝ) :
    AbsolutelyContinuousOnInterval (fun x => max (f x) c) a b := by
  exact (LipschitzWith.id.max_const c).comp_absolutelyContinuousOnInterval hf

/-- This is an almost-everywhere derivative formula, including the
clipping level. The latter case follows from the level set of the
clipped function itself. -/
theorem ae_hasDerivAt_max_const
    {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) (c : ℝ) :
    ∀ᵐ x : ℝ ∂volume, x ∈ uIcc a b →
      HasDerivAt (fun y => max (f y) c)
        (if c < f x then deriv f x else 0) x := by
  have hg := absolutelyContinuousOnInterval_max_const hf c
  filter_upwards [hf.ae_differentiableAt, hg.ae_differentiableAt,
    ae_deriv_eq_zero_on_level (fun y => max (f y) c) c] with x hdf hdg hz
  intro hx
  by_cases hpos : c < f x
  · have heq : (fun y => max (f y) c) =ᶠ[𝓝 x] f := by
      filter_upwards [(hdf hx).continuousAt.eventually (eventually_gt_nhds hpos)]
        with y hy
      exact max_eq_left hy.le
    simpa only [if_pos hpos] using (hdf hx).hasDerivAt.congr_of_eventuallyEq heq
  · have heq : max (f x) c = c := max_eq_right (le_of_not_gt hpos)
    simpa only [if_neg hpos, hz heq] using (hdg hx).hasDerivAt

theorem absolutelyContinuousOnInterval_le_initial_of_ae_deriv_nonpos
    {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hab : a ≤ b)
    (hd : ∀ᵐ x : ℝ ∂volume.restrict (Ioo a b), deriv f x ≤ 0)
    {x : ℝ} (hx : x ∈ Icc a b) :
    f x ≤ f a := by
  have hax : AbsolutelyContinuousOnInterval f a x := hf.mono (by
    rw [uIcc_of_le hx.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hx.2)
  have hdcc : ∀ᵐ y : ℝ ∂volume.restrict (Icc a b), deriv f y ≤ 0 := by
    rwa [← restrict_Ioo_eq_restrict_Icc]
  have hdx : ∀ᵐ y : ℝ ∂volume.restrict (Icc a x), 0 ≤ -deriv f y := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (Icc_subset_Icc le_rfl hx.2) hdcc] with y hy
    exact neg_nonneg.mpr hy
  have hnonneg := intervalIntegral.integral_nonneg_of_ae_restrict hx.1 hdx
  rw [intervalIntegral.integral_neg, hax.integral_deriv_eq_sub] at hnonneg
  linarith

/-- An absolutely continuous function cannot cross a height at which
its derivative is nonpositive almost everywhere above that height. -/
theorem absolutelyContinuousOnInterval_le_of_ae_deriv_nonpos_above
    {f : ℝ → ℝ} {a b H : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hab : a ≤ b) (hstart : f a ≤ H)
    (hd : ∀ᵐ x : ℝ ∂volume.restrict (Ioo a b), H < f x → deriv f x ≤ 0)
    {x : ℝ} (hx : x ∈ Icc a b) :
    f x ≤ H := by
  have hg := absolutelyContinuousOnInterval_max_const hf H
  have hgd : ∀ᵐ y : ℝ ∂volume.restrict (Ioo a b),
      deriv (fun t => max (f t) H) y ≤ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hd,
      ae_restrict_of_ae (ae_hasDerivAt_max_const hf H)] with y hy hdy hmy
    have hymem : y ∈ uIcc a b := by
      rw [uIcc_of_le hab]
      exact ⟨hy.1.le, hy.2.le⟩
    rw [(hmy hymem).deriv]
    split_ifs with hpos
    · exact hdy hpos
    · exact le_rfl
  have hle := absolutelyContinuousOnInterval_le_initial_of_ae_deriv_nonpos hg hab hgd hx
  rw [max_eq_right hstart] at hle
  exact (le_max_left (f x) H).trans hle

end AmbidextrousSofa
