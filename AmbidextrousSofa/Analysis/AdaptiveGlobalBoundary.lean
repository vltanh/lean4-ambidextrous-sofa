module

public import AmbidextrousSofa.Analysis.EulerFlux

@[expose] public section

/-!
# Width traces and reflection-symmetric pairs

`QuarterPair.WidthTraces u a` prescribes the four endpoint values of a pair
whose common horizontal endpoint `a`, the width, is allowed to vary. Twice
the functional is the integral of the value density
`2 * density - self-variation density` plus the self-variation.

A symmetric pair has the reflection `t ↦ π/2 - t` of its first support as
its companion support. Its second flux and force are the reflections of the
first ones, so the Euler equation of the first flux alone gives stationarity
and the boundary value of the self-variation.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa.Analysis

def QuarterPair.WidthTraces (u : QuarterPair) (a : ℝ) : Prop :=
  u.f 0 = a ∧ u.g 0 = 1 ∧ u.f (Real.pi / 2) = 1 ∧ u.g (Real.pi / 2) = a

theorem QuarterPair.sameTraces_of_widthTraces {u v : QuarterPair} {a : ℝ}
    (hu : u.WidthTraces a) (hv : v.WidthTraces a) : u.SameTraces v :=
  ⟨hu.1.trans hv.1.symm, hu.2.1.trans hv.2.1.symm, hu.2.2.1.trans hv.2.2.1.symm,
    hu.2.2.2.trans hv.2.2.2.symm⟩

theorem two_mul_adaptiveFunctional (u : QuarterPair) :
    2 * adaptiveFunctional u = (∫ t in (0 : ℝ)..(Real.pi / 2),
      2 * adaptiveDensity u t - adaptiveLinearDensity u u t) + adaptiveFirstVariation u u := by
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rw [intervalIntegral.integral_sub
    (((continuousOn_adaptiveDensity u).intervalIntegrable_of_Icc hL).const_mul 2)
    ((continuousOn_adaptiveLinearDensity u u).intervalIntegrable_of_Icc hL),
    intervalIntegral.integral_const_mul, adaptiveFunctional, adaptiveFirstVariation]
  ring

/-- The pair whose companion support is the reflection `t ↦ π/2 - t` of `F`. -/
def symmetricPair (F FD : ℝ → ℝ) (hF : ∀ t, HasDerivAt F (FD t) t) (hFD : Continuous FD) :
    QuarterPair where
  f := F
  g t := F (Real.pi / 2 - t)
  fD := FD
  gD t := -FD (Real.pi / 2 - t)
  continuous_f := (continuous_iff_continuousAt.2 fun t => (hF t).continuousAt).continuousOn
  continuous_g := ((continuous_iff_continuousAt.2 fun t => (hF t).continuousAt).comp
    (continuous_sub_left _)).continuousOn
  continuous_fD := hFD.continuousOn
  continuous_gD := (hFD.comp (continuous_sub_left _)).neg.continuousOn
  hasDeriv_f t _ := (hF t).hasDerivWithinAt
  hasDeriv_g t _ := ((hF _).comp_const_sub _ t).hasDerivWithinAt

variable {F FD : ℝ → ℝ} {hF : ∀ t, HasDerivAt F (FD t) t} {hFD : Continuous FD}

theorem symmetricPair_widthTraces {a : ℝ} (h0 : F 0 = a) (hL : F (Real.pi / 2) = 1) :
    (symmetricPair F FD hF hFD).WidthTraces a := by
  simp [QuarterPair.WidthTraces, symmetricPair, h0, hL]

/-- The companion flux and force are the reflections of the first ones. -/
theorem symmetricPair_reflect (t : ℝ) :
    (symmetricPair F FD hF hFD).fluxG t =
        -(symmetricPair F FD hF hFD).fluxF (Real.pi / 2 - t) ∧
      (symmetricPair F FD hF hFD).forceG t =
        (symmetricPair F FD hF hFD).forceF (Real.pi / 2 - t) := by
  simp only [QuarterPair.fluxF, QuarterPair.fluxG, QuarterPair.forceF, QuarterPair.forceG,
    QuarterPair.p, QuarterPair.q, symmetricPair, sub_sub_cancel, min_def, max_def]
  constructor <;> split_ifs <;> linarith

/-- The Euler equation of the first flux gives both Euler equations. -/
theorem symmetricPair_euler (h : ∀ t ∈ Ioo 0 (Real.pi / 2),
      HasDerivAt (symmetricPair F FD hF hFD).fluxF ((symmetricPair F FD hF hFD).forceF t) t) :
    (∀ t ∈ Ioo 0 (Real.pi / 2), HasDerivWithinAt (symmetricPair F FD hF hFD).fluxF
      ((symmetricPair F FD hF hFD).forceF t) (Ioi t) t) ∧
    ∀ t ∈ Ioo 0 (Real.pi / 2), HasDerivWithinAt (symmetricPair F FD hF hFD).fluxG
      ((symmetricPair F FD hF hFD).forceG t) (Ioi t) t := by
  refine ⟨fun t ht => (h t ht).hasDerivWithinAt, fun t ht => ?_⟩
  rw [(symmetricPair_reflect t).2]
  have hs : Real.pi / 2 - t ∈ Ioo 0 (Real.pi / 2) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  exact (((h _ hs).comp_const_sub _ t).neg.hasDerivWithinAt.congr
    (fun s _ => (symmetricPair_reflect s).1) (symmetricPair_reflect t).1).congr_deriv (neg_neg _)

theorem symmetricPair_stationary (h : ∀ t ∈ Ioo 0 (Real.pi / 2),
      HasDerivAt (symmetricPair F FD hF hFD).fluxF ((symmetricPair F FD hF hFD).forceF t) t) :
    (symmetricPair F FD hF hFD).Stationary :=
  QuarterPair.stationary_of_euler _ (symmetricPair_euler h).1 (symmetricPair_euler h).2

theorem symmetricPair_self_variation (h : ∀ t ∈ Ioo 0 (Real.pi / 2),
      HasDerivAt (symmetricPair F FD hF hFD).fluxF ((symmetricPair F FD hF hFD).forceF t) t) :
    adaptiveFirstVariation (symmetricPair F FD hF hFD) (symmetricPair F FD hF hFD) =
      2 * ((symmetricPair F FD hF hFD).fluxF (Real.pi / 2) * F (Real.pi / 2) -
        (symmetricPair F FD hF hFD).fluxF 0 * F 0) := by
  rw [adaptiveFirstVariation_eq_boundary _ _ (symmetricPair_euler h).1 (symmetricPair_euler h).2,
    (symmetricPair_reflect _).1, (symmetricPair_reflect _).1, sub_self, sub_zero]
  simp only [symmetricPair, sub_self, sub_zero]
  ring

end AmbidextrousSofa.Analysis
