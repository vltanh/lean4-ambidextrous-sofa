module

public import MovingSofaOptimality.Basic.SurfaceArea
public import MovingSofaOptimality.Injectivity.ArmLengths

@[expose] public section

/-!
# Three facts about the surface area measure of a convex body

The formalization of Baek's paper in `MovingSofaOptimality` proves these three facts as private
helpers (`sa_sigmaFun_sub` in `Basic/SurfaceArea.lean`, `inj_measurable_vplus` and
`inj_dot_vplus_vvec_sub` in `Injectivity/ArmLengths.lean`). This module proves them again from
that library's public results, so that the ambidextrous proofs can use them.

* `sigmaFun_sub`: the increment of the distribution function `σ_K` of the surface area measure;
* `measurable_vplus`: the right support point `v_K⁺` is measurable;
* `dot_vplus_vvec_sub`: `v_K⁺(b) · v_b - v_K⁺(a) · v_a = σ_K((a, b]) - ∫_a^b h_K`.
-/

noncomputable section

open Set MeasureTheory MovingSofaOptimality

namespace AmbidextrousSofa

/-- The increment of the distribution function `σ_K` of the surface area measure. -/
theorem sigmaFun_sub {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (s t : ℝ) :
    sigmaFun K t - sigmaFun K s =
      dot (vplus K t) (vvec t) - dot (vplus K s) (vvec s) + ∫ r in s..t, supp K r := by
  unfold sigmaFun
  rw [← intervalIntegral.integral_interval_sub_left (hK.continuous_supp.intervalIntegrable 0 t)
    (hK.continuous_supp.intervalIntegrable 0 s)]
  ring

/-- The right support point `v_K⁺` of a convex body is measurable: it is
`h_K(t) u_t + (σ_K(t) - ∫₀ᵗ h_K) v_t`, with a monotone distribution function `σ_K`. -/
theorem measurable_vplus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    Measurable (vplus K) := by
  have e : vplus K = fun t =>
      supp K t • uvec t + (sigmaFun K t - ∫ s in (0 : ℝ)..t, supp K s) • vvec t := by
    funext t; rw [← inj_dot_vplus_vvec_eq]; exact vplus_eq_frame K t
  exact e ▸ (hK.continuous_supp.measurable.smul continuous_uvec.measurable).add
    (((monotone_sigmaFun hK).measurable.sub (continuous_integral_supp hK).measurable).smul
      continuous_vvec.measurable)

/-- `v_K⁺(b) · v_b - v_K⁺(a) · v_a = σ_K((a, b]) - ∫_a^b h_K`. -/
theorem dot_vplus_vvec_sub {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ}
    (hab : a < b) :
    dot (vplus K b) (vvec b) - dot (vplus K a) (vvec a) =
      (sigma K (Ioc a b)).toReal - ∫ s in a..b, supp K s := by
  rw [sigma_Ioc hK, ENNReal.toReal_ofReal (sub_nonneg.mpr (monotone_sigmaFun hK hab.le)),
    sigmaFun_sub hK a b]
  ring

end AmbidextrousSofa
