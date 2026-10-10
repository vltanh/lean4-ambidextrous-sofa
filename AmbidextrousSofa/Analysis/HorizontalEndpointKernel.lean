module

public import AmbidextrousSofa.Analysis.TangencyEndpoints
public import AmbidextrousSofa.Analysis.TerminalCompanionCurvature
public import MovingSofaOptimality.Convex.ConvexCurve

@[expose] public section

/-!
# The actual horizontal endpoint leakage kernel

The open-arc Stieltjes identity ends at the left-continuous endpoint of
the top face. Consequently the top atom is retained in the endpoint
data and does not enter the first-quarter density integral. This proves
the exact first-wall kernel directly from the actual curvature measure.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem IsDownwardCap.firstWall_eq_horizontal_density_kernel
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K C t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hsub : Ioo t (Real.pi / 2) ⊆ S)
    (htop : MovingSofaOptimality.vminus U (Real.pi / 2) = (C, 1)) :
    firstWall U t C =
      (∫ s in t..(Real.pi / 2), Real.sin (s - t) * (ρ s - 1)) / Real.sin t := by
  have hvec := MovingSofaOptimality.cvx_integral_vvec_Ioo hU.imported_isConvexBody ht.2
  have hi : IntegrableOn MovingSofaOptimality.vvec (Ioo t (Real.pi / 2)) (MovingSofaOptimality.sigma U) :=
    MovingSofaOptimality.continuous_vvec.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hx := congrArg Prod.fst hvec
  have hy := congrArg Prod.snd hvec
  rw [fst_integral hi, htop] at hx
  rw [snd_integral hi, htop] at hy
  change (∫ s in Ioo t (Real.pi / 2), -Real.sin s ∂upperCurvature U) =
    C - (MovingSofaOptimality.vplus U t).1 at hx
  change (∫ s in Ioo t (Real.pi / 2), Real.cos s ∂upperCurvature U) =
    1 - (MovingSofaOptimality.vplus U t).2 at hy
  rw [setIntegral_eq_density_mul_of_restrict_withDensity hρ hρ0 heq
    measurableSet_Ioo hsub, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le ht.2.le] at hx hy
  have hρi := intervalIntegrable_bounded_real_density hρ hρ0 hρK t (Real.pi / 2)
  have hsin := hρi.mul_continuousOn Real.continuous_sin.continuousOn
  have hcos := hρi.mul_continuousOn Real.continuous_cos.continuousOn
  have hx' : (∫ s in t..(Real.pi / 2), ρ s * Real.sin s) =
      (MovingSofaOptimality.vplus U t).1 - C := by
    simp only [mul_neg, intervalIntegral.integral_neg] at hx
    linarith only [hx]
  have hkernel : (∫ s in t..(Real.pi / 2), Real.sin (s - t) * (ρ s - 1)) =
      Real.cos t * ((MovingSofaOptimality.vplus U t).1 - C - Real.cos t) -
        Real.sin t * (1 - (MovingSofaOptimality.vplus U t).2 - (1 - Real.sin t)) := by
    calc
      _ = ∫ s in t..(Real.pi / 2),
          Real.cos t * (ρ s * Real.sin s - Real.sin s) -
            Real.sin t * (ρ s * Real.cos s - Real.cos s) := by
        apply intervalIntegral.integral_congr
        intro s _hs
        dsimp only
        rw [Real.sin_sub]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub
            ((hsin.sub (Real.continuous_sin.intervalIntegrable _ _)).const_mul _)
            ((hcos.sub (Real.continuous_cos.intervalIntegrable _ _)).const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub hsin (Real.continuous_sin.intervalIntegrable _ _),
          intervalIntegral.integral_sub hcos (Real.continuous_cos.intervalIntegrable _ _),
          hx', hy, integral_sin, integral_cos,
          Real.sin_pi_div_two, Real.cos_pi_div_two, sub_zero]
  have hsupp := MovingSofaOptimality.dot_vplus_uvec U t
  change (MovingSofaOptimality.vplus U t).1 * Real.cos t +
    (MovingSofaOptimality.vplus U t).2 * Real.sin t = support U (unitNormal t) at hsupp
  unfold firstWall
  congr 1
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- The actual maximizing cap supplies both the density domain and the
literal right endpoint of its top face. -/
theorem IsFullCapMaximizer.firstWall_eq_horizontal_density_kernel
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {K t : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity
        (fun s => ENNReal.ofReal (ρ s)))
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    firstWall U t (horizontalRight U - capWidth U / 4) =
      (∫ s in t..(Real.pi / 2), Real.sin (s - t) * (ρ s - 1)) / Real.sin t := by
  apply hU.isCap.firstWall_eq_horizontal_density_kernel hρ hρ0 hρK heq ht
    _ (hU.top_vminus_pi_div_two hheight hmiddle)
  intro s hs
  apply mem_regularCurvatureDomain_iff.mpr
  refine ⟨ht.1.trans hs.1, hs.2.trans (by linarith [Real.pi_pos]), ?_, ?_⟩
  · exact ne_of_lt hs.2
  · simpa only [zero_mul, add_zero] using
      (Real.cos_pos_of_mem_Ioo (show s ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [ht.1, hs.1, hs.2, Real.pi_pos])).ne'

end AmbidextrousSofa
