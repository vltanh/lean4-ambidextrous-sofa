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
  have hi : IntegrableOn MovingSofaOptimality.vvec (Ioo t (Real.pi / 2)) (upperCurvature U) :=
    MovingSofaOptimality.continuous_vvec.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hvec : ∫ s in Ioo t (Real.pi / 2), MovingSofaOptimality.vvec s ∂upperCurvature U = _ :=
    MovingSofaOptimality.cvx_integral_vvec_Ioo hU.imported_isConvexBody ht.2
  rw [htop, Prod.ext_iff, fst_integral hi, snd_integral hi] at hvec
  simp only [MovingSofaOptimality.vvec, setIntegral_eq_density_mul_of_restrict_withDensity hρ hρ0
    heq measurableSet_Ioo hsub, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le ht.2.le, mul_neg, intervalIntegral.integral_neg,
    Prod.fst_sub, Prod.snd_sub] at hvec
  have hsupp := MovingSofaOptimality.dot_vplus_uvec U t
  change (MovingSofaOptimality.vplus U t).1 * Real.cos t +
    (MovingSofaOptimality.vplus U t).2 * Real.sin t = support U (unitNormal t) at hsupp
  have hρi := intervalIntegrable_bounded_real_density hρ hρ0 hρK t (Real.pi / 2)
  have hsin := (hρi.mul_continuousOn Real.continuous_sin.continuousOn).const_mul (Real.cos t)
  have hcos := (hρi.mul_continuousOn Real.continuous_cos.continuousOn).const_mul (Real.sin t)
  have hk (s : ℝ) : Real.sin (s - t) * (ρ s - 1) = Real.cos t * (ρ s * Real.sin s) -
      Real.sin t * (ρ s * Real.cos s) - Real.sin (s - t) := by rw [Real.sin_sub]; ring
  rw [firstWall]
  congr 1
  simp only [hk]
  rw [intervalIntegral.integral_sub (hsin.sub hcos)
      (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_sub hsin hcos,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp [Real.cos_pi_div_two_sub]
  linear_combination Real.cos t * hvec.1 + Real.sin t * hvec.2 - hsupp

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
  refine hU.isCap.firstWall_eq_horizontal_density_kernel hρ hρ0 hρK heq ht (fun s hs => ?_)
    (hU.top_vminus_pi_div_two hheight hmiddle)
  have := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, hs.1, Real.pi_pos], hs.2⟩
  exact mem_regularCurvatureDomain_iff.mpr
    ⟨ht.1.trans hs.1, by linarith [hs.2, Real.pi_pos], hs.2.ne, by simpa using this.ne'⟩

end AmbidextrousSofa
