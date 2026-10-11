module

public import AmbidextrousSofa.Analysis.TerminalCompanionCurvature

@[expose] public section

/-!
# The actual initial companion wall under unit curvature

The two Stieltjes coordinate moments start at the literal left endpoint
of the top face. Their sine-kernel combination bounds the companion wall
at that abscissa by the initial height deficit. The top-face atom is
outside the half-open density interval throughout.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem IsDownwardCap.secondWall_le_height_sub_one_of_unit_prefix
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {K t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hsub : Ioc (Real.pi / 2) (t + Real.pi / 2) ⊆ S)
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) t), ρ (s + Real.pi / 2) ≤ 1) :
    secondWall U t (MovingSofaOptimality.vplus U (Real.pi / 2)).1 ≤ capHeight U - 1 := by
  have hmom := hU.shiftedCompanion_sub_eq_integral_of_density hρ hρ0 hρK heq ht.1.le
    (by simpa only [zero_add] using hsub)
  simp only [shiftedCompanionX, shiftedCompanionY, zero_add, Real.sin_zero, Real.cos_zero,
    add_zero, top_vplus_snd_eq_capHeight] at hmom
  have hvi : IntervalIntegrable (fun s => 1 - ρ (s + Real.pi / 2)) volume 0 t :=
    intervalIntegrable_const.sub (intervalIntegrable_bounded_real_density
      (hρ.comp (measurable_id.add_const _)) (fun s => hρ0 _) (fun s => hρK _) _ _)
  -- The sine kernel `sin (t - s)` is nonnegative on `[0, t]`.
  have hnonneg : 0 ≤ ∫ s in 0..t, (1 - ρ (s + Real.pi / 2)) * Real.sin (t - s) := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict ht.1.le ?_
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hunit] with s hs hu
    exact mul_nonneg (sub_nonneg.2 hu) (Real.sin_nonneg_of_nonneg_of_le_pi
      (sub_nonneg.2 hs.2.le) (by linarith [hs.1, ht.2, Real.pi_pos]))
  have hkernel : (∫ s in 0..t, (1 - ρ (s + Real.pi / 2)) * Real.sin (t - s)) =
      Real.sin t * (∫ s in 0..t, (1 - ρ (s + Real.pi / 2)) * Real.cos s) -
        Real.cos t * ∫ s in 0..t, (1 - ρ (s + Real.pi / 2)) * Real.sin s := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub
        ((hvi.mul_continuousOn Real.continuous_cos.continuousOn).const_mul _)
        ((hvi.mul_continuousOn Real.continuous_sin.continuousOn).const_mul _)]
    congr 1 with s
    rw [Real.sin_sub]
    ring
  rw [← hmom.1, ← hmom.2] at hkernel
  have hsupp : coordDot (MovingSofaOptimality.vplus U (t + Real.pi / 2)) (companionNormal t) =
      support U (companionNormal t) := by
    rw [companionNormal_eq_unitNormal]
    exact MovingSofaOptimality.dot_vplus_uvec U (t + Real.pi / 2)
  rw [secondWall, div_le_iff₀ (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)]
  simp only [coordDot, companionNormal] at hsupp ⊢
  linear_combination hnonneg - hsupp + hkernel + Real.sin_sq_add_cos_sq t

end AmbidextrousSofa
