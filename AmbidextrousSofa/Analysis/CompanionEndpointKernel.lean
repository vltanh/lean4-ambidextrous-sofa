import AmbidextrousSofa.Analysis.TerminalCompanionCurvature

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
    secondWall U t (Imported.vplus U (Real.pi / 2)).1 ≤ capHeight U - 1 := by
  have hmom := hU.shiftedCompanion_sub_eq_integral_of_density hρ hρ0 hρK heq ht.1.le
    (by simpa only [zero_add] using hsub)
  simp only [shiftedCompanionX_zero, shiftedCompanionY_zero, top_vplus_snd_eq_capHeight] at hmom
  have hρi : IntervalIntegrable (fun s => ρ (s + Real.pi / 2)) volume 0 t :=
    intervalIntegrable_bounded_real_density (hρ.comp (measurable_id.add_const _))
      (fun s => hρ0 _) (fun s => hρK _) _ _
  have hvi : IntervalIntegrable (fun s => 1 - ρ (s + Real.pi / 2)) volume 0 t :=
    intervalIntegrable_const.sub hρi
  have hsi := hvi.mul_continuousOn Real.continuous_sin.continuousOn
  have hci := hvi.mul_continuousOn Real.continuous_cos.continuousOn
  have hki : IntervalIntegrable (fun s => (1 - ρ (s + Real.pi / 2)) * Real.sin (s - t))
      volume 0 t := hvi.mul_continuousOn
    ((Real.continuous_sin.comp (continuous_id.sub continuous_const)).continuousOn)
  have hkernel : (∫ s in 0..t, (1 - ρ (s + Real.pi / 2)) * Real.sin (s - t)) =
      Real.cos t * (shiftedCompanionY U t - (capHeight U - 1)) -
        Real.sin t * (shiftedCompanionX U t - (Imported.vplus U (Real.pi / 2)).1) := by
    calc
      _ = ∫ s in 0..t,
          Real.cos t * ((1 - ρ (s + Real.pi / 2)) * Real.sin s) -
            Real.sin t * ((1 - ρ (s + Real.pi / 2)) * Real.cos s) := by
        apply intervalIntegral.integral_congr
        intro s _hs
        rw [Real.sin_sub]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (hsi.const_mul _) (hci.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          ← hmom.2, ← hmom.1]
  have hnonpos : (∫ s in 0..t,
      (1 - ρ (s + Real.pi / 2)) * Real.sin (s - t)) ≤ 0 := by
    have hbound := intervalIntegral.integral_mono_ae_restrict ht.1.le hki
      (intervalIntegrable_const (c := (0 : ℝ))) (show ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) t),
        (1 - ρ (s + Real.pi / 2)) * Real.sin (s - t) ≤ (0 : ℝ) from by
          rw [← restrict_Ioo_eq_restrict_Icc]
          filter_upwards [ae_restrict_mem measurableSet_Ioo, hunit] with s hs hu
          have hsin : Real.sin (s - t) ≤ 0 := by
            rw [show s - t = -(t - s) by ring, Real.sin_neg]
            exact neg_nonpos.mpr (Real.sin_nonneg_of_nonneg_of_le_pi
              (sub_nonneg.mpr hs.2.le) (by linarith only [hs.1, ht.2, Real.pi_pos]))
          exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu) hsin)
    simpa only [intervalIntegral.integral_zero] using hbound
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  have hsupp : coordDot (Imported.vplus U (t + Real.pi / 2)) (companionNormal t) =
      support U (companionNormal t) := by
    rw [companionNormal_eq_unitNormal]
    exact Imported.dot_vplus_uvec U (t + Real.pi / 2)
  unfold secondWall
  apply (div_le_iff₀ hc).mpr
  dsimp only [shiftedCompanionX, shiftedCompanionY] at hkernel
  dsimp only [coordDot, companionNormal] at hsupp
  nlinarith only [hnonpos, hkernel, hsupp, Real.sin_sq_add_cos_sq t]

end AmbidextrousSofa
