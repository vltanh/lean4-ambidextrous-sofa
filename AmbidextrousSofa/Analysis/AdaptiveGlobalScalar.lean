module

public import AmbidextrousSofa.Analysis.AdaptiveGlobalParameters

@[expose] public section

/-!
# The unique maximum along the complete competitive-width family

The exact scalar value has derivative `(2 B - 1) a'`. The width derivative
is negative, while the endpoint factor increases strictly and vanishes at
the cubic-defined reference angle. This proves a global comparison on the
whole parameter interval, including both endpoints.
-/

noncomputable section

open Set

namespace AmbidextrousSofa.Analysis

theorem beta_mem_family_interval : beta ∈ Icc (0 : ℝ) (Real.pi / 4) :=
  ⟨beta_pos.le, beta_lt_pi_div_four.le⟩

theorem hasDerivAt_familyBoundary {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    HasDerivAt (fun x => 2 * familyEndpoint x - 1)
      (familyCot b * (2 * Real.cos b - familyCot b * Real.sin b)) b := by
  apply (((((Real.hasDerivAt_cos b).div_const 2).const_sub (1 / 2)).add
    ((hasDerivAt_familyCot hb).mul (Real.hasDerivAt_sin b))).const_mul 2).sub_const 1
    |>.congr_deriv
  ring

theorem familyWidth_derivative_neg {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    -(familyCot b * (familyCot b * Real.cos b + 2 * Real.sin b)) / 3 < 0 := by
  have hc : 0 < Real.cos b := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hb.1, Real.pi_pos], by linarith [hb.2, Real.pi_pos]⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hb.1 (by linarith [hb.2, Real.pi_pos])
  have hK := familyCot_pos hb
  linarith [mul_pos (mul_pos hK hK) hc, mul_nonneg hK.le hs]

theorem strictMonoOn_familyBoundary :
    StrictMonoOn (fun b => 2 * familyEndpoint b - 1) (Icc (0 : ℝ) (Real.pi / 4)) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun _ hb => (hasDerivAt_familyBoundary hb).continuousAt.continuousWithinAt) fun b hb => ?_
  rw [interior_Icc] at hb
  rw [(hasDerivAt_familyBoundary (Ioo_subset_Icc_self hb)).deriv]
  have hc : 0 < Real.cos b := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hb.1, Real.pi_pos], by linarith [hb.2, Real.pi_pos]⟩
  exact mul_pos (familyCot_pos (Ioo_subset_Icc_self hb))
    (by linarith [familyCot_mul_sin_le_cos (Ioo_subset_Icc_self hb)])

theorem familyCot_beta_identity : 2 * familyCot beta * Real.sin beta = Real.cos beta := by
  have hs : Reference.R * Real.sin (tailPhase beta) = 2 / 3 := Reference.R_mul_sin_firstPhase
  have hc : Reference.R * Real.cos (tailPhase beta) = (1 - Reference.k) * Real.cos beta :=
    Reference.R_mul_cos_firstPhase
  have hA : 4 * Reference.A * Real.sin beta = 1 := Reference.four_mul_A_mul_sinBeta
  have hR : Reference.R ≠ 0 := fun h => by norm_num [h] at hs
  rw [familyCot, ← mul_div_mul_left _ _ hR, hs, hc, Reference.k]
  linear_combination Real.cos beta * hA

theorem familyEndpoint_beta : familyEndpoint beta = 1 / 2 := by
  unfold familyEndpoint
  linear_combination familyCot_beta_identity / 2

theorem familyWidth_beta : familyWidth beta = 4 / 3 * Reference.A := by
  have hA : 4 * Reference.A * Real.sin beta = 1 := Reference.four_mul_A_mul_sinBeta
  apply mul_right_cancel₀ (show Real.sin beta ≠ 0 from Reference.sinBeta_ne_zero)
  unfold familyWidth
  linear_combination Real.cos beta / 3 * familyCot_beta_identity +
    Real.sin_sq_add_cos_sq beta / 3 - hA / 3

theorem hasDerivAt_familyScore {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    HasDerivAt familyScore
      ((2 * familyEndpoint b - 1) *
        (-(familyCot b * (familyCot b * Real.cos b + 2 * Real.sin b)) / 3)) b := by
  apply ((((((hasDerivAt_familyBoundary hb).mul
    ((hasDerivAt_familyWidth hb).add (Real.hasDerivAt_sin b))).add
      (((hasDerivAt_familyWidth hb).const_mul 3).mul (Real.hasDerivAt_cos b))).add
        (hasDerivAt_id b)).sub_const 2).div_const 2).congr_deriv
  simp only [familyWidth, familyEndpoint, Pi.add_apply]
  linear_combination -1 / 2 * Real.sin_sq_add_cos_sq b

theorem continuousOn_familyScore :
    ContinuousOn familyScore (Icc (0 : ℝ) (Real.pi / 4)) :=
  fun _ hb => (hasDerivAt_familyScore hb).continuousAt.continuousWithinAt

theorem strictMonoOn_familyScore_before_beta : StrictMonoOn familyScore (Icc (0 : ℝ) beta) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (continuousOn_familyScore.mono fun _ hb => ⟨hb.1, hb.2.trans beta_lt_pi_div_four.le⟩)
    fun b hb => ?_
  rw [interior_Icc] at hb
  have hi : b ∈ Icc (0 : ℝ) (Real.pi / 4) := ⟨hb.1.le, (hb.2.trans beta_lt_pi_div_four).le⟩
  rw [(hasDerivAt_familyScore hi).deriv]
  have hbound := strictMonoOn_familyBoundary hi beta_mem_family_interval hb.2
  simp only [familyEndpoint_beta] at hbound
  exact mul_pos_of_neg_of_neg (by linarith) (familyWidth_derivative_neg hi)

theorem strictAntiOn_familyScore_after_beta :
    StrictAntiOn familyScore (Icc beta (Real.pi / 4)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (continuousOn_familyScore.mono fun _ hb => ⟨beta_pos.le.trans hb.1, hb.2⟩) fun b hb => ?_
  rw [interior_Icc] at hb
  have hi : b ∈ Icc (0 : ℝ) (Real.pi / 4) := ⟨(beta_pos.trans hb.1).le, hb.2.le⟩
  rw [(hasDerivAt_familyScore hi).deriv]
  have hbound := strictMonoOn_familyBoundary beta_mem_family_interval hi hb.1
  simp only [familyEndpoint_beta] at hbound
  exact mul_neg_of_pos_of_neg (by linarith) (familyWidth_derivative_neg hi)

theorem familyScore_lt_beta_of_ne {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (hne : b ≠ beta) : familyScore b < familyScore beta := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact strictMonoOn_familyScore_before_beta ⟨hb.1, hlt.le⟩ ⟨beta_pos.le, le_rfl⟩ hlt
  · exact strictAntiOn_familyScore_after_beta ⟨le_rfl, beta_lt_pi_div_four.le⟩
      ⟨hgt.le, hb.2⟩ hgt

theorem familyScore_beta : familyScore beta = M / 2 := by
  have hM : M - beta + 2 = 1 / Y := (eq_div_iff Y_ne_zero).2 M_sub_beta_add_two_mul_Y
  have hA : Reference.A * Real.cos beta = 1 / (4 * Y) := Reference.A_mul_cosBeta
  rw [familyScore, familyEndpoint_beta, familyWidth_beta]
  linear_combination 2 * hA - hM / 2

theorem familyScore_le_half_M {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyScore b ≤ M / 2 := by
  rw [← familyScore_beta]
  obtain rfl | hne := eq_or_ne b beta
  exacts [le_rfl, (familyScore_lt_beta_of_ne hb hne).le]

theorem familyScore_eq_half_M_iff {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyScore b = M / 2 ↔ b = beta := by
  rw [← familyScore_beta]
  exact ⟨fun h => not_not.1 fun hne => (familyScore_lt_beta_of_ne hb hne).ne h, fun h => h ▸ rfl⟩

end AmbidextrousSofa.Analysis
