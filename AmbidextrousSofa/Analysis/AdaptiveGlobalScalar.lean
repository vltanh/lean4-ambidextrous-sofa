import AmbidextrousSofa.Analysis.AdaptiveGlobalParameters

/-!
# The unique maximum along the complete competitive-width family

The exact scalar value has derivative `(2 B - 1) a'`. The width derivative
is negative, while the endpoint factor increases strictly and vanishes at
the cubic-defined reference angle. This proves a global comparison on the
whole parameter interval, including both endpoints.
-/

noncomputable section

open Set
open scoped Topology

namespace AmbidextrousSofa.Analysis

theorem beta_mem_family_interval : beta ∈ Icc (0 : ℝ) (Real.pi / 4) :=
  ⟨beta_pos.le, beta_lt_pi_div_four.le⟩

theorem hasDerivAt_familyEndpoint {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    HasDerivAt familyEndpoint
      (familyCot b * Real.cos b - familyCot b ^ 2 * Real.sin b / 2) b := by
  apply ((((Real.hasDerivAt_cos b).div_const 2).const_sub (1 / 2)).add
    ((hasDerivAt_familyCot hb).mul (Real.hasDerivAt_sin b))).congr_deriv
  ring

theorem hasDerivAt_familyBoundary {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    HasDerivAt (fun x => 2 * familyEndpoint x - 1)
      (familyCot b * (2 * Real.cos b - familyCot b * Real.sin b)) b := by
  apply (((hasDerivAt_familyEndpoint hb).const_mul 2).sub_const 1).congr_deriv
  ring

theorem continuousOn_familyEndpoint :
    ContinuousOn familyEndpoint (Icc (0 : ℝ) (Real.pi / 4)) :=
  fun _ hb => (hasDerivAt_familyEndpoint hb).continuousAt.continuousWithinAt

theorem familyWidth_derivative_neg {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    -(familyCot b * (familyCot b * Real.cos b + 2 * Real.sin b)) / 3 < 0 := by
  have hc : 0 < Real.cos b := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hb.1, Real.pi_pos], by linarith [hb.2, Real.pi_pos]⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hb.1
    (by linarith [hb.2, Real.pi_pos])
  have hi : 0 < familyCot b * Real.cos b + 2 * Real.sin b :=
    add_pos_of_pos_of_nonneg (mul_pos (familyCot_pos hb) hc) (by positivity)
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos (familyCot_pos hb) hi)) (by norm_num)

theorem strictMonoOn_familyBoundary :
    StrictMonoOn (fun b => 2 * familyEndpoint b - 1) (Icc (0 : ℝ) (Real.pi / 4)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    ((continuousOn_familyEndpoint.const_mul 2).sub continuousOn_const)
  intro b hb
  rw [interior_Icc] at hb
  have hi : b ∈ Icc (0 : ℝ) (Real.pi / 4) := ⟨hb.1.le, hb.2.le⟩
  rw [(hasDerivAt_familyBoundary hi).deriv]
  have hc : 0 < Real.cos b := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hb.1, Real.pi_pos], by linarith [hb.2, Real.pi_pos]⟩
  exact mul_pos (familyCot_pos hi) (by linarith [familyCot_mul_sin_le_cos hi])

theorem familyCot_beta_identity : 2 * familyCot beta * Real.sin beta = Real.cos beta := by
  have hs : Reference.R * Real.sin (tailPhase beta) = 2 / 3 :=
    Reference.R_mul_sin_firstPhase
  have hc : Reference.R * Real.cos (tailPhase beta) =
      4 / 3 * Reference.A * Real.cos beta := by
    have h := Reference.R_mul_cos_firstPhase
    unfold Reference.k Reference.cosBeta at h
    change Reference.R * Real.cos (tailPhase beta) = _ at h
    nlinarith
  have hcot : familyCot beta * Real.sin (tailPhase beta) = Real.cos (tailPhase beta) := by
    unfold familyCot
    exact div_mul_cancel₀ _ (ne_of_gt (sin_family_phase_pos beta_mem_family_interval))
  calc
    2 * familyCot beta * Real.sin beta =
        3 * (Reference.R * Real.sin (tailPhase beta)) * familyCot beta * Real.sin beta := by
      rw [hs]
      ring
    _ = 3 * (Reference.R * Real.cos (tailPhase beta)) * Real.sin beta := by
      rw [← hcot]
      ring
    _ = 4 * Reference.A * Real.sin beta * Real.cos beta := by rw [hc]; ring
    _ = Real.cos beta := by
      have hA := Reference.four_mul_A_mul_sinBeta
      unfold Reference.sinBeta at hA
      rw [hA]
      ring

theorem familyEndpoint_beta : familyEndpoint beta = 1 / 2 := by
  unfold familyEndpoint
  nlinarith [familyCot_beta_identity]

theorem familyWidth_beta : familyWidth beta = 4 / 3 * Reference.A := by
  have hcross := congrArg (fun x : ℝ => x * Real.cos beta) familyCot_beta_identity
  have hw : 3 * familyWidth beta * Real.sin beta = 1 := by
    unfold familyWidth
    nlinarith [hcross, Real.sin_sq_add_cos_sq beta]
  have hA := Reference.four_mul_A_mul_sinBeta
  unfold Reference.sinBeta at hA
  have heq : (familyWidth beta - 4 / 3 * Reference.A) * Real.sin beta = 0 := by
    nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right Reference.sinBeta_ne_zero)

theorem hasDerivAt_familyScore {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    HasDerivAt familyScore
      ((2 * familyEndpoint b - 1) *
        (-(familyCot b * (familyCot b * Real.cos b + 2 * Real.sin b)) / 3)) b := by
  apply ((((((hasDerivAt_familyBoundary hb).mul
    ((hasDerivAt_familyWidth hb).add (Real.hasDerivAt_sin b))).add
      (((hasDerivAt_familyWidth hb).const_mul 3).mul (Real.hasDerivAt_cos b))).add
        (hasDerivAt_id b)).sub_const 2).div_const 2).congr_deriv
  unfold familyWidth familyEndpoint
  nlinarith [Real.sin_sq_add_cos_sq b]

theorem continuousOn_familyScore :
    ContinuousOn familyScore (Icc (0 : ℝ) (Real.pi / 4)) :=
  fun _ hb => (hasDerivAt_familyScore hb).continuousAt.continuousWithinAt

theorem strictMonoOn_familyScore_before_beta : StrictMonoOn familyScore (Icc (0 : ℝ) beta) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (continuousOn_familyScore.mono (fun _ hb => ⟨hb.1, hb.2.trans beta_lt_pi_div_four.le⟩))
  intro b hb
  rw [interior_Icc] at hb
  have hi : b ∈ Icc (0 : ℝ) (Real.pi / 4) :=
    ⟨hb.1.le, (hb.2.trans beta_lt_pi_div_four).le⟩
  rw [(hasDerivAt_familyScore hi).deriv]
  have hbound := strictMonoOn_familyBoundary hi beta_mem_family_interval hb.2
  rw [familyEndpoint_beta] at hbound
  exact mul_pos_of_neg_of_neg (by linarith) (familyWidth_derivative_neg hi)

theorem strictAntiOn_familyScore_after_beta :
    StrictAntiOn familyScore (Icc beta (Real.pi / 4)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (continuousOn_familyScore.mono (fun _ hb => ⟨beta_pos.le.trans hb.1, hb.2⟩))
  intro b hb
  rw [interior_Icc] at hb
  have hi : b ∈ Icc (0 : ℝ) (Real.pi / 4) :=
    ⟨(beta_pos.trans hb.1).le, hb.2.le⟩
  rw [(hasDerivAt_familyScore hi).deriv]
  have hbound := strictMonoOn_familyBoundary beta_mem_family_interval hi hb.1
  rw [familyEndpoint_beta] at hbound
  exact mul_neg_of_pos_of_neg (by linarith) (familyWidth_derivative_neg hi)

theorem familyScore_lt_beta_of_ne {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (hne : b ≠ beta) : familyScore b < familyScore beta := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact strictMonoOn_familyScore_before_beta ⟨hb.1, hlt.le⟩ ⟨beta_pos.le, le_rfl⟩ hlt
  · exact strictAntiOn_familyScore_after_beta ⟨le_rfl, beta_lt_pi_div_four.le⟩
      ⟨hgt.le, hb.2⟩ hgt

theorem familyScore_le_beta {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyScore b ≤ familyScore beta := by
  by_cases heq : b = beta
  · rw [heq]
  · exact (familyScore_lt_beta_of_ne hb heq).le

theorem familyScore_beta : familyScore beta = M / 2 := by
  have hM : M - beta + 2 = 1 / Y := (eq_div_iff Y_ne_zero).2 M_sub_beta_add_two_mul_Y
  have hA : 4 * Reference.A * Real.cos beta = 1 / Y := by
    calc
      _ = 4 * (Reference.A * Reference.cosBeta) := by unfold Reference.cosBeta; ring
      _ = 4 * (1 / (4 * Y)) := by rw [Reference.A_mul_cosBeta]
      _ = 1 / Y := by field_simp [Y_ne_zero] <;> ring
  unfold familyScore
  rw [familyEndpoint_beta, familyWidth_beta]
  nlinarith

theorem familyScore_le_half_M {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyScore b ≤ M / 2 := by
  simpa only [familyScore_beta] using familyScore_le_beta hb

theorem familyScore_eq_half_M_iff {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyScore b = M / 2 ↔ b = beta := by
  constructor
  · intro h
    by_contra hne
    have hlt := familyScore_lt_beta_of_ne hb hne
    rw [familyScore_beta, h] at hlt
    exact (lt_irrefl _ hlt)
  · rintro rfl
    exact familyScore_beta

end AmbidextrousSofa.Analysis
