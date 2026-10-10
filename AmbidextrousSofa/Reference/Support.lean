module

public import AmbidextrousSofa.Reference.Parameters

@[expose] public section

/-!
# The explicit three-phase reference support formulas

These are the two upper-quarter coordinate functions in MS.11. Each smooth
phase has actual first and second derivative certificates. The interfaces match
in value and first derivative by the cubic-derived identities in `Parameters`.
The file does not yet assert that the periodic extension is the support of a
convex body or that its swept-corridor envelope is feasible.

This source is an uncompiled draft.
-/

noncomputable section

open Set
open scoped Topology

namespace AmbidextrousSofa.Reference

def fEarly (t : ℝ) : ℝ := Real.cos t + 1 / 2 * Real.sin t

def gEarly (t : ℝ) : ℝ := (2 * A - 1) * Real.sin t + 1 / 2 * Real.cos t + 1 / 2

def fMiddle (t : ℝ) : ℝ :=
  R * Real.cos (t / 2 + Real.pi / 8) + k * Real.cos t + 1 / 2 * Real.sin t

def gMiddle (t : ℝ) : ℝ :=
  R * Real.sin (t / 2 + Real.pi / 8) - k * Real.sin t + 1 / 2 * Real.cos t

def fLate (t : ℝ) : ℝ :=
  (1 - 2 / 3 * A) * Real.cos t + 1 / 2 * Real.sin t + 1 / 2

def gLate (t : ℝ) : ℝ := (8 / 3 * A - 1) * Real.sin t + 1 / 2 * Real.cos t

def fEarlyD (t : ℝ) : ℝ := -Real.sin t + 1 / 2 * Real.cos t

def gEarlyD (t : ℝ) : ℝ := (2 * A - 1) * Real.cos t - 1 / 2 * Real.sin t

def fMiddleD (t : ℝ) : ℝ :=
  -(R / 2) * Real.sin (t / 2 + Real.pi / 8) - k * Real.sin t + 1 / 2 * Real.cos t

def gMiddleD (t : ℝ) : ℝ :=
  R / 2 * Real.cos (t / 2 + Real.pi / 8) - k * Real.cos t - 1 / 2 * Real.sin t

def fLateD (t : ℝ) : ℝ := -(1 - 2 / 3 * A) * Real.sin t + 1 / 2 * Real.cos t

def gLateD (t : ℝ) : ℝ := (8 / 3 * A - 1) * Real.cos t - 1 / 2 * Real.sin t

/-- The first upper-quarter support coordinate; interface values are proved below. -/
def referenceF (t : ℝ) : ℝ :=
  if t ≤ beta then fEarly t else if t ≤ lateSwitch then fMiddle t else fLate t

/-- The companion upper-quarter support coordinate. -/
def referenceG (t : ℝ) : ℝ :=
  if t ≤ beta then gEarly t else if t ≤ lateSwitch then gMiddle t else gLate t

/-- The derivative selected from the same three phases. -/
def referenceFD (t : ℝ) : ℝ :=
  if t ≤ beta then fEarlyD t else if t ≤ lateSwitch then fMiddleD t else fLateD t

/-- The companion derivative selected from the same three phases. -/
def referenceGD (t : ℝ) : ℝ :=
  if t ≤ beta then gEarlyD t else if t ≤ lateSwitch then gMiddleD t else gLateD t

/-- A binary gluing theorem proved from the two one-sided derivative statements. -/
theorem hasDerivAt_if_le (c : ℝ) {f g fD gD : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (fD x) x) (hg : ∀ x, HasDerivAt g (gD x) x)
    (hvalue : f c = g c) (hderiv : fD c = gD c) (x : ℝ) :
    HasDerivAt (fun y => if y ≤ c then f y else g y)
      (if x ≤ c then fD x else gD x) x := by
  rcases lt_trichotomy x c with hlt | heq | hgt
  · rw [if_pos hlt.le]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hlt] with y hy
    exact if_pos hy.le
  · subst x
    rw [if_pos le_rfl]
    have hleft : HasDerivWithinAt (fun y => if y ≤ c then f y else g y)
        (fD c) (Iic c) c := by
      apply (hf c).hasDerivWithinAt.congr
      · intro y hy
        exact if_pos hy
      · exact if_pos le_rfl
    have hright : HasDerivWithinAt (fun y => if y ≤ c then f y else g y)
        (fD c) (Ici c) c := by
      apply ((hg c).congr_deriv hderiv.symm).hasDerivWithinAt.congr
      · intro y hy
        by_cases hyc : y ≤ c
        · have heq : y = c := le_antisymm hyc hy
          subst y
          simpa only [if_pos le_rfl] using hvalue
        · exact if_neg hyc
      · simpa only [if_pos le_rfl] using hvalue
    have h := hleft.union hright
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using h
  · rw [if_neg (not_le.mpr hgt)]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hgt] with y hy
    exact if_neg (not_le.mpr hy)

theorem hasDerivAt_middlePhaseAngle (t : ℝ) :
    HasDerivAt (fun x : ℝ => x / 2 + Real.pi / 8) (1 / 2) t := by
  simpa only [one_div] using ((hasDerivAt_id' t).div_const 2).add_const (Real.pi / 8)

theorem hasDerivAt_fEarly (t : ℝ) : HasDerivAt fEarly (fEarlyD t) t := by
  unfold fEarly fEarlyD
  exact (Real.hasDerivAt_cos t).add ((Real.hasDerivAt_sin t).const_mul (1 / 2))

theorem hasDerivAt_gEarly (t : ℝ) : HasDerivAt gEarly (gEarlyD t) t := by
  unfold gEarly
  apply ((((Real.hasDerivAt_sin t).const_mul (2 * A - 1)).add
    ((Real.hasDerivAt_cos t).const_mul (1 / 2))).add_const (1 / 2)).congr_deriv
  unfold gEarlyD
  ring

theorem hasDerivAt_fMiddle (t : ℝ) : HasDerivAt fMiddle (fMiddleD t) t := by
  unfold fMiddle
  apply ((((hasDerivAt_middlePhaseAngle t).cos.const_mul R).add
    ((Real.hasDerivAt_cos t).const_mul k)).add
    ((Real.hasDerivAt_sin t).const_mul (1 / 2))).congr_deriv
  unfold fMiddleD
  ring

theorem hasDerivAt_gMiddle (t : ℝ) : HasDerivAt gMiddle (gMiddleD t) t := by
  unfold gMiddle
  apply ((((hasDerivAt_middlePhaseAngle t).sin.const_mul R).sub
    ((Real.hasDerivAt_sin t).const_mul k)).add
    ((Real.hasDerivAt_cos t).const_mul (1 / 2))).congr_deriv
  unfold gMiddleD
  ring

theorem hasDerivAt_fLate (t : ℝ) : HasDerivAt fLate (fLateD t) t := by
  unfold fLate
  apply ((((Real.hasDerivAt_cos t).const_mul (1 - 2 / 3 * A)).add
    ((Real.hasDerivAt_sin t).const_mul (1 / 2))).add_const (1 / 2)).congr_deriv
  unfold fLateD
  ring

theorem hasDerivAt_gLate (t : ℝ) : HasDerivAt gLate (gLateD t) t := by
  unfold gLate
  apply (((Real.hasDerivAt_sin t).const_mul (8 / 3 * A - 1)).add
    ((Real.hasDerivAt_cos t).const_mul (1 / 2))).congr_deriv
  unfold gLateD
  ring

theorem hasDerivAt_fEarlyD (t : ℝ) :
    HasDerivAt fEarlyD (-Real.cos t - 1 / 2 * Real.sin t) t := by
  unfold fEarlyD
  apply ((Real.hasDerivAt_sin t).neg.add
    ((Real.hasDerivAt_cos t).const_mul (1 / 2))).congr_deriv
  ring

theorem hasDerivAt_gEarlyD (t : ℝ) :
    HasDerivAt gEarlyD (-(2 * A - 1) * Real.sin t - 1 / 2 * Real.cos t) t := by
  unfold gEarlyD
  apply (((Real.hasDerivAt_cos t).const_mul (2 * A - 1)).sub
    ((Real.hasDerivAt_sin t).const_mul (1 / 2))).congr_deriv
  ring

theorem hasDerivAt_fMiddleD (t : ℝ) :
    HasDerivAt fMiddleD
      (-(R / 4) * Real.cos (t / 2 + Real.pi / 8) -
        k * Real.cos t - 1 / 2 * Real.sin t) t := by
  unfold fMiddleD
  apply ((((hasDerivAt_middlePhaseAngle t).sin.const_mul (-(R / 2))).sub
    ((Real.hasDerivAt_sin t).const_mul k)).add
    ((Real.hasDerivAt_cos t).const_mul (1 / 2))).congr_deriv
  ring

theorem hasDerivAt_gMiddleD (t : ℝ) :
    HasDerivAt gMiddleD
      (-(R / 4) * Real.sin (t / 2 + Real.pi / 8) +
        k * Real.sin t - 1 / 2 * Real.cos t) t := by
  unfold gMiddleD
  apply ((((hasDerivAt_middlePhaseAngle t).cos.const_mul (R / 2)).sub
    ((Real.hasDerivAt_cos t).const_mul k)).sub
    ((Real.hasDerivAt_sin t).const_mul (1 / 2))).congr_deriv
  ring

theorem hasDerivAt_fLateD (t : ℝ) :
    HasDerivAt fLateD
      (-(1 - 2 / 3 * A) * Real.cos t - 1 / 2 * Real.sin t) t := by
  unfold fLateD
  apply (((Real.hasDerivAt_sin t).const_mul (-(1 - 2 / 3 * A))).add
    ((Real.hasDerivAt_cos t).const_mul (1 / 2))).congr_deriv
  ring

theorem hasDerivAt_gLateD (t : ℝ) :
    HasDerivAt gLateD (-(8 / 3 * A - 1) * Real.sin t - 1 / 2 * Real.cos t) t := by
  unfold gLateD
  apply (((Real.hasDerivAt_cos t).const_mul (8 / 3 * A - 1)).sub
    ((Real.hasDerivAt_sin t).const_mul (1 / 2))).congr_deriv
  ring

theorem curvature_fEarly (t : ℝ) : deriv (deriv fEarly) t + fEarly t = 0 := by
  rw [show deriv fEarly = fEarlyD from funext fun x => (hasDerivAt_fEarly x).deriv,
    (hasDerivAt_fEarlyD t).deriv]
  unfold fEarly
  ring

theorem curvature_gEarly (t : ℝ) : deriv (deriv gEarly) t + gEarly t = 1 / 2 := by
  rw [show deriv gEarly = gEarlyD from funext fun x => (hasDerivAt_gEarly x).deriv,
    (hasDerivAt_gEarlyD t).deriv]
  unfold gEarly
  ring

theorem curvature_fMiddle (t : ℝ) :
    deriv (deriv fMiddle) t + fMiddle t =
      3 / 4 * R * Real.cos (t / 2 + Real.pi / 8) := by
  rw [show deriv fMiddle = fMiddleD from funext fun x => (hasDerivAt_fMiddle x).deriv,
    (hasDerivAt_fMiddleD t).deriv]
  unfold fMiddle
  ring

theorem curvature_gMiddle (t : ℝ) :
    deriv (deriv gMiddle) t + gMiddle t =
      3 / 4 * R * Real.sin (t / 2 + Real.pi / 8) := by
  rw [show deriv gMiddle = gMiddleD from funext fun x => (hasDerivAt_gMiddle x).deriv,
    (hasDerivAt_gMiddleD t).deriv]
  unfold gMiddle
  ring

theorem curvature_fLate (t : ℝ) : deriv (deriv fLate) t + fLate t = 1 / 2 := by
  rw [show deriv fLate = fLateD from funext fun x => (hasDerivAt_fLate x).deriv,
    (hasDerivAt_fLateD t).deriv]
  unfold fLate
  ring

theorem curvature_gLate (t : ℝ) : deriv (deriv gLate) t + gLate t = 0 := by
  rw [show deriv gLate = gLateD from funext fun x => (hasDerivAt_gLate x).deriv,
    (hasDerivAt_gLateD t).deriv]
  unfold gLate
  ring

theorem f_matching_first : fMiddle beta = fEarly beta := by
  unfold fMiddle fEarly
  rw [R_mul_cos_firstPhase]
  change (1 - k) * cosBeta + k * cosBeta + 1 / 2 * sinBeta =
    cosBeta + 1 / 2 * sinBeta
  ring

theorem g_matching_first : gMiddle beta = gEarly beta := by
  unfold gMiddle gEarly
  rw [R_mul_sin_firstPhase]
  change 2 / 3 - k * sinBeta + 1 / 2 * cosBeta =
    (2 * A - 1) * sinBeta + 1 / 2 * cosBeta + 1 / 2
  unfold k
  nlinarith [four_mul_A_mul_sinBeta]

theorem fD_matching_first : fMiddleD beta = fEarlyD beta := by
  unfold fMiddleD fEarlyD
  change -(R / 2) * Real.sin (beta / 2 + Real.pi / 8) -
    k * sinBeta + 1 / 2 * cosBeta = -sinBeta + 1 / 2 * cosBeta
  unfold k
  nlinarith [R_mul_sin_firstPhase, four_mul_A_mul_sinBeta]

theorem gD_matching_first : gMiddleD beta = gEarlyD beta := by
  have h := R_mul_cos_firstPhase
  unfold gMiddleD gEarlyD
  change R / 2 * Real.cos (beta / 2 + Real.pi / 8) -
    k * cosBeta - 1 / 2 * sinBeta = (2 * A - 1) * cosBeta - 1 / 2 * sinBeta
  unfold k at h ⊢
  nlinarith [h]

theorem fLate_reflection (t : ℝ) :
    fLate (Real.pi / 2 - t) = gEarly t + 2 * k * Real.sin t := by
  unfold fLate gEarly k
  rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  ring

theorem gLate_reflection (t : ℝ) :
    gLate (Real.pi / 2 - t) = fEarly t - 2 * k * Real.cos t := by
  unfold gLate fEarly k
  rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  ring

theorem fMiddle_reflection (t : ℝ) :
    fMiddle (Real.pi / 2 - t) = gMiddle t + 2 * k * Real.sin t := by
  have hangle : (Real.pi / 2 - t) / 2 + Real.pi / 8 =
      Real.pi / 2 - (t / 2 + Real.pi / 8) := by ring
  unfold fMiddle gMiddle
  rw [hangle, Real.cos_pi_div_two_sub, Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub]
  ring

theorem gMiddle_reflection (t : ℝ) :
    gMiddle (Real.pi / 2 - t) = fMiddle t - 2 * k * Real.cos t := by
  have hangle : (Real.pi / 2 - t) / 2 + Real.pi / 8 =
      Real.pi / 2 - (t / 2 + Real.pi / 8) := by ring
  unfold gMiddle fMiddle
  rw [hangle, Real.sin_pi_div_two_sub, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub]
  ring

theorem f_matching_last : fMiddle lateSwitch = fLate lateSwitch := by
  unfold lateSwitch
  rw [fMiddle_reflection, fLate_reflection, g_matching_first]

theorem g_matching_last : gMiddle lateSwitch = gLate lateSwitch := by
  unfold lateSwitch
  rw [gMiddle_reflection, gLate_reflection, f_matching_first]

/-- The actual piecewise coordinate is continuous, including both joins. -/
theorem continuous_referenceF : Continuous referenceF := by
  have hearly : Continuous fEarly := by unfold fEarly; fun_prop
  have hmiddle : Continuous fMiddle := by unfold fMiddle; fun_prop
  have hlate : Continuous fLate := by unfold fLate; fun_prop
  have htail : Continuous (fun t : ℝ => if t ≤ lateSwitch then fMiddle t else fLate t) := by
    apply hmiddle.if_le hlate continuous_id continuous_const
    intro t ht
    change t = lateSwitch at ht
    subst t
    exact f_matching_last
  unfold referenceF
  apply hearly.if_le htail continuous_id continuous_const
  intro t ht
  change t = beta at ht
  subst t
  rw [if_pos (le_of_lt beta_lt_lateSwitch)]
  exact f_matching_first.symm

/-- Continuity of the companion coordinate is also proved at both joins. -/
theorem continuous_referenceG : Continuous referenceG := by
  have hearly : Continuous gEarly := by unfold gEarly; fun_prop
  have hmiddle : Continuous gMiddle := by unfold gMiddle; fun_prop
  have hlate : Continuous gLate := by unfold gLate; fun_prop
  have htail : Continuous (fun t : ℝ => if t ≤ lateSwitch then gMiddle t else gLate t) := by
    apply hmiddle.if_le hlate continuous_id continuous_const
    intro t ht
    change t = lateSwitch at ht
    subst t
    exact g_matching_last
  unfold referenceG
  apply hearly.if_le htail continuous_id continuous_const
  intro t ht
  change t = beta at ht
  subst t
  rw [if_pos (le_of_lt beta_lt_lateSwitch)]
  exact g_matching_first.symm

theorem fD_matching_last : fMiddleD lateSwitch = fLateD lateSwitch := by
  have h := R_mul_cos_firstPhase
  have hangle : lateSwitch / 2 + Real.pi / 8 =
      Real.pi / 2 - (beta / 2 + Real.pi / 8) := by unfold lateSwitch; ring
  unfold fMiddleD fLateD
  rw [hangle, Real.sin_pi_div_two_sub]
  unfold lateSwitch
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  change -(R / 2) * Real.cos (beta / 2 + Real.pi / 8) -
    k * cosBeta + 1 / 2 * sinBeta = -(1 - 2 / 3 * A) * cosBeta + 1 / 2 * sinBeta
  unfold k at h ⊢
  nlinarith [h]

theorem gD_matching_last : gMiddleD lateSwitch = gLateD lateSwitch := by
  have hangle : lateSwitch / 2 + Real.pi / 8 =
      Real.pi / 2 - (beta / 2 + Real.pi / 8) := by unfold lateSwitch; ring
  unfold gMiddleD gLateD
  rw [hangle, Real.cos_pi_div_two_sub]
  unfold lateSwitch
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  change R / 2 * Real.sin (beta / 2 + Real.pi / 8) -
    k * sinBeta - 1 / 2 * cosBeta = (8 / 3 * A - 1) * sinBeta - 1 / 2 * cosBeta
  unfold k
  nlinarith [R_mul_sin_firstPhase, four_mul_A_mul_sinBeta]

/-- The first piecewise support coordinate is differentiable at every switch as well. -/
theorem hasDerivAt_referenceF (t : ℝ) : HasDerivAt referenceF (referenceFD t) t := by
  unfold referenceF referenceFD
  apply hasDerivAt_if_le beta hasDerivAt_fEarly
    (hasDerivAt_if_le lateSwitch hasDerivAt_fMiddle hasDerivAt_fLate
      f_matching_last fD_matching_last)
  · rw [if_pos (le_of_lt beta_lt_lateSwitch)]
    exact f_matching_first.symm
  · rw [if_pos (le_of_lt beta_lt_lateSwitch)]
    exact fD_matching_first.symm

/-- The companion coordinate has the stated derivative at both joins. -/
theorem hasDerivAt_referenceG (t : ℝ) : HasDerivAt referenceG (referenceGD t) t := by
  unfold referenceG referenceGD
  apply hasDerivAt_if_le beta hasDerivAt_gEarly
    (hasDerivAt_if_le lateSwitch hasDerivAt_gMiddle hasDerivAt_gLate
      g_matching_last gD_matching_last)
  · rw [if_pos (le_of_lt beta_lt_lateSwitch)]
    exact g_matching_first.symm
  · rw [if_pos (le_of_lt beta_lt_lateSwitch)]
    exact gD_matching_first.symm

theorem deriv_referenceF (t : ℝ) : deriv referenceF t = referenceFD t :=
  (hasDerivAt_referenceF t).deriv

theorem deriv_referenceG (t : ℝ) : deriv referenceG t = referenceGD t :=
  (hasDerivAt_referenceG t).deriv

theorem continuous_referenceFD : Continuous referenceFD := by
  have hearly : Continuous fEarlyD := by unfold fEarlyD; fun_prop
  have hmiddle : Continuous fMiddleD := by unfold fMiddleD; fun_prop
  have hlate : Continuous fLateD := by unfold fLateD; fun_prop
  have htail : Continuous (fun t : ℝ => if t ≤ lateSwitch then fMiddleD t else fLateD t) := by
    apply hmiddle.if_le hlate continuous_id continuous_const
    intro t ht
    change t = lateSwitch at ht
    subst t
    exact fD_matching_last
  unfold referenceFD
  apply hearly.if_le htail continuous_id continuous_const
  intro t ht
  change t = beta at ht
  subst t
  rw [if_pos (le_of_lt beta_lt_lateSwitch)]
  exact fD_matching_first.symm

theorem continuous_referenceGD : Continuous referenceGD := by
  have hearly : Continuous gEarlyD := by unfold gEarlyD; fun_prop
  have hmiddle : Continuous gMiddleD := by unfold gMiddleD; fun_prop
  have hlate : Continuous gLateD := by unfold gLateD; fun_prop
  have htail : Continuous (fun t : ℝ => if t ≤ lateSwitch then gMiddleD t else gLateD t) := by
    apply hmiddle.if_le hlate continuous_id continuous_const
    intro t ht
    change t = lateSwitch at ht
    subst t
    exact gD_matching_last
  unfold referenceGD
  apply hearly.if_le htail continuous_id continuous_const
  intro t ht
  change t = beta at ht
  subst t
  rw [if_pos (le_of_lt beta_lt_lateSwitch)]
  exact gD_matching_first.symm

/-- The first displayed coordinate is genuinely continuously differentiable across both joins. -/
theorem contDiff_referenceF : ContDiff ℝ 1 referenceF := by
  rw [contDiff_one_iff_deriv, funext deriv_referenceF]
  exact ⟨fun t => (hasDerivAt_referenceF t).differentiableAt, continuous_referenceFD⟩

/-- The same global first-order regularity holds for the companion coordinate. -/
theorem contDiff_referenceG : ContDiff ℝ 1 referenceG := by
  rw [contDiff_one_iff_deriv, funext deriv_referenceG]
  exact ⟨fun t => (hasDerivAt_referenceG t).differentiableAt, continuous_referenceGD⟩

theorem referenceF_zero : referenceF 0 = 1 := by
  norm_num [referenceF, fEarly, le_of_lt beta_pos]

theorem referenceG_zero : referenceG 0 = 1 := by
  norm_num [referenceG, gEarly, le_of_lt beta_pos]

theorem referenceF_pi_div_two : referenceF (Real.pi / 2) = 1 := by
  norm_num [referenceF, fLate, not_le.mpr beta_lt_pi_div_two,
    not_le.mpr lateSwitch_lt_pi_div_two]

theorem referenceG_pi_div_two : referenceG (Real.pi / 2) = 8 / 3 * A - 1 := by
  simp [referenceG, gLate, not_le.mpr beta_lt_pi_div_two,
    not_le.mpr lateSwitch_lt_pi_div_two]

theorem fEarlyD_zero : fEarlyD 0 = 1 / 2 := by simp [fEarlyD]

theorem gLateD_pi_div_two : gLateD (Real.pi / 2) = -(1 / 2) := by simp [gLateD]

theorem fLateD_pi_div_two : fLateD (Real.pi / 2) = 2 / 3 * A - 1 := by
  simp [fLateD] <;> ring

theorem gEarlyD_zero : gEarlyD 0 = 2 * A - 1 := by simp [gEarlyD]

/-- The first contact velocity vanishes at the first switch. -/
theorem early_contact_switch : fEarlyD beta - gEarly beta + 1 = 0 := by
  unfold fEarlyD gEarly
  change -sinBeta + 1 / 2 * cosBeta -
    ((2 * A - 1) * sinBeta + 1 / 2 * cosBeta + 1 / 2) + 1 = 0
  nlinarith [four_mul_A_mul_sinBeta]

/-- The companion contact velocity vanishes at the second switch. -/
theorem late_contact_switch : gLateD lateSwitch + fLate lateSwitch - 1 = 0 := by
  unfold gLateD fLate lateSwitch
  rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  change (8 / 3 * A - 1) * sinBeta - 1 / 2 * cosBeta +
    ((1 - 2 / 3 * A) * sinBeta + 1 / 2 * cosBeta + 1 / 2) - 1 = 0
  nlinarith [four_mul_A_mul_sinBeta]

/-- Strictly positive cosine curvature throughout the closed middle phase. -/
theorem curvature_fMiddle_pos {t : ℝ} (ht : t ∈ Set.Icc beta lateSwitch) :
    0 < deriv (deriv fMiddle) t + fMiddle t := by
  rw [curvature_fMiddle]
  apply mul_pos (mul_pos (by norm_num) R_pos)
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · linarith [ht.1, beta_pos, Real.pi_pos]
  · linarith [ht.2, lateSwitch_lt_pi_div_two, Real.pi_pos]

/-- Strictly positive sine curvature throughout the closed middle phase. -/
theorem curvature_gMiddle_pos {t : ℝ} (ht : t ∈ Set.Icc beta lateSwitch) :
    0 < deriv (deriv gMiddle) t + gMiddle t := by
  rw [curvature_gMiddle]
  apply mul_pos (mul_pos (by norm_num) R_pos)
  exact Real.sin_pos_of_pos_of_lt_pi
    (by linarith [ht.1, beta_pos, Real.pi_pos])
    (by linarith [ht.2, lateSwitch_lt_pi_div_two, Real.pi_pos])

/-- The exact upper margin in MS.13 for the cosine curvature. -/
theorem curvature_fMiddle_lt_seven_eighths {t : ℝ}
    (ht : t ∈ Set.Icc beta lateSwitch) :
    deriv (deriv fMiddle) t + fMiddle t < 7 / 8 := by
  rw [curvature_fMiddle]
  have hcos : Real.cos (t / 2 + Real.pi / 8) ≤
      Real.cos (beta / 2 + Real.pi / 8) := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · linarith [beta_pos, Real.pi_pos]
    · linarith [ht.2, lateSwitch_lt_pi_div_two, Real.pi_pos]
    · linarith [ht.1]
  have hmul := mul_le_mul_of_nonneg_left hcos
    (le_of_lt (mul_pos (show (0 : ℝ) < 3 / 4 by norm_num) R_pos))
  have hendpoint : 3 / 4 * R * Real.cos (beta / 2 + Real.pi / 8) = A * cosBeta := by
    have h := R_mul_cos_firstPhase
    unfold k at h
    nlinarith [h]
  calc
    _ ≤ 3 / 4 * R * Real.cos (beta / 2 + Real.pi / 8) := hmul
    _ = A * cosBeta := hendpoint
    _ < 7 / 8 := A_mul_cosBeta_lt_seven_eighths

/-- The same exact upper margin for the reflected sine curvature. -/
theorem curvature_gMiddle_lt_seven_eighths {t : ℝ}
    (ht : t ∈ Set.Icc beta lateSwitch) :
    deriv (deriv gMiddle) t + gMiddle t < 7 / 8 := by
  have hreflect : Real.pi / 2 - t ∈ Set.Icc beta lateSwitch := by
    constructor <;> unfold lateSwitch at * <;> linarith [ht.1, ht.2]
  have h := curvature_fMiddle_lt_seven_eighths hreflect
  rw [curvature_fMiddle] at h
  rw [curvature_gMiddle]
  have hangle : (Real.pi / 2 - t) / 2 + Real.pi / 8 =
      Real.pi / 2 - (t / 2 + Real.pi / 8) := by ring
  simpa only [hangle, Real.cos_pi_div_two_sub] using h

/-- The explicit center lies below every first-quarter reference support line. -/
theorem referenceF_ge_center {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    k * Real.cos t + 1 / 2 * Real.sin t ≤ referenceF t := by
  have hc : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  have hphase : 0 < Real.cos (t / 2 + Real.pi / 8) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [ht.1, ht.2, Real.pi_pos]
  unfold referenceF
  split_ifs with hearly hmiddle
  · unfold fEarly k
    nlinarith [mul_nonneg (le_of_lt A_pos) hc]
  · unfold fMiddle
    nlinarith [mul_pos R_pos hphase]
  · unfold fLate k
    nlinarith [mul_nonneg (le_of_lt A_pos) hc]

/-- The same point satisfies all companion upper-quarter support lines. -/
theorem referenceG_ge_center {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    -k * Real.sin t + 1 / 2 * Real.cos t ≤ referenceG t := by
  have hs : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi
    ht.1 (by linarith [ht.2, Real.pi_pos])
  have hphase : 0 < Real.sin (t / 2 + Real.pi / 8) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [ht.1, Real.pi_pos]
    · linarith [ht.2, Real.pi_pos]
  unfold referenceG
  split_ifs with hearly hmiddle
  · unfold gEarly k
    nlinarith [mul_nonneg (le_of_lt A_pos) hs]
  · unfold gMiddle
    nlinarith [mul_pos R_pos hphase]
  · unfold gLate k
    nlinarith [mul_nonneg (le_of_lt A_pos) hs]

end AmbidextrousSofa.Reference
