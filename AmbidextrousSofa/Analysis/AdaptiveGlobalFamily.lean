import AmbidextrousSofa.Analysis.AdaptiveGlobalParameters

/-!
# Actual three-phase stationary profiles

This file constructs the profiles, verifies both value and derivative
matching, and packages their genuine derivatives as `QuarterPair` data.
The parameter inequalities are ordinary switching-angle bounds.
-/

noncomputable section

open Set
open scoped Topology

namespace AmbidextrousSofa.Analysis

def joinThree (c d : ℝ) (E N W : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ c then E t else if t ≤ d then N t else W t

theorem joinThree_eq_early {c d t : ℝ} {E N W : ℝ → ℝ} (ht : t ≤ c) :
    joinThree c d E N W t = E t := by simp only [joinThree, if_pos ht]

theorem joinThree_eq_middle {c d t : ℝ} {E N W : ℝ → ℝ}
    (hmatch : E c = N c) (ht : t ∈ Icc c d) :
    joinThree c d E N W t = N t := by
  by_cases htc : t ≤ c
  · have heq : t = c := le_antisymm htc ht.1
    subst t
    simpa only [joinThree, if_pos le_rfl] using hmatch
  · simp only [joinThree, if_neg htc, if_pos ht.2]

theorem joinThree_eq_late {c d t : ℝ} {E N W : ℝ → ℝ}
    (hcd : c ≤ d) (hfirst : E c = N c) (hlast : N d = W d) (ht : d ≤ t) :
    joinThree c d E N W t = W t := by
  by_cases htc : t ≤ c
  · have heq : t = c := le_antisymm htc (hcd.trans ht)
    subst t
    have heq : d = c := le_antisymm ht hcd
    subst d
    simpa only [joinThree, if_pos le_rfl] using hfirst.trans hlast
  · by_cases htd : t ≤ d
    · have heq : t = d := le_antisymm htd ht
      subst t
      simpa only [joinThree, if_neg htc, if_pos le_rfl] using hlast
    · simp only [joinThree, if_neg htc, if_neg htd]

theorem continuous_joinThree {c d : ℝ} {E N W : ℝ → ℝ}
    (hcd : c ≤ d) (hE : Continuous E) (hN : Continuous N) (hW : Continuous W)
    (hfirst : E c = N c) (hlast : N d = W d) :
    Continuous (joinThree c d E N W) := by
  have htail : Continuous (fun t : ℝ => if t ≤ d then N t else W t) := by
    apply hN.if_le hW continuous_id continuous_const
    intro t ht
    change t = d at ht
    subst t
    exact hlast
  unfold joinThree
  apply hE.if_le htail continuous_id continuous_const
  intro t ht
  change t = c at ht
  subst t
  simpa only [if_pos hcd] using hfirst

theorem hasDerivAt_joinThree {c d : ℝ} {E N W ED ND WD : ℝ → ℝ}
    (hcd : c ≤ d)
    (hE : ∀ t, HasDerivAt E (ED t) t)
    (hN : ∀ t, HasDerivAt N (ND t) t)
    (hW : ∀ t, HasDerivAt W (WD t) t)
    (hfirst : E c = N c) (hlast : N d = W d)
    (hfirstD : ED c = ND c) (hlastD : ND d = WD d) (t : ℝ) :
    HasDerivAt (joinThree c d E N W) (joinThree c d ED ND WD t) t := by
  unfold joinThree
  apply Reference.hasDerivAt_if_le c hE
    (Reference.hasDerivAt_if_le d hN hW hlast hlastD)
  · simpa only [if_pos hcd] using hfirst
  · simpa only [if_pos hcd] using hfirstD

def familyFEarly (b t : ℝ) : ℝ :=
  familyWidth b * Real.cos t + familyEndpoint b * Real.sin t

def familyGEarly (b t : ℝ) : ℝ :=
  1 / 2 + Real.cos t / 2 + familyWidth b / 2 * Real.sin t

def familyFMiddle (b t : ℝ) : ℝ :=
  familyRadius b * Real.cos (tailPhase t) + familySineCoefficient b * Real.sin t

def familyGMiddle (b t : ℝ) : ℝ :=
  familyRadius b * Real.sin (tailPhase t) + familySineCoefficient b * Real.cos t

def familyFLate (b t : ℝ) : ℝ :=
  1 / 2 + Real.sin t / 2 + familyWidth b / 2 * Real.cos t

def familyGLate (b t : ℝ) : ℝ :=
  familyWidth b * Real.sin t + familyEndpoint b * Real.cos t

def familyFEarlyD (b t : ℝ) : ℝ :=
  -(familyWidth b) * Real.sin t + familyEndpoint b * Real.cos t

def familyGEarlyD (b t : ℝ) : ℝ :=
  -(Real.sin t) / 2 + familyWidth b / 2 * Real.cos t

def familyFMiddleD (b t : ℝ) : ℝ :=
  -(familyRadius b / 2) * Real.sin (tailPhase t) + familySineCoefficient b * Real.cos t

def familyGMiddleD (b t : ℝ) : ℝ :=
  familyRadius b / 2 * Real.cos (tailPhase t) - familySineCoefficient b * Real.sin t

def familyFLateD (b t : ℝ) : ℝ :=
  Real.cos t / 2 - familyWidth b / 2 * Real.sin t

def familyGLateD (b t : ℝ) : ℝ :=
  familyWidth b * Real.cos t - familyEndpoint b * Real.sin t

def familyF (b : ℝ) : ℝ → ℝ := joinThree b (familyLateSwitch b)
  (familyFEarly b) (familyFMiddle b) (familyFLate b)

def familyG (b : ℝ) : ℝ → ℝ := joinThree b (familyLateSwitch b)
  (familyGEarly b) (familyGMiddle b) (familyGLate b)

def familyFD (b : ℝ) : ℝ → ℝ := joinThree b (familyLateSwitch b)
  (familyFEarlyD b) (familyFMiddleD b) (familyFLateD b)

def familyGD (b : ℝ) : ℝ → ℝ := joinThree b (familyLateSwitch b)
  (familyGEarlyD b) (familyGMiddleD b) (familyGLateD b)

theorem hasDerivAt_familyFEarly (b t : ℝ) :
    HasDerivAt (familyFEarly b) (familyFEarlyD b t) t := by
  apply (((Real.hasDerivAt_cos t).const_mul (familyWidth b)).add
    ((Real.hasDerivAt_sin t).const_mul (familyEndpoint b))).congr_deriv
  unfold familyFEarlyD
  ring

theorem hasDerivAt_familyGEarly (b t : ℝ) :
    HasDerivAt (familyGEarly b) (familyGEarlyD b t) t := by
  apply ((((Real.hasDerivAt_cos t).div_const 2).const_add (1 / 2)).add
    ((Real.hasDerivAt_sin t).const_mul (familyWidth b / 2))).congr_deriv
  unfold familyGEarlyD
  ring

theorem hasDerivAt_familyFMiddle (b t : ℝ) :
    HasDerivAt (familyFMiddle b) (familyFMiddleD b t) t := by
  apply ((((hasDerivAt_tailPhase t).cos).const_mul (familyRadius b)).add
    ((Real.hasDerivAt_sin t).const_mul (familySineCoefficient b))).congr_deriv
  unfold familyFMiddleD
  ring

theorem hasDerivAt_familyGMiddle (b t : ℝ) :
    HasDerivAt (familyGMiddle b) (familyGMiddleD b t) t := by
  apply ((((hasDerivAt_tailPhase t).sin).const_mul (familyRadius b)).add
    ((Real.hasDerivAt_cos t).const_mul (familySineCoefficient b))).congr_deriv
  unfold familyGMiddleD
  ring

theorem hasDerivAt_familyFLate (b t : ℝ) :
    HasDerivAt (familyFLate b) (familyFLateD b t) t := by
  apply ((((Real.hasDerivAt_sin t).div_const 2).const_add (1 / 2)).add
    ((Real.hasDerivAt_cos t).const_mul (familyWidth b / 2))).congr_deriv
  unfold familyFLateD
  ring

theorem hasDerivAt_familyGLate (b t : ℝ) :
    HasDerivAt (familyGLate b) (familyGLateD b t) t := by
  apply (((Real.hasDerivAt_sin t).const_mul (familyWidth b)).add
    ((Real.hasDerivAt_cos t).const_mul (familyEndpoint b))).congr_deriv
  unfold familyGLateD
  ring

theorem familyF_matching_first {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyFEarly b b = familyFMiddle b b := by
  unfold familyFEarly familyFMiddle
  rw [familyRadius_mul_cos hb]
  have hs := congrArg (fun x : ℝ => familyCot b * x) (Real.sin_sq_add_cos_sq b)
  unfold familyWidth familyEndpoint familySineCoefficient
  nlinarith [hs]

theorem familyG_matching_first {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyGEarly b b = familyGMiddle b b := by
  unfold familyGEarly familyGMiddle
  rw [familyRadius_mul_sin hb]
  unfold familyWidth familySineCoefficient
  nlinarith [Real.sin_sq_add_cos_sq b]

theorem familyFD_matching_first {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyFEarlyD b b = familyFMiddleD b b := by
  have hs := familyRadius_mul_sin hb
  unfold familyFEarlyD familyFMiddleD familyWidth familyEndpoint familySineCoefficient
  nlinarith [Real.sin_sq_add_cos_sq b]

theorem familyGD_matching_first {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyGEarlyD b b = familyGMiddleD b b := by
  have hc := familyRadius_mul_cos hb
  have hs := congrArg (fun x : ℝ => familyCot b * x) (Real.sin_sq_add_cos_sq b)
  unfold familyGEarlyD familyGMiddleD familyWidth familySineCoefficient
  nlinarith [hs]

theorem tailPhase_reflection (t : ℝ) :
    tailPhase (Real.pi / 2 - t) = Real.pi / 2 - tailPhase t := by
  unfold tailPhase tailAngle0
  ring

theorem familyFMiddle_reflection (b t : ℝ) :
    familyFMiddle b (Real.pi / 2 - t) = familyGMiddle b t := by
  simp only [familyFMiddle, familyGMiddle, tailPhase_reflection,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]

theorem familyGMiddle_reflection (b t : ℝ) :
    familyGMiddle b (Real.pi / 2 - t) = familyFMiddle b t := by
  simp only [familyFMiddle, familyGMiddle, tailPhase_reflection,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]

theorem familyFLate_reflection (b t : ℝ) :
    familyFLate b (Real.pi / 2 - t) = familyGEarly b t := by
  simp only [familyFLate, familyGEarly, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]

theorem familyGLate_reflection (b t : ℝ) :
    familyGLate b (Real.pi / 2 - t) = familyFEarly b t := by
  simp only [familyGLate, familyFEarly, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]

theorem familyFMiddleD_reflection (b t : ℝ) :
    familyFMiddleD b (Real.pi / 2 - t) = -familyGMiddleD b t := by
  simp only [familyFMiddleD, familyGMiddleD, tailPhase_reflection,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  ring

theorem familyGMiddleD_reflection (b t : ℝ) :
    familyGMiddleD b (Real.pi / 2 - t) = -familyFMiddleD b t := by
  simp only [familyFMiddleD, familyGMiddleD, tailPhase_reflection,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  ring

theorem familyFLateD_reflection (b t : ℝ) :
    familyFLateD b (Real.pi / 2 - t) = -familyGEarlyD b t := by
  simp only [familyFLateD, familyGEarlyD, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  ring

theorem familyGLateD_reflection (b t : ℝ) :
    familyGLateD b (Real.pi / 2 - t) = -familyFEarlyD b t := by
  simp only [familyGLateD, familyFEarlyD, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  ring

theorem familyF_matching_last {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyFMiddle b (familyLateSwitch b) = familyFLate b (familyLateSwitch b) := by
  unfold familyLateSwitch
  rw [familyFMiddle_reflection, familyFLate_reflection, familyG_matching_first hb]

theorem familyG_matching_last {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyGMiddle b (familyLateSwitch b) = familyGLate b (familyLateSwitch b) := by
  unfold familyLateSwitch
  rw [familyGMiddle_reflection, familyGLate_reflection, familyF_matching_first hb]

theorem familyFD_matching_last {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyFMiddleD b (familyLateSwitch b) = familyFLateD b (familyLateSwitch b) := by
  unfold familyLateSwitch
  rw [familyFMiddleD_reflection, familyFLateD_reflection, familyGD_matching_first hb]

theorem familyGD_matching_last {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyGMiddleD b (familyLateSwitch b) = familyGLateD b (familyLateSwitch b) := by
  unfold familyLateSwitch
  rw [familyGMiddleD_reflection, familyGLateD_reflection, familyFD_matching_first hb]

theorem continuous_familyF {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    Continuous (familyF b) := by
  apply continuous_joinThree (family_switch_order hb)
    (by unfold familyFEarly; fun_prop)
    (by unfold familyFMiddle tailPhase; fun_prop)
    (by unfold familyFLate; fun_prop)
    (familyF_matching_first hb) (familyF_matching_last hb)

theorem continuous_familyG {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    Continuous (familyG b) := by
  apply continuous_joinThree (family_switch_order hb)
    (by unfold familyGEarly; fun_prop)
    (by unfold familyGMiddle tailPhase; fun_prop)
    (by unfold familyGLate; fun_prop)
    (familyG_matching_first hb) (familyG_matching_last hb)

theorem continuous_familyFD {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    Continuous (familyFD b) := by
  apply continuous_joinThree (family_switch_order hb)
    (by unfold familyFEarlyD; fun_prop)
    (by unfold familyFMiddleD tailPhase; fun_prop)
    (by unfold familyFLateD; fun_prop)
    (familyFD_matching_first hb) (familyFD_matching_last hb)

theorem continuous_familyGD {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    Continuous (familyGD b) := by
  apply continuous_joinThree (family_switch_order hb)
    (by unfold familyGEarlyD; fun_prop)
    (by unfold familyGMiddleD tailPhase; fun_prop)
    (by unfold familyGLateD; fun_prop)
    (familyGD_matching_first hb) (familyGD_matching_last hb)

theorem hasDerivAt_familyF {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (t : ℝ) :
    HasDerivAt (familyF b) (familyFD b t) t :=
  hasDerivAt_joinThree (family_switch_order hb)
    (hasDerivAt_familyFEarly b) (hasDerivAt_familyFMiddle b) (hasDerivAt_familyFLate b)
    (familyF_matching_first hb) (familyF_matching_last hb)
    (familyFD_matching_first hb) (familyFD_matching_last hb) t

theorem hasDerivAt_familyG {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (t : ℝ) :
    HasDerivAt (familyG b) (familyGD b t) t :=
  hasDerivAt_joinThree (family_switch_order hb)
    (hasDerivAt_familyGEarly b) (hasDerivAt_familyGMiddle b) (hasDerivAt_familyGLate b)
    (familyG_matching_first hb) (familyG_matching_last hb)
    (familyGD_matching_first hb) (familyGD_matching_last hb) t

def familyPair (b : ℝ) (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) : QuarterPair where
  f := familyF b
  g := familyG b
  fD := familyFD b
  gD := familyGD b
  continuous_f := (continuous_familyF hb).continuousOn
  continuous_g := (continuous_familyG hb).continuousOn
  continuous_fD := (continuous_familyFD hb).continuousOn
  continuous_gD := (continuous_familyGD hb).continuousOn
  hasDeriv_f := fun t _ => (hasDerivAt_familyF hb t).hasDerivWithinAt
  hasDeriv_g := fun t _ => (hasDerivAt_familyG hb t).hasDerivWithinAt

theorem familyF_eq_middle {b t : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (ht : t ∈ Icc b (familyLateSwitch b)) : familyF b t = familyFMiddle b t :=
  joinThree_eq_middle (familyF_matching_first hb) ht

theorem familyG_eq_middle {b t : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (ht : t ∈ Icc b (familyLateSwitch b)) : familyG b t = familyGMiddle b t :=
  joinThree_eq_middle (familyG_matching_first hb) ht

theorem familyFD_eq_middle {b t : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (ht : t ∈ Icc b (familyLateSwitch b)) : familyFD b t = familyFMiddleD b t :=
  joinThree_eq_middle (familyFD_matching_first hb) ht

theorem familyGD_eq_middle {b t : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (ht : t ∈ Icc b (familyLateSwitch b)) : familyGD b t = familyGMiddleD b t :=
  joinThree_eq_middle (familyGD_matching_first hb) ht

theorem familyF_eq_late {b t : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (ht : familyLateSwitch b ≤ t) : familyF b t = familyFLate b t :=
  joinThree_eq_late (family_switch_order hb)
    (familyF_matching_first hb) (familyF_matching_last hb) ht

theorem familyG_eq_late {b t : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (ht : familyLateSwitch b ≤ t) : familyG b t = familyGLate b t :=
  joinThree_eq_late (family_switch_order hb)
    (familyG_matching_first hb) (familyG_matching_last hb) ht

theorem familyFD_eq_late {b t : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (ht : familyLateSwitch b ≤ t) : familyFD b t = familyFLateD b t :=
  joinThree_eq_late (family_switch_order hb)
    (familyFD_matching_first hb) (familyFD_matching_last hb) ht

theorem familyGD_eq_late {b t : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (ht : familyLateSwitch b ≤ t) : familyGD b t = familyGLateD b t :=
  joinThree_eq_late (family_switch_order hb)
    (familyGD_matching_first hb) (familyGD_matching_last hb) ht

theorem familyPair_widthTraces {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    (familyPair b hb).WidthTraces (familyWidth b) := by
  have hL : familyLateSwitch b ≤ Real.pi / 2 := by unfold familyLateSwitch; linarith [hb.1]
  change familyF b 0 = familyWidth b ∧ familyG b 0 = 1 ∧
    familyF b (Real.pi / 2) = 1 ∧ familyG b (Real.pi / 2) = familyWidth b
  rw [familyF_eq_late hb hL, familyG_eq_late hb hL]
  simp only [familyF, familyG, joinThree, if_pos hb.1, familyFEarly,
    familyGEarly, familyFLate, familyGLate, Real.cos_zero, Real.sin_zero,
    Real.sin_pi_div_two, Real.cos_pi_div_two]
  norm_num

end AmbidextrousSofa.Analysis
