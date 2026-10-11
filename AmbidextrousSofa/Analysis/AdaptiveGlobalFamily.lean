module

public import AmbidextrousSofa.Analysis.AdaptiveGlobalParameters

@[expose] public section

/-!
# Actual three-phase stationary profiles

This file constructs the profiles, verifies both value and derivative
matching, and packages their genuine derivatives as `QuarterPair` data.
The parameter inequalities are ordinary switching-angle bounds.
-/

noncomputable section

open Set

namespace AmbidextrousSofa.Analysis

def joinThree (c d : ℝ) (E N W : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ c then E t else if t ≤ d then N t else W t

theorem joinThree_eq_middle {c d t : ℝ} {E N W : ℝ → ℝ}
    (hmatch : E c = N c) (ht : t ∈ Icc c d) :
    joinThree c d E N W t = N t := by
  rcases ht.1.eq_or_lt with rfl | h
  · simp [joinThree, hmatch]
  · simp [joinThree, not_le.2 h, ht.2]

theorem joinThree_eq_late {c d t : ℝ} {E N W : ℝ → ℝ}
    (hcd : c ≤ d) (hfirst : E c = N c) (hlast : N d = W d) (ht : d ≤ t) :
    joinThree c d E N W t = W t := by
  rcases ht.eq_or_lt with rfl | h
  · rw [← hlast]; exact joinThree_eq_middle hfirst ⟨hcd, le_rfl⟩
  · simp [joinThree, not_le.2 h, not_le.2 (hcd.trans_lt h)]

theorem continuous_joinThree {c d : ℝ} {E N W : ℝ → ℝ}
    (hcd : c ≤ d) (hE : Continuous E) (hN : Continuous N) (hW : Continuous W)
    (hfirst : E c = N c) (hlast : N d = W d) :
    Continuous (joinThree c d E N W) :=
  hE.if_le (hN.if_le hW continuous_id continuous_const fun _ (h : _ = _) => h ▸ hlast)
    continuous_id continuous_const fun _ (h : _ = _) => by rw [h, ite_eq_left hcd, hfirst]

theorem hasDerivAt_joinThree {c d : ℝ} {E N W ED ND WD : ℝ → ℝ} (hcd : c ≤ d)
    (hE : ∀ t, HasDerivAt E (ED t) t) (hN : ∀ t, HasDerivAt N (ND t) t)
    (hW : ∀ t, HasDerivAt W (WD t) t) (hfirst : E c = N c) (hlast : N d = W d)
    (hfirstD : ED c = ND c) (hlastD : ND d = WD d) (t : ℝ) :
    HasDerivAt (joinThree c d E N W) (joinThree c d ED ND WD t) t :=
  Reference.hasDerivAt_if_le c hE (Reference.hasDerivAt_if_le d hN hW hlast hlastD)
    (by rw [ite_eq_left hcd, hfirst]) (by rw [ite_eq_left hcd, hfirstD]) t

def familyFEarly (b t : ℝ) : ℝ := familyWidth b * Real.cos t + familyEndpoint b * Real.sin t

def familyGEarly (b t : ℝ) : ℝ := 1 / 2 + Real.cos t / 2 + familyWidth b / 2 * Real.sin t

def familyFMiddle (b t : ℝ) : ℝ :=
  familyRadius b * Real.cos (tailPhase t) + familySineCoefficient b * Real.sin t

def familyGMiddle (b t : ℝ) : ℝ :=
  familyRadius b * Real.sin (tailPhase t) + familySineCoefficient b * Real.cos t

def familyFLate (b t : ℝ) : ℝ := 1 / 2 + Real.sin t / 2 + familyWidth b / 2 * Real.cos t

def familyGLate (b t : ℝ) : ℝ := familyWidth b * Real.sin t + familyEndpoint b * Real.cos t

def familyFEarlyD (b t : ℝ) : ℝ := -(familyWidth b) * Real.sin t + familyEndpoint b * Real.cos t

def familyGEarlyD (b t : ℝ) : ℝ := -(Real.sin t) / 2 + familyWidth b / 2 * Real.cos t

def familyFMiddleD (b t : ℝ) : ℝ :=
  -(familyRadius b / 2) * Real.sin (tailPhase t) + familySineCoefficient b * Real.cos t

def familyGMiddleD (b t : ℝ) : ℝ :=
  familyRadius b / 2 * Real.cos (tailPhase t) - familySineCoefficient b * Real.sin t

def familyFLateD (b t : ℝ) : ℝ := Real.cos t / 2 - familyWidth b / 2 * Real.sin t

def familyGLateD (b t : ℝ) : ℝ := familyWidth b * Real.cos t - familyEndpoint b * Real.sin t

def familyF (b : ℝ) : ℝ → ℝ := joinThree b (familyLateSwitch b)
  (familyFEarly b) (familyFMiddle b) (familyFLate b)

def familyG (b : ℝ) : ℝ → ℝ := joinThree b (familyLateSwitch b)
  (familyGEarly b) (familyGMiddle b) (familyGLate b)

def familyFD (b : ℝ) : ℝ → ℝ := joinThree b (familyLateSwitch b)
  (familyFEarlyD b) (familyFMiddleD b) (familyFLateD b)

def familyGD (b : ℝ) : ℝ → ℝ := joinThree b (familyLateSwitch b)
  (familyGEarlyD b) (familyGMiddleD b) (familyGLateD b)

theorem familyF_matching_first {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyFEarly b b = familyFMiddle b b := by
  unfold familyFEarly familyFMiddle familyWidth familyEndpoint familySineCoefficient
  linear_combination 2 / 3 * familyCot b * Real.sin_sq_add_cos_sq b - familyRadius_mul_cos hb

theorem familyG_matching_first {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyGEarly b b = familyGMiddle b b := by
  unfold familyGEarly familyGMiddle familyWidth familySineCoefficient
  linear_combination 1 / 6 * Real.sin_sq_add_cos_sq b - familyRadius_mul_sin hb

theorem familyFD_matching_first {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyFEarlyD b b = familyFMiddleD b b := by
  unfold familyFEarlyD familyFMiddleD familyWidth familyEndpoint familySineCoefficient
  linear_combination -1 / 3 * Real.sin_sq_add_cos_sq b + 1 / 2 * familyRadius_mul_sin hb

theorem familyGD_matching_first {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyGEarlyD b b = familyGMiddleD b b := by
  unfold familyGEarlyD familyGMiddleD familyWidth familySineCoefficient
  linear_combination familyCot b / 3 * Real.sin_sq_add_cos_sq b - 1 / 2 * familyRadius_mul_cos hb

theorem tailPhase_reflection (t : ℝ) :
    tailPhase (Real.pi / 2 - t) = Real.pi / 2 - tailPhase t := by
  unfold tailPhase tailAngle0; ring

theorem familyF_matching_last {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyFMiddle b (familyLateSwitch b) = familyFLate b (familyLateSwitch b) := by
  simpa only [familyFMiddle, familyFLate, familyGEarly, familyGMiddle, familyLateSwitch,
    tailPhase_reflection, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    using (familyG_matching_first hb).symm

theorem familyG_matching_last {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyGMiddle b (familyLateSwitch b) = familyGLate b (familyLateSwitch b) := by
  simpa only [familyGMiddle, familyGLate, familyFEarly, familyFMiddle, familyLateSwitch,
    tailPhase_reflection, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    using (familyF_matching_first hb).symm

theorem familyFD_matching_last {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyFMiddleD b (familyLateSwitch b) = familyFLateD b (familyLateSwitch b) := by
  simp only [familyFMiddleD, familyFLateD, familyLateSwitch, tailPhase_reflection, familyWidth,
    familySineCoefficient, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  linear_combination familyCot b / 3 * Real.sin_sq_add_cos_sq b - 1 / 2 * familyRadius_mul_cos hb

theorem familyGD_matching_last {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyGMiddleD b (familyLateSwitch b) = familyGLateD b (familyLateSwitch b) := by
  simp only [familyGMiddleD, familyGLateD, familyLateSwitch, tailPhase_reflection, familyWidth,
    familyEndpoint, familySineCoefficient, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  linear_combination -1 / 3 * Real.sin_sq_add_cos_sq b + 1 / 2 * familyRadius_mul_sin hb

theorem hasDerivAt_familyF {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (t : ℝ) :
    HasDerivAt (familyF b) (familyFD b t) t :=
  hasDerivAt_joinThree (family_switch_order hb)
    (fun t => (((Real.hasDerivAt_cos t).const_mul _).add
      ((Real.hasDerivAt_sin t).const_mul _)).congr_deriv (by unfold familyFEarlyD; ring))
    (fun t => (((hasDerivAt_tailPhase t).cos.const_mul _).add
      ((Real.hasDerivAt_sin t).const_mul _)).congr_deriv (by unfold familyFMiddleD; ring))
    (fun t => ((((Real.hasDerivAt_sin t).div_const 2).const_add _).add
      ((Real.hasDerivAt_cos t).const_mul _)).congr_deriv (by unfold familyFLateD; ring))
    (familyF_matching_first hb) (familyF_matching_last hb)
    (familyFD_matching_first hb) (familyFD_matching_last hb) t

theorem hasDerivAt_familyG {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (t : ℝ) :
    HasDerivAt (familyG b) (familyGD b t) t :=
  hasDerivAt_joinThree (family_switch_order hb)
    (fun t => ((((Real.hasDerivAt_cos t).div_const 2).const_add _).add
      ((Real.hasDerivAt_sin t).const_mul _)).congr_deriv (by unfold familyGEarlyD; ring))
    (fun t => (((hasDerivAt_tailPhase t).sin.const_mul _).add
      ((Real.hasDerivAt_cos t).const_mul _)).congr_deriv (by unfold familyGMiddleD; ring))
    (fun t => (((Real.hasDerivAt_sin t).const_mul _).add
      ((Real.hasDerivAt_cos t).const_mul _)).congr_deriv (by unfold familyGLateD; ring))
    (familyG_matching_first hb) (familyG_matching_last hb)
    (familyGD_matching_first hb) (familyGD_matching_last hb) t

theorem continuous_familyF {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    Continuous (familyF b) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_familyF hb t).continuousAt

theorem continuous_familyG {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    Continuous (familyG b) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_familyG hb t).continuousAt

theorem continuous_familyFD {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    Continuous (familyFD b) :=
  continuous_joinThree (family_switch_order hb) (by unfold familyFEarlyD; fun_prop)
    (by unfold familyFMiddleD tailPhase; fun_prop) (by unfold familyFLateD; fun_prop)
    (familyFD_matching_first hb) (familyFD_matching_last hb)

theorem continuous_familyGD {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    Continuous (familyGD b) :=
  continuous_joinThree (family_switch_order hb) (by unfold familyGEarlyD; fun_prop)
    (by unfold familyGMiddleD tailPhase; fun_prop) (by unfold familyGLateD; fun_prop)
    (familyGD_matching_first hb) (familyGD_matching_last hb)

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
  refine ⟨?_, ?_, (familyF_eq_late hb hL).trans ?_, (familyG_eq_late hb hL).trans ?_⟩ <;>
    norm_num [familyPair, familyF, familyG, joinThree, hb.1, familyFEarly, familyGEarly,
      familyFLate, familyGLate]

end AmbidextrousSofa.Analysis
