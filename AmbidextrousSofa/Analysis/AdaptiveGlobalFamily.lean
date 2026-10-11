module

public import AmbidextrousSofa.Analysis.AdaptiveGlobalParameters

@[expose] public section

/-!
# Actual three-phase stationary profiles

The first support of each member is joined from an early phase without
contact, the fully active phase, and a late phase. Values and derivatives
match at both switching angles, so the support is continuously
differentiable, and the member is the symmetric pair it generates. The
parameter inequalities are ordinary switching-angle bounds.
-/

noncomputable section

open Set

namespace AmbidextrousSofa.Analysis

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

def familyFEarly (b t : ℝ) : ℝ := familyWidth b * Real.cos t + familyEndpoint b * Real.sin t

def familyFEarlyD (b t : ℝ) : ℝ := -(familyWidth b) * Real.sin t + familyEndpoint b * Real.cos t

def familyFLate (b t : ℝ) : ℝ := 1 / 2 + Real.sin t / 2 + familyWidth b / 2 * Real.cos t

def familyFLateD (b t : ℝ) : ℝ := Real.cos t / 2 - familyWidth b / 2 * Real.sin t

def familyF (b : ℝ) : ℝ → ℝ := joinThree b (familyLateSwitch b)
  (familyFEarly b) (activeF (familyRadius b) (familySineCoefficient b)) (familyFLate b)

def familyFD (b : ℝ) : ℝ → ℝ := joinThree b (familyLateSwitch b)
  (familyFEarlyD b) (activeFD (familyRadius b) (familySineCoefficient b)) (familyFLateD b)

/-- Values and derivatives match at both switching angles. -/
theorem familyF_matching {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyFEarly b b = activeF (familyRadius b) (familySineCoefficient b) b ∧
      familyFEarlyD b b = activeFD (familyRadius b) (familySineCoefficient b) b ∧
      activeF (familyRadius b) (familySineCoefficient b) (familyLateSwitch b) =
        familyFLate b (familyLateSwitch b) ∧
      activeFD (familyRadius b) (familySineCoefficient b) (familyLateSwitch b) =
        familyFLateD b (familyLateSwitch b) := by
  simp only [familyFEarly, familyFEarlyD, familyFLate, familyFLateD, activeF, activeFD,
    familyLateSwitch, tailPhase_reflection, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub,
    familyWidth, familyEndpoint, familySineCoefficient]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination 2 / 3 * familyCot b * Real.sin_sq_add_cos_sq b - familyRadius_mul_cos hb
  · linear_combination -1 / 3 * Real.sin_sq_add_cos_sq b + 1 / 2 * familyRadius_mul_sin hb
  · linear_combination familyRadius_mul_sin hb - 1 / 6 * Real.sin_sq_add_cos_sq b
  · linear_combination familyCot b / 3 * Real.sin_sq_add_cos_sq b - 1 / 2 * familyRadius_mul_cos hb

theorem hasDerivAt_familyF {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (t : ℝ) :
    HasDerivAt (familyF b) (familyFD b t) t :=
  hasDerivAt_joinThree (family_switch_order hb)
    (fun t => (((Real.hasDerivAt_cos t).const_mul _).add
      ((Real.hasDerivAt_sin t).const_mul _)).congr_deriv (by unfold familyFEarlyD; ring))
    (hasDerivAt_activeF _ _)
    (fun t => ((((Real.hasDerivAt_sin t).div_const 2).const_add _).add
      ((Real.hasDerivAt_cos t).const_mul _)).congr_deriv (by unfold familyFLateD; ring))
    (familyF_matching hb).1 (familyF_matching hb).2.2.1 (familyF_matching hb).2.1
    (familyF_matching hb).2.2.2 t

theorem continuous_familyFD {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    Continuous (familyFD b) :=
  continuous_joinThree (family_switch_order hb) (by unfold familyFEarlyD; fun_prop)
    (continuous_activeFD _ _) (by unfold familyFLateD; fun_prop)
    (familyF_matching hb).2.1 (familyF_matching hb).2.2.2

abbrev familyPair (b : ℝ) (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) : QuarterPair :=
  symmetricPair (familyF b) (familyFD b) (hasDerivAt_familyF hb) (continuous_familyFD hb)

theorem familyF_eq_middle {b t : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (ht : t ∈ Icc b (familyLateSwitch b)) :
    familyF b t = activeF (familyRadius b) (familySineCoefficient b) t ∧
      familyFD b t = activeFD (familyRadius b) (familySineCoefficient b) t :=
  ⟨joinThree_eq_middle (familyF_matching hb).1 ht,
    joinThree_eq_middle (familyF_matching hb).2.1 ht⟩

theorem familyF_eq_late {b t : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (ht : familyLateSwitch b ≤ t) :
    familyF b t = familyFLate b t ∧ familyFD b t = familyFLateD b t :=
  ⟨joinThree_eq_late (family_switch_order hb) (familyF_matching hb).1
      (familyF_matching hb).2.2.1 ht,
    joinThree_eq_late (family_switch_order hb) (familyF_matching hb).2.1
      (familyF_matching hb).2.2.2 ht⟩

theorem familyF_traces {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyF b 0 = familyWidth b ∧ familyF b (Real.pi / 2) = 1 :=
  ⟨by simp [familyF, joinThree, hb.1, familyFEarly],
    (familyF_eq_late hb (by unfold familyLateSwitch; linarith [hb.1])).1.trans
      (by norm_num [familyFLate])⟩

theorem familyPair_widthTraces {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    (familyPair b hb).WidthTraces (familyWidth b) :=
  symmetricPair_widthTraces (familyF_traces hb).1 (familyF_traces hb).2

end AmbidextrousSofa.Analysis
