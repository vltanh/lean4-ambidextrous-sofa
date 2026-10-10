module

public import AmbidextrousSofa.Analysis.AdaptiveGlobalMomenta
public import AmbidextrousSofa.Reference.Value

@[expose] public section

/-!
# Integral value of the actual stationary family

The three phase formulas are integrated here, including both degenerate
switching configurations. The self-variation is computed from the actual
Euler fluxes, and subtraction leaves elementary sine and cosine primitives.
Thus the scalar `familyScore` is identified with the support functional of
the constructed `QuarterPair`; its value is not an input to the construction.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa.Analysis

def familyValueRemainder (b : ℝ) (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (t : ℝ) : ℝ :=
  2 * adaptiveDensity (familyPair b hb) t -
    adaptiveLinearDensity (familyPair b hb) (familyPair b hb) t

theorem continuousOn_familyValueRemainder {b : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    ContinuousOn (familyValueRemainder b hb) (Icc (0 : ℝ) (Real.pi / 2)) :=
  ((continuousOn_adaptiveDensity (familyPair b hb)).const_mul 2).sub
    (continuousOn_adaptiveLinearDensity (familyPair b hb) (familyPair b hb))

theorem familyValueRemainder_early {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ∈ Icc (0 : ℝ) b) :
    familyValueRemainder b hb t =
      1 / 2 + (familyEndpoint b / 2 + familyWidth b / 4 - 1 / 2) * Real.cos t -
        (familyWidth b + 1 / 4) * Real.sin t := by
  rw [familyValueRemainder, Reference.twice_density_sub_self_variation,
    min_eq_right (familyPair_signs_early hb ht).1,
    max_eq_left (familyPair_signs_early hb ht).2]
  simp only [QuarterPair.q, familyPair, familyF, familyG, familyFD, familyGD,
    joinThree, if_pos ht.2, familyFEarly, familyGEarly, familyFEarlyD, familyGEarlyD]
  ring

theorem familyValueRemainder_middle {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (ht : t ∈ Icc b (familyLateSwitch b)) :
    familyValueRemainder b hb t = (familyGD b t - familyFD b t) / 2 := by
  rw [familyValueRemainder, Reference.twice_density_sub_self_variation,
    min_eq_left (familyPair_signs_middle hb ht).1,
    max_eq_left (familyPair_signs_middle hb ht).2]
  unfold QuarterPair.p QuarterPair.q familyPair
  ring

theorem familyValueRemainder_late {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (ht : t ∈ Icc (familyLateSwitch b) (Real.pi / 2)) :
    familyValueRemainder b hb t =
      1 / 2 + (familyEndpoint b / 2 + familyWidth b / 4 - 1 / 2) * Real.sin t -
        (familyWidth b + 1 / 4) * Real.cos t := by
  rw [familyValueRemainder, Reference.twice_density_sub_self_variation,
    min_eq_left (familyPair_signs_late hb ht).1,
    max_eq_right (familyPair_signs_late hb ht).2]
  simp only [QuarterPair.p, familyPair]
  rw [familyF_eq_late hb ht.1, familyG_eq_late hb ht.1,
    familyFD_eq_late hb ht.1, familyGD_eq_late hb ht.1]
  unfold familyFLate familyGLate familyFLateD familyGLateD
  ring

def familyEarlyValuePrimitive (b t : ℝ) : ℝ :=
  t / 2 + (familyEndpoint b / 2 + familyWidth b / 4 - 1 / 2) * Real.sin t +
    (familyWidth b + 1 / 4) * Real.cos t

def familyLateValuePrimitive (b t : ℝ) : ℝ :=
  t / 2 - (familyEndpoint b / 2 + familyWidth b / 4 - 1 / 2) * Real.cos t -
    (familyWidth b + 1 / 4) * Real.sin t

theorem hasDerivAt_familyEarlyValuePrimitive (b t : ℝ) :
    HasDerivAt (familyEarlyValuePrimitive b)
      (1 / 2 + (familyEndpoint b / 2 + familyWidth b / 4 - 1 / 2) * Real.cos t -
        (familyWidth b + 1 / 4) * Real.sin t) t := by
  apply ((((hasDerivAt_id t).div_const 2).add
    ((Real.hasDerivAt_sin t).const_mul
      (familyEndpoint b / 2 + familyWidth b / 4 - 1 / 2))).add
    ((Real.hasDerivAt_cos t).const_mul (familyWidth b + 1 / 4))).congr_deriv
  ring

theorem hasDerivAt_familyLateValuePrimitive (b t : ℝ) :
    HasDerivAt (familyLateValuePrimitive b)
      (1 / 2 + (familyEndpoint b / 2 + familyWidth b / 4 - 1 / 2) * Real.sin t -
        (familyWidth b + 1 / 4) * Real.cos t) t := by
  apply ((((hasDerivAt_id t).div_const 2).sub
    ((Real.hasDerivAt_cos t).const_mul
      (familyEndpoint b / 2 + familyWidth b / 4 - 1 / 2))).sub
    ((Real.hasDerivAt_sin t).const_mul (familyWidth b + 1 / 4))).congr_deriv
  ring

theorem intervalIntegrable_familyValueRemainder {b a c : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (hac : a ≤ c)
    (ha : 0 ≤ a) (hc : c ≤ Real.pi / 2) :
    IntervalIntegrable (familyValueRemainder b hb) volume a c :=
  ContinuousOn.intervalIntegrable_of_Icc hac
    ((continuousOn_familyValueRemainder hb).mono (fun _ ht =>
      ⟨ha.trans ht.1, ht.2.trans hc⟩))

theorem integral_familyValueRemainder_early {b : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    (∫ t in (0 : ℝ)..b, familyValueRemainder b hb t) =
      familyEarlyValuePrimitive b b - familyEarlyValuePrimitive b 0 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb.1
    (by unfold familyEarlyValuePrimitive; fun_prop)
  · intro t ht
    rw [familyValueRemainder_early hb ⟨ht.1.le, ht.2.le⟩]
    exact hasDerivAt_familyEarlyValuePrimitive b t
  · exact intervalIntegrable_familyValueRemainder hb hb.1 le_rfl
      (by linarith [hb.2, Real.pi_pos])

theorem integral_familyValueRemainder_middle {b : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    (∫ t in b..familyLateSwitch b, familyValueRemainder b hb t) =
      (familyG b (familyLateSwitch b) - familyF b (familyLateSwitch b)) / 2 -
        (familyG b b - familyF b b) / 2 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (family_switch_order hb)
    (((continuous_familyG hb).sub (continuous_familyF hb)).div_const 2).continuousOn
  · intro t ht
    rw [familyValueRemainder_middle hb ⟨ht.1.le, ht.2.le⟩]
    exact ((hasDerivAt_familyG hb t).sub (hasDerivAt_familyF hb t)).div_const 2
  · exact intervalIntegrable_familyValueRemainder hb (family_switch_order hb) hb.1
      (by unfold familyLateSwitch; linarith [hb.1])

theorem integral_familyValueRemainder_late {b : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    (∫ t in familyLateSwitch b..(Real.pi / 2), familyValueRemainder b hb t) =
      familyLateValuePrimitive b (Real.pi / 2) -
        familyLateValuePrimitive b (familyLateSwitch b) := by
  have hlate : familyLateSwitch b ≤ Real.pi / 2 := by
    unfold familyLateSwitch
    linarith [hb.1]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlate
    (by unfold familyLateValuePrimitive; fun_prop)
  · intro t ht
    rw [familyValueRemainder_late hb ⟨ht.1.le, ht.2.le⟩]
    exact hasDerivAt_familyLateValuePrimitive b t
  · exact intervalIntegrable_familyValueRemainder hb hlate
      (hb.1.trans (family_switch_order hb)) le_rfl

/-- The contact formulas agree on both sides, so all three integral
identities remain valid when the early or middle phase has zero length. -/
theorem integral_familyValueRemainder {b : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    (∫ t in (0 : ℝ)..(Real.pi / 2), familyValueRemainder b hb t) =
      b + (2 * familyEndpoint b - 1) * Real.sin b +
        3 * familyWidth b * Real.cos b - 2 * familyWidth b - 1 := by
  have hlate : familyLateSwitch b ≤ Real.pi / 2 := by
    unfold familyLateSwitch
    linarith [hb.1]
  have hE := intervalIntegrable_familyValueRemainder hb hb.1 le_rfl
    (show b ≤ Real.pi / 2 by linarith [hb.2, Real.pi_pos])
  have hM := intervalIntegrable_familyValueRemainder hb (family_switch_order hb) hb.1 hlate
  have hL := intervalIntegrable_familyValueRemainder hb hlate
    (hb.1.trans (family_switch_order hb)) le_rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals (hE.trans hM) hL,
    ← intervalIntegral.integral_add_adjacent_intervals hE hM,
    integral_familyValueRemainder_early hb, integral_familyValueRemainder_middle hb,
    integral_familyValueRemainder_late hb,
    familyG_eq_late hb le_rfl, familyF_eq_late hb le_rfl]
  simp only [familyF, familyG, joinThree, if_pos le_rfl, familyFEarly, familyGEarly,
    familyFLate, familyGLate, familyEarlyValuePrimitive, familyLateValuePrimitive,
    familyLateSwitch, Real.sin_zero, Real.cos_zero, Real.sin_pi_div_two,
    Real.cos_pi_div_two, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring

theorem familyP_zero {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyP b 0 = familyEndpoint b := by
  simp only [familyP, joinThree, if_pos hb.1, familyPEarly, Real.sin_zero, Real.cos_zero]
  ring

theorem familyQ_zero {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyQ b 0 = 3 * familyWidth b - 2 := by
  simp only [familyQ, joinThree, if_pos hb.1, familyQEarly, Real.sin_zero, Real.cos_zero]
  ring

theorem familyP_pi_div_two {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyP b (Real.pi / 2) = 2 - 3 * familyWidth b := by
  have hlate : familyLateSwitch b ≤ Real.pi / 2 := by
    unfold familyLateSwitch
    linarith [hb.1]
  rw [familyP, joinThree_eq_late (family_switch_order hb)
    (familyP_matching_first hb) (familyP_matching_last hb) hlate]
  simp only [familyPLate, Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

theorem familyQ_pi_div_two {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyQ b (Real.pi / 2) = -familyEndpoint b := by
  have hlate : familyLateSwitch b ≤ Real.pi / 2 := by
    unfold familyLateSwitch
    linarith [hb.1]
  rw [familyQ, joinThree_eq_late (family_switch_order hb)
    (familyQ_matching_first hb) (familyQ_matching_last hb) hlate]
  simp only [familyQLate, Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

theorem familyPair_self_variation {b : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    adaptiveFirstVariation (familyPair b hb) (familyPair b hb) =
      3 * familyWidth b - 1 + 2 * familyEndpoint b * familyWidth b := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have htop : Real.pi / 2 ∈ Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], le_rfl⟩
  rcases familyPair_widthTraces hb with ⟨hf0, hg0, hfL, hgL⟩
  change familyF b 0 = familyWidth b at hf0
  change familyG b 0 = 1 at hg0
  change familyF b (Real.pi / 2) = 1 at hfL
  change familyG b (Real.pi / 2) = familyWidth b at hgL
  rw [adaptiveFirstVariation_eq_boundary (familyPair b hb) (familyPair b hb)
    (fun _ ht => familyPair_eulerF hb ht) (fun _ ht => familyPair_eulerG hb ht),
    familyPair_fluxF_eq hb htop, familyPair_fluxG_eq hb htop,
    familyPair_fluxF_eq hb hzero, familyPair_fluxG_eq hb hzero,
    familyP_zero hb, familyQ_zero hb, familyP_pi_div_two hb, familyQ_pi_div_two hb]
  simp only [familyPair, hf0, hg0, hfL, hgL]
  ring

/-- The scalar objective is the actual integral of the constructed
stationary pair, with its actual half-width subtracted. -/
theorem familyPair_score {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    adaptiveFunctional (familyPair b hb) - familyWidth b = familyScore b := by
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hd := ContinuousOn.intervalIntegrable_of_Icc hL
    (continuousOn_adaptiveDensity (familyPair b hb))
  have hv := ContinuousOn.intervalIntegrable_of_Icc hL
    (continuousOn_adaptiveLinearDensity (familyPair b hb) (familyPair b hb))
  have h := integral_familyValueRemainder hb
  unfold familyValueRemainder at h
  rw [intervalIntegral.integral_sub (hd.const_mul 2) hv,
    intervalIntegral.integral_const_mul, ← adaptiveFunctional,
    ← adaptiveFirstVariation, familyPair_self_variation hb] at h
  unfold familyScore
  linarith

end AmbidextrousSofa.Analysis
