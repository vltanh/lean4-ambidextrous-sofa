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

def familyValueRemainder (b : ℝ) (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (t : ℝ) : ℝ :=
  2 * adaptiveDensity (familyPair b hb) t -
    adaptiveLinearDensity (familyPair b hb) (familyPair b hb) t

theorem intervalIntegrable_familyValueRemainder {b a c : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (hac : a ≤ c) (ha : 0 ≤ a) (hc : c ≤ Real.pi / 2) :
    IntervalIntegrable (familyValueRemainder b hb) volume a c :=
  ContinuousOn.intervalIntegrable_of_Icc hac ((((continuousOn_adaptiveDensity _).const_mul 2).sub
    (continuousOn_adaptiveLinearDensity _ _)).mono fun _ ht => ⟨ha.trans ht.1, ht.2.trans hc⟩)

def familyEarlyValuePrimitive (b t : ℝ) : ℝ :=
  t / 2 + (familyEndpoint b / 2 + familyWidth b / 4 - 1 / 2) * Real.sin t +
    (familyWidth b + 1 / 4) * Real.cos t

def familyLateValuePrimitive (b t : ℝ) : ℝ :=
  t / 2 - (familyEndpoint b / 2 + familyWidth b / 4 - 1 / 2) * Real.cos t -
    (familyWidth b + 1 / 4) * Real.sin t

theorem integral_familyValueRemainder_early {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    (∫ t in (0 : ℝ)..b, familyValueRemainder b hb t) =
      familyEarlyValuePrimitive b b - familyEarlyValuePrimitive b 0 := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := familyEarlyValuePrimitive b)
    hb.1 (by unfold familyEarlyValuePrimitive; fun_prop) (fun t ht => ?_)
    (intervalIntegrable_familyValueRemainder hb hb.1 le_rfl (by linarith [hb.2, Real.pi_pos]))
  obtain ⟨hp, hq⟩ := familyPair_signs_early hb (Ioo_subset_Icc_self ht)
  rw [familyValueRemainder, Reference.twice_density_sub_self_variation, min_eq_right hp,
    max_eq_left hq]
  simp only [QuarterPair.q, familyPair, familyF, familyG, familyFD, familyGD, joinThree, ht.2.le,
    ↓reduceIte, familyFEarly, familyGEarly, familyFEarlyD, familyGEarlyD]
  exact ((((hasDerivAt_id t).div_const 2).add ((Real.hasDerivAt_sin t).const_mul _)).add
    ((Real.hasDerivAt_cos t).const_mul _)).congr_deriv (by ring)

theorem integral_familyValueRemainder_middle {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    (∫ t in b..familyLateSwitch b, familyValueRemainder b hb t) =
      (familyG b (familyLateSwitch b) - familyF b (familyLateSwitch b)) / 2 -
        (familyG b b - familyF b b) / 2 := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (family_switch_order hb)
    (((continuous_familyG hb).sub (continuous_familyF hb)).div_const 2).continuousOn
    (fun t ht => ?_) (intervalIntegrable_familyValueRemainder hb (family_switch_order hb) hb.1
      (by unfold familyLateSwitch; linarith [hb.1]))
  obtain ⟨hp, hq⟩ := familyPair_signs_middle hb (Ioo_subset_Icc_self ht)
  rw [familyValueRemainder, Reference.twice_density_sub_self_variation, min_eq_left hp,
    max_eq_left hq]
  refine (((hasDerivAt_familyG hb t).sub (hasDerivAt_familyF hb t)).div_const 2).congr_deriv ?_
  unfold QuarterPair.p QuarterPair.q familyPair
  ring

theorem integral_familyValueRemainder_late {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    (∫ t in familyLateSwitch b..(Real.pi / 2), familyValueRemainder b hb t) =
      familyLateValuePrimitive b (Real.pi / 2) -
        familyLateValuePrimitive b (familyLateSwitch b) := by
  have hlate : familyLateSwitch b ≤ Real.pi / 2 := by unfold familyLateSwitch; linarith [hb.1]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := familyLateValuePrimitive b)
    hlate (by unfold familyLateValuePrimitive; fun_prop) (fun t ht => ?_)
    (intervalIntegrable_familyValueRemainder hb hlate (hb.1.trans (family_switch_order hb)) le_rfl)
  have ht' : t ∈ Icc (familyLateSwitch b) (Real.pi / 2) := Ioo_subset_Icc_self ht
  rw [familyValueRemainder, Reference.twice_density_sub_self_variation,
    min_eq_left (familyPair_signs_late hb ht').1, max_eq_right (familyPair_signs_late hb ht').2]
  simp only [QuarterPair.p, familyPair, familyF_eq_late hb ht'.1, familyG_eq_late hb ht'.1,
    familyFD_eq_late hb ht'.1, familyGD_eq_late hb ht'.1, familyFLate, familyGLate, familyFLateD,
    familyGLateD]
  exact ((((hasDerivAt_id t).div_const 2).sub ((Real.hasDerivAt_cos t).const_mul _)).sub
    ((Real.hasDerivAt_sin t).const_mul _)).congr_deriv (by ring)

/-- The contact formulas agree on both sides, so all three integral
identities remain valid when the early or middle phase has zero length. -/
theorem integral_familyValueRemainder {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    (∫ t in (0 : ℝ)..(Real.pi / 2), familyValueRemainder b hb t) =
      b + (2 * familyEndpoint b - 1) * Real.sin b +
        3 * familyWidth b * Real.cos b - 2 * familyWidth b - 1 := by
  have hlate : familyLateSwitch b ≤ Real.pi / 2 := by unfold familyLateSwitch; linarith [hb.1]
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
  simp only [familyF, familyG, joinThree, le_rfl, ↓reduceIte, familyFEarly, familyGEarly,
    familyFLate, familyGLate, familyEarlyValuePrimitive, familyLateValuePrimitive,
    familyLateSwitch, Real.sin_zero, Real.cos_zero, Real.sin_pi_div_two,
    Real.cos_pi_div_two, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring

theorem familyPair_self_variation {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    adaptiveFirstVariation (familyPair b hb) (familyPair b hb) =
      3 * familyWidth b - 1 + 2 * familyEndpoint b * familyWidth b := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (Real.pi / 2) := ⟨le_rfl, by positivity⟩
  have hL : Real.pi / 2 ∈ Icc (0 : ℝ) (Real.pi / 2) := ⟨by positivity, le_rfl⟩
  have hlate : familyLateSwitch b ≤ Real.pi / 2 := by unfold familyLateSwitch; linarith [hb.1]
  have h := familyPair_widthTraces hb
  simp only [QuarterPair.WidthTraces, familyPair] at h
  rw [adaptiveFirstVariation_eq_boundary _ _ (fun _ => familyPair_eulerF hb)
      (fun _ => familyPair_eulerG hb), familyPair_fluxF_eq hb hL, familyPair_fluxG_eq hb hL,
    familyPair_fluxF_eq hb h0, familyPair_fluxG_eq hb h0, familyP, familyQ,
    joinThree_eq_late (family_switch_order hb) (familyP_matching_first hb)
      (familyP_matching_last hb) hlate,
    joinThree_eq_late (family_switch_order hb) (familyQ_matching_first hb)
      (familyQ_matching_last hb) hlate]
  simp only [familyPair, h, joinThree, hb.1, ↓reduceIte, familyPEarly, familyQEarly, familyPLate,
    familyQLate, Real.sin_zero, Real.cos_zero, Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

/-- The scalar objective is the actual integral of the constructed
stationary pair, with its actual half-width subtracted. -/
theorem familyPair_score {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    adaptiveFunctional (familyPair b hb) - familyWidth b = familyScore b := by
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have h := integral_familyValueRemainder hb
  unfold familyValueRemainder at h
  rw [intervalIntegral.integral_sub
      (((continuousOn_adaptiveDensity _).intervalIntegrable_of_Icc hL).const_mul 2)
      ((continuousOn_adaptiveLinearDensity _ _).intervalIntegrable_of_Icc hL),
    intervalIntegral.integral_const_mul, ← adaptiveFunctional, ← adaptiveFirstVariation,
    familyPair_self_variation hb] at h
  unfold familyScore
  linear_combination h / 2

end AmbidextrousSofa.Analysis
