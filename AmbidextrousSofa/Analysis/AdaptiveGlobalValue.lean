module

public import AmbidextrousSofa.Analysis.AdaptiveGlobalMomenta

@[expose] public section

/-!
# Integral value of the actual stationary family

The value density is integrated over the three phases, including both
degenerate switching configurations: the outer phases have elementary sine
and cosine primitives, and on the fully active phase the density is the
derivative of the half difference of the supports. The self-variation is
the boundary term of the Euler fluxes. Thus the scalar `familyScore` is
identified with the support functional of the constructed `QuarterPair`;
its value is not an input to the construction.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa.Analysis

def familyEarlyValuePrimitive (b t : ℝ) : ℝ :=
  t / 2 + (familyEndpoint b / 2 + familyWidth b / 4 - 1 / 2) * Real.sin t +
    (familyWidth b + 1 / 4) * Real.cos t

def familyLateValuePrimitive (b t : ℝ) : ℝ :=
  t / 2 - (familyEndpoint b / 2 + familyWidth b / 4 - 1 / 2) * Real.cos t -
    (familyWidth b + 1 / 4) * Real.sin t

/-- The scalar objective is the actual integral of the constructed
stationary pair, with its actual half-width subtracted. -/
theorem familyPair_score {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    adaptiveFunctional (familyPair b hb) - familyWidth b = familyScore b := by
  have hbL := family_switch_order hb
  have hL : familyLateSwitch b ≤ Real.pi / 2 := by unfold familyLateSwitch; linarith [hb.1]
  have hi {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ Real.pi / 2) :
      IntervalIntegrable (fun t => 2 * adaptiveDensity (familyPair b hb) t -
        adaptiveLinearDensity (familyPair b hb) (familyPair b hb) t) volume a c :=
    ContinuousOn.intervalIntegrable_of_Icc hac ((((continuousOn_adaptiveDensity _).const_mul 2).sub
      (continuousOn_adaptiveLinearDensity _ _)).mono fun _ ht => ⟨ha.trans ht.1, ht.2.trans hc⟩)
  have hearly := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := familyEarlyValuePrimitive b) hb.1 (by unfold familyEarlyValuePrimitive; fun_prop)
    (fun t ht => by
      rw [(familyPair_early hb (Ioo_subset_Icc_self ht)).2.2]
      exact ((((hasDerivAt_id t).div_const 2).add ((Real.hasDerivAt_sin t).const_mul _)).add
        ((Real.hasDerivAt_cos t).const_mul _)).congr_deriv (by ring))
    (hi le_rfl hb.1 (hbL.trans hL))
  have hlate := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := familyLateValuePrimitive b) hL (by unfold familyLateValuePrimitive; fun_prop)
    (fun t ht => by
      rw [(familyPair_late hb (Ioo_subset_Icc_self ht)).2.2]
      exact ((((hasDerivAt_id t).div_const 2).sub ((Real.hasDerivAt_cos t).const_mul _)).sub
        ((Real.hasDerivAt_sin t).const_mul _)).congr_deriv (by ring))
    (hi (hb.1.trans hbL) hL le_rfl)
  have h := two_mul_adaptiveFunctional (familyPair b hb)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi le_rfl (hb.1.trans hbL) hL)
      (hi (hb.1.trans hbL) hL le_rfl),
    ← intervalIntegral.integral_add_adjacent_intervals (hi le_rfl hb.1 (hbL.trans hL))
      (hi hb.1 hbL hL), hearly, hlate,
    integral_remainder_of_active hb.1 hbL hL fun s hs => (familyPair_middle hb hs).1,
    symmetricPair_self_variation fun t ht => familyPair_euler hb ht,
    (familyPair_early hb ⟨le_rfl, hb.1⟩).1, (familyPair_late hb ⟨hL, le_rfl⟩).1,
    (familyF_traces hb).1, (familyF_traces hb).2] at h
  have hF : familyF b b = familyFEarly b b := by simp [familyF, joinThree]
  have hFL := (familyF_eq_late hb le_rfl).1
  have hg : (familyPair b hb).g (familyLateSwitch b) = familyFEarly b b := by
    simp [symmetricPair, familyLateSwitch, hF]
  rw [hg, show (familyPair b hb).g b = familyFLate b (familyLateSwitch b) from hFL,
    show (familyPair b hb).f (familyLateSwitch b) = familyFLate b (familyLateSwitch b) from hFL,
    show (familyPair b hb).f b = familyFEarly b b from hF] at h
  simp only [familyEarlyValuePrimitive, familyLateValuePrimitive, familyFluxEarly, familyFluxLate,
    familyFEarly, familyFLate, familyLateSwitch, Real.sin_zero, Real.cos_zero,
    Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub] at h
  unfold familyScore
  linear_combination h / 2

end AmbidextrousSofa.Analysis
