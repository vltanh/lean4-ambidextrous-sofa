module

public import AmbidextrousSofa.Reference.Momenta
public import AmbidextrousSofa.Analysis.EulerFlux

@[expose] public section

/-!
# Actual Euler equations for the explicit reference pair

The clipped momenta are realized by three continuously differentiable
phases. Matching is checked at both switches, then the Euler equations
give the exact boundary variation and strict optimality at the reference
width. No global cap theorem is used in this construction.
-/

noncomputable section

open Set MeasureTheory
open AmbidextrousSofa.Analysis

namespace AmbidextrousSofa.Reference

def referencePair : QuarterPair where
  f := referenceF
  g := referenceG
  fD := referenceFD
  gD := referenceGD
  continuous_f := continuous_referenceF.continuousOn
  continuous_g := continuous_referenceG.continuousOn
  continuous_fD := continuous_referenceFD.continuousOn
  continuous_gD := continuous_referenceGD.continuousOn
  hasDeriv_f := fun t _ => (hasDerivAt_referenceF t).hasDerivWithinAt
  hasDeriv_g := fun t _ => (hasDerivAt_referenceG t).hasDerivWithinAt

def adjustedMomentP (t : ℝ) : ℝ :=
  if t ≤ beta then 1 / 2 - 2 * A * Real.sin t
  else if t ≤ lateSwitch then 2 - 3 * R * Real.sin (t / 2 + Real.pi / 8)
  else 2 - 4 * A * Real.sin t

def adjustedMomentQ (t : ℝ) : ℝ :=
  if t ≤ beta then 4 * A * Real.cos t - 2
  else if t ≤ lateSwitch then 3 * R * Real.cos (t / 2 + Real.pi / 8) - 2
  else 2 * A * Real.cos t - 1 / 2

def adjustedMomentPD (t : ℝ) : ℝ :=
  if t ≤ beta then -2 * A * Real.cos t
  else if t ≤ lateSwitch then -(3 / 2) * R * Real.cos (t / 2 + Real.pi / 8)
  else -4 * A * Real.cos t

def adjustedMomentQD (t : ℝ) : ℝ :=
  if t ≤ beta then -4 * A * Real.sin t
  else if t ≤ lateSwitch then -(3 / 2) * R * Real.sin (t / 2 + Real.pi / 8)
  else -2 * A * Real.sin t

theorem R_mul_cos_firstPhase_explicit :
    R * Real.cos (beta / 2 + Real.pi / 8) = 4 / 3 * A * cosBeta := by
  rw [R_mul_cos_firstPhase]
  unfold k
  ring

theorem R_mul_sin_lastPhase :
    R * Real.sin (lateSwitch / 2 + Real.pi / 8) = 4 / 3 * A * cosBeta := by
  have hangle : lateSwitch / 2 + Real.pi / 8 =
      Real.pi / 2 - (beta / 2 + Real.pi / 8) := by
    unfold lateSwitch
    ring
  rw [hangle, Real.sin_pi_div_two_sub]
  exact R_mul_cos_firstPhase_explicit

theorem adjustedMomentP_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    adjustedMomentP t = momentP t + min (momentP t) 0 := by
  by_cases hearly : t ≤ beta
  · simp only [min_eq_right (momentP_nonneg_early ⟨ht.1, hearly⟩), add_zero,
      momentP_phases, adjustedMomentP, if_pos hearly]
  · simp only [min_eq_left (momentP_nonpos_after_beta ⟨(le_of_not_ge hearly), ht.2⟩),
      momentP_phases, adjustedMomentP, if_neg hearly]
    split_ifs <;> ring

theorem adjustedMomentQ_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    adjustedMomentQ t = momentQ t + max (momentQ t) 0 := by
  by_cases hbefore : t ≤ lateSwitch
  · have hq := momentQ_nonneg_before_lateSwitch ⟨ht.1, hbefore⟩
    by_cases hearly : t ≤ beta
    · simp only [max_eq_left hq, momentQ_phases, adjustedMomentQ, if_pos hearly] <;> ring
    · simp only [max_eq_left hq, momentQ_phases, adjustedMomentQ,
        if_neg hearly, if_pos hbefore] <;> ring
  · simp only [max_eq_right (momentQ_nonpos_late ⟨(le_of_not_ge hbefore), ht.2⟩), add_zero,
      momentQ_phases, adjustedMomentQ,
      if_neg (not_le.mpr (beta_lt_lateSwitch.trans (lt_of_not_ge hbefore))), if_neg hbefore]

theorem hasDerivAt_adjustedMomentP (t : ℝ) :
    HasDerivAt adjustedMomentP (adjustedMomentPD t) t := by
  have hearly : ∀ x : ℝ, HasDerivAt (fun y => 1 / 2 - 2 * A * Real.sin y)
      (-2 * A * Real.cos x) x := by
    intro x
    exact (((Real.hasDerivAt_sin x).const_mul (2 * A)).const_sub (1 / 2)).congr_deriv
      (by ring)
  have hmiddle : ∀ x : ℝ,
      HasDerivAt (fun y => 2 - 3 * R * Real.sin (y / 2 + Real.pi / 8))
        (-(3 / 2) * R * Real.cos (x / 2 + Real.pi / 8)) x := by
    intro x
    exact ((((hasDerivAt_middlePhaseAngle x).sin).const_mul (3 * R)).const_sub 2).congr_deriv
      (by ring)
  have hlate : ∀ x : ℝ, HasDerivAt (fun y => 2 - 4 * A * Real.sin y)
      (-4 * A * Real.cos x) x := by
    intro x
    exact (((Real.hasDerivAt_sin x).const_mul (4 * A)).const_sub 2).congr_deriv (by ring)
  have hvalueLast :
      2 - 3 * R * Real.sin (lateSwitch / 2 + Real.pi / 8) =
        2 - 4 * A * Real.sin lateSwitch := by
    simp only [lateSwitch, Real.sin_pi_div_two_sub]
    have h := R_mul_sin_lastPhase
    unfold lateSwitch cosBeta at h
    nlinarith
  have hderivLast :
      -(3 / 2) * R * Real.cos (lateSwitch / 2 + Real.pi / 8) =
        -4 * A * Real.cos lateSwitch := by
    have h := R_mul_cos_lastPhase
    unfold lateSwitch at h
    have hA := four_mul_A_mul_sinBeta
    simp only [lateSwitch, Real.cos_pi_div_two_sub, sinBeta] at hA ⊢
    nlinarith
  unfold adjustedMomentP adjustedMomentPD
  apply hasDerivAt_if_le beta hearly
    (hasDerivAt_if_le lateSwitch hmiddle hlate hvalueLast hderivLast)
  · rw [if_pos beta_lt_lateSwitch.le]
    have hA := four_mul_A_mul_sinBeta
    unfold sinBeta at hA
    nlinarith [R_mul_sin_firstPhase]
  · rw [if_pos beta_lt_lateSwitch.le]
    have h := R_mul_cos_firstPhase_explicit
    unfold cosBeta at h
    nlinarith

theorem hasDerivAt_adjustedMomentQ (t : ℝ) :
    HasDerivAt adjustedMomentQ (adjustedMomentQD t) t := by
  have hearly : ∀ x : ℝ, HasDerivAt (fun y => 4 * A * Real.cos y - 2)
      (-4 * A * Real.sin x) x := by
    intro x
    exact (((Real.hasDerivAt_cos x).const_mul (4 * A)).sub_const 2).congr_deriv (by ring)
  have hmiddle : ∀ x : ℝ,
      HasDerivAt (fun y => 3 * R * Real.cos (y / 2 + Real.pi / 8) - 2)
        (-(3 / 2) * R * Real.sin (x / 2 + Real.pi / 8)) x := by
    intro x
    exact ((((hasDerivAt_middlePhaseAngle x).cos).const_mul (3 * R)).sub_const 2).congr_deriv
      (by ring)
  have hlate : ∀ x : ℝ, HasDerivAt (fun y => 2 * A * Real.cos y - 1 / 2)
      (-2 * A * Real.sin x) x := by
    intro x
    exact (((Real.hasDerivAt_cos x).const_mul (2 * A)).sub_const (1 / 2)).congr_deriv
      (by ring)
  have hvalueLast :
      3 * R * Real.cos (lateSwitch / 2 + Real.pi / 8) - 2 =
        2 * A * Real.cos lateSwitch - 1 / 2 := by
    have h := R_mul_cos_lastPhase
    unfold lateSwitch at h
    have hA := four_mul_A_mul_sinBeta
    simp only [lateSwitch, Real.cos_pi_div_two_sub, sinBeta] at hA ⊢
    nlinarith
  have hderivLast :
      -(3 / 2) * R * Real.sin (lateSwitch / 2 + Real.pi / 8) =
        -2 * A * Real.sin lateSwitch := by
    simp only [lateSwitch, Real.sin_pi_div_two_sub]
    have h := R_mul_sin_lastPhase
    unfold lateSwitch cosBeta at h
    nlinarith
  unfold adjustedMomentQ adjustedMomentQD
  apply hasDerivAt_if_le beta hearly
    (hasDerivAt_if_le lateSwitch hmiddle hlate hvalueLast hderivLast)
  · rw [if_pos beta_lt_lateSwitch.le]
    have h := R_mul_cos_firstPhase_explicit
    unfold cosBeta at h
    nlinarith
  · rw [if_pos beta_lt_lateSwitch.le]
    have hA := four_mul_A_mul_sinBeta
    unfold sinBeta at hA
    nlinarith [R_mul_sin_firstPhase]

/-- The two explicit phases satisfy the clipped Euler system at both joins. -/
theorem adjustedMomentPD_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    adjustedMomentPD t = -1 - 2 * momentQ t + max (momentQ t) 0 := by
  by_cases hearly : t ≤ beta
  · have hq := momentQ_nonneg_before_lateSwitch ⟨ht.1, hearly.trans beta_lt_lateSwitch.le⟩
    simp only [max_eq_left hq, momentQ_phases, adjustedMomentPD, if_pos hearly] <;> ring
  · by_cases hmiddle : t ≤ lateSwitch
    · simp only [max_eq_left (momentQ_nonneg_before_lateSwitch ⟨ht.1, hmiddle⟩),
        momentQ_phases, adjustedMomentPD, if_neg hearly, if_pos hmiddle] <;> ring
    · simp only [max_eq_right (momentQ_nonpos_late ⟨(le_of_not_ge hmiddle), ht.2⟩),
        momentQ_phases, adjustedMomentPD, if_neg hearly, if_neg hmiddle] <;> ring

theorem adjustedMomentQD_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    adjustedMomentQD t = -1 + 2 * momentP t - min (momentP t) 0 := by
  by_cases hearly : t ≤ beta
  · simp only [min_eq_right (momentP_nonneg_early ⟨ht.1, hearly⟩),
      momentP_phases, adjustedMomentQD, if_pos hearly] <;> ring
  · simp only [min_eq_left (momentP_nonpos_after_beta ⟨(le_of_not_ge hearly), ht.2⟩),
      momentP_phases, adjustedMomentQD, if_neg hearly]
    split_ifs <;> ring

theorem referencePair_fluxF_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    referencePair.fluxF t = -adjustedMomentP t - 3 / 2 * (referenceG t - 1) := by
  rw [adjustedMomentP_eq ht]
  unfold QuarterPair.fluxF QuarterPair.p referencePair momentP
  ring

theorem referencePair_fluxG_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    referencePair.fluxG t = -adjustedMomentQ t + 3 / 2 * (referenceF t - 1) := by
  rw [adjustedMomentQ_eq ht]
  unfold QuarterPair.fluxG QuarterPair.q referencePair momentQ
  ring

theorem referencePair_eulerF {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivWithinAt referencePair.fluxF (referencePair.forceF t) (Ioi t) t := by
  have h := (hasDerivAt_adjustedMomentP t).neg.sub
    (((hasDerivAt_referenceG t).sub_const 1).const_mul (3 / 2))
  have hderiv : -adjustedMomentPD t - 3 / 2 * referenceGD t = referencePair.forceF t := by
    rw [adjustedMomentPD_eq ⟨ht.1.le, ht.2.le⟩]
    unfold QuarterPair.forceF QuarterPair.q referencePair momentQ
    ring
  apply (h.congr_deriv hderiv).hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [(Ioo_mem_nhds ht.1 ht.2).filter_mono nhdsWithin_le_nhds] with s hs
    exact referencePair_fluxF_eq ⟨hs.1.le, hs.2.le⟩
  · exact referencePair_fluxF_eq ⟨ht.1.le, ht.2.le⟩

theorem referencePair_eulerG {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivWithinAt referencePair.fluxG (referencePair.forceG t) (Ioi t) t := by
  have h := (hasDerivAt_adjustedMomentQ t).neg.add
    (((hasDerivAt_referenceF t).sub_const 1).const_mul (3 / 2))
  have hderiv : -adjustedMomentQD t + 3 / 2 * referenceFD t = referencePair.forceG t := by
    rw [adjustedMomentQD_eq ⟨ht.1.le, ht.2.le⟩]
    unfold QuarterPair.forceG QuarterPair.p referencePair momentP
    ring
  apply (h.congr_deriv hderiv).hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [(Ioo_mem_nhds ht.1 ht.2).filter_mono nhdsWithin_le_nhds] with s hs
    exact referencePair_fluxG_eq ⟨hs.1.le, hs.2.le⟩
  · exact referencePair_fluxG_eq ⟨ht.1.le, ht.2.le⟩

theorem referencePair_stationary : referencePair.Stationary :=
  referencePair.stationary_of_euler (fun _ ht => referencePair_eulerF ht)
    (fun _ ht => referencePair_eulerG ht)

theorem adaptiveFunctional_le_reference_of_sameTraces {u : QuarterPair}
    (htrace : u.SameTraces referencePair) :
    adaptiveFunctional u ≤ adaptiveFunctional referencePair :=
  adaptiveFunctional_le_of_stationary referencePair_stationary htrace

theorem eqOn_reference_of_sameTraces_of_ge {u : QuarterPair}
    (htrace : u.SameTraces referencePair)
    (hvalue : adaptiveFunctional referencePair ≤ adaptiveFunctional u) :
    EqOn u.f referenceF (Icc 0 (Real.pi / 2)) ∧
      EqOn u.g referenceG (Icc 0 (Real.pi / 2)) :=
  eqOn_of_stationary_of_sameTraces_of_ge referencePair_stationary htrace hvalue

end AmbidextrousSofa.Reference
