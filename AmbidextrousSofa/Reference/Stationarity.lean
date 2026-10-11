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

/-- The first-switch identities of `Parameters`, with `k`, `sinBeta` and `cosBeta` unfolded. -/
private theorem firstSwitch_eqs :
    R * Real.cos (beta / 2 + Real.pi / 8) = 4 / 3 * A * Real.cos beta ∧
      R * Real.sin (beta / 2 + Real.pi / 8) = 2 / 3 ∧ 4 * A * Real.sin beta = 1 :=
  ⟨by rw [R_mul_cos_firstPhase, k, cosBeta]; ring, R_mul_sin_firstPhase, four_mul_A_mul_sinBeta⟩

/-- The phase angle at the second switch, reflected to the first switch. -/
private theorem lateSwitch_angle :
    (Real.pi / 2 - beta) / 2 + Real.pi / 8 = Real.pi / 2 - (beta / 2 + Real.pi / 8) := by ring

private theorem beta_le_lateSwitch : beta ≤ Real.pi / 2 - beta := beta_lt_lateSwitch.le

/-- The clipped `P`-momentum and its derivative, from one case split at the first switch. -/
theorem adjustedMomentP_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    adjustedMomentP t = momentP t + min (momentP t) 0 ∧
      adjustedMomentQD t = -1 + 2 * momentP t - min (momentP t) 0 := by
  by_cases hearly : t ≤ beta
  · rw [min_eq_right (momentP_nonneg_early ⟨ht.1, hearly⟩), momentP_phases]
    simp only [adjustedMomentP, adjustedMomentQD, hearly, ite_true]
    constructor <;> ring
  · rw [min_eq_left (momentP_nonpos_after_beta ⟨le_of_not_ge hearly, ht.2⟩), momentP_phases]
    simp only [adjustedMomentP, adjustedMomentQD, hearly, ite_false]
    constructor <;> split_ifs <;> ring

/-- The two explicit phases satisfy the clipped Euler system at both joins: the clipped
`Q`-momentum and the derivative of the `P`-momentum, split at the second switch. -/
theorem adjustedMomentQ_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    adjustedMomentQ t = momentQ t + max (momentQ t) 0 ∧
      adjustedMomentPD t = -1 - 2 * momentQ t + max (momentQ t) 0 := by
  by_cases hbefore : t ≤ lateSwitch
  · rw [max_eq_left (momentQ_nonneg_before_lateSwitch ⟨ht.1, hbefore⟩), momentQ_phases]
    simp only [adjustedMomentQ, adjustedMomentPD, hbefore, ite_true]
    constructor <;> split_ifs <;> ring
  · rw [max_eq_right (momentQ_nonpos_late ⟨le_of_not_ge hbefore, ht.2⟩), momentQ_phases]
    simp only [adjustedMomentQ, adjustedMomentPD, hbefore, ite_false,
      show ¬t ≤ beta from fun h => hbefore (h.trans beta_lt_lateSwitch.le)]
    constructor <;> ring

theorem hasDerivAt_adjustedMomentP (t : ℝ) :
    HasDerivAt adjustedMomentP (adjustedMomentPD t) t := by
  obtain ⟨hC, hS, hA⟩ := firstSwitch_eqs
  have h₁ (x : ℝ) : HasDerivAt (fun y => 1 / 2 - 2 * A * Real.sin y) (-2 * A * Real.cos x) x :=
    (((Real.hasDerivAt_sin x).const_mul (2 * A)).const_sub (1 / 2)).congr_deriv (by ring)
  have h₂ (x : ℝ) : HasDerivAt (fun y => 2 - 3 * R * Real.sin (y / 2 + Real.pi / 8))
      (-(3 / 2) * R * Real.cos (x / 2 + Real.pi / 8)) x :=
    ((((hasDerivAt_middlePhaseAngle x).sin).const_mul (3 * R)).const_sub 2).congr_deriv (by ring)
  have h₃ (x : ℝ) : HasDerivAt (fun y => 2 - 4 * A * Real.sin y) (-4 * A * Real.cos x) x :=
    (((Real.hasDerivAt_sin x).const_mul (4 * A)).const_sub 2).congr_deriv (by ring)
  refine hasDerivAt_if_le beta h₁ (hasDerivAt_if_le lateSwitch h₂ h₃ ?_ ?_) ?_ ?_ t <;>
    simp only [lateSwitch, beta_le_lateSwitch, ite_true, lateSwitch_angle,
      Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub] <;> linarith

theorem hasDerivAt_adjustedMomentQ (t : ℝ) :
    HasDerivAt adjustedMomentQ (adjustedMomentQD t) t := by
  obtain ⟨hC, hS, hA⟩ := firstSwitch_eqs
  have h₁ (x : ℝ) : HasDerivAt (fun y => 4 * A * Real.cos y - 2) (-4 * A * Real.sin x) x :=
    (((Real.hasDerivAt_cos x).const_mul (4 * A)).sub_const 2).congr_deriv (by ring)
  have h₂ (x : ℝ) : HasDerivAt (fun y => 3 * R * Real.cos (y / 2 + Real.pi / 8) - 2)
      (-(3 / 2) * R * Real.sin (x / 2 + Real.pi / 8)) x :=
    ((((hasDerivAt_middlePhaseAngle x).cos).const_mul (3 * R)).sub_const 2).congr_deriv (by ring)
  have h₃ (x : ℝ) : HasDerivAt (fun y => 2 * A * Real.cos y - 1 / 2) (-2 * A * Real.sin x) x :=
    (((Real.hasDerivAt_cos x).const_mul (2 * A)).sub_const (1 / 2)).congr_deriv (by ring)
  refine hasDerivAt_if_le beta h₁ (hasDerivAt_if_le lateSwitch h₂ h₃ ?_ ?_) ?_ ?_ t <;>
    simp only [lateSwitch, beta_le_lateSwitch, ite_true, lateSwitch_angle,
      Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub] <;> linarith

theorem referencePair_fluxF_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    referencePair.fluxF t = -adjustedMomentP t - 3 / 2 * (referenceG t - 1) := by
  rw [(adjustedMomentP_eq ht).1]
  unfold QuarterPair.fluxF QuarterPair.p referencePair momentP
  ring

theorem referencePair_fluxG_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    referencePair.fluxG t = -adjustedMomentQ t + 3 / 2 * (referenceF t - 1) := by
  rw [(adjustedMomentQ_eq ht).1]
  unfold QuarterPair.fluxG QuarterPair.q referencePair momentQ
  ring

theorem referencePair_eulerF {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivWithinAt referencePair.fluxF (referencePair.forceF t) (Ioi t) t := by
  have hderiv : -adjustedMomentPD t - 3 / 2 * referenceGD t = referencePair.forceF t := by
    rw [(adjustedMomentQ_eq ⟨ht.1.le, ht.2.le⟩).2]
    unfold QuarterPair.forceF QuarterPair.q referencePair momentQ
    ring
  refine (((hasDerivAt_adjustedMomentP t).neg.sub (((hasDerivAt_referenceG t).sub_const
    1).const_mul (3 / 2))).congr_deriv hderiv).hasDerivWithinAt.congr_of_eventuallyEq ?_
    (referencePair_fluxF_eq ⟨ht.1.le, ht.2.le⟩)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds ht.1 ht.2)] with s hs
  exact referencePair_fluxF_eq ⟨hs.1.le, hs.2.le⟩

theorem referencePair_eulerG {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivWithinAt referencePair.fluxG (referencePair.forceG t) (Ioi t) t := by
  have hderiv : -adjustedMomentQD t + 3 / 2 * referenceFD t = referencePair.forceG t := by
    rw [(adjustedMomentP_eq ⟨ht.1.le, ht.2.le⟩).2]
    unfold QuarterPair.forceG QuarterPair.p referencePair momentP
    ring
  refine (((hasDerivAt_adjustedMomentQ t).neg.add (((hasDerivAt_referenceF t).sub_const
    1).const_mul (3 / 2))).congr_deriv hderiv).hasDerivWithinAt.congr_of_eventuallyEq ?_
    (referencePair_fluxG_eq ⟨ht.1.le, ht.2.le⟩)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds ht.1 ht.2)] with s hs
  exact referencePair_fluxG_eq ⟨hs.1.le, hs.2.le⟩

end AmbidextrousSofa.Reference
