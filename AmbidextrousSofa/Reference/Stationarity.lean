module

public import AmbidextrousSofa.Reference.Momenta
public import AmbidextrousSofa.Analysis.EulerFlux

@[expose] public section

/-!
# Actual Euler equations for the explicit reference pair

To the right of each angle, the clipped momenta `min P 0` and `max Q 0` are
either a momentum or zero, so the fluxes have explicit right derivatives, and
the Euler equations reduce to identities on each of the three phases. They give
the exact boundary variation and strict optimality at the reference width. No
global cap theorem is used in this construction.
-/

noncomputable section

open Set
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

/-- At an interior angle, the clipped first momentum `min P 0` is `0` before `beta` and `P`
after it, and so is it to the right of that angle. -/
theorem min_momentP {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    min (momentP t) 0 = (if t < beta then 0 else momentP t) ∧
      HasDerivWithinAt (fun s => min (momentP s) 0)
        (if t < beta then 0 else referenceFSecond t - referenceGD t) (Ioi t) t := by
  split_ifs with h
  · have h₀ := min_eq_right (momentP_nonneg_early ⟨ht.1.le, h.le⟩)
    refine ⟨h₀, (hasDerivWithinAt_const t _ 0).congr_of_eventuallyEq ?_ h₀⟩
    filter_upwards [Ioo_mem_nhdsGT h] with s hs
    exact min_eq_right (momentP_nonneg_early ⟨ht.1.le.trans hs.1.le, hs.2.le⟩)
  · have h₀ := min_eq_left (momentP_nonpos_after_beta ⟨not_lt.1 h, ht.2.le⟩)
    refine ⟨h₀, (((hasDerivWithinAt_referenceFD_right t).sub
      (hasDerivAt_referenceG t).hasDerivWithinAt).add_const 1).congr_of_eventuallyEq ?_ h₀⟩
    filter_upwards [Ioo_mem_nhdsGT ht.2] with s hs
    exact min_eq_left (momentP_nonpos_after_beta ⟨(not_lt.1 h).trans hs.1.le, hs.2.le⟩)

/-- Likewise the clipped second momentum `max Q 0` is `Q` before `lateSwitch` and `0` after it. -/
theorem max_momentQ {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    max (momentQ t) 0 = (if t < lateSwitch then momentQ t else 0) ∧
      HasDerivWithinAt (fun s => max (momentQ s) 0)
        (if t < lateSwitch then referenceGSecond t + referenceFD t else 0) (Ioi t) t := by
  split_ifs with h
  · have h₀ := max_eq_left (momentQ_nonneg_before_lateSwitch ⟨ht.1.le, h.le⟩)
    refine ⟨h₀, (((hasDerivWithinAt_referenceGD_right t).add
      (hasDerivAt_referenceF t).hasDerivWithinAt).sub_const 1).congr_of_eventuallyEq ?_ h₀⟩
    filter_upwards [Ioo_mem_nhdsGT h] with s hs
    exact max_eq_left (momentQ_nonneg_before_lateSwitch ⟨ht.1.le.trans hs.1.le, hs.2.le⟩)
  · have h₀ := max_eq_right (momentQ_nonpos_late ⟨not_lt.1 h, ht.2.le⟩)
    refine ⟨h₀, (hasDerivWithinAt_const t _ 0).congr_of_eventuallyEq ?_ h₀⟩
    filter_upwards [Ioo_mem_nhdsGT ht.2] with s hs
    exact max_eq_right (momentQ_nonpos_late ⟨(not_lt.1 h).trans hs.1.le, hs.2.le⟩)

/-- The first Euler equation; on each phase it is an identity between the explicit formulas. -/
theorem referencePair_eulerF {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivWithinAt referencePair.fluxF (referencePair.forceF t) (Ioi t) t := by
  refine (((hasDerivWithinAt_referenceFD_right t).neg.sub
    (((hasDerivAt_referenceG t).hasDerivWithinAt.sub_const 1).div_const 2)).sub
    (min_momentP ht).2).congr_deriv ?_
  rw [QuarterPair.forceF, show max (referencePair.q t) 0 = _ from (max_momentQ ht).1]
  simp only [momentQ, referencePair, referenceF_eq_right_phases, referenceFSecond,
    referenceGD, phases_eq_right gD_matching_first gD_matching_last]
  split_ifs <;> first
    | (exfalso; linarith [beta_lt_lateSwitch])
    | (simp only [fEarly, fMiddle, fLate, gEarlyD, gMiddleD, gLateD]; ring)

/-- The second Euler equation, in the same way. -/
theorem referencePair_eulerG {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivWithinAt referencePair.fluxG (referencePair.forceG t) (Ioi t) t := by
  refine (((hasDerivWithinAt_referenceGD_right t).neg.add
    (((hasDerivAt_referenceF t).hasDerivWithinAt.sub_const 1).div_const 2)).sub
    (max_momentQ ht).2).congr_deriv ?_
  rw [QuarterPair.forceG, show min (referencePair.p t) 0 = _ from (min_momentP ht).1]
  simp only [momentP, referencePair, referenceG_eq_right_phases, referenceGSecond,
    referenceFD, phases_eq_right fD_matching_first fD_matching_last]
  split_ifs <;> first
    | (exfalso; linarith [beta_lt_lateSwitch])
    | (simp only [gEarly, gMiddle, gLate, fEarlyD, fMiddleD, fLateD]; ring)

end AmbidextrousSofa.Reference
