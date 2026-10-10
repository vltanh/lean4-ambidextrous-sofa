module

public import AmbidextrousSofa.Analysis.AdaptiveGlobalFamily

@[expose] public section

/-!
# Contact signs and Euler equations for the stationary family

The momenta are computed from the actual support derivatives. Their sign
regions are proved, and their adjusted values match with a continuous first
derivative at the two contacts. Thus stationarity is a conclusion.
-/

noncomputable section

open Set
open scoped Topology

namespace AmbidextrousSofa.Analysis

def familyPEarly (b t : ℝ) : ℝ :=
  1 / 2 + (familyEndpoint b - 1 / 2) * Real.cos t - 3 / 2 * familyWidth b * Real.sin t

def familyQEarly (b t : ℝ) : ℝ :=
  -2 + 3 * familyWidth b * Real.cos t + 2 * (familyEndpoint b - 1 / 2) * Real.sin t

def familyPMiddle (b t : ℝ) : ℝ := 2 - 3 * familyRadius b * Real.sin (tailPhase t)

def familyQMiddle (b t : ℝ) : ℝ := -2 + 3 * familyRadius b * Real.cos (tailPhase t)

def familyPLate (b t : ℝ) : ℝ :=
  2 - 3 * familyWidth b * Real.sin t - 2 * (familyEndpoint b - 1 / 2) * Real.cos t

def familyQLate (b t : ℝ) : ℝ :=
  -1 / 2 + 3 / 2 * familyWidth b * Real.cos t - (familyEndpoint b - 1 / 2) * Real.sin t

def familyPEarlyD (b t : ℝ) : ℝ :=
  -(familyEndpoint b - 1 / 2) * Real.sin t - 3 / 2 * familyWidth b * Real.cos t

def familyQEarlyD (b t : ℝ) : ℝ :=
  -3 * familyWidth b * Real.sin t + 2 * (familyEndpoint b - 1 / 2) * Real.cos t

def familyPMiddleD (b t : ℝ) : ℝ := -(3 / 2) * familyRadius b * Real.cos (tailPhase t)

def familyQMiddleD (b t : ℝ) : ℝ := -(3 / 2) * familyRadius b * Real.sin (tailPhase t)

def familyPLateD (b t : ℝ) : ℝ :=
  -3 * familyWidth b * Real.cos t + 2 * (familyEndpoint b - 1 / 2) * Real.sin t

def familyQLateD (b t : ℝ) : ℝ :=
  -(3 / 2) * familyWidth b * Real.sin t - (familyEndpoint b - 1 / 2) * Real.cos t

def familyP (b : ℝ) : ℝ → ℝ := joinThree b (familyLateSwitch b)
  (familyPEarly b) (familyPMiddle b) (familyPLate b)

def familyQ (b : ℝ) : ℝ → ℝ := joinThree b (familyLateSwitch b)
  (familyQEarly b) (familyQMiddle b) (familyQLate b)

def familyPD (b : ℝ) : ℝ → ℝ := joinThree b (familyLateSwitch b)
  (familyPEarlyD b) (familyPMiddleD b) (familyPLateD b)

def familyQD (b : ℝ) : ℝ → ℝ := joinThree b (familyLateSwitch b)
  (familyQEarlyD b) (familyQMiddleD b) (familyQLateD b)

theorem familyPEarly_from_switch (b t : ℝ) :
    familyPEarly b t = 1 / 2 - Real.cos (b - t) / 2 + familyCot b * Real.sin (b - t) := by
  unfold familyPEarly familyWidth familyEndpoint
  rw [Real.cos_sub, Real.sin_sub]
  ring

theorem familyQEarly_from_switch (b t : ℝ) :
    familyQEarly b t = -2 + Real.sin (b - t) + 2 * familyCot b * Real.cos (b - t) := by
  unfold familyQEarly familyWidth familyEndpoint
  rw [Real.cos_sub, Real.sin_sub]
  ring

theorem familyEarly_momentum_signs {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ∈ Icc (0 : ℝ) b) :
    0 ≤ familyPEarly b t ∧ 0 ≤ familyQEarly b t := by
  have hu : b - t ∈ Icc (0 : ℝ) (Real.pi / 4) :=
    ⟨sub_nonneg.mpr ht.2, by linarith [ht.1, hb.2]⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hu.1
    (by linarith [hu.2, Real.pi_pos])
  have hc : 0 ≤ Real.cos (b - t) := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hu.1, Real.pi_pos], by linarith [hu.2, Real.pi_pos]⟩).le
  rw [familyPEarly_from_switch, familyQEarly_from_switch]
  constructor
  · nlinarith [Real.cos_le_one (b - t), mul_nonneg (familyCot_pos hb).le hs]
  · nlinarith [one_le_cos_add_half_sin hu,
      mul_nonneg (sub_nonneg.mpr (one_le_familyCot hb)) hc]

theorem familyMiddle_momentum_signs {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (ht : t ∈ Icc b (familyLateSwitch b)) :
    familyPMiddle b t ≤ 0 ∧ 0 ≤ familyQMiddle b t := by
  have hs : Real.sin (tailPhase b) ≤ Real.sin (tailPhase t) := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · linarith [(family_phase_bounds hb).1, Real.pi_pos]
    · unfold tailPhase tailAngle0 familyLateSwitch at *
      linarith [ht.2, hb.1, Real.pi_pos]
    · unfold tailPhase
      linarith [ht.1]
  have hc : Real.sin (tailPhase b) ≤ Real.cos (tailPhase t) := by
    rw [← Real.sin_pi_div_two_sub]
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · linarith [(family_phase_bounds hb).1, Real.pi_pos]
    · unfold tailPhase tailAngle0
      linarith [ht.1, hb.1, Real.pi_pos]
    · unfold tailPhase tailAngle0 familyLateSwitch at *
      linarith [ht.2]
  have hps := mul_le_mul_of_nonneg_left hs (familyRadius_pos hb).le
  have hqs := mul_le_mul_of_nonneg_left hc (familyRadius_pos hb).le
  unfold familyPMiddle familyQMiddle
  constructor <;> nlinarith [familyRadius_mul_sin hb]

theorem familyPLate_reflection (b t : ℝ) :
    familyPLate b t = -familyQEarly b (Real.pi / 2 - t) := by
  simp only [familyPLate, familyQEarly, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring

theorem familyQLate_reflection (b t : ℝ) :
    familyQLate b t = -familyPEarly b (Real.pi / 2 - t) := by
  simp only [familyQLate, familyPEarly, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring

theorem familyLate_momentum_signs {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (ht : t ∈ Icc (familyLateSwitch b) (Real.pi / 2)) :
    familyPLate b t ≤ 0 ∧ familyQLate b t ≤ 0 := by
  have hu : Real.pi / 2 - t ∈ Icc (0 : ℝ) b := by
    unfold familyLateSwitch at ht
    constructor <;> linarith [ht.1, ht.2]
  rw [familyPLate_reflection, familyQLate_reflection]
  have h := familyEarly_momentum_signs hb hu
  constructor <;> linarith

theorem familyPair_momenta_early {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ≤ b) :
    (familyPair b hb).p t = familyPEarly b t ∧
      (familyPair b hb).q t = familyQEarly b t / 2 := by
  simp only [QuarterPair.p, QuarterPair.q, familyPair, familyF, familyG,
    familyFD, familyGD, joinThree, if_pos ht, familyFEarly, familyGEarly,
    familyFEarlyD, familyGEarlyD, familyPEarly, familyQEarly]
  constructor <;> ring

theorem familyPair_momenta_middle {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ∈ Icc b (familyLateSwitch b)) :
    (familyPair b hb).p t = familyPMiddle b t / 2 ∧
      (familyPair b hb).q t = familyQMiddle b t / 2 := by
  change familyFD b t - familyG b t + 1 = _ ∧ familyGD b t + familyF b t - 1 = _
  rw [familyFD_eq_middle hb ht, familyG_eq_middle hb ht,
    familyGD_eq_middle hb ht, familyF_eq_middle hb ht]
  unfold familyFMiddleD familyGMiddle familyGMiddleD familyFMiddle familyPMiddle familyQMiddle
  constructor <;> ring

theorem familyPair_momenta_late {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : familyLateSwitch b ≤ t) :
    (familyPair b hb).p t = familyPLate b t / 2 ∧
      (familyPair b hb).q t = familyQLate b t := by
  change familyFD b t - familyG b t + 1 = _ ∧ familyGD b t + familyF b t - 1 = _
  rw [familyFD_eq_late hb ht, familyG_eq_late hb ht,
    familyGD_eq_late hb ht, familyF_eq_late hb ht]
  unfold familyFLateD familyGLate familyGLateD familyFLate familyPLate familyQLate
  constructor <;> ring

theorem familyPair_signs_early {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ∈ Icc (0 : ℝ) b) :
    0 ≤ (familyPair b hb).p t ∧ 0 ≤ (familyPair b hb).q t := by
  rw [(familyPair_momenta_early hb ht.2).1, (familyPair_momenta_early hb ht.2).2]
  have h := familyEarly_momentum_signs hb ht
  constructor <;> linarith

theorem familyPair_signs_middle {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ∈ Icc b (familyLateSwitch b)) :
    (familyPair b hb).p t ≤ 0 ∧ 0 ≤ (familyPair b hb).q t := by
  rw [(familyPair_momenta_middle hb ht).1, (familyPair_momenta_middle hb ht).2]
  have h := familyMiddle_momentum_signs hb ht
  constructor <;> linarith

theorem familyPair_signs_late {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (ht : t ∈ Icc (familyLateSwitch b) (Real.pi / 2)) :
    (familyPair b hb).p t ≤ 0 ∧ (familyPair b hb).q t ≤ 0 := by
  rw [(familyPair_momenta_late hb ht.1).1, (familyPair_momenta_late hb ht.1).2]
  have h := familyLate_momentum_signs hb ht
  constructor <;> linarith

theorem familyP_matching_first {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyPEarly b b = familyPMiddle b b := by
  have h := family_width_endpoint_rotation b
  unfold familyPEarly familyPMiddle
  nlinarith [familyRadius_mul_sin hb]

theorem familyQ_matching_first {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyQEarly b b = familyQMiddle b b := by
  have h := family_width_endpoint_rotation b
  unfold familyQEarly familyQMiddle
  nlinarith [familyRadius_mul_cos hb]

theorem familyPD_matching_first {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyPEarlyD b b = familyPMiddleD b b := by
  have h := family_width_endpoint_rotation b
  unfold familyPEarlyD familyPMiddleD
  nlinarith [familyRadius_mul_cos hb]

theorem familyQD_matching_first {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyQEarlyD b b = familyQMiddleD b b := by
  have h := family_width_endpoint_rotation b
  unfold familyQEarlyD familyQMiddleD
  nlinarith [familyRadius_mul_sin hb]

theorem familyP_matching_last {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyPMiddle b (familyLateSwitch b) = familyPLate b (familyLateSwitch b) := by
  have h := family_width_endpoint_rotation b
  simp only [familyPMiddle, familyPLate, familyLateSwitch, tailPhase_reflection,
    Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  nlinarith [familyRadius_mul_cos hb]

theorem familyQ_matching_last {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyQMiddle b (familyLateSwitch b) = familyQLate b (familyLateSwitch b) := by
  have h := family_width_endpoint_rotation b
  simp only [familyQMiddle, familyQLate, familyLateSwitch, tailPhase_reflection,
    Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  nlinarith [familyRadius_mul_sin hb]

theorem familyPD_matching_last {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyPMiddleD b (familyLateSwitch b) = familyPLateD b (familyLateSwitch b) := by
  have h := family_width_endpoint_rotation b
  simp only [familyPMiddleD, familyPLateD, familyLateSwitch, tailPhase_reflection,
    Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  nlinarith [familyRadius_mul_sin hb]

theorem familyQD_matching_last {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyQMiddleD b (familyLateSwitch b) = familyQLateD b (familyLateSwitch b) := by
  have h := family_width_endpoint_rotation b
  simp only [familyQMiddleD, familyQLateD, familyLateSwitch, tailPhase_reflection,
    Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  nlinarith [familyRadius_mul_cos hb]

theorem hasDerivAt_familyPEarly (b t : ℝ) :
    HasDerivAt (familyPEarly b) (familyPEarlyD b t) t := by
  apply ((((Real.hasDerivAt_cos t).const_mul (familyEndpoint b - 1 / 2)).const_add (1 / 2)).sub
    ((Real.hasDerivAt_sin t).const_mul (3 / 2 * familyWidth b))).congr_deriv
  unfold familyPEarlyD
  ring

theorem hasDerivAt_familyQEarly (b t : ℝ) :
    HasDerivAt (familyQEarly b) (familyQEarlyD b t) t := by
  apply ((((Real.hasDerivAt_cos t).const_mul (3 * familyWidth b)).const_add (-2)).add
    ((Real.hasDerivAt_sin t).const_mul (2 * (familyEndpoint b - 1 / 2)))).congr_deriv
  unfold familyQEarlyD
  ring

theorem hasDerivAt_familyPMiddle (b t : ℝ) :
    HasDerivAt (familyPMiddle b) (familyPMiddleD b t) t := by
  apply ((((hasDerivAt_tailPhase t).sin).const_mul (3 * familyRadius b)).const_sub 2).congr_deriv
  unfold familyPMiddleD
  ring

theorem hasDerivAt_familyQMiddle (b t : ℝ) :
    HasDerivAt (familyQMiddle b) (familyQMiddleD b t) t := by
  apply ((((hasDerivAt_tailPhase t).cos).const_mul (3 * familyRadius b)).const_add (-2)).congr_deriv
  unfold familyQMiddleD
  ring

theorem hasDerivAt_familyPLate (b t : ℝ) :
    HasDerivAt (familyPLate b) (familyPLateD b t) t := by
  apply ((((Real.hasDerivAt_sin t).const_mul (3 * familyWidth b)).const_sub 2).sub
    ((Real.hasDerivAt_cos t).const_mul (2 * (familyEndpoint b - 1 / 2)))).congr_deriv
  unfold familyPLateD
  ring

theorem hasDerivAt_familyQLate (b t : ℝ) :
    HasDerivAt (familyQLate b) (familyQLateD b t) t := by
  apply ((((Real.hasDerivAt_cos t).const_mul (3 / 2 * familyWidth b)).const_add (-1 / 2)).sub
    ((Real.hasDerivAt_sin t).const_mul (familyEndpoint b - 1 / 2))).congr_deriv
  unfold familyQLateD
  ring

theorem hasDerivAt_familyP {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (t : ℝ) :
    HasDerivAt (familyP b) (familyPD b t) t :=
  hasDerivAt_joinThree (family_switch_order hb)
    (hasDerivAt_familyPEarly b) (hasDerivAt_familyPMiddle b) (hasDerivAt_familyPLate b)
    (familyP_matching_first hb) (familyP_matching_last hb)
    (familyPD_matching_first hb) (familyPD_matching_last hb) t

theorem hasDerivAt_familyQ {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (t : ℝ) :
    HasDerivAt (familyQ b) (familyQD b t) t :=
  hasDerivAt_joinThree (family_switch_order hb)
    (hasDerivAt_familyQEarly b) (hasDerivAt_familyQMiddle b) (hasDerivAt_familyQLate b)
    (familyQ_matching_first hb) (familyQ_matching_last hb)
    (familyQD_matching_first hb) (familyQD_matching_last hb) t

theorem familyP_eq_adjusted {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    familyP b t = (familyPair b hb).p t + min ((familyPair b hb).p t) 0 := by
  by_cases he : t ≤ b
  · rw [min_eq_right (familyPair_signs_early hb ⟨ht.1, he⟩).1,
      (familyPair_momenta_early hb he).1]
    simp only [familyP, joinThree, if_pos he, add_zero]
  · by_cases hm : t ≤ familyLateSwitch b
    · have hi : t ∈ Icc b (familyLateSwitch b) := ⟨(lt_of_not_ge he).le, hm⟩
      rw [min_eq_left (familyPair_signs_middle hb hi).1,
        (familyPair_momenta_middle hb hi).1]
      simp only [familyP, joinThree, if_neg he, if_pos hm]
      ring
    · have hi : t ∈ Icc (familyLateSwitch b) (Real.pi / 2) := ⟨(lt_of_not_ge hm).le, ht.2⟩
      rw [min_eq_left (familyPair_signs_late hb hi).1,
        (familyPair_momenta_late hb hi.1).1]
      simp only [familyP, joinThree, if_neg he, if_neg hm]
      ring

theorem familyQ_eq_adjusted {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    familyQ b t = (familyPair b hb).q t + max ((familyPair b hb).q t) 0 := by
  by_cases he : t ≤ b
  · rw [max_eq_left (familyPair_signs_early hb ⟨ht.1, he⟩).2,
      (familyPair_momenta_early hb he).2]
    simp only [familyQ, joinThree, if_pos he]
    ring
  · by_cases hm : t ≤ familyLateSwitch b
    · have hi : t ∈ Icc b (familyLateSwitch b) := ⟨(lt_of_not_ge he).le, hm⟩
      rw [max_eq_left (familyPair_signs_middle hb hi).2,
        (familyPair_momenta_middle hb hi).2]
      simp only [familyQ, joinThree, if_neg he, if_pos hm]
      ring
    · have hi : t ∈ Icc (familyLateSwitch b) (Real.pi / 2) := ⟨(lt_of_not_ge hm).le, ht.2⟩
      rw [max_eq_right (familyPair_signs_late hb hi).2,
        (familyPair_momenta_late hb hi.1).2]
      simp only [familyQ, joinThree, if_neg he, if_neg hm, add_zero]

theorem familyPD_eq {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    familyPD b t = -1 - 2 * (familyPair b hb).q t + max ((familyPair b hb).q t) 0 := by
  by_cases he : t ≤ b
  · rw [max_eq_left (familyPair_signs_early hb ⟨ht.1, he⟩).2,
      (familyPair_momenta_early hb he).2]
    simp only [familyPD, joinThree, if_pos he, familyPEarlyD, familyQEarly]
    ring
  · by_cases hm : t ≤ familyLateSwitch b
    · have hi : t ∈ Icc b (familyLateSwitch b) := ⟨(lt_of_not_ge he).le, hm⟩
      rw [max_eq_left (familyPair_signs_middle hb hi).2,
        (familyPair_momenta_middle hb hi).2]
      simp only [familyPD, joinThree, if_neg he, if_pos hm, familyPMiddleD, familyQMiddle]
      ring
    · have hi : t ∈ Icc (familyLateSwitch b) (Real.pi / 2) := ⟨(lt_of_not_ge hm).le, ht.2⟩
      rw [max_eq_right (familyPair_signs_late hb hi).2,
        (familyPair_momenta_late hb hi.1).2]
      simp only [familyPD, joinThree, if_neg he, if_neg hm, familyPLateD, familyQLate]
      ring

theorem familyQD_eq {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    familyQD b t = -1 + 2 * (familyPair b hb).p t - min ((familyPair b hb).p t) 0 := by
  by_cases he : t ≤ b
  · rw [min_eq_right (familyPair_signs_early hb ⟨ht.1, he⟩).1,
      (familyPair_momenta_early hb he).1]
    simp only [familyQD, joinThree, if_pos he, familyQEarlyD, familyPEarly]
    ring
  · by_cases hm : t ≤ familyLateSwitch b
    · have hi : t ∈ Icc b (familyLateSwitch b) := ⟨(lt_of_not_ge he).le, hm⟩
      rw [min_eq_left (familyPair_signs_middle hb hi).1,
        (familyPair_momenta_middle hb hi).1]
      simp only [familyQD, joinThree, if_neg he, if_pos hm, familyQMiddleD, familyPMiddle]
      ring
    · have hi : t ∈ Icc (familyLateSwitch b) (Real.pi / 2) := ⟨(lt_of_not_ge hm).le, ht.2⟩
      rw [min_eq_left (familyPair_signs_late hb hi).1,
        (familyPair_momenta_late hb hi.1).1]
      simp only [familyQD, joinThree, if_neg he, if_neg hm, familyQLateD, familyPLate]
      ring

theorem familyPair_fluxF_eq {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (familyPair b hb).fluxF t = -familyP b t - 3 / 2 * (familyG b t - 1) := by
  rw [familyP_eq_adjusted hb ht]
  unfold QuarterPair.fluxF QuarterPair.p familyPair
  ring

theorem familyPair_fluxG_eq {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (familyPair b hb).fluxG t = -familyQ b t + 3 / 2 * (familyF b t - 1) := by
  rw [familyQ_eq_adjusted hb ht]
  unfold QuarterPair.fluxG QuarterPair.q familyPair
  ring

theorem familyPair_eulerF {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivWithinAt (familyPair b hb).fluxF ((familyPair b hb).forceF t) (Ioi t) t := by
  have h := (hasDerivAt_familyP hb t).neg.sub
    (((hasDerivAt_familyG hb t).sub_const 1).const_mul (3 / 2))
  have hd : -familyPD b t - 3 / 2 * familyGD b t = (familyPair b hb).forceF t := by
    rw [familyPD_eq hb ⟨ht.1.le, ht.2.le⟩]
    unfold QuarterPair.forceF QuarterPair.q familyPair
    ring
  apply (h.congr_deriv hd).hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [(Ioo_mem_nhds ht.1 ht.2).filter_mono nhdsWithin_le_nhds] with s hs
    exact familyPair_fluxF_eq hb ⟨hs.1.le, hs.2.le⟩
  · exact familyPair_fluxF_eq hb ⟨ht.1.le, ht.2.le⟩

theorem familyPair_eulerG {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivWithinAt (familyPair b hb).fluxG ((familyPair b hb).forceG t) (Ioi t) t := by
  have h := (hasDerivAt_familyQ hb t).neg.add
    (((hasDerivAt_familyF hb t).sub_const 1).const_mul (3 / 2))
  have hd : -familyQD b t + 3 / 2 * familyFD b t = (familyPair b hb).forceG t := by
    rw [familyQD_eq hb ⟨ht.1.le, ht.2.le⟩]
    unfold QuarterPair.forceG QuarterPair.p familyPair
    ring
  apply (h.congr_deriv hd).hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [(Ioo_mem_nhds ht.1 ht.2).filter_mono nhdsWithin_le_nhds] with s hs
    exact familyPair_fluxG_eq hb ⟨hs.1.le, hs.2.le⟩
  · exact familyPair_fluxG_eq hb ⟨ht.1.le, ht.2.le⟩

theorem familyPair_stationary {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    (familyPair b hb).Stationary :=
  (familyPair b hb).stationary_of_euler
    (fun _ ht => familyPair_eulerF hb ht) (fun _ ht => familyPair_eulerG hb ht)

theorem adaptiveFunctional_le_family_of_widthTraces {u : QuarterPair} {b : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (hu : u.WidthTraces (familyWidth b)) :
    adaptiveFunctional u ≤ adaptiveFunctional (familyPair b hb) :=
  adaptiveFunctional_le_of_stationary (familyPair_stationary hb)
    (QuarterPair.sameTraces_of_widthTraces hu (familyPair_widthTraces hb))

end AmbidextrousSofa.Analysis
