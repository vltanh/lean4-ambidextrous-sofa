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

theorem familyEarly_momentum_signs {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ∈ Icc (0 : ℝ) b) :
    0 ≤ familyPEarly b t ∧ 0 ≤ familyQEarly b t := by
  have hu : b - t ∈ Icc (0 : ℝ) (Real.pi / 4) :=
    ⟨sub_nonneg.mpr ht.2, by linarith [ht.1, hb.2]⟩
  have h1 := mul_nonneg (familyCot_pos hb).le
    (Real.sin_nonneg_of_nonneg_of_le_pi hu.1 (by linarith [hu.2, Real.pi_pos]))
  have h2 := mul_nonneg (sub_nonneg.mpr (one_le_familyCot hb))
    (Real.cos_nonneg_of_mem_Icc (x := b - t) ⟨by linarith [hu.1, Real.pi_pos],
      by linarith [hu.2, Real.pi_pos]⟩)
  have h3 := one_le_cos_add_half_sin hu
  have h4 := Real.cos_le_one (b - t)
  simp only [Real.sin_sub, Real.cos_sub] at h1 h2 h3 h4
  unfold familyPEarly familyQEarly familyWidth familyEndpoint
  constructor <;> linarith

theorem familyMiddle_momentum_signs {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (ht : t ∈ Icc b (familyLateSwitch b)) :
    familyPMiddle b t ≤ 0 ∧ 0 ≤ familyQMiddle b t := by
  obtain ⟨h1, h2⟩ := ht
  unfold familyLateSwitch at h2
  have h : Real.sin (tailPhase b) ≤ Real.sin (tailPhase t) ∧
      Real.sin (tailPhase b) ≤ Real.cos (tailPhase t) := by
    rw [← Real.sin_pi_div_two_sub (tailPhase t)]
    constructor <;> apply Real.sin_le_sin_of_le_of_le_pi_div_two <;>
      simp only [tailPhase, tailAngle0] <;> linarith [hb.1, Real.pi_pos]
  have hR := (familyRadius_pos hb).le
  unfold familyPMiddle familyQMiddle
  constructor <;> linarith [familyRadius_mul_sin hb, mul_le_mul_of_nonneg_left h.1 hR,
    mul_le_mul_of_nonneg_left h.2 hR]

theorem familyLate_momentum_signs {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (ht : t ∈ Icc (familyLateSwitch b) (Real.pi / 2)) :
    familyPLate b t ≤ 0 ∧ familyQLate b t ≤ 0 := by
  unfold familyLateSwitch at ht
  have h := familyEarly_momentum_signs hb (t := Real.pi / 2 - t)
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  simp only [familyPEarly, familyQEarly, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub] at h
  unfold familyPLate familyQLate
  constructor <;> linarith

theorem familyPair_momenta_early {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ≤ b) :
    (familyPair b hb).p t = familyPEarly b t ∧
      (familyPair b hb).q t = familyQEarly b t / 2 := by
  simp only [QuarterPair.p, QuarterPair.q, familyPair, familyF, familyG, familyFD, familyGD,
    joinThree, ht, ↓reduceIte, familyFEarly, familyGEarly, familyFEarlyD, familyGEarlyD,
    familyPEarly, familyQEarly]
  constructor <;> ring

theorem familyPair_momenta_middle {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ∈ Icc b (familyLateSwitch b)) :
    (familyPair b hb).p t = familyPMiddle b t / 2 ∧
      (familyPair b hb).q t = familyQMiddle b t / 2 := by
  simp only [QuarterPair.p, QuarterPair.q, familyPair, familyFD_eq_middle hb ht,
    familyG_eq_middle hb ht, familyGD_eq_middle hb ht, familyF_eq_middle hb ht, familyFMiddleD,
    familyGMiddle, familyGMiddleD, familyFMiddle, familyPMiddle, familyQMiddle]
  constructor <;> ring

theorem familyPair_momenta_late {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : familyLateSwitch b ≤ t) :
    (familyPair b hb).p t = familyPLate b t / 2 ∧
      (familyPair b hb).q t = familyQLate b t := by
  simp only [QuarterPair.p, QuarterPair.q, familyPair, familyFD_eq_late hb ht,
    familyG_eq_late hb ht, familyGD_eq_late hb ht, familyF_eq_late hb ht, familyFLateD,
    familyGLate, familyGLateD, familyFLate, familyPLate, familyQLate]
  constructor <;> ring

theorem familyPair_signs_early {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ∈ Icc (0 : ℝ) b) :
    0 ≤ (familyPair b hb).p t ∧ 0 ≤ (familyPair b hb).q t := by
  simp only [familyPair_momenta_early hb ht.2]
  constructor <;> linarith [familyEarly_momentum_signs hb ht]

theorem familyPair_signs_middle {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ∈ Icc b (familyLateSwitch b)) :
    (familyPair b hb).p t ≤ 0 ∧ 0 ≤ (familyPair b hb).q t := by
  simp only [familyPair_momenta_middle hb ht]
  constructor <;> linarith [familyMiddle_momentum_signs hb ht]

theorem familyPair_signs_late {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (ht : t ∈ Icc (familyLateSwitch b) (Real.pi / 2)) :
    (familyPair b hb).p t ≤ 0 ∧ (familyPair b hb).q t ≤ 0 := by
  simp only [familyPair_momenta_late hb ht.1]
  constructor <;> linarith [familyLate_momentum_signs hb ht]

theorem familyP_matching_first {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyPEarly b b = familyPMiddle b b := by
  unfold familyPEarly familyPMiddle
  linear_combination 3 * familyRadius_mul_sin hb - (family_width_endpoint_rotation b).1

theorem familyQ_matching_first {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyQEarly b b = familyQMiddle b b := by
  unfold familyQEarly familyQMiddle
  linear_combination 2 * (family_width_endpoint_rotation b).2 - 3 * familyRadius_mul_cos hb

theorem familyPD_matching_first {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyPEarlyD b b = familyPMiddleD b b := by
  unfold familyPEarlyD familyPMiddleD
  linear_combination 3 / 2 * familyRadius_mul_cos hb - (family_width_endpoint_rotation b).2

theorem familyQD_matching_first {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyQEarlyD b b = familyQMiddleD b b := by
  unfold familyQEarlyD familyQMiddleD
  linear_combination 3 / 2 * familyRadius_mul_sin hb - 2 * (family_width_endpoint_rotation b).1

theorem familyP_matching_last {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyPMiddle b (familyLateSwitch b) = familyPLate b (familyLateSwitch b) := by
  simp only [familyPMiddle, familyPLate, familyLateSwitch, tailPhase_reflection,
    Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  linear_combination 2 * (family_width_endpoint_rotation b).2 - 3 * familyRadius_mul_cos hb

theorem familyQ_matching_last {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyQMiddle b (familyLateSwitch b) = familyQLate b (familyLateSwitch b) := by
  simp only [familyQMiddle, familyQLate, familyLateSwitch, tailPhase_reflection,
    Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  linear_combination 3 * familyRadius_mul_sin hb - (family_width_endpoint_rotation b).1

theorem familyPD_matching_last {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyPMiddleD b (familyLateSwitch b) = familyPLateD b (familyLateSwitch b) := by
  simp only [familyPMiddleD, familyPLateD, familyLateSwitch, tailPhase_reflection,
    Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  linear_combination 2 * (family_width_endpoint_rotation b).1 - 3 / 2 * familyRadius_mul_sin hb

theorem familyQD_matching_last {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    familyQMiddleD b (familyLateSwitch b) = familyQLateD b (familyLateSwitch b) := by
  simp only [familyQMiddleD, familyQLateD, familyLateSwitch, tailPhase_reflection,
    Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  linear_combination (family_width_endpoint_rotation b).2 - 3 / 2 * familyRadius_mul_cos hb

theorem hasDerivAt_familyP {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (t : ℝ) :
    HasDerivAt (familyP b) (familyPD b t) t :=
  hasDerivAt_joinThree (family_switch_order hb)
    (fun t => ((((Real.hasDerivAt_cos t).const_mul _).const_add _).sub
      ((Real.hasDerivAt_sin t).const_mul _)).congr_deriv (by unfold familyPEarlyD; ring))
    (fun t => (((hasDerivAt_tailPhase t).sin.const_mul _).const_sub _).congr_deriv
      (by unfold familyPMiddleD; ring))
    (fun t => ((((Real.hasDerivAt_sin t).const_mul _).const_sub _).sub
      ((Real.hasDerivAt_cos t).const_mul _)).congr_deriv (by unfold familyPLateD; ring))
    (familyP_matching_first hb) (familyP_matching_last hb)
    (familyPD_matching_first hb) (familyPD_matching_last hb) t

theorem hasDerivAt_familyQ {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (t : ℝ) :
    HasDerivAt (familyQ b) (familyQD b t) t :=
  hasDerivAt_joinThree (family_switch_order hb)
    (fun t => ((((Real.hasDerivAt_cos t).const_mul _).const_add _).add
      ((Real.hasDerivAt_sin t).const_mul _)).congr_deriv (by unfold familyQEarlyD; ring))
    (fun t => (((hasDerivAt_tailPhase t).cos.const_mul _).const_add _).congr_deriv
      (by unfold familyQMiddleD; ring))
    (fun t => ((((Real.hasDerivAt_cos t).const_mul _).const_add _).sub
      ((Real.hasDerivAt_sin t).const_mul _)).congr_deriv (by unfold familyQLateD; ring))
    (familyQ_matching_first hb) (familyQ_matching_last hb)
    (familyQD_matching_first hb) (familyQD_matching_last hb) t

/-- The adjusted momenta and their derivatives in terms of the actual momenta. -/
theorem familyPair_adjusted {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    familyP b t = (familyPair b hb).p t + min ((familyPair b hb).p t) 0 ∧
      familyQ b t = (familyPair b hb).q t + max ((familyPair b hb).q t) 0 ∧
      familyPD b t = -1 - 2 * (familyPair b hb).q t + max ((familyPair b hb).q t) 0 ∧
      familyQD b t = -1 + 2 * (familyPair b hb).p t - min ((familyPair b hb).p t) 0 := by
  rcases le_or_gt t b with he | he
  · obtain ⟨hp, hq⟩ := familyPair_signs_early hb ⟨ht.1, he⟩
    rw [min_eq_right hp, max_eq_left hq]
    simp only [familyPair_momenta_early hb he, familyP, familyQ, familyPD, familyQD, joinThree, he,
      ↓reduceIte, familyPEarly, familyQEarly, familyPEarlyD, familyQEarlyD]
    exact ⟨by ring, by ring, by ring, by ring⟩
  rcases le_or_gt t (familyLateSwitch b) with hm | hm
  · have hi : t ∈ Icc b (familyLateSwitch b) := ⟨he.le, hm⟩
    obtain ⟨hp, hq⟩ := familyPair_signs_middle hb hi
    rw [min_eq_left hp, max_eq_left hq]
    simp only [familyPair_momenta_middle hb hi, familyP, familyQ, familyPD, familyQD, joinThree,
      not_le.2 he, hm, ↓reduceIte, familyPMiddle, familyQMiddle, familyPMiddleD, familyQMiddleD]
    exact ⟨by ring, by ring, by ring, by ring⟩
  · obtain ⟨hp, hq⟩ := familyPair_signs_late hb ⟨hm.le, ht.2⟩
    rw [min_eq_left hp, max_eq_right hq]
    simp only [familyPair_momenta_late hb hm.le, familyP, familyQ, familyPD, familyQD, joinThree,
      not_le.2 he, not_le.2 hm, ↓reduceIte, familyPLate, familyQLate, familyPLateD, familyQLateD]
    exact ⟨by ring, by ring, by ring, by ring⟩

theorem familyPair_fluxF_eq {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (familyPair b hb).fluxF t = -familyP b t - 3 / 2 * (familyG b t - 1) := by
  rw [(familyPair_adjusted hb ht).1]
  unfold QuarterPair.fluxF QuarterPair.p familyPair; ring

theorem familyPair_fluxG_eq {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (familyPair b hb).fluxG t = -familyQ b t + 3 / 2 * (familyF b t - 1) := by
  rw [(familyPair_adjusted hb ht).2.1]
  unfold QuarterPair.fluxG QuarterPair.q familyPair; ring

theorem familyPair_eulerF {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivWithinAt (familyPair b hb).fluxF ((familyPair b hb).forceF t) (Ioi t) t := by
  have h := (hasDerivAt_familyP hb t).neg.sub
    (((hasDerivAt_familyG hb t).sub_const 1).const_mul (3 / 2))
  refine ((h.congr_of_eventuallyEq <| Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2)
    fun s hs => familyPair_fluxF_eq hb (Ioo_subset_Icc_self hs)).congr_deriv ?_).hasDerivWithinAt
  rw [(familyPair_adjusted hb (Ioo_subset_Icc_self ht)).2.2.1]
  unfold QuarterPair.forceF QuarterPair.q familyPair; ring

theorem familyPair_eulerG {b t : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivWithinAt (familyPair b hb).fluxG ((familyPair b hb).forceG t) (Ioi t) t := by
  have h := (hasDerivAt_familyQ hb t).neg.add
    (((hasDerivAt_familyF hb t).sub_const 1).const_mul (3 / 2))
  refine ((h.congr_of_eventuallyEq <| Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2)
    fun s hs => familyPair_fluxG_eq hb (Ioo_subset_Icc_self hs)).congr_deriv ?_).hasDerivWithinAt
  rw [(familyPair_adjusted hb (Ioo_subset_Icc_self ht)).2.2.2]
  unfold QuarterPair.forceG QuarterPair.p familyPair; ring

theorem familyPair_stationary {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    (familyPair b hb).Stationary :=
  (familyPair b hb).stationary_of_euler (fun _ => familyPair_eulerF hb)
    (fun _ => familyPair_eulerG hb)

theorem adaptiveFunctional_le_family_of_widthTraces {u : QuarterPair} {b : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (hu : u.WidthTraces (familyWidth b)) :
    adaptiveFunctional u ≤ adaptiveFunctional (familyPair b hb) :=
  adaptiveFunctional_le_of_stationary (familyPair_stationary hb)
    (QuarterPair.sameTraces_of_widthTraces hu (familyPair_widthTraces hb))

end AmbidextrousSofa.Analysis
