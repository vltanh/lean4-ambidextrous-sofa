module

public import AmbidextrousSofa.Analysis.AdaptiveGlobalFamily

@[expose] public section

/-!
# Contact signs and Euler equations for the stationary family

The momenta are computed from the actual support derivatives, and their
sign regions are proved. On each phase the first flux is then an explicit
trigonometric polynomial whose derivative is the force, and the value
density is explicit. The phases agree at the two contacts, so the first
flux is differentiable, and stationarity is a conclusion.
-/

noncomputable section

open Set

namespace AmbidextrousSofa.Analysis

/-- The two momenta of the early phase are nonnegative. -/
theorem familyEarly_signs {b t : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (ht : t ∈ Icc (0 : ℝ) b) :
    0 ≤ 1 / 2 + (familyEndpoint b - 1 / 2) * Real.cos t - 3 / 2 * familyWidth b * Real.sin t ∧
      0 ≤ -1 + 3 / 2 * familyWidth b * Real.cos t + (familyEndpoint b - 1 / 2) * Real.sin t := by
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
  unfold familyWidth familyEndpoint
  constructor <;> linarith

def familyFluxEarly (b t : ℝ) : ℝ :=
  3 / 4 * familyWidth b * Real.sin t - (familyEndpoint b + 1 / 4) * Real.cos t + 1 / 4

def familyForceEarly (b t : ℝ) : ℝ :=
  3 / 4 * familyWidth b * Real.cos t + (familyEndpoint b + 1 / 4) * Real.sin t

def familyFluxLate (b t : ℝ) : ℝ :=
  3 / 2 * familyWidth b * Real.sin t + (familyEndpoint b / 2 - 1) * Real.cos t - 1 / 2

def familyForceLate (b t : ℝ) : ℝ :=
  3 / 2 * familyWidth b * Real.cos t - (familyEndpoint b / 2 - 1) * Real.sin t

/-- Before the first switch neither contact is active. -/
theorem familyPair_early {b s : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (hs : s ∈ Icc 0 b) :
    (familyPair b hb).fluxF s = familyFluxEarly b s ∧
      (familyPair b hb).forceF s = familyForceEarly b s ∧
      2 * adaptiveDensity (familyPair b hb) s -
          adaptiveLinearDensity (familyPair b hb) (familyPair b hb) s =
        1 / 2 + (familyEndpoint b / 2 + familyWidth b / 4 - 1 / 2) * Real.cos s -
          (familyWidth b + 1 / 4) * Real.sin s := by
  have hF : familyF b s = familyFEarly b s ∧ familyFD b s = familyFEarlyD b s := by
    simp [familyF, familyFD, joinThree, hs.2]
  have hG := familyF_eq_late hb (show familyLateSwitch b ≤ Real.pi / 2 - s by
    unfold familyLateSwitch; linarith [hs.2])
  obtain ⟨hp, hq⟩ := familyEarly_signs hb hs
  have hp' : 0 ≤ (familyPair b hb).p s := by
    simp only [QuarterPair.p, symmetricPair, hF, hG, familyFEarlyD, familyFLate,
      Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    linarith
  have hq' : 0 ≤ (familyPair b hb).q s := by
    simp only [QuarterPair.q, symmetricPair, hF, hG, familyFEarly, familyFLateD,
      Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    linarith
  simp only [QuarterPair.fluxF, QuarterPair.forceF, adaptiveDensity, adaptiveLinearDensity,
    min_eq_right hp', max_eq_left hq']
  simp only [QuarterPair.q, symmetricPair, hF, hG, familyFEarly, familyFEarlyD,
    familyFLate, familyFLateD, familyFluxEarly, familyForceEarly, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub]
  refine ⟨by ring, by ring, by ring⟩

/-- On the fully active phase both contacts are active. -/
theorem familyPair_middle {b s : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (hs : s ∈ Icc b (familyLateSwitch b)) :
    ((familyPair b hb).p s ≤ 0 ∧ 0 ≤ (familyPair b hb).q s) ∧
      (familyPair b hb).fluxF s = activeFlux (familyRadius b) (familySineCoefficient b) s ∧
      (familyPair b hb).forceF s = activeForce (familyRadius b) (familySineCoefficient b) s :=
  symmetricPair_active hb.1 (familyRadius_mul_sin hb).ge (fun _ ht => familyF_eq_middle hb ht) hs

/-- After the second switch the first contact is active and the second reversed. -/
theorem familyPair_late {b s : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (hs : s ∈ Icc (familyLateSwitch b) (Real.pi / 2)) :
    (familyPair b hb).fluxF s = familyFluxLate b s ∧
      (familyPair b hb).forceF s = familyForceLate b s ∧
      2 * adaptiveDensity (familyPair b hb) s -
          adaptiveLinearDensity (familyPair b hb) (familyPair b hb) s =
        1 / 2 + (familyEndpoint b / 2 + familyWidth b / 4 - 1 / 2) * Real.sin s -
          (familyWidth b + 1 / 4) * Real.cos s := by
  have hF := familyF_eq_late hb hs.1
  have hsb : Real.pi / 2 - s ≤ b := by unfold familyLateSwitch at hs; linarith [hs.1]
  have hG : familyF b (Real.pi / 2 - s) = familyFEarly b (Real.pi / 2 - s) ∧
      familyFD b (Real.pi / 2 - s) = familyFEarlyD b (Real.pi / 2 - s) := by
    simp [familyF, familyFD, joinThree, hsb]
  have h := familyEarly_signs hb ⟨by linarith [hs.2], hsb⟩
  simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub] at h
  have hp' : (familyPair b hb).p s ≤ 0 := by
    simp only [QuarterPair.p, symmetricPair, hF, hG, familyFLateD, familyFEarly,
      Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    linarith [h.2]
  have hq' : (familyPair b hb).q s ≤ 0 := by
    simp only [QuarterPair.q, symmetricPair, hF, hG, familyFLate, familyFEarlyD,
      Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    linarith [h.1]
  simp only [QuarterPair.fluxF, QuarterPair.forceF, adaptiveDensity, adaptiveLinearDensity,
    min_eq_left hp', max_eq_right hq']
  simp only [QuarterPair.p, symmetricPair, hF, hG, familyFEarly, familyFEarlyD,
    familyFLate, familyFLateD, familyFluxLate, familyForceLate, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub]
  refine ⟨by ring, by ring, by ring⟩

/-- The first flux is joined from the three phase fluxes, whose derivatives are the force. -/
theorem familyPair_euler {b t : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4))
    (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    HasDerivAt (familyPair b hb).fluxF ((familyPair b hb).forceF t) t := by
  have hbL := family_switch_order hb
  have hL : familyLateSwitch b ≤ Real.pi / 2 := by unfold familyLateSwitch; linarith [hb.1]
  have key (s : ℝ) (hs : s ∈ Icc 0 (Real.pi / 2)) :
      (familyPair b hb).fluxF s = joinThree b (familyLateSwitch b) (familyFluxEarly b)
          (activeFlux (familyRadius b) (familySineCoefficient b)) (familyFluxLate b) s ∧
        (familyPair b hb).forceF s = joinThree b (familyLateSwitch b) (familyForceEarly b)
          (activeForce (familyRadius b) (familySineCoefficient b)) (familyForceLate b) s := by
    unfold joinThree
    split_ifs with h1 h2
    · exact ⟨(familyPair_early hb ⟨hs.1, h1⟩).1, (familyPair_early hb ⟨hs.1, h1⟩).2.1⟩
    · exact (familyPair_middle hb ⟨(not_le.1 h1).le, h2⟩).2
    · exact ⟨(familyPair_late hb ⟨(not_le.1 h2).le, hs.2⟩).1,
        (familyPair_late hb ⟨(not_le.1 h2).le, hs.2⟩).2.1⟩
  have hE := familyPair_early hb ⟨hb.1, le_rfl⟩
  have hM₁ := familyPair_middle hb ⟨le_rfl, hbL⟩
  have hM₂ := familyPair_middle hb ⟨hbL, le_rfl⟩
  have hL₂ := familyPair_late hb ⟨le_rfl, hL⟩
  refine ((hasDerivAt_joinThree (E := familyFluxEarly b) (W := familyFluxLate b) hbL
    (fun s => ((((Real.hasDerivAt_sin s).const_mul _).sub ((Real.hasDerivAt_cos s).const_mul
      _)).add_const _).congr_deriv (by unfold familyForceEarly; ring))
    (hasDerivAt_activeFlux _ _)
    (fun s => ((((Real.hasDerivAt_sin s).const_mul _).add ((Real.hasDerivAt_cos s).const_mul
      _)).sub_const _).congr_deriv (by unfold familyForceLate; ring))
    (hE.1.symm.trans hM₁.2.1) (hM₂.2.1.symm.trans hL₂.1) (hE.2.1.symm.trans hM₁.2.2)
    (hM₂.2.2.symm.trans hL₂.2.1) t).congr_of_eventuallyEq (Filter.eventuallyEq_of_mem
      (Icc_mem_nhds ht.1 ht.2) fun s hs => (key s hs).1)).congr_deriv
    (key t (Ioo_subset_Icc_self ht)).2.symm

theorem familyPair_stationary {b : ℝ} (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    (familyPair b hb).Stationary :=
  symmetricPair_stationary fun _ ht => familyPair_euler hb ht

theorem adaptiveFunctional_le_family_of_widthTraces {u : QuarterPair} {b : ℝ}
    (hb : b ∈ Icc (0 : ℝ) (Real.pi / 4)) (hu : u.WidthTraces (familyWidth b)) :
    adaptiveFunctional u ≤ adaptiveFunctional (familyPair b hb) :=
  adaptiveFunctional_le_of_stationary (familyPair_stationary hb)
    (QuarterPair.sameTraces_of_widthTraces hu (familyPair_widthTraces hb))

end AmbidextrousSofa.Analysis
