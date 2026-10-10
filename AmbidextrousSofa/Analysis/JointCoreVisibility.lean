module

public import AmbidextrousSofa.Analysis.JointCoreProjectionEquality
public import AmbidextrousSofa.Analysis.UniqueWallContact
public import AmbidextrousSofa.Measure.GraphDensitySaturation

@[expose] public section

/-!
# Full corner occupation at uniquely exposed positive contacts

The two corner branches have one common spatial projection. On the
image of uniquely exposed positive core contacts, that projection is
Lebesgue measure. The exact one-dimensional area formula transfers
this equality to the strictly decreasing core parameter. Together
with the signed corner flux balance, it determines both branch
densities and forces their shared occupation to be one.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem StrictCornerSignPhases.mem_core_of_first_neg_second_pos
    {p q : ℝ → ℝ} {L α η t : ℝ} (hphase : StrictCornerSignPhases p q L α η)
    (ht : t ∈ Icc (0 : ℝ) L) (hp : p t < 0) (hq : 0 < q t) : t ∈ Ioo α η := by
  refine ⟨hphase.first_lt_of_first_neg ht hp, ?_⟩
  by_contra hnot
  rcases (le_of_not_gt hnot).eq_or_lt with heq | hlt
  · have hzero : q t = 0 := by rw [← heq, hphase.second_zero]
    linarith only [hq, hzero]
  · have hnegative := (hphase.final_signs t ⟨hlt, ht.2⟩).2
    linarith only [hq, hnegative]

namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)
  (hU : IsFullCapMaximizer target) {C h m c : ℝ}
  (hl : horizontalLeft target = -2 * C) (hr : horizontalRight target = 2 * C)
  (hC : 1 / 2 < C) (hm : 0 < m) (hheight : capHeight target = 1)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
    capRoof target x = m * x + c)
  (hlow : capRoof target (-C) = 1 - h) (hhigh : capRoof target C = 1) (hh : 0 < h)
  {ρ : ℝ → ℝ} {K : ℝ} (hρ : Measurable ρ)
  (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature target).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))
  (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1)
  (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
  (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)

local notation "F" => fullTiltedSupportQuarterPair hU hm.le haffine hρ hρ0 hρK heq
set_option quotPrecheck false in
local notation "Z" => innerCornerPoint (F).f (F).g
set_option quotPrecheck false in
local notation "p" => supportP (F).fD (F).g
set_option quotPrecheck false in
local notation "q" => supportQ (F).gD (F).f
set_option quotPrecheck false in
local notation "X" => (fun t => (Z t).1)
set_option quotPrecheck false in
local notation "Y" => (fun t => (Z t).2)
local notation "XD" => (fun t => p t * Real.cos t - q t * Real.sin t)
local notation "aZ" => J.sourceBranchDensity (firstCornerSource target) 0
local notation "aW" => J.sourceBranchDensity (secondCornerSource target) (Real.pi / 2)
local notation "w" => (fun t => aZ t * Real.sin t + aW t * Real.cos t)

include hl hr hC hheight hlow hhigh hh hunit hTargetBox hleft hright in
theorem ae_corner_densities_eq_momenta_of_unique_contact {α η : ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    ∀ᵐ t ∂volume.restrict (Ioo α η),
      X t ∈ Ioo (-C) C → 0 < Y t →
      sweptNiche target (Real.pi / 2) (X t) = Y t →
      (∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
        fullWallClip hU.isCap.toCompactCap (X t) s =
          sweptNiche target (Real.pi / 2) (X t) → s = t) →
      aZ t = q t ∧ aW t = -p t := by
  let T : Set ℝ := {t | t ∈ Ioo α η ∧ X t ∈ Ioo (-C) C ∧ 0 < Y t ∧
    sweptNiche target (Real.pi / 2) (X t) = Y t ∧
    ∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
      fullWallClip hU.isCap.toCompactCap (X t) s =
        sweptNiche target (Real.pi / 2) (X t) → s = t}
  obtain ⟨hX, hY⟩ := fullTiltedSupportQuarterPair_core_continuous_global
    hU hm.le haffine hρ hρ0 hρK heq
  have hN : Continuous (fun t => sweptNiche target (Real.pi / 2) (X t)) := by
    have h := continuous_capSweptNiche.comp
      ((continuous_const : Continuous (fun _ : ℝ => hU.isCap.toCompactCap)).prodMk hX)
    simpa only [Function.comp_def, IsDownwardCap.toCompactCap_carrier] using h
  have hT : MeasurableSet T :=
    measurableSet_Ioo.inter ((measurableSet_Ioo.preimage hX.measurable).inter
      ((isOpen_lt continuous_const hY).measurableSet.inter
        ((isClosed_eq hN hY).measurableSet.inter
          (hU.isCap.measurableSet_unique_fullWallClip_contact hX))))
  have hTS : T ⊆ Ioo α η := fun _ ht => ht.1
  have hTquarter : T ⊆ Ioo (0 : ℝ) (Real.pi / 2) := fun _ ht =>
    ⟨hphase.first_mem.1.trans ht.1.1, ht.1.2.trans hphase.second_mem.2⟩
  have hinj : InjOn X (Ioo α η) :=
    (fullTiltedSupportQuarterPair_core_strictAntiOn_open
      hU hm.le haffine hρ hρ0 hρK heq hphase).injOn
  have himage : MeasurableSet (X '' T) :=
    hT.image_of_continuousOn_injOn hX.continuousOn (hinj.mono hTS)
  have hD : ∀ t ∈ Ioo α η, HasDerivAt X (XD t) t := by
    intro t ht
    exact (fullTiltedSupportQuarterPair_core_hasDerivAt hU hm.le haffine hρ hρ0 hρK heq
      ⟨hphase.first_mem.1.trans ht.1, ht.2.trans hphase.second_mem.2⟩).1
  have hw : Measurable w :=
    ((J.measurable_sourceBranchDensity _ _).mul Real.measurable_sin).add
      ((J.measurable_sourceBranchDensity _ _).mul Real.measurable_cos)
  have hw0 : ∀ᵐ t ∂volume.restrict T, 0 ≤ w t := by
    filter_upwards [ae_restrict_mem hT] with t ht
    have htq := hTquarter ht
    exact add_nonneg
      (mul_nonneg (J.sourceBranchDensity_nonneg _ _ _)
        (Real.sin_pos_of_pos_of_lt_pi htq.1
          (by linarith only [htq.2, Real.pi_pos])).le)
      (mul_nonneg (J.sourceBranchDensity_nonneg _ _ _)
        (Real.cos_pos_of_mem_Ioo
          ⟨by linarith only [htq.1, Real.pi_pos], htq.2⟩).le)
  have hsaturated :
      (((volume.restrict (Ioo α η)).withDensity (fun t => ENNReal.ofReal (w t))).map X).restrict
          (X '' T) = volume.restrict (X '' T) := by
    rw [← J.coreSourceProjection_eq_density_graph hU hl hr hC hm hheight haffine hlow
      hhigh hh hρ hρ0 hρK heq hunit hTargetBox hleft hright hphase]
    apply J.coreSourceProjection_restrict_unique_positive_image_eq_volume
      hU hl hr hC hm hheight haffine hlow hhigh hh hρ hρ0 hρK heq hunit
      hleft hright himage
    · intro t ht
      exact ⟨ht.2.1, by rw [ht.2.2.2.1]; exact ht.2.2.1⟩
    · exact fun _ ht => ht.2.2.2.2
  have hweight := ae_weight_eq_abs_deriv_of_graph_saturated_on
    measurableSet_Ioo hT hTS hD hinj hw.aemeasurable hw0 hsaturated
  have hbalance := ae_restrict_of_ae_restrict_of_subset hTquarter
    (J.ae_corner_density_balance hU hl hr hC hm hheight haffine hlow hhigh hh
      hρ hρ0 hρK heq hunit hTargetBox hleft hright hphase)
  have hmass : ∀ᵐ t ∂volume.restrict T, aZ t = q t ∧ aW t = -p t := by
    filter_upwards [ae_restrict_mem hT, hweight, hbalance] with t ht hwgt hb
    have htq := hTquarter ht
    have hsign := hphase.core_signs t ht.1
    have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi htq.1
      (by linarith only [htq.2, Real.pi_pos])
    have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
      ⟨by linarith only [htq.1, Real.pi_pos], htq.2⟩
    have hneg : XD t < 0 := sub_neg.mpr
      ((mul_neg_of_neg_of_pos hsign.1 hc).trans (mul_pos hsign.2 hs))
    have hspeed : 0 < q t * Real.sin t - p t * Real.cos t := by
      linarith only [hneg]
    have hfull : w t = q t * Real.sin t - p t * Real.cos t := by
      simpa only [abs_of_nonpos hneg.le, neg_sub] using hwgt
    have hproduct : (aZ t - q t) * (q t * Real.sin t - p t * Real.cos t) = 0 := by
      calc
        _ = q t * (w t - (q t * Real.sin t - p t * Real.cos t)) -
            Real.cos t * (p t * aZ t + q t * aW t) := by ring
        _ = 0 := by rw [hfull, hb]; ring
    have hfirst : aZ t = q t :=
      sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right hspeed.ne')
    have hsecond : q t * (aW t + p t) = 0 := by
      rw [hfirst] at hb
      nlinarith only [hb]
    refine ⟨hfirst, ?_⟩
    have hsum := (mul_eq_zero.mp hsecond).resolve_left hsign.2.ne'
    linarith only [hsum]
  have hglobal := (ae_restrict_iff' hT).mp hmass
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hglobal] with t ht hmasses
  intro hx hy hcontact hunique
  exact hmasses ⟨ht, hx, hy, hcontact, hunique⟩

include hl hr hC hheight hlow hhigh hh hunit hTargetBox hleft hright in
theorem ae_first_corner_density_eq_q_of_unique_contact {α η : ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    ∀ᵐ t ∂volume.restrict (regularCornerDomain m),
      p t < 0 → 0 < q t → X t ∈ Ioo (-C) C → 0 < Y t →
      sweptNiche target (Real.pi / 2) (X t) = Y t →
      (∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
        fullWallClip hU.isCap.toCompactCap (X t) s =
          sweptNiche target (Real.pi / 2) (X t) → s = t) → aZ t = q t := by
  have hcore := (ae_restrict_iff' measurableSet_Ioo).mp
    (J.ae_corner_densities_eq_momenta_of_unique_contact hU hl hr hC hm hheight haffine
      hlow hhigh hh hρ hρ0 hρK heq hunit hTargetBox hleft hright hphase)
  filter_upwards [ae_restrict_mem (isOpen_regularCornerDomain m).measurableSet,
    ae_restrict_of_ae hcore] with t ht hdensity
  intro hp hq hx hy hcontact hunique
  have htcore := hphase.mem_core_of_first_neg_second_pos (Ioo_subset_Icc_self ht.1) hp hq
  exact (hdensity htcore hx hy hcontact hunique).1

end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
