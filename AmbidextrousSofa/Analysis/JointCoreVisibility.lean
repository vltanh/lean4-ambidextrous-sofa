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
with the signed corner flux balance, it determines the first corner
density and forces the shared occupation to be one.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem StrictCornerSignPhases.mem_core_of_first_neg_second_pos
    {p q : ℝ → ℝ} {L α η t : ℝ} (hphase : StrictCornerSignPhases p q L α η)
    (ht : t ∈ Icc (0 : ℝ) L) (hp : p t < 0) (hq : 0 < q t) : t ∈ Ioo α η := by
  refine ⟨hphase.first_lt_of_first_neg ht hp, lt_of_not_ge fun hle => ?_⟩
  rcases hle.eq_or_lt with rfl | hlt
  · exact hq.ne' hphase.second_zero
  · linarith [(hphase.final_signs t ⟨hlt, ht.2⟩).2]

namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b C h m c K : ℝ} {ρ : ℝ → ℝ}
  (J : SelectedJointSourceLimit target a b) (H : IsTiltedFirstUnitTarget target a b C h m c ρ K)

set_option quotPrecheck false
local notation "F" => fullTiltedSupportQuarterPair H.hU H.hm.le H.haffine H.hρ H.hρ0 H.hρK H.heq
local notation "Z" => innerCornerPoint (F).f (F).g
local notation "p" => supportP (F).fD (F).g
local notation "q" => supportQ (F).gD (F).f
local notation "X" => (fun t => (Z t).1)
local notation "Y" => (fun t => (Z t).2)
local notation "XD" => (fun t => p t * Real.cos t - q t * Real.sin t)
local notation "aZ" => J.sourceBranchDensity (firstCornerSource target) 0
local notation "aW" => J.sourceBranchDensity (secondCornerSource target) (Real.pi / 2)
local notation "w" => (fun t => aZ t * Real.sin t + aW t * Real.cos t)

theorem ae_first_corner_density_eq_q_of_unique_contact {α η : ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    ∀ᵐ t ∂volume.restrict (regularCornerDomain m),
      p t < 0 → 0 < q t → X t ∈ Ioo (-C) C → 0 < Y t →
      sweptNiche target (Real.pi / 2) (X t) = Y t →
      (∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
        fullWallClip H.hU.isCap.toCompactCap (X t) s =
          sweptNiche target (Real.pi / 2) (X t) → s = t) → aZ t = q t := by
  -- The core parameters with a uniquely exposed positive contact.
  let T : Set ℝ := {t | t ∈ Ioo α η ∧ X t ∈ Ioo (-C) C ∧ 0 < Y t ∧
    sweptNiche target (Real.pi / 2) (X t) = Y t ∧
    ∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
      fullWallClip H.hU.isCap.toCompactCap (X t) s =
        sweptNiche target (Real.pi / 2) (X t) → s = t}
  obtain ⟨hX, hY⟩ := H.core_continuous
  have hN : Continuous fun t => sweptNiche target (Real.pi / 2) (X t) := by
    simpa only [Function.comp_def, IsDownwardCap.toCompactCap_carrier] using
      continuous_capSweptNiche.comp ((continuous_const (y := H.hU.isCap.toCompactCap)).prodMk hX)
  have hT : MeasurableSet T :=
    measurableSet_Ioo.inter ((measurableSet_Ioo.preimage hX.measurable).inter
      ((isOpen_lt continuous_const hY).measurableSet.inter
        ((isClosed_eq hN hY).measurableSet.inter
          (H.hU.isCap.measurableSet_unique_fullWallClip_contact hX))))
  have hTS : T ⊆ Ioo α η := fun _ ht => ht.1
  have hinj : InjOn X (Ioo α η) :=
    (fullTiltedSupportQuarterPair_core_strictAntiOn_open
      H.hU H.hm.le H.haffine H.hρ H.hρ0 H.hρK H.heq hphase).injOn
  -- Above `X '' T` the core projection is Lebesgue measure, so the weight saturates the speed.
  have hsaturated :
      (((volume.restrict (Ioo α η)).withDensity (fun t => ENNReal.ofReal (w t))).map X).restrict
          (X '' T) = volume.restrict (X '' T) := by
    rw [← J.coreSourceProjection_eq_density_graph H hphase]
    exact J.coreSourceProjection_restrict_unique_positive_image_eq_volume H
      (hT.image_of_continuousOn_injOn hX.continuousOn (hinj.mono hTS))
      (fun t ht => ⟨ht.2.1, ht.2.2.2.1 ▸ ht.2.2.1⟩) fun _ ht => ht.2.2.2.2
  have hw0 : ∀ᵐ t ∂volume.restrict T, 0 ≤ w t := by
    filter_upwards [ae_restrict_mem hT] with t ht
    obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter
      ⟨hphase.first_mem.1.trans ht.1.1, ht.1.2.trans hphase.second_mem.2⟩
    exact add_nonneg (mul_nonneg (J.sourceBranchDensity_nonneg _ _ _) hs.le)
      (mul_nonneg (J.sourceBranchDensity_nonneg _ _ _) hc.le)
  have hweight := ae_weight_eq_abs_deriv_of_graph_saturated_on measurableSet_Ioo hT hTS
    (fun t ht => (fullTiltedSupportQuarterPair_core_hasDerivAt H.hU H.hm.le H.haffine H.hρ H.hρ0
      H.hρK H.heq ⟨hphase.first_mem.1.trans ht.1, ht.2.trans hphase.second_mem.2⟩).1) hinj
    (((J.measurable_sourceBranchDensity _ _).fun_mul Real.measurable_sin).fun_add
      ((J.measurable_sourceBranchDensity _ _).fun_mul Real.measurable_cos)).aemeasurable
    hw0 hsaturated
  -- With the signed corner balance, the saturated weight determines the first density.
  filter_upwards [ae_restrict_mem (isOpen_regularCornerDomain m).measurableSet,
    ae_restrict_of_ae ((ae_restrict_iff' hT).mp hweight),
    ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Ioo).mp
      (J.ae_corner_density_balance H hphase))]
    with t ht hwgt hb hp hq hx hy hcontact hunique
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ht.1
  have hneg : XD t < 0 := sub_neg.mpr ((mul_neg_of_neg_of_pos hp hc).trans (mul_pos hq hs))
  have hfull : aZ t * Real.sin t + aW t * Real.cos t = q t * Real.sin t - p t * Real.cos t := by
    simpa only [abs_of_neg hneg, neg_sub] using hwgt
      ⟨hphase.mem_core_of_first_neg_second_pos (Ioo_subset_Icc_self ht.1) hp hq, hx, hy,
        hcontact, hunique⟩
  refine mul_right_cancel₀ (sub_pos.mpr (sub_neg.mp hneg)).ne' ?_
  linear_combination q t * hfull - Real.cos t * hb ht.1

end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
