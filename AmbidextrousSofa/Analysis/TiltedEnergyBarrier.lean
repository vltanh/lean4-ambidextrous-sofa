module

public import AmbidextrousSofa.Analysis.TiltedInitialCircle

@[expose] public section

/-!
# Whole-quarter energy propagation for the actual tilted pair

The cut companion can make the first momentum exceed one before the
middle normal. Both sources are already zero on that interval, and the
clipped energy then decreases for every value of the first momentum.
This gives an energy barrier across the entire actual quarter. Combined
with the internally constructed stopped circle, it proves the actual
initial-floor unit-curvature criterion without a later phase partition.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem clippedCornerEnergy_derivative_nonpos_of_zero_sources
    {p q u v : ℝ} (hq : -1 ≤ q) (hu : u = 0) (hv : v = 0) :
    2 * (max p 0 - 1 / 2) * (if 0 < p then u - 1 - q else 0) +
      2 * (q + 1) * (v - 1 + p) ≤ 0 := by
  by_cases hp : 0 < p
  · rw [max_eq_left hp.le, if_pos hp, hu, hv]
    nlinarith only [hq]
  · have hp0 : p ≤ 0 := le_of_not_gt hp
    rw [max_eq_right hp0, if_neg hp, hv, mul_zero, zero_add]
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith only [hq])
      (by linarith only [hp0])

theorem clippedCornerEnergy_le_max_of_zero_source_alternative
    {p q u v : ℝ → ℝ} {a b : ℝ}
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hq : AbsolutelyContinuousOnInterval q a b) (hab : a ≤ b)
    (hode : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hqbound : ∀ᵐ t ∂volume.restrict (Ioo a b), -1 ≤ q t)
    (hκ : ∀ᵐ t ∂volume.restrict (Ioo a b), v t ≤ sourceKappa (p t))
    (hshadow : ∀ᵐ t ∂volume.restrict (Ioo a b),
      0 < p t → 0 < q t → u t = 0 ∧ v t ≤ 1 / 2)
    (halternative : ∀ᵐ t ∂volume.restrict (Ioo a b), p t ≤ 1 ∨ u t = 0 ∧ v t = 0)
    {t : ℝ} (ht : t ∈ Icc a b) :
    clippedCornerEnergy p q t ≤ max (17 / 4) (clippedCornerEnergy p q a) := by
  apply absolutelyContinuousOnInterval_le_of_ae_deriv_nonpos_above
    (absolutelyContinuousOnInterval_clippedCornerEnergy hp hq) hab (le_max_right _ _) _ ht
  filter_upwards [ae_hasDerivAt_clippedCornerEnergy hp hab hode,
    hqbound, hκ, hshadow, halternative] with s hd hqb hk hs ha
  intro hE
  rw [hd.deriv]
  rcases ha with hp1 | ⟨hu0, hv0⟩
  · exact clippedCornerEnergy_derivative_nonpos_above hp1 hqb hk hs
      ((le_max_left _ _).trans_lt hE)
  · exact clippedCornerEnergy_derivative_nonpos_of_zero_sources hqb hu0 hv0

theorem clippedCornerEnergy_le_initialFloorEnergy (p q : ℝ → ℝ) (t : ℝ) :
    clippedCornerEnergy p q t ≤ Analysis.initialFloorEnergy (p t) (q t) := by
  unfold clippedCornerEnergy Analysis.initialFloorEnergy
  by_cases hp : 0 ≤ p t
  · rw [max_eq_left hp]
  · rw [max_eq_right (le_of_not_ge hp)]
    nlinarith only [le_of_not_ge hp, sq_nonneg (p t)]

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
set_option quotPrecheck false in
local notation "p" => supportP (F).fD (F).g
set_option quotPrecheck false in
local notation "q" => supportQ (F).gD (F).f

theorem fullTiltedSupportQuarterPair_first_arm_or_zero_sources {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 0 < C) (hsmall : C + m < 1)
    (hheight : capHeight U = 1) (hhigh : capRoof U C = 1) :
    ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
      p t ≤ 1 ∨ ρ t = 0 ∧ leftCompanionWingDensity m ρ (t + Real.pi / 2) = 0 := by
  have hinit := (ae_restrict_iff' measurableSet_Ioo).mp
    (hU.full_tilted_wing_densities_zero_before_affine hl hr hC hm hsmall
      hheight haffine hhigh hρ hρ0 heq)
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hinit] with t ht hz
  by_cases hpost : Real.arctan m ≤ t
  · exact Or.inl (fullTiltedSupportQuarterPair_p_le_one_after_affine
      hU hm haffine hρ hρ0 hρK heq ⟨ht.1.le, ht.2⟩ hpost)
  · exact Or.inr (hz ⟨ht.1, lt_of_not_ge hpost⟩)

theorem fullTiltedSupportQuarterPair_energy_le_max_from {C a t : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 0 < C) (hsmall : C + m < 1)
    (hheight : capHeight U = 1) (hhigh : capRoof U C = 1)
    (hκ : ∀ s, ρ s ≤ sourceKappa (upperCornerVelocity U s))
    (ha : a ∈ Icc 0 (Real.pi / 2)) (ht : t ∈ Icc a (Real.pi / 2)) :
    clippedCornerEnergy p q t ≤ max (17 / 4) (clippedCornerEnergy p q a) := by
  obtain ⟨hp, hq, hode⟩ :=
    fullTiltedSupportQuarterPair_corner_calculus hU hm haffine hρ hρ0 hρK heq
  have hsubcc : uIcc a (Real.pi / 2) ⊆ uIcc 0 (Real.pi / 2) := by
    rw [uIcc_of_le ha.2, uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    exact Icc_subset_Icc ha.1 le_rfl
  have hsub : Ioo a (Real.pi / 2) ⊆ Ioo (0 : ℝ) (Real.pi / 2) :=
    Ioo_subset_Ioo ha.1 le_rfl
  have hcontrols := ae_restrict_of_ae_restrict_of_subset hsub
    (hU.fullTiltedSupportQuarterPair_source_controls hl hr hC hm hsmall hheight
      haffine hhigh hρ hρ0 hρK hκ heq)
  apply clippedCornerEnergy_le_max_of_zero_source_alternative
    (hp.mono hsubcc) (hq.mono hsubcc) ha.2
    (ae_restrict_of_ae_restrict_of_subset hsub hode) _
    (hcontrols.mono (fun _ hs => hs.2.1))
    (hcontrols.mono (fun _ hs => hs.2.2.1))
    (ae_restrict_of_ae_restrict_of_subset hsub
      (fullTiltedSupportQuarterPair_first_arm_or_zero_sources
        hU hm haffine hρ hρ0 hρK heq hl hr hC hsmall hheight hhigh)) ht
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact fullTiltedSupportQuarterPair_q_ge_neg_one hU hm haffine hρ hρ0 hρK heq
    ⟨ha.1.trans hs.1.le, hs.2.le⟩

theorem fullTiltedSupportQuarterPair_ae_first_le_one_after_energy {C a : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 0 < C) (hsmall : C + m < 1)
    (hheight : capHeight U = 1) (hhigh : capRoof U C = 1)
    (hκ : ∀ s, ρ s ≤ sourceKappa (upperCornerVelocity U s))
    (ha : a ∈ Icc 0 (Real.pi / 2)) (hstart : clippedCornerEnergy p q a ≤ 17 / 4) :
    ∀ᵐ t ∂volume.restrict (Ioo a (Real.pi / 2)), ρ t ≤ 1 := by
  have hsub : Ioo a (Real.pi / 2) ⊆ Ioo (0 : ℝ) (Real.pi / 2) :=
    Ioo_subset_Ioo ha.1 le_rfl
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae_restrict_of_subset hsub
      (hU.fullTiltedSupportQuarterPair_source_controls hl hr hC hm hsmall hheight
        haffine hhigh hρ hρ0 hρK hκ heq)] with t ht hs
  have henergy := fullTiltedSupportQuarterPair_energy_le_max_from
    hU hm haffine hρ hρ0 hρK heq hl hr hC hsmall hheight hhigh hκ ha ⟨ht.1.le, ht.2.le⟩
  rw [max_eq_left hstart] at henergy
  exact curvature_le_one_of_clippedCornerEnergy
    (fullTiltedSupportQuarterPair_q_ge_neg_one hU hm haffine hρ hρ0 hρK heq
      ⟨ha.1.trans ht.1.le, ht.2.le⟩) hs.1
    (fun hp hq => (hs.2.2.1 hp hq).1) henergy

/-- The initial-floor scalar conditions now imply unit curvature of
the actual original first quarter. Every stopping, source and energy
propagation hypothesis is discharged from the cap inside this proof. -/
theorem fullTiltedSupportQuarterPair_ae_first_le_one_of_initial_floor_conditions {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 1 / 2 < C) (hmpos : 0 < m) (hsmall : C + m < 1)
    (hh : 0 < h) (hheight : capHeight U = 1) (hhigh : capRoof U C = 1)
    (hlow : capRoof U (-C) = 1 - h)
    (hκ : ∀ s, ρ s ≤ sourceKappa (upperCornerVelocity U s))
    (hconditions : Analysis.InitialFloorEnergyConditions (3 * C)
      (capRoof U (horizontalRight U) - 1 + h) h) :
    ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)), ρ t ≤ 1 := by
  obtain ⟨τ, hτ, _hphase, hzero, hpcircle, hqcircle, _hDcircle, _hqτ, hstop⟩ :=
    fullTiltedSupportQuarterPair_exists_initial_stopping_circle
      hU hm haffine hρ hρ0 hρK heq hl hr hC hmpos hsmall hh hheight hhigh hlow hκ
  have hh2 : h ≤ 2 := by
    have hlow0 := capRoof_nonneg hU.isCap.isCompact (fun x hx => (hU.isCap.inStrip hx).1) (-C)
    rw [hlow] at hlow0
    linarith only [hlow0]
  have hτmem : τ ∈ Icc (0 : ℝ) τ := ⟨hτ.1.le, le_rfl⟩
  have hstopCircle : Analysis.initialFloorCircleP (3 * C)
      (capRoof U (horizontalRight U) - 1 + h) τ = 0 ∨ τ = Analysis.initialFloorAngle h := by
    rcases hstop with hpzero | hfloor
    · exact Or.inl ((hpcircle τ hτmem).symm.trans hpzero)
    · exact Or.inr hfloor
  have henergy := Analysis.initialFloor_stopped_energy_le hh.le hh2 hconditions hstopCircle
  rw [← hpcircle τ hτmem, ← hqcircle τ hτmem] at henergy
  have hstart : clippedCornerEnergy p q τ ≤ 17 / 4 :=
    (clippedCornerEnergy_le_initialFloorEnergy p q τ).trans henergy
  have hfuture := fullTiltedSupportQuarterPair_ae_first_le_one_after_energy
    hU hm haffine hρ hρ0 hρK heq hl hr (by linarith only [hC]) hsmall hheight hhigh hκ
    ⟨hτ.1.le, hτ.2.le⟩ hstart
  have hz := (ae_restrict_iff' measurableSet_Ioo).mp hzero
  have hf := (ae_restrict_iff' measurableSet_Ioo).mp hfuture
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hz,
    ae_restrict_of_ae hf, ae_restrict_of_ae (volume.ae_ne τ)] with t ht hz hf hne
  by_cases hpre : t < τ
  · rw [(hz ⟨ht.1, hpre⟩).1]
    norm_num
  · exact hf ⟨lt_of_le_of_ne (le_of_not_gt hpre) (Ne.symm hne), ht.2⟩

end ActualPair

end AmbidextrousSofa
