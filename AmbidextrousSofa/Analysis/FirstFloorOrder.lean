module

public import AmbidextrousSofa.Analysis.FirstFloorTrapping
public import AmbidextrousSofa.Analysis.FirstFloorVisibility
public import AmbidextrousSofa.Analysis.FirstUnitBadEntry

@[expose] public section

/-!
# Ordering the actual first companion floor crossing

At the second momentum zero the companion tangent is the positive inner
corner. Thus its first floor zero occurs earlier, independently of any
companion unit assumption. At bad entry, an initial nonpositive floor
history supplies actual unique core contacts and a genuine visibility
neighborhood. The explicit local source law then feeds the trapping
theorem. The source-law premise in the bad-entry theorem is retained
until the common occupation measure supplies it.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

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
local notation "B" => firstTangentPoint (F).f (F).fD
set_option quotPrecheck false in
local notation "D" => secondTangentPoint (F).g (F).gD
set_option quotPrecheck false in
local notation "Z" => innerCornerPoint (F).f (F).g
set_option quotPrecheck false in
local notation "p" => supportP (F).fD (F).g
set_option quotPrecheck false in
local notation "q" => supportQ (F).gD (F).f
local notation "v" => (fun t : ℝ => leftCompanionWingDensity m ρ (t + Real.pi / 2))
local notation "V" => leftCompanionCap U (horizontalLeft U + capWidth U / 4)

/-- A negative first momentum keeps the inner corner strictly above the floor. -/
theorem fullTiltedSupportQuarterPair_core_pos_of_momentum_neg {t : ℝ}
    (hheight : capHeight U = 1)
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ s ≤ 1)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hp : p t < 0) : 0 < (Z t).2 := by
  rw [innerCorner_snd_eq_firstTangent (F).f (F).g (F).fD]
  exact sub_pos.mpr ((mul_neg_of_neg_of_pos hp (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)).trans_le
    (fullTiltedSupportQuarterPair_first_tangent_nonneg hU hm haffine hρ hρ0 hρK heq hheight hunit
      (Ioo_subset_Icc_self ht)))

/-- The positive core and its strict right middle bound continue through
the entire opposite-sign phase, including its last endpoint. No bound
on the companion density is used. -/
theorem fullTiltedSupportQuarterPair_core_phase_positive_and_right {C h α η t : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50)
    (hheight : capHeight U = 1) (hlow : capRoof U (-C) = 1 - h)
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ s ≤ 1)
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (ht : t ∈ Ioc α η) : (Z t).1 < C ∧ 0 < (Z t).2 := by
  have hBxα : (Z α).1 < C := by
    rw [innerCorner_eq_firstTangent_of_momentum_zero hphase.first_zero]
    exact lt_of_not_ge fun h => (fullTiltedSupportQuarterPair_first_momentum_neg_after_middle
      hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh hlow
      (Ioo_subset_Icc_self hphase.first_mem) h).2.ne hphase.first_zero
  have hp : p t < 0 := by
    rcases ht.2.eq_or_lt with rfl | hlt
    exacts [hphase.first_at_second, (hphase.core_signs t ⟨ht.1, hlt⟩).1]
  exact ⟨(fullTiltedSupportQuarterPair_core_strictAntiOn hU hm haffine hρ hρ0 hρK heq
      hphase.first_mem.1.le hphase.second_mem.2.le hphase.core_signs
      ⟨le_rfl, hphase.second_mem.1.le⟩ ⟨ht.1.le, ht.2⟩ ht.1).trans hBxα,
    fullTiltedSupportQuarterPair_core_pos_of_momentum_neg hU hm haffine hρ hρ0 hρK heq hheight
      hunit ⟨hphase.first_mem.1.trans ht.1, ht.2.trans_lt hphase.second_mem.2⟩ hp⟩

theorem fullTiltedSupportQuarterPair_companion_floor_pos_at_second_phase {α η : ℝ}
    (hheight : capHeight U = 1)
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ s ≤ 1)
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) : 0 < (D η).2 := by
  rw [← innerCorner_eq_secondTangent_of_momentum_zero hphase.second_zero]
  exact fullTiltedSupportQuarterPair_core_pos_of_momentum_neg hU hm haffine hρ hρ0 hρK heq
    hheight hunit ⟨hphase.first_mem.1.trans hphase.second_mem.1, hphase.second_mem.2⟩
    hphase.first_at_second

theorem fullTiltedSupportQuarterPair_exists_first_floor_before_second_phase {C h α η : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hmpos : 0 < m) (hheight : capHeight U = 1)
    (hh : 0 < h) (hlow : capRoof U (-C) = 1 - h)
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ s ≤ 1)
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    ∃ γ ∈ Ioo 0 η, (D γ).2 = 0 ∧ (∀ t ∈ Ico (0 : ℝ) γ, (D t).2 < 0) ∧
      companionZero V ≤ (D γ).1 ∧ C + (D γ).1 ≤ 1 := by
  obtain ⟨γ, hγ, hzero, hbefore, hzeroX, hX⟩ :=
    fullTiltedSupportQuarterPair_first_floor_crossing hU hm haffine hρ hρ0 hρK heq
      hl hr hmpos hheight hh hlow
  -- The floor is already positive at the second momentum zero.
  have hpositive := fullTiltedSupportQuarterPair_companion_floor_pos_at_second_phase
    hU hm haffine hρ hρ0 hρK heq hheight hunit hphase
  refine ⟨γ, ⟨hγ.1, lt_of_not_ge fun hηγ => ?_⟩, hzero, hbefore, hzeroX, hX⟩
  rcases hηγ.eq_or_lt with rfl | hlt
  · linarith
  · linarith [hbefore η ⟨(hphase.first_mem.1.trans hphase.second_mem.1).le, hlt⟩]

/-- The only analytic premise still exposed here is the local source
law at the actual uniquely visible core. Initial-floor visibility and
the boundary neighborhood are proved from the literal two-cap walls. -/
theorem fullTiltedSupportQuarterPair_first_floor_lt_bad_entry_of_visible_law
    {C h α η τ γ : ℝ} {δ : ℝ → ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50)
    (hheight : capHeight U = 1) (hlow : capRoof U (-C) = 1 - h)
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ s ≤ 1)
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (hτ : τ ∈ Ioo α η) (hpτ : p τ = -1)
    (hγzero : (D γ).2 = 0) (hbefore : ∀ t ∈ Ico (0 : ℝ) γ, (D t).2 < 0)
    (hsource : ∀ᵐ t ∂volume.restrict (Ioo τ η),
      sweptNiche U (Real.pi / 2) (Z t).1 = (Z t).2 →
      (∀ r ∈ Icc (0 : ℝ) (Real.pi / 2),
        fullWallClip hU.isCap.toCompactCap (Z t).1 r =
          sweptNiche U (Real.pi / 2) (Z t).1 → r = t) →
      Analysis.firstFloorVisibleLaw p q ρ v δ t) : γ < τ := by
  have hτq : τ ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨hphase.first_mem.1.trans hτ.1, hτ.2.trans hphase.second_mem.2⟩
  have hJR : horizontalRight U - capWidth U / 4 = C := by rw [capWidth, hl, hr]; ring
  have hgeometry (t : ℝ) (ht : t ∈ Ioc α η) :=
    fullTiltedSupportQuarterPair_core_phase_positive_and_right
      hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh hheight hlow hunit hphase ht
  obtain ⟨hpAC, -, hpD⟩ := fullTiltedSupportQuarterPair_corner_calculus
    hU hm haffine hρ hρ0 hρK heq
  obtain ⟨-, -, -, hyAC, hyD⟩ := fullTiltedSupportQuarterPair_tangent_calculus
    hU hm haffine hρ hρ0 hρK heq
  have hsub : uIcc τ η ⊆ uIcc (0 : ℝ) (Real.pi / 2) :=
    uIcc_subset_uIcc (Icc_subset_uIcc (Ioo_subset_Icc_self hτq))
      (Icc_subset_uIcc ⟨(hτq.1.trans hτ.2).le, hphase.second_mem.2.le⟩)
  by_contra! hτγ
  have hinitial : ∀ s ∈ Icc (0 : ℝ) τ, (D s).2 ≤ 0 := fun s hs => by
    rcases (hs.2.trans hτγ).eq_or_lt with rfl | hlt
    exacts [hγzero.le, (hbefore s ⟨hs.1, hlt⟩).le]
  have hvisible : ∀ b ∈ Ioc τ η, (∀ s ∈ Icc τ b, (D s).2 ≤ 0) →
      ∀ᵐ t ∂volume.restrict (Ioo τ b), Analysis.firstFloorVisibleLaw p q ρ v δ t := by
    intro b hb hnonpos
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hb.2) hsource]
      with t ht hs
    have htphase : t ∈ Ioo α η := ⟨hτ.1.trans ht.1, ht.2.trans_le hb.2⟩
    have hgeo := hgeometry t (Ioo_subset_Ioc_self htphase)
    have hfloor : ∀ r ∈ Ioc (0 : ℝ) t, (D r).2 ≤ 0 := fun r hr => by
      rcases le_or_gt r τ with hrτ | hrτ
      exacts [hinitial r ⟨hr.1.le, hrτ⟩, hnonpos r ⟨hrτ.le, hr.2.trans ht.2.le⟩]
    obtain ⟨h1, h2⟩ := fullTiltedSupportQuarterPair_core_contact_of_initial_floor_nonpos
      hU hm haffine hρ hρ0 hρK heq hunit
      ⟨hphase.first_mem.1.trans htphase.1, htphase.2.trans hphase.second_mem.2⟩
      (hphase.core_signs t htphase).1 hgeo.2 (hJR ▸ hgeo.1.le) hfloor
    exact hs h1 h2
  have hboundary : (D τ).2 = 0 → ∃ b ∈ Ioc τ η,
      ∀ᵐ t ∂volume.restrict (Ioo τ b), Analysis.firstFloorVisibleLaw p q ρ v δ t := by
    intro _
    have hgeo := hgeometry τ (Ioo_subset_Ioc_self hτ)
    obtain ⟨b, hb, hlocal⟩ := ((TFAE_mem_nhdsGT hτ.2 _).out 1 4).mp (nhdsWithin_le_nhds
      (fullTiltedSupportQuarterPair_core_contact_eventually_of_initial_floor_nonpos
        hU hm haffine hρ hρ0 hρK heq hunit hτq (by rw [hpτ]; norm_num)
        (hphase.core_signs τ hτ).2 hgeo.2 (hJR ▸ hgeo.1) (fun s hs => hinitial s ⟨hs.1.le, hs.2⟩)))
    refine ⟨b, hb, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hb.2) hsource] with t ht hs
    exact hs (hlocal ht).2.1 (hlocal ht).2.2
  exact Analysis.firstFloor_bad_entry_trapping hτq.1.le hτ.2
    (by linarith [hphase.second_mem.2, Real.pi_pos]) (hpAC.mono hsub) (hyAC.mono hsub) hpτ.le
    (hinitial τ ⟨hτq.1.le, le_rfl⟩)
    (fullTiltedSupportQuarterPair_companion_floor_pos_at_second_phase
      hU hm haffine hρ hρ0 hρK heq hheight hunit hphase)
    ((ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hτq.1.le hphase.second_mem.2.le)
      (hpD.and hyD)).mono fun t h => ⟨h.1.1, h.2.2.2.2⟩) hvisible hboundary

/-- Actual top projection keeps the whole positive core phase inside
the middle interval. The literal positive-wall identity also excludes
the affine normal, so these are regular source angles. -/
theorem fullTiltedSupportQuarterPair_core_phase_geometry {C h α η t : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh0 : 0 < h) (hh1 : h < 17 / 50)
    (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1)
    (hκ : ∀ s, ρ s ≤ sourceKappa (upperCornerVelocity U s))
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ s ≤ 1)
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (ht : t ∈ Ioc α η) :
    (Z t).1 ∈ Ioo (-C) C ∧ 0 < (Z t).2 ∧
      t ∈ regularCornerDomain m ∧ Z t = attachedCorner U t := by
  have hmid : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]; congr 1 <;> ring
  have hJL : horizontalLeft U + capWidth U / 4 = -C := by rw [capWidth, hl, hr]; ring
  have hJR : horizontalRight U - capWidth U / 4 = C := by rw [capWidth, hl, hr]; ring
  have hdry := hU.firstUnit_dry_left_and_overhang_bounds
    hl hr hC0 hC1 hh0 hh1 hheight (by simpa only [hmid] using haffine)
    hlow hhigh hρ hρ0 hρK heq hκ hunit
  have hgeo := fullTiltedSupportQuarterPair_core_phase_positive_and_right
    hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh1.le hheight hlow hunit hphase ht
  have htq : t ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨hphase.first_mem.1.trans ht.1, ht.2.trans_lt hphase.second_mem.2⟩
  -- A positive cut wall places the core strictly right of the low-wing zero.
  have hleft : companionZero V < (Z t).1 := lt_of_not_ge fun h => hgeo.2.not_ge
    ((fullTiltedSupportQuarterPair_walls_core hU hm haffine hρ hρ0 hρK heq htq).2 ▸
      hU.isCap_fullLeftCompanion.secondWall_nonpos_of_le_companionZero h htq)
  have hright : (Z t).1 ≤ horizontalRight U - capWidth U / 4 := hJR ▸ hgeo.1.le
  have hzero : -C < companionZero V := by rw [hJL]; linarith [hdry.1, hdry.2.2.1]
  exact ⟨⟨hzero.trans hleft, hgeo.1⟩, hgeo.2,
    mem_regularCornerDomain_of_after_nonneg_affine hm htq
      (fullTiltedSupportQuarterPair_positive_core_after_affine
        hU hm haffine hρ hρ0 hρK heq (hJR ▸ hhigh) htq hgeo.2 hright),
    fullTiltedSupportQuarterPair_core_eq_attachedCorner
      hU hm haffine hρ hρ0 hρK heq htq hgeo.2 hright⟩

/-- Adapter for an occupation law on the genuine regular domain. Every
geometric condition is supplied by the actual phase, top projection,
first-unit tangent order, and fixed-cap wall contact. -/
theorem fullTiltedSupportQuarterPair_first_floor_lt_bad_entry_of_regular_visible_law
    {C h α β η τ γ : ℝ} {δ : ℝ → ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh0 : 0 < h) (hh1 : h < 17 / 50)
    (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1)
    (hκ : ∀ s, ρ s ≤ sourceKappa (upperCornerVelocity U s))
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ s ≤ 1)
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (hβ : β ∈ Icc (0 : ℝ) (Real.pi / 2)) (hβx : (B β).1 = C)
    (hβτ : β ≤ τ) (hτ : τ ∈ Ioo α η) (hpτ : p τ = -1)
    (hγzero : (D γ).2 = 0) (hbefore : ∀ t ∈ Ico (0 : ℝ) γ, (D t).2 < 0)
    (hsource : ∀ᵐ t ∂volume.restrict (regularCornerDomain m),
      p t < 0 → 0 < q t → (Z t).1 ∈ Ioo (-C) C → 0 < (Z t).2 → C ≤ (B t).1 →
      sweptNiche U (Real.pi / 2) (Z t).1 = (Z t).2 →
      (∀ r ∈ Icc (0 : ℝ) (Real.pi / 2),
        fullWallClip hU.isCap.toCompactCap (Z t).1 r =
          sweptNiche U (Real.pi / 2) (Z t).1 → r = t) →
      Analysis.firstFloorVisibleLaw p q ρ v δ t) : γ < τ := by
  have hgeometry (t : ℝ) (ht : t ∈ Ioc α η) :=
    fullTiltedSupportQuarterPair_core_phase_geometry
      hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh0 hh1 hheight hlow hhigh
      hκ hunit hphase ht
  have hregular : Ioo τ η ⊆ regularCornerDomain m := fun t ht =>
    (hgeometry t ⟨hτ.1.trans ht.1, ht.2.le⟩).2.2.1
  have hBmono := (fullTiltedSupportQuarterPair_first_tangent_order
    hU hm haffine hρ hρ0 hρK heq hunit).1
  apply fullTiltedSupportQuarterPair_first_floor_lt_bad_entry_of_visible_law
    hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh1.le hheight hlow hunit
    hphase hτ hpτ hγzero hbefore
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae_restrict_of_subset hregular hsource] with t ht hs
  have htphase : t ∈ Ioo α η := ⟨hτ.1.trans ht.1, ht.2⟩
  have hgeo := hgeometry t (Ioo_subset_Ioc_self htphase)
  have hBt : C ≤ (B t).1 := hβx ▸ hBmono hβ
    ⟨(hphase.first_mem.1.trans htphase.1).le, htphase.2.le.trans hphase.second_mem.2.le⟩
    (hβτ.trans ht.1.le)
  exact hs (hphase.core_signs t htphase).1 (hphase.core_signs t htphase).2 hgeo.1 hgeo.2.1 hBt

end ActualPair

end AmbidextrousSofa

