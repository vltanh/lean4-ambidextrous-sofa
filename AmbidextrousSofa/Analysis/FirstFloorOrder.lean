import AmbidextrousSofa.Analysis.FirstFloorTrapping
import AmbidextrousSofa.Analysis.FirstFloorVisibility
import AmbidextrousSofa.Analysis.FirstUnitBadEntry

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
local notation "B" => firstTangentPoint F.f F.fD
local notation "D" => secondTangentPoint F.g F.gD
local notation "Z" => innerCornerPoint F.f F.g
local notation "p" => supportP F.fD F.g
local notation "q" => supportQ F.gD F.f
local notation "v" => (fun t : ℝ => leftCompanionWingDensity m ρ (t + Real.pi / 2))
local notation "V" => leftCompanionCap U (horizontalLeft U + capWidth U / 4)

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
  have hαη : α < η := hphase.second_mem.1
  have htq : t ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨hphase.first_mem.1.trans ht.1, ht.2.trans_lt hphase.second_mem.2⟩
  have hBxα : (B α).1 < C := by
    by_contra hnot
    have hnegative := (fullTiltedSupportQuarterPair_first_momentum_neg_after_middle
      hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh hlow
      (Ioo_subset_Icc_self hphase.first_mem) (le_of_not_gt hnot)).2
    rw [hphase.first_zero] at hnegative
    exact lt_irrefl 0 hnegative
  have hjoin : Z α = B α := innerCorner_eq_firstTangent_of_momentum_zero hphase.first_zero
  have hreverse := fullTiltedSupportQuarterPair_core_strictAntiOn
    hU hm haffine hρ hρ0 hρK heq hphase.first_mem.1.le hphase.second_mem.2.le
    hphase.core_signs ⟨le_rfl, hαη.le⟩ ⟨ht.1.le, ht.2⟩ ht.1
  have hright : (Z t).1 < C := by
    rw [hjoin] at hreverse
    exact hreverse.trans hBxα
  have hp : p t < 0 := by
    rcases ht.2.eq_or_lt with heq | hlt
    · simpa only [heq] using hphase.first_at_second
    · exact (hphase.core_signs t ⟨ht.1, hlt⟩).1
  have hcos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [htq.1, Real.pi_pos], htq.2⟩
  have hBy := fullTiltedSupportQuarterPair_first_tangent_nonneg
    hU hm haffine hρ hρ0 hρK heq hheight hunit (Ioo_subset_Icc_self htq)
  refine ⟨hright, ?_⟩
  rw [innerCorner_snd_eq_firstTangent F.f F.g F.fD]
  exact sub_pos.mpr ((mul_neg_of_neg_of_pos hp hcos).trans_le hBy)

theorem fullTiltedSupportQuarterPair_companion_floor_pos_at_second_phase {α η : ℝ}
    (hheight : capHeight U = 1)
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ s ≤ 1)
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) : 0 < (D η).2 := by
  have hη : η ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨hphase.first_mem.1.trans hphase.second_mem.1, hphase.second_mem.2⟩
  have hjoin : Z η = D η := innerCorner_eq_secondTangent_of_momentum_zero hphase.second_zero
  have hBy := fullTiltedSupportQuarterPair_first_tangent_nonneg
    hU hm haffine hρ hρ0 hρK heq hheight hunit (Ioo_subset_Icc_self hη)
  have hcos : 0 < Real.cos η := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [hη.1, Real.pi_pos], hη.2⟩
  rw [← hjoin, innerCorner_snd_eq_firstTangent F.f F.g F.fD]
  exact sub_pos.mpr ((mul_neg_of_neg_of_pos hphase.first_at_second hcos).trans_le hBy)

/-- This ordering is valid in both branches of the companion-unit
dichotomy. The first-zero data are the literal tangent data. -/
theorem fullTiltedSupportQuarterPair_first_floor_lt_second_phase {α η γ : ℝ}
    (hheight : capHeight U = 1)
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ s ≤ 1)
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (hγzero : (D γ).2 = 0) (hbefore : ∀ t ∈ Ico (0 : ℝ) γ, (D t).2 < 0) : γ < η := by
  have hpositive := fullTiltedSupportQuarterPair_companion_floor_pos_at_second_phase
    hU hm haffine hρ hρ0 hρK heq hheight hunit hphase
  by_contra hnot
  rcases (le_of_not_gt hnot).eq_or_lt with heq | hlt
  · rw [heq, hγzero] at hpositive
    exact lt_irrefl 0 hpositive
  · have hnegative := hbefore η
      ⟨(hphase.first_mem.1.trans hphase.second_mem.1).le, hlt⟩
    exact (not_lt_of_ge hpositive.le) hnegative

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
  exact ⟨γ, ⟨hγ.1, fullTiltedSupportQuarterPair_first_floor_lt_second_phase
    hU hm haffine hρ hρ0 hρK heq hheight hunit hphase hzero hbefore⟩,
    hzero, hbefore, hzeroX, hX⟩

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
  have hJR : horizontalRight U - capWidth U / 4 = C := by
    unfold capWidth
    rw [hl, hr]
    ring
  have hgeometry (t : ℝ) (ht : t ∈ Ioc α η) :=
    fullTiltedSupportQuarterPair_core_phase_positive_and_right
      hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh hheight hlow hunit hphase ht
  have hpositive := fullTiltedSupportQuarterPair_companion_floor_pos_at_second_phase
    hU hm haffine hρ hρ0 hρK heq hheight hunit hphase
  obtain ⟨hpAC, _hqAC, hpD⟩ := fullTiltedSupportQuarterPair_corner_calculus
    hU hm haffine hρ hρ0 hρK heq
  obtain ⟨_hBx, _hBy, _hDx, hyAC, hyD⟩ := fullTiltedSupportQuarterPair_tangent_calculus
    hU hm haffine hρ hρ0 hρK heq
  have hsub : uIcc τ η ⊆ uIcc (0 : ℝ) (Real.pi / 2) := by
    rw [uIcc_of_le hτ.2.le, uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    exact Icc_subset_Icc hτq.1.le hphase.second_mem.2.le
  have hinterval : Ioo τ η ⊆ Ioo (0 : ℝ) (Real.pi / 2) :=
    Ioo_subset_Ioo hτq.1.le hphase.second_mem.2.le
  have hode : ∀ᵐ t ∂volume.restrict (Ioo τ η),
      HasDerivAt p (ρ t - 1 - q t) t ∧
        HasDerivAt (fun s => (D s).2) ((1 - v t) * Real.sin t) t := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hinterval hpD,
      ae_restrict_of_ae_restrict_of_subset hinterval hyD] with t hp hy
    exact ⟨hp.1, hy.2.2.2⟩
  by_contra hnot
  have hτγ : τ ≤ γ := le_of_not_gt hnot
  have hinitial : ∀ s ∈ Icc (0 : ℝ) τ, (D s).2 ≤ 0 := by
    intro s hs
    rcases (hs.2.trans hτγ).eq_or_lt with heq | hlt
    · simpa only [heq, hγzero] using (le_rfl : (0 : ℝ) ≤ 0)
    · exact (hbefore s ⟨hs.1, hlt⟩).le
  have hvisible : ∀ b ∈ Ioc τ η, (∀ s ∈ Icc τ b, (D s).2 ≤ 0) →
      ∀ᵐ t ∂volume.restrict (Ioo τ b), Analysis.firstFloorVisibleLaw p q ρ v δ t := by
    intro b hb hnonpos
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hb.2) hsource]
      with t ht hs
    have htphase : t ∈ Ioo α η := ⟨hτ.1.trans ht.1, ht.2.trans_le hb.2⟩
    have htq : t ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨hphase.first_mem.1.trans htphase.1, htphase.2.trans hphase.second_mem.2⟩
    have hgeo := hgeometry t (Ioo_subset_Ioc_self htphase)
    have hfloor : ∀ r ∈ Ioc (0 : ℝ) t, (D r).2 ≤ 0 := by
      intro r hrI
      by_cases hrτ : r ≤ τ
      · exact hinitial r ⟨hrI.1.le, hrτ⟩
      · exact hnonpos r ⟨(lt_of_not_ge hrτ).le, hrI.2.trans ht.2.le⟩
    have hcontact := fullTiltedSupportQuarterPair_core_contact_of_initial_floor_nonpos
      hU hm haffine hρ hρ0 hρK heq hunit htq (hphase.core_signs t htphase).1
      hgeo.2 (by rw [hJR]; exact hgeo.1.le) hfloor
    exact hs hcontact.1 hcontact.2
  have hboundary : (D τ).2 = 0 → ∃ b ∈ Ioc τ η,
      ∀ᵐ t ∂volume.restrict (Ioo τ b), Analysis.firstFloorVisibleLaw p q ρ v δ t := by
    intro _hzero
    have hgeo := hgeometry τ (Ioo_subset_Ioc_self hτ)
    have hevent := fullTiltedSupportQuarterPair_core_contact_eventually_of_initial_floor_nonpos
      hU hm haffine hρ hρ0 hρK heq hunit hτq (by rw [hpτ]; norm_num)
      (hphase.core_signs τ hτ).2 hgeo.2 (by rw [hJR]; exact hgeo.1)
      (fun s hs => hinitial s ⟨hs.1.le, hs.2⟩)
    obtain ⟨l, u, hτlu, hlocal⟩ := mem_nhds_iff_exists_Ioo_subset.mp hevent
    obtain ⟨b, hτb, hb⟩ := exists_between (lt_min hτlu.2 hτ.2)
    have hbη : b ≤ η := (hb.trans_le (min_le_right _ _)).le
    refine ⟨b, ⟨hτb, hbη⟩, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hbη) hsource]
      with t ht hs
    have hcontact := hlocal (show t ∈ Ioo l u from
      ⟨hτlu.1.trans ht.1, ht.2.trans (hb.trans_le (min_le_left _ _))⟩)
    exact hs hcontact.2.1 hcontact.2.2
  exact Analysis.firstFloor_bad_entry_trapping hτq.1.le hτ.2
    (by linarith only [hphase.second_mem.2, Real.pi_pos])
    (hpAC.mono hsub) (hyAC.mono hsub) hpτ.le
    (hinitial τ ⟨hτq.1.le, le_rfl⟩) hpositive hode hvisible hboundary

/-- A positive literal cut wall already places the core strictly to the
right of the actual low-wing zero. This does not require any contact or
companion tangent monotonicity. -/
theorem fullTiltedSupportQuarterPair_companionZero_lt_positive_core {t : ℝ}
    (ht : t ∈ Ioo 0 (Real.pi / 2)) (hy : 0 < (Z t).2) :
    companionZero V < (Z t).1 := by
  by_contra hnot
  have hwall := hU.isCap_fullLeftCompanion.secondWall_nonpos_of_le_companionZero
    (le_of_not_gt hnot) ht
  rw [(fullTiltedSupportQuarterPair_walls_core
    hU hm haffine hρ hρ0 hρK heq ht).2] at hwall
  exact (not_le_of_gt hy) hwall

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
    rw [middleHalfInterval, hl, hr]
    congr 1 <;> ring
  have hJL : horizontalLeft U + capWidth U / 4 = -C := by
    unfold capWidth
    rw [hl, hr]
    ring
  have hJR : horizontalRight U - capWidth U / 4 = C := by
    unfold capWidth
    rw [hl, hr]
    ring
  have hdry := hU.firstUnit_dry_left_and_overhang_bounds
    hl hr hC0 hC1 hh0 hh1 hheight (by simpa only [hmid] using haffine)
    hlow hhigh hρ hρ0 hρK heq hκ hunit
  have hzero : -C < companionZero V := by
    rw [hJL]
    linarith only [hdry.1, hdry.2.2.1]
  have hgeo := fullTiltedSupportQuarterPair_core_phase_positive_and_right
    hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh1.le hheight hlow hunit hphase ht
  have htq : t ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨hphase.first_mem.1.trans ht.1, ht.2.trans_lt hphase.second_mem.2⟩
  have hleft := hzero.trans (fullTiltedSupportQuarterPair_companionZero_lt_positive_core
    hU hm haffine hρ hρ0 hρK heq htq hgeo.2)
  have hright : (Z t).1 ≤ horizontalRight U - capWidth U / 4 := by
    rw [hJR]
    exact hgeo.1.le
  have hpost := fullTiltedSupportQuarterPair_positive_core_after_affine
    hU hm haffine hρ hρ0 hρK heq (by rw [hJR]; exact hhigh) htq hgeo.2 hright
  exact ⟨⟨hleft, hgeo.1⟩, hgeo.2,
    mem_regularCornerDomain_of_after_nonneg_affine hm htq hpost,
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
  have hregular : Ioo τ η ⊆ regularCornerDomain m := by
    intro t ht
    exact (hgeometry t ⟨hτ.1.trans ht.1, ht.2.le⟩).2.2.1
  have hBmono := (fullTiltedSupportQuarterPair_first_tangent_order
    hU hm haffine hρ hρ0 hρK heq hunit).1
  apply fullTiltedSupportQuarterPair_first_floor_lt_bad_entry_of_visible_law
    hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh1.le hheight hlow hunit
    hphase hτ hpτ hγzero hbefore
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae_restrict_of_subset hregular hsource] with t ht hs
  intro hcontact hunique
  have htphase : t ∈ Ioo α η := ⟨hτ.1.trans ht.1, ht.2⟩
  have hgeo := hgeometry t (Ioo_subset_Ioc_self htphase)
  have hBt := hBmono hβ
    ⟨(hphase.first_mem.1.trans htphase.1).le, htphase.2.le.trans hphase.second_mem.2.le⟩
    (hβτ.trans ht.1.le)
  rw [hβx] at hBt
  exact hs (hphase.core_signs t htphase).1 (hphase.core_signs t htphase).2
    hgeo.1 hgeo.2.1 hBt hcontact hunique

end ActualPair

end AmbidextrousSofa
