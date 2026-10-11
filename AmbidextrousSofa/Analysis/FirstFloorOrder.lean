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
neighborhood. An occupation law on the regular domain then gives the
explicit local source law that feeds the trapping theorem, so the first
floor zero also precedes the bad entry.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

open scoped ActualPair

theorem FirstUnitSetting.exists_first_floor_before_second_phase {C h α η : ℝ}
    (P : FirstUnitSetting U m ρ C h) (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    ∃ γ ∈ Ioo 0 η, (D γ).2 = 0 ∧ ∀ t ∈ Ico (0 : ℝ) γ, (D t).2 < 0 := by
  have hpos : 0 < (D η).2 := innerCorner_eq_secondTangent_of_momentum_zero hphase.second_zero ▸
    (P.core_phase_geometry hU hm haffine hρ hρ0 hρK heq hphase ⟨hphase.second_mem.1, le_rfl⟩).2.1
  obtain ⟨-, -, hD0, -⟩ := fullTiltedSupportQuarterPair_initial_values
    hU hm haffine hρ hρ0 hρK heq P.hl P.hr P.hmpos P.hlow
  have hcont : ContinuousOn (fun t => -(D t).2) (Icc 0 η) :=
    ((fullTiltedSupportQuarterPair_tangent_calculus hU hm haffine hρ hρ0 hρK heq).2.2.2.1
      |>.continuousOn.mono ((Icc_subset_Icc le_rfl hphase.second_mem.2.le).trans
        Icc_subset_uIcc)).neg
  obtain ⟨γ, hγ, hγy, hbefore⟩ := exists_first_level_crossing
    (hphase.first_mem.1.trans hphase.second_mem.1) hcont
    (show (0 : ℝ) < -(D 0).2 by rw [hD0, neg_neg]; exact P.hh0)
    (show -(D η).2 ≤ 0 by linarith only [hpos])
  refine ⟨γ, ⟨hγ.1, hγ.2.lt_of_ne ?_⟩, neg_eq_zero.mp hγy, fun t ht => neg_pos.mp (hbefore t ht)⟩
  rintro rfl
  linarith only [hγy, hpos]

/-- The only analytic premise is the occupation law on the genuine
regular domain at the actual uniquely visible core. Initial-floor
visibility and the boundary neighborhood are proved from the literal
two-cap walls; the actual phase, top projection, and first-unit tangent
order supply every geometric condition of the law. -/
theorem FirstUnitSetting.first_floor_lt_bad_entry {C h α β η τ γ : ℝ} {δ : ℝ → ℝ}
    (P : FirstUnitSetting U m ρ C h) (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (hβ : β ∈ Icc (0 : ℝ) (Real.pi / 2)) (hβx : (B β).1 = C)
    (hβτ : β ≤ τ) (hτ : τ ∈ Ioo α η) (hpτ : p τ = -1)
    (hγzero : (D γ).2 = 0) (hbefore : ∀ t ∈ Ico (0 : ℝ) γ, (D t).2 < 0)
    (hsource : ∀ᵐ t ∂volume.restrict (regularCornerDomain m),
      p t < 0 → 0 < q t → (Z t).1 ∈ Ioo (-C) C → 0 < (Z t).2 → C ≤ (B t).1 →
      UniqueNicheContact hU.isCap (Z t) t → Analysis.firstFloorVisibleLaw p q ρ v δ t) :
    γ < τ := by
  have hτq : τ ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨hphase.first_mem.1.trans hτ.1, hτ.2.trans hphase.second_mem.2⟩
  have hgeometry (t : ℝ) (ht : t ∈ Ioc α η) :=
    P.core_phase_geometry hU hm haffine hρ hρ0 hρK heq hphase ht
  -- After `τ` the law holds at every uniquely visible core contact.
  have hlaw : ∀ᵐ t ∂volume.restrict (Ioo τ η),
      UniqueNicheContact hU.isCap (Z t) t → Analysis.firstFloorVisibleLaw p q ρ v δ t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae_restrict_of_subset
      (fun t ht => (hgeometry t ⟨hτ.1.trans ht.1, ht.2.le⟩).2.2) hsource] with t ht hs
    have htphase : t ∈ Ioo α η := ⟨hτ.1.trans ht.1, ht.2⟩
    have hgeo := hgeometry t (Ioo_subset_Ioc_self htphase)
    exact hs (hphase.core_signs t htphase).1 (hphase.core_signs t htphase).2 hgeo.1 hgeo.2.1
      (hβx ▸ (fullTiltedSupportQuarterPair_first_tangent_order hU hm haffine hρ hρ0 hρK heq
        P.hunit).1 hβ ⟨(hphase.first_mem.1.trans htphase.1).le,
          htphase.2.le.trans hphase.second_mem.2.le⟩ (hβτ.trans ht.1.le))
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
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hb.2) hlaw] with t ht hs
    have htphase : t ∈ Ioo α η := ⟨hτ.1.trans ht.1, ht.2.trans_le hb.2⟩
    have htq : t ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨hphase.first_mem.1.trans htphase.1, htphase.2.trans hphase.second_mem.2⟩
    have hgeo := hgeometry t (Ioo_subset_Ioc_self htphase)
    exact hs (fullTiltedSupportQuarterPair_core_contact_of_earlier_cut_walls
      hU hm haffine hρ hρ0 hρK heq P.hunit htq (hphase.core_signs t htphase).1 hgeo.2.1
      (P.right_quarter ▸ hgeo.1.2.le)
      (fullTiltedSupportQuarterPair_cut_wall_lt_core_of_initial_floor_nonpos
        hU hm haffine hρ hρ0 hρK heq htq hgeo.2.1 fun r hr => by
          rcases le_or_gt r τ with hrτ | hrτ
          exacts [hinitial r ⟨hr.1.le, hrτ⟩, hnonpos r ⟨hrτ.le, hr.2.trans ht.2.le⟩]))
  have hboundary : (D τ).2 = 0 → ∃ b ∈ Ioc τ η,
      ∀ᵐ t ∂volume.restrict (Ioo τ b), Analysis.firstFloorVisibleLaw p q ρ v δ t := by
    intro _
    have hgeo := hgeometry τ (Ioo_subset_Ioc_self hτ)
    obtain ⟨b, hb, hlocal⟩ := ((TFAE_mem_nhdsGT hτ.2 _).out 1 4).mp (nhdsWithin_le_nhds
      (fullTiltedSupportQuarterPair_core_contact_eventually_of_initial_floor_nonpos
        hU hm haffine hρ hρ0 hρK heq P.hunit hτq (by rw [hpτ]; norm_num)
        (hphase.core_signs τ hτ).2 hgeo.2.1 (P.right_quarter ▸ hgeo.1.2)
        (fun s hs => hinitial s ⟨hs.1.le, hs.2⟩)))
    refine ⟨b, hb, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hb.2) hlaw] with t ht hs
    exact hs (hlocal ht).2
  exact Analysis.firstFloor_bad_entry_trapping hτq.1.le hτ.2
    (by linarith [hphase.second_mem.2, Real.pi_pos]) (hpAC.mono hsub) (hyAC.mono hsub) hpτ.le
    (hinitial τ ⟨hτq.1.le, le_rfl⟩)
    (innerCorner_eq_secondTangent_of_momentum_zero hphase.second_zero ▸
      (hgeometry η ⟨hphase.second_mem.1, le_rfl⟩).2.1)
    ((ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hτq.1.le hphase.second_mem.2.le)
      (hpD.and hyD)).mono fun t h => ⟨h.1.1, h.2.2.2.2⟩) hvisible hboundary

end ActualPair

end AmbidextrousSofa
