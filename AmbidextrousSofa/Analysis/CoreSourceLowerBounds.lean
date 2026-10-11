module

public import AmbidextrousSofa.Analysis.CoreContactGeometry
public import AmbidextrousSofa.Analysis.FirstSourceDensity
public import AmbidextrousSofa.Analysis.FirstUnitPhases

@[expose] public section

/-!
# First-source lower bounds on the actual tilted core prefix

The actual top projection keeps the whole opposite-sign phase over the
open middle interval and strictly above the floor; its corner lies after
the affine normal, which supplies the regular-domain condition needed by
source differentiation. On a companion-unit prefix each corner is the
unique contact over its abscissa, and every contact piece is constructed
from the literal support pair. The final lower bounds have no supplied
contact, occupation, or flux certificate. The charged bound stops at the
actual middle crossing.
-/

open Set MeasureTheory

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

/-- The whole opposite-sign phase, including its last endpoint, has a
positive corner over the open middle interval after the affine normal.
No bound on the companion density is used. -/
theorem FirstUnitSetting.core_phase_geometry {C h α η t : ℝ} (P : FirstUnitSetting U m ρ C h)
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) (ht : t ∈ Ioc α η) :
    (Z t).1 ∈ Ioo (-C) C ∧ 0 < (Z t).2 ∧ t ∈ regularCornerDomain m := by
  have htq : t ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨hphase.first_mem.1.trans ht.1, ht.2.trans_lt hphase.second_mem.2⟩
  -- A negative first momentum keeps the corner above the first tangent, hence the floor.
  have hy : 0 < (Z t).2 := by
    rw [innerCorner_snd_eq_firstTangent (F).f (F).g (F).fD]
    exact sub_pos.mpr ((mul_neg_of_neg_of_pos (hphase.first_neg ⟨ht.1, htq.2.le⟩)
      (sin_cos_pos_of_mem_quarter htq).2).trans_le
        (fullTiltedSupportQuarterPair_first_tangent_nonneg hU hm haffine hρ hρ0 hρK heq P.hheight
          P.hunit (Ioo_subset_Icc_self htq)))
  -- The corner starts at the first tangent point, left of `C`, and moves left.
  have hright : (Z t).1 < C := by
    have hZα : (Z α).1 ≤ C := by
      rw [innerCorner_eq_firstTangent_of_momentum_zero hphase.first_zero]
      exact not_lt.mp fun hB => (P.first_momentum_neg_after_middle hU hm haffine hρ hρ0 hρK heq
        (Ioo_subset_Icc_self hphase.first_mem) hB.le).2.ne hphase.first_zero
    exact (fullTiltedSupportQuarterPair_core_strictAntiOn hU hm haffine hρ hρ0 hρK heq
      hphase.first_mem.1.le hphase.second_mem.2.le hphase.core_signs
      ⟨le_rfl, hphase.second_mem.1.le⟩ ⟨ht.1.le, ht.2⟩ ht.1).trans_le hZα
  -- A positive cut wall places the corner right of the low-wing zero, hence of `-C`.
  have hleft : companionZero V < (Z t).1 := lt_of_not_ge fun h => hy.not_ge
    ((fullTiltedSupportQuarterPair_walls_core hU hm haffine hρ hρ0 hρK heq htq).2 ▸
      hU.isCap_fullLeftCompanion.secondWall_nonpos_of_le_companionZero h htq)
  rw [P.left_quarter] at hleft
  obtain ⟨hT, hTz, -⟩ := P.top_overhang hU hm haffine hρ hρ0 hρK heq
  exact ⟨⟨by linarith only [hT, hTz, hleft], hright⟩, hy,
    mem_regularCornerDomain_of_after_nonneg_affine hm htq
      (fullTiltedSupportQuarterPair_positive_core_after_affine hU hm haffine hρ hρ0 hρK heq
        (P.right_quarter ▸ P.hhigh) htq hy (P.right_quarter ▸ hright.le))⟩

/-- On a companion-unit prefix of the core phase, every corner is the
unique contact of the actual swept wall over its abscissa. -/
theorem FirstUnitSetting.unique_core_contact_on_prefix {C h α η τ t : ℝ}
    (P : FirstUnitSetting U m ρ C h) (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (hτη : τ ≤ η) (hcompanion : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) τ), v s ≤ 1)
    (ht : t ∈ Ioo α τ) :
    t ∈ regularCornerDomain m ∧ (Z t).1 ∈ Ioo (-C) C ∧ 0 < (Z t).2 ∧
      UniqueNicheContact hU.isCap (Z t) t := by
  have htphase : t ∈ Ioo α η := ⟨ht.1, ht.2.trans_le hτη⟩
  have hgeo := P.core_phase_geometry hU hm haffine hρ hρ0 hρK heq hphase
    (Ioo_subset_Ioc_self htphase)
  exact ⟨hgeo.2.2, hgeo.1, hgeo.2.1, fullTiltedSupportQuarterPair_core_contact
    hU hm haffine hρ hρ0 hρK heq ⟨(hphase.first_mem.1.trans (ht.1.trans ht.2)).le,
      hτη.trans hphase.second_mem.2.le⟩ P.hunit hcompanion ⟨hphase.first_mem.1.trans ht.1, ht.2⟩
    (hphase.core_signs t htphase).1 (hphase.core_signs t htphase).2 hgeo.2.1
    (P.right_quarter ▸ hgeo.1.2.le)⟩

theorem FirstUnitSetting.first_source_core_piece {C h α η τ s t : ℝ}
    (P : FirstUnitSetting U m ρ C h) (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (hτη : τ ≤ η) (hcompanion : ∀ᵐ r ∂volume.restrict (Ioo 0 τ), v r ≤ 1)
    (hs : α < s) (hst : s < t) (ht : t < τ) : FirstSourceCorePiece hU.isCap Z s t := by
  have hcore (r : ℝ) (hr : r ∈ Icc s t) := P.unique_core_contact_on_prefix
    hU hm haffine hρ hρ0 hρK heq hphase hτη hcompanion ⟨hs.trans_le hr.1, hr.2.trans_lt ht⟩
  have hsI : s ∈ Icc s t := left_mem_Icc.mpr hst.le
  have htI : t ∈ Icc s t := right_mem_Icc.mpr hst.le
  have hIVT (x : ℝ) (hx : x ∈ Ioo (Z t).1 (Z s).1) : ∃ r ∈ Icc s t, (Z r).1 = x :=
    intermediate_value_Icc' hst.le ((fullTiltedSupportQuarterPair_core_continuous
      hU hm haffine hρ hρ0 hρK heq).1.mono fun r hr => ⟨(hphase.first_mem.1.trans
        (hs.trans_le hr.1)).le, (hr.2.trans_lt ht).le.trans (hτη.trans hphase.second_mem.2.le)⟩)
      (Ioo_subset_Icc_self hx)
  refine ⟨fullTiltedSupportQuarterPair_core_strictAntiOn hU hm haffine hρ hρ0 hρK heq
      hphase.first_mem.1.le hphase.second_mem.2.le hphase.core_signs
      ⟨hs.le, (hst.trans ht).le.trans hτη⟩ ⟨(hs.trans hst).le, ht.le.trans hτη⟩ hst,
    P.left_quarter ▸ (hcore t htI).2.1.1.le, P.right_quarter ▸ (hcore s hsI).2.1.2.le,
    (hcore s hsI).2.2.2.1, (hcore t htI).2.2.2.1, fun x hx => ?_, fun x hx a ha hmax => ?_⟩
  · obtain ⟨r, hr, rfl⟩ := hIVT x hx
    exact (hcore r hr).2.2.2.1 ▸ (hcore r hr).2.2.1
  · obtain ⟨r, hr, rfl⟩ := hIVT x hx
    rw [(hcore r hr).2.2.2.2 a ha hmax]
    exact ⟨hr.1.lt_of_ne (by rintro rfl; exact lt_irrefl _ hx.2),
      hr.2.lt_of_ne (by rintro rfl; exact lt_irrefl _ hx.1)⟩

theorem FirstUnitSetting.first_source_charged_pieces {C h α η τ β s t : ℝ}
    (P : FirstUnitSetting U m ρ C h) (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (hτη : τ ≤ η) (hcompanion : ∀ᵐ r ∂volume.restrict (Ioo 0 τ), v r ≤ 1)
    (hβ : β ∈ Icc 0 (Real.pi / 2)) (hβx : (B β).1 = C)
    (hs : α < s) (hst : s < t) (ht : t < min β τ) :
    FirstSourceChargedPieces hU.isCap B Z s t := by
  have htτ := ht.trans_le (min_le_right _ _)
  have hsub (r : ℝ) (hr : r ∈ Icc s t) : r ∈ Ioo α η :=
    ⟨hs.trans_le hr.1, (hr.2.trans_lt htτ).trans_le hτη⟩
  have hopen (r : ℝ) (hr : r ∈ Icc s t) : r ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨hphase.first_mem.1.trans (hsub r hr).1, (hsub r hr).2.trans hphase.second_mem.2⟩
  have hsI : s ∈ Icc s t := left_mem_Icc.mpr hst.le
  have htI : t ∈ Icc s t := right_mem_Icc.mpr hst.le
  have hB := (fullTiltedSupportQuarterPair_first_tangent_order
    hU hm haffine hρ hρ0 hρK heq P.hunit).1
  have hp (r : ℝ) (hr : r ∈ Icc s t) := (hphase.core_signs r (hsub r hr)).1
  have hcontact (r : ℝ) (hr : r ∈ Icc s t) :=
    fullTiltedSupportQuarterPair_niche_first_tangency hU hm haffine hρ hρ0 hρK heq
      P.hunit (hopen r hr) (hp r hr).le
      (fullTiltedSupportQuarterPair_first_tangent_nonneg hU hm haffine hρ hρ0 hρK heq
        P.hheight P.hunit (Ioo_subset_Icc_self (hopen r hr)))
  have hy (r : ℝ) (hr : r ∈ Icc s t) (hx : (B r).1 < (B t).1) : 0 < (B r).2 :=
    fullTiltedSupportQuarterPair_first_tangent_height_pos_of_abscissa_lt hU hm haffine hρ hρ0
      hρK heq P.hheight P.hunit (Ioo_subset_Icc_self (hopen r hr)) (hopen t htI) hr.2 hx
  have hIVT (x : ℝ) (hx : x ∈ Ioo (B s).1 (B t).1) : ∃ r ∈ Icc s t, (B r).1 = x :=
    intermediate_value_Icc hst.le ((fullTiltedSupportQuarterPair_tangent_calculus
      hU hm haffine hρ hρ0 hρK heq).1.continuousOn.mono
        fun r hr => Icc_subset_uIcc (Ioo_subset_Icc_self (hopen r hr))) (Ioo_subset_Icc_self hx)
  refine ⟨P.first_source_core_piece hU hm haffine hρ hρ0 hρK heq hphase hτη hcompanion hs hst htτ,
    hB (Ioo_subset_Icc_self (hopen s hsI)) (Ioo_subset_Icc_self (hopen t htI)) hst.le,
    by linarith [innerCorner_fst_eq_firstTangent (F).f (F).g (F).fD s,
      mul_neg_of_neg_of_pos (hp s hsI) (sin_cos_pos_of_mem_quarter (hopen s hsI)).1],
    P.right_quarter ▸ hβx ▸ hB (Ioo_subset_Icc_self (hopen t htI)) hβ
      (ht.le.trans (min_le_left _ _)),
    hcontact s hsI, hcontact t htI, fun x hx => ?_, fun x hx a ha hmax => ?_⟩
  · obtain ⟨r, hr, rfl⟩ := hIVT x hx
    exact hcontact r hr ▸ hy r hr hx.2
  · obtain ⟨r, hr, rfl⟩ := hIVT x hx
    have hangle := fullTiltedSupportQuarterPair_first_tangent_abscissa_of_maximizing_angle
      hU hm haffine hρ hρ0 hρK heq P.hunit (hopen r hr) (hp r hr).le (hy r hr hx.2) ha hmax
    exact ⟨lt_of_not_ge fun hle => hx.1.not_ge
        (hangle.2 ▸ hB (Ioo_subset_Icc_self hangle.1) (Ioo_subset_Icc_self (hopen s hsI)) hle),
      lt_of_not_ge fun hle => hx.2.not_ge
        (hangle.2 ▸ hB (Ioo_subset_Icc_self (hopen t htI)) (Ioo_subset_Icc_self hangle.1) hle)⟩

/-- The core and charged source lower bounds on a companion-unit prefix of the core phase. -/
theorem FirstUnitSetting.ae_first_density_ge_on_prefix {C h α η τ β : ℝ}
    (P : FirstUnitSetting U m ρ C h) (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (hτη : τ ≤ η) (hcompanion : ∀ᵐ r ∂volume.restrict (Ioo 0 τ), v r ≤ 1)
    (hβ : β ∈ Icc 0 (Real.pi / 2)) (hβx : (B β).1 = C) :
    (∀ᵐ t ∂volume.restrict (Ioo α τ), q t ≤ ρ t) ∧
      ∀ᵐ t ∂volume.restrict (Ioo α (min β τ)), 1 + q t ≤ 2 * ρ t := by
  have hregular : Ioo α τ ⊆ regularCornerDomain m := fun t ht =>
    (P.core_phase_geometry hU hm haffine hρ hρ0 hρK heq hphase
      ⟨ht.1, (ht.2.trans_le hτη).le⟩).2.2
  exact ⟨fullTiltedSupportQuarterPair_ae_first_density_ge_core hU hm haffine hρ hρ0 hρK heq
      P.hheight hregular fun _ _ => P.first_source_core_piece hU hm haffine hρ hρ0 hρK heq
        hphase hτη hcompanion,
    fullTiltedSupportQuarterPair_ae_first_density_ge_charged hU hm haffine hρ hρ0 hρK heq
      P.hheight ((Ioo_subset_Ioo_right (min_le_right _ _)).trans hregular)
      fun _ _ => P.first_source_charged_pieces hU hm haffine hρ hρ0 hρK heq
        hphase hτη hcompanion hβ hβx⟩

end ActualPair

end AmbidextrousSofa
