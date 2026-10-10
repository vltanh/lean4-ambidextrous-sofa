import AmbidextrousSofa.Analysis.FirstUnitOccupationGeometry
import AmbidextrousSofa.Analysis.FirstUnitGeometricMoments
import AmbidextrousSofa.Analysis.FirstUnitSourceSectors
import AmbidextrousSofa.Analysis.FirstUnitFoldBudget
import AmbidextrousSofa.Analysis.FirstUnitLateWindowClosure

/-!
# Applying one common occupation law to the actual first-unit cap

All events, endpoint values, floor contacts, and displacement moments
are constructed from the actual cap. The explicit common occupation
law is the remaining measure input: the same corner coefficient must
occur in both source equations. This adapter handles both the global
companion-unit case and the first possible excess, including either
order of the final sign change and the charged-window exit.
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

local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
local notation "p" => supportP F.fD F.g
local notation "q" => supportQ F.gD F.f
local notation "v" => (fun t : ℝ => leftCompanionWingDensity m ρ (t + Real.pi / 2))
local notation "B" => firstTangentPoint F.f F.fD
local notation "D" => secondTangentPoint F.g F.gD
local notation "Z" => innerCornerPoint F.f F.g

theorem fullTiltedSupportQuarterPair_false_of_common_occupation
    {C h : ℝ} {b δ χ : ℝ → ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh0 : 0 < h) (hh1 : h < 17 / 50)
    (hmpos : 0 < m) (hsmall : C + m < 1) (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1)
    (hδm : Measurable δ)
    (hcoeff : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      0 ≤ b t ∧ 0 ≤ δ t ∧ δ t ≤ 1 ∧ 0 ≤ χ t ∧ χ t ≤ 1)
    (hbalance : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      ρ t = (1 - ρ t) * b t + q t * χ t ∧
        v t = (1 - v t) * δ t - p t * χ t)
    (hfirstFlag : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      (p t < 0 → (B t).1 ∈ Ioo (-C) C → 0 < (B t).2 →
        sweptNiche U (Real.pi / 2) (B t).1 = (B t).2 → b t = 1) ∧
      (C ≤ (B t).1 → b t = 0))
    (hvisible : ∀ᵐ t ∂volume.restrict (regularCornerDomain m),
      p t < 0 → 0 < q t → (Z t).1 ∈ Ioo (-C) C → 0 < (Z t).2 →
      sweptNiche U (Real.pi / 2) (Z t).1 = (Z t).2 →
      (∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
        fullWallClip hU.isCap.toCompactCap (Z t).1 s =
          sweptNiche U (Real.pi / 2) (Z t).1 → s = t) → χ t = 1)
    (hsecondShadow : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      ((D t).2 < 0 → δ t = 0) ∧ (1 < v t → δ t = 0)) : False := by
  obtain ⟨α, β, η, hphase, _hαδ, hαβ, hβ, hβx, hBbefore, hBafter,
    hβsin, _hβy, hcases⟩ :=
    fullTiltedSupportQuarterPair_exists_firstUnit_events
      hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh0 hh1 hmpos hsmall
      hheight hlow hhigh hκ hunit
  have hη0 : 0 < η := hphase.first_mem.1.trans hphase.second_mem.1
  have hηL : η < Real.pi / 2 := hphase.second_mem.2
  obtain ⟨γ, hγ, hγzero, hγbefore, _hzeroX, _hSX⟩ :=
    fullTiltedSupportQuarterPair_exists_first_floor_before_second_phase
      hU hm haffine hρ hρ0 hρK heq hl hr hmpos hheight hh0 hlow hunit hphase
  have hγq : γ ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hγ.1, hγ.2.trans hηL⟩
  have hpafter (t : ℝ) (ht : t ∈ Ioc α (Real.pi / 2)) : p t < 0 := by
    rcases lt_trichotomy t η with hlt | heq | hgt
    · exact (hphase.core_signs t ⟨ht.1, hlt⟩).1
    · simpa only [heq] using hphase.first_at_second
    · exact (hphase.final_signs t ⟨hgt, ht.2⟩).1
  have hβp : p β ≤ 0 := (hpafter β ⟨hαβ, hβ.2.le⟩).le
  have hmid : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]
    congr 1 <;> ring
  have haff : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c := by
    simpa only [hmid] using haffine
  have hdry := hU.firstUnit_dry_left_and_overhang_bounds
    hl hr hC0 hC1 hh0 hh1 hheight haff hlow hhigh hρ hρ0 hρK heq hκ hunit
  let T : ℝ := (Imported.vminus U (Real.pi / 2)).1 - C
  let S : ℝ := C + (D γ).1
  let z : ℝ := sweptNiche U (Real.pi / 2) C
  let eR : ℝ := capRoof U (horizontalRight U)
  let eL : ℝ := capRoof U (horizontalLeft U)
  have hTpos : 0 < T := hdry.1
  have hgeometry : T ≤ S ∧ S ≤ 1 ∧ T ≤ C :=
    fullTiltedSupportQuarterPair_floor_abscissa_bounds hU hm haffine hρ hρ0 hρK heq
      hl hr hC0 hC1 hh0 hh1 hheight hlow hhigh hunit
      (by linarith only [hdry.1]) hγq hγzero
  obtain ⟨hS, hh, hT, hz⟩ := fullTiltedSupportQuarterPair_first_floor_right_moments
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hheight hlow hunit hβ
      (Ioo_subset_Icc_self hγq) hβx hβp hγzero
  have hEP := hU.tilted_endpoint_laws hl hr hheight haff hlow hhigh
  rw [hdry.2.1] at hEP
  have hR : eR = 1 / 2 + h / 4 + 3 * z / 4 := by
    dsimp only [eR, z]
    linarith only [hEP.1]
  have hL : eL = 1 / 2 - 3 * h / 4 - z / 4 := by
    dsimp only [eL, z]
    linarith only [hEP.2]
  have hhz : h + z ≤ 2 := by
    have heL : 0 < eL := (hU.endpoint_heights_pos_of_affine hheight ⟨m, c, haffine⟩).2
    linarith only [heL, hL, hh0]
  obtain ⟨hp0, hq0, _hD0, _hDL⟩ := fullTiltedSupportQuarterPair_initial_values
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hlow
  obtain ⟨_hB0, _hBL, _hD0, _hDL, hpLraw, hqL⟩ := fullTiltedSupportQuarterPair_tangent_traces
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hheight hlow
  have hpL : p (Real.pi / 2) = 1 - 3 * C - T := by
    dsimp only [T]
    linarith only [hpLraw]
  obtain ⟨hpAC, hqAC, hodeOpen⟩ := fullTiltedSupportQuarterPair_corner_calculus
    hU hm haffine hρ hρ0 hρK heq
  have hode : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (Real.pi / 2)),
      HasDerivAt p (ρ t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact hodeOpen
  have hu := intervalIntegrable_bounded_real_density hρ hρ0 hρK 0 (Real.pi / 2)
  have hvm : Measurable v := (measurable_leftCompanionWingDensity hρ m).comp
    (measurable_id.add_const (Real.pi / 2))
  have hv := intervalIntegrable_bounded_real_density hvm
    (fun t => (leftCompanionWingDensity_bounds (m := m) hρ0 hρK (t + Real.pi / 2)).1)
    (fun t => (leftCompanionWingDensity_bounds (m := m) hρ0 hρK (t + Real.pi / 2)).2)
    0 (Real.pi / 2)
  have hunitClosed : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (Real.pi / 2)),
      0 ≤ ρ t ∧ ρ t ≤ 1 := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact hunit.mono (fun t ht => ⟨hρ0 t, ht⟩)
  have hcoeffClosed : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (Real.pi / 2)),
      0 ≤ b t ∧ 0 ≤ δ t ∧ δ t ≤ 1 ∧ 0 ≤ χ t ∧ χ t ≤ 1 := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact hcoeff
  have hδ : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) η), 0 ≤ δ t ∧ δ t ≤ 1 :=
    (Analysis.ae_restrict_Icc_subinterval le_rfl hηL.le hcoeffClosed).mono
      (fun _ ht => ⟨ht.2.1, ht.2.2.1⟩)
  have hqnonneg : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) η), -1 ≤ q t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact fullTiltedSupportQuarterPair_q_ge_neg_one hU hm haffine hρ hρ0 hρK heq
      ⟨ht.1, ht.2.trans hηL.le⟩
  have hfloor : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) γ), δ t = 0 := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hγq.2.le) hsecondShadow]
      with t ht hs
    exact hs.1 (hγbefore t ⟨ht.1.le, ht.2⟩)
  have hsource := hU.fullTiltedSupportQuarterPair_source_controls
    hl hr (by linarith only [hC0]) hm hsmall hheight haffine hhigh hρ hρ0 hρK hκ heq
  have hfirstShadow : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      0 < p t → 0 < q t → ρ t = 0 :=
    hsource.mono (fun _ ht hp hq => (ht.2.2.1 hp hq).1)
  have hfinalShadow : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      p t < 0 → q t < 0 → v t = 0 :=
    hsource.mono (fun _ ht hp hq => (ht.2.2.2 hp hq).1)
  have hnonneg : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      0 ≤ b t ∧ 0 ≤ δ t ∧ 0 ≤ χ t :=
    hcoeff.mono (fun _ ht => ⟨ht.1, ht.2.1, ht.2.2.2.1⟩)
  have hcharged : ∀ᵐ t ∂volume.restrict (Ioo α β), b t = 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset
        (Ioo_subset_Ioo hphase.first_mem.1.le hβ.2.le) hfirstFlag] with t ht hb
    have hg := fullTiltedSupportQuarterPair_first_window_positive_contact
      hU hm haffine hρ hρ0 hρK heq hl hr hC0 hmpos hheight hlow hunit
      hphase hβ hβx hBbefore ht
    exact hb.1 hg.1 hg.2.1 hg.2.2.1 hg.2.2.2
  have hafter : ∀ᵐ t ∂volume.restrict (Ioo β (Real.pi / 2)), b t = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hβ.1.le le_rfl) hfirstFlag]
      with t ht hb
    exact hb.2 (hBafter t (Ioo_subset_Icc_self ht))
  have hprefixVisible (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (Real.pi / 2)) (hτη : τ ≤ η)
      (hcompanion : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) τ), v t ≤ 1) :
      ∀ᵐ t ∂volume.restrict (Ioo α τ), χ t = 1 := by
    have hgeometry (t : ℝ) (ht : t ∈ Ioo α τ) :=
      fullTiltedSupportQuarterPair_unique_core_contact_on_prefix
        hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh0 hh1 hheight hlow hhigh
        hκ hunit hphase hτ hτη hcompanion ht
    have hregular : Ioo α τ ⊆ regularCornerDomain m := fun t ht => (hgeometry t ht).1
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset hregular hvisible] with t ht hvis
    have hg := hgeometry t ht
    have hsign := hphase.core_signs t ⟨ht.1, ht.2.trans_le hτη⟩
    exact hvis hsign.1 hsign.2 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2
  have hregularSub : regularCornerDomain m ⊆ Ioo (0 : ℝ) (Real.pi / 2) := inter_subset_left
  have hfloorSource : ∀ᵐ t ∂volume.restrict (regularCornerDomain m),
      p t < 0 → 0 < q t → (Z t).1 ∈ Ioo (-C) C → 0 < (Z t).2 → C ≤ (B t).1 →
      sweptNiche U (Real.pi / 2) (Z t).1 = (Z t).2 →
      (∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
        fullWallClip hU.isCap.toCompactCap (Z t).1 s =
          sweptNiche U (Real.pi / 2) (Z t).1 → s = t) →
      Analysis.firstFloorVisibleLaw p q ρ v δ t := by
    filter_upwards [hvisible,
      ae_restrict_of_ae_restrict_of_subset hregularSub hbalance,
      ae_restrict_of_ae_restrict_of_subset hregularSub hcoeff,
      ae_restrict_of_ae_restrict_of_subset hregularSub hfirstFlag,
      ae_restrict_of_ae_restrict_of_subset hregularSub hsecondShadow]
      with t hvis hs hc hb hd
    intro hp hq hx hy hBx hcontact hunique
    have hχ := hvis hp hq hx hy hcontact hunique
    have hb0 := hb.2 hBx
    change ρ t = q t ∧ v t = (1 - v t) * δ t - p t ∧
      0 ≤ δ t ∧ (1 < v t → δ t = 0)
    exact ⟨by simpa only [hb0, hχ, mul_zero, zero_add, mul_one] using hs.1,
      by simpa only [hχ, mul_one] using hs.2, hc.2.1, hd.2⟩
  rcases hcases with hcompanion | ⟨τ, hτ, hpτ, _hqτ0, hqτ, _hpfirst, hprefix, _hE, hbad⟩
  · have hcompanionClosed : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (Real.pi / 2)), v t ≤ 1 := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact hcompanion
    have hvisibleCore := hprefixVisible η ⟨hη0.le, hηL.le⟩ le_rfl
      (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hηL.le) hcompanion)
    have hvisibleCharged := ae_restrict_of_ae_restrict_of_subset
      (Ioo_subset_Ioo le_rfl (min_le_right β η)) hvisibleCore
    obtain ⟨hfirst, hchargedSector, hcore, hlate, hfinal⟩ :=
      Analysis.firstUnit_source_sectors_of_common_balance hphase hαβ.le hβ.2.le
        hbalance hnonneg hfirstShadow hfinalShadow hcharged hafter hvisibleCharged
    have hcoreFull : ∀ᵐ t ∂volume.restrict (Icc (min β η) η),
        ρ t = q t ∧ v t = (1 - v t) * δ t - p t := by
      rw [← restrict_Ioo_eq_restrict_Icc] at hcore ⊢
      filter_upwards [hcore, ae_restrict_of_ae_restrict_of_subset
        (Ioo_subset_Ioo (le_min hαβ.le hphase.second_mem.1.le) le_rfl) hvisibleCore]
        with t hs hχ
      simpa only [hχ, mul_one] using hs
    exact Analysis.firstUnit_unit_companion_raw_data_impossible
      hphase.first_mem.1.le hαβ.le hphase.second_mem.1.le hβ.2.le hηL.le hγ.1.le hγ.2.le
      hpAC hqAC hu hv hδm.aestronglyMeasurable hδ hode hfirst hchargedSector hcoreFull
      hlate hfinal hphase.first_zero hphase.second_zero hunitClosed hcompanionClosed
      hfloor hqnonneg hp0 hq0 hpL hqL hR hL hS hh hT hz
      hC0 hTpos hgeometry.1 hgeometry.2.1 hgeometry.2.2 hhz hβsin
  · have hταη : τ ∈ Ioo α η := ⟨hαβ.trans hτ.1, hτ.2⟩
    have hτq : τ ∈ Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨(hβ.1.trans hτ.1).le, (hτ.2.trans hηL).le⟩
    have hvisiblePrefix := hprefixVisible τ hτq hτ.2.le hprefix
    have hvisibleCharged := ae_restrict_of_ae_restrict_of_subset
      (Ioo_subset_Ioo le_rfl ((min_le_left β η).trans hτ.1.le)) hvisiblePrefix
    obtain ⟨hfirst, hchargedSector, hcore, _hlate, hfinal⟩ :=
      Analysis.firstUnit_source_sectors_of_common_balance hphase hαβ.le hβ.2.le
        hbalance hnonneg hfirstShadow hfinalShadow hcharged hafter hvisibleCharged
    have hβη : β ≤ η := (hτ.1.trans hτ.2).le
    rw [min_eq_left hβη] at hchargedSector hcore
    rw [max_eq_right hβη] at hfinal
    have hγτ := fullTiltedSupportQuarterPair_first_floor_lt_bad_entry_of_regular_visible_law
      hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh0 hh1 hheight hlow hhigh hκ hunit
      hphase (Ioo_subset_Icc_self hβ) hβx hτ.1.le hταη hpτ hγzero hγbefore hfloorSource
    have dyn := fullTiltedSupportQuarterPair_cornerArcDynamics
      hU hm haffine hρ hρ0 hρK heq hl hr (by linarith only [hC0]) hsmall hheight hhigh hκ
    have hsourceTail : ∀ᵐ t ∂volume.restrict (Ioo τ η),
        ρ t = q t * χ t ∧ v t = (1 - v t) * δ t - p t * χ t := by
      rw [← restrict_Ioo_eq_restrict_Icc] at hcore
      exact ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hτ.1.le le_rfl) hcore
    have hrangeTail : ∀ᵐ t ∂volume.restrict (Ioo τ η),
        0 ≤ δ t ∧ δ t ≤ 1 ∧ χ t ≤ 1 :=
      (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hτq.1 hηL.le) hcoeff).mono
        (fun _ ht => ⟨ht.2.1, ht.2.2.1, ht.2.2.2.2⟩)
    obtain ⟨htail, hfold⟩ := dyn.first_bad_fold_budget hphase hταη hpτ hqτ
      hunit hprefix hfinalShadow hsourceTail hrangeTail
    have hχ := Analysis.firstUnit_core_residual_condition
      ((ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hβ.1.le hηL.le) hcoeff).mono
        (fun _ ht => ht.2.2.2.2))
      (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hαβ.le le_rfl) hvisiblePrefix)
      (fun t ht => (htail t ht).2.trans (by norm_num))
    have hprefixClosed : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) τ), v t ≤ 1 := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact hprefix
    have hvfloor := Analysis.ae_restrict_Icc_subinterval le_rfl hγτ.le hprefixClosed
    have hvbefore := Analysis.ae_restrict_Icc_subinterval le_rfl hτ.1.le hprefixClosed
    have hbadClosed : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) η), 1 < v t → q t ≤ 1 / 4 := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hηL.le) hbad
    have hcoreClosed : ∀ᵐ t ∂volume.restrict (Icc β η),
        ρ t = q t * χ t ∧ v t = (1 - v t) * δ t - p t * χ t := hcore
    exact Analysis.firstUnit_raw_momentum_data_impossible
      hphase.first_mem.1.le hαβ.le hβη hηL.le hγ.1.le hγ.2.le
      hpAC hqAC hu hv hδm.aestronglyMeasurable hδ hode hfirst hchargedSector hcoreClosed
      hχ hfinal hphase.first_zero hphase.second_zero hunitClosed hfloor hvfloor hvbefore
      hqnonneg hbadClosed (hfold.mono (fun _ ht => ht.2)) hp0 hq0 hpL hqL hR hL hS hh hT hz
      hC0 hTpos hgeometry.1 hgeometry.2.1 hgeometry.2.2 hhz hβsin

end ActualPair

end AmbidextrousSofa
