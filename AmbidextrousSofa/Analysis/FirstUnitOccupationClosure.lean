module

public import AmbidextrousSofa.Analysis.FirstUnitOccupationGeometry
public import AmbidextrousSofa.Analysis.FirstUnitGeometricMoments
public import AmbidextrousSofa.Analysis.FirstUnitSourceSectors
public import AmbidextrousSofa.Analysis.FirstUnitFoldBudget
public import AmbidextrousSofa.Analysis.FirstUnitLateWindowClosure

@[expose] public section

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

open scoped ActualPair

theorem fullTiltedSupportQuarterPair_false_of_common_occupation
    {C h : ℝ} {b δ χ : ℝ → ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh0 : 0 < h) (hh1 : h < 1 / 3)
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
  have P : FirstUnitSetting U m ρ C h :=
    ⟨hl, hr, hC0, hC1, hh0, hh1, hmpos, hsmall, hheight, hlow, hhigh, hκ, hunit⟩
  obtain ⟨α, η, hphase⟩ := fullTiltedSupportQuarterPair_exists_strict_sign_phases
    hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh0 hh1 hmpos hsmall hheight hlow hhigh hκ hunit
  obtain ⟨β, hαβ, hβ, hβx, hBbefore, hBafter, hβsin, hcases⟩ :=
    P.exists_firstUnit_events hU hm haffine hρ hρ0 hρK heq hphase
  have hηL : η < Real.pi / 2 := hphase.second_mem.2
  obtain ⟨γ, hγ, hγzero, hγbefore⟩ :=
    P.exists_first_floor_before_second_phase hU hm haffine hρ hρ0 hρK heq hphase
  have hγq : γ ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hγ.1, hγ.2.trans hηL⟩
  -- Scalar data: endpoint laws, traces, displacement moments and floor bounds.
  obtain ⟨hT, -, hdry⟩ := P.top_overhang hU hm haffine hρ hρ0 hρK heq
  have hgeometry := P.floor_abscissa_bounds hU hm haffine hρ hρ0 hρK heq hγq hγzero
  obtain ⟨hS, hh, hT', hz⟩ := P.first_floor_right_moments hU hm haffine hρ hρ0 hρK heq
    hβ (Ioo_subset_Icc_self hγq) hβx hγzero
  have hEP := hU.tilted_endpoint_laws hl hr hheight (P.middle ▸ haffine) hlow hhigh
  have hR : capRoof U (horizontalRight U) =
      1 / 2 + h / 4 + 3 * sweptNiche U (Real.pi / 2) C / 4 := by linarith only [hEP.1, hdry]
  have hL : capRoof U (horizontalLeft U) =
      1 / 2 - 3 * h / 4 - sweptNiche U (Real.pi / 2) C / 4 := by linarith only [hEP.2, hdry]
  have hhz : h + sweptNiche U (Real.pi / 2) C ≤ 2 := by
    linarith only [(hU.endpoint_heights_pos_of_affine hheight ⟨m, c, haffine⟩).2, hL, hh0]
  obtain ⟨hp0, hq0, -, -⟩ := fullTiltedSupportQuarterPair_initial_values
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hlow
  obtain ⟨-, -, -, hpL, hqL⟩ := fullTiltedSupportQuarterPair_tangent_traces
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hheight hlow
  -- Analytic data of the actual momenta on closed intervals.
  obtain ⟨hpAC, hqAC, hode⟩ := fullTiltedSupportQuarterPair_corner_calculus
    hU hm haffine hρ hρ0 hρK heq
  rw [restrict_Ioo_eq_restrict_Icc] at hode
  have hIcc {a b : ℝ} {Q : ℝ → Prop} (h : ∀ᵐ t ∂volume.restrict (Ioo a b), Q t) :
      ∀ᵐ t ∂volume.restrict (Icc a b), Q t := by rwa [← restrict_Ioo_eq_restrict_Icc]
  have hu := intervalIntegrable_bounded_real_density hρ hρ0 hρK 0 (Real.pi / 2)
  have hv : IntervalIntegrable v volume 0 (Real.pi / 2) := intervalIntegrable_bounded_real_density
    ((measurable_leftCompanionWingDensity hρ m).comp (measurable_add_const _))
    (fun _ => (leftCompanionWingDensity_bounds hρ0 hρK _).1)
    (fun _ => (leftCompanionWingDensity_bounds hρ0 hρK _).2) _ _
  have hunitClosed := hIcc (hunit.mono fun t ht => And.intro (hρ0 t) ht)
  have hδ := hIcc ((ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hηL.le)
    hcoeff).mono fun _ ht => And.intro ht.2.1 ht.2.2.1)
  have hqnonneg : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) η), -1 ≤ q t :=
    ae_restrict_of_forall_mem measurableSet_Icc fun t ht =>
      fullTiltedSupportQuarterPair_q_ge_neg_one hU hm haffine hρ hρ0 hρK heq
        ⟨ht.1, ht.2.trans hηL.le⟩
  have hfloor : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) γ), δ t = 0 := hIcc (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hγq.2.le) hsecondShadow]
      with t ht hs
    exact hs.1 (hγbefore t ⟨ht.1.le, ht.2⟩))
  -- The source sectors of the common occupation law.
  obtain ⟨Dyn, hshadow⟩ := P.corner_dynamics hU hm haffine hρ hρ0 hρK heq
  have hfinalShadow := hshadow.mono fun _ ht hp hq => (ht.2 hp hq).1
  have hprefixVisible (τ : ℝ) (hτη : τ ≤ η)
      (hcompanion : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) τ), v t ≤ 1) :
      ∀ᵐ t ∂volume.restrict (Ioo α τ), χ t = 1 := by
    have hgeometry (t : ℝ) (ht : t ∈ Ioo α τ) := P.unique_core_contact_on_prefix
      hU hm haffine hρ hρ0 hρK heq hphase hτη hcompanion ht
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae_restrict_of_subset
      (fun t ht => (hgeometry t ht).1) hvisible] with t ht hvis
    obtain ⟨-, hx, hy, hcontact⟩ := hgeometry t ht
    obtain ⟨hp, hq⟩ := hphase.core_signs t ⟨ht.1, ht.2.trans_le hτη⟩
    exact hvis hp hq hx hy hcontact.1 hcontact.2
  have hcompMin : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (min β η)), v t ≤ 1 := by
    rcases hcases with h | ⟨τ, hτ, -, -, h, -⟩ <;>
      refine ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl ?_) h
    exacts [(min_le_right _ _).trans hηL.le, (min_le_left _ _).trans hτ.1.le]
  obtain ⟨hfirst, hchargedSector, hcore, hlate, hfinal⟩ :=
    Analysis.firstUnit_source_sectors_of_common_balance hphase hαβ.le hβ.2.le hbalance
      (hcoeff.mono fun _ ht => ⟨ht.1, ht.2.1, ht.2.2.2.1⟩)
      (hshadow.mono fun _ ht => ht.1) hfinalShadow
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae_restrict_of_subset
          (Ioo_subset_Ioo hphase.first_mem.1.le hβ.2.le) hfirstFlag] with t ht hb
        obtain ⟨hp, hx, hy, hn⟩ := P.first_window_positive_contact
          hU hm haffine hρ hρ0 hρK heq hphase hβ hβx hBbefore ht
        exact hb.1 hp hx hy hn)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae_restrict_of_subset
          (Ioo_subset_Ioo hβ.1.le le_rfl) hfirstFlag] with t ht hb
        exact hb.2 (hBafter t (Ioo_subset_Icc_self ht)))
      (hprefixVisible (min β η) (min_le_right _ _) hcompMin)
  rcases hcases with hcompanion | ⟨τ, hτ, hpτ, hqτ, hprefix, hbad⟩
  · have hvisibleCore := hprefixVisible η le_rfl
      (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hηL.le) hcompanion)
    refine Analysis.firstUnit_unit_companion_raw_data_impossible
      hphase.first_mem.1.le hαβ.le hphase.second_mem.1.le hβ.2.le hηL.le hγ.1.le hγ.2.le
      hpAC hqAC hu hv hδm.aestronglyMeasurable hδ hode hfirst hchargedSector ?_
      hlate hfinal hphase.first_zero hphase.second_zero hunitClosed
      (hIcc hcompanion)
      hfloor hqnonneg hp0 hq0 (by linarith only [hpL]) hqL hR hL hS hh hT' hz
      hC0 hT hgeometry.1 hgeometry.2 hhz hh0.le (sweptNiche_nonneg _ _ _) hβsin
    rw [← restrict_Ioo_eq_restrict_Icc] at hcore ⊢
    filter_upwards [hcore, ae_restrict_of_ae_restrict_of_subset
      (Ioo_subset_Ioo (le_min hαβ.le hphase.second_mem.1.le) le_rfl) hvisibleCore]
      with t hs hχ
    simpa only [hχ, mul_one] using hs
  · have hταη : τ ∈ Ioo α η := ⟨hαβ.trans hτ.1, hτ.2⟩
    have hβη : β ≤ η := (hτ.1.trans hτ.2).le
    rw [min_eq_left hβη] at hchargedSector hcore
    rw [max_eq_right hβη] at hfinal
    have hγτ := P.first_floor_lt_bad_entry hU hm haffine hρ hρ0 hρK heq hphase
      (Ioo_subset_Icc_self hβ) hβx hτ.1.le hταη hpτ hγzero hγbefore (by
        filter_upwards [hvisible,
          ae_restrict_of_ae_restrict_of_subset inter_subset_left hbalance,
          ae_restrict_of_ae_restrict_of_subset inter_subset_left hcoeff,
          ae_restrict_of_ae_restrict_of_subset inter_subset_left hfirstFlag,
          ae_restrict_of_ae_restrict_of_subset inter_subset_left hsecondShadow]
          with t hvis hs hc hb hd hp hq hx hy hBx hcontact
        have hχ := hvis hp hq hx hy hcontact.1 hcontact.2
        exact show _ ∧ _ ∧ _ ∧ _ from
          ⟨by simpa only [hb.2 hBx, hχ, mul_zero, zero_add, mul_one] using hs.1,
            by simpa only [hχ, mul_one] using hs.2, hc.2.1, hd.2⟩)
    obtain ⟨htail, hfold⟩ := Dyn.first_bad_fold_budget hphase hταη hpτ hqτ hunit hprefix
      hfinalShadow
      (by rw [restrict_Ioo_eq_restrict_Icc]
          exact Analysis.ae_restrict_Icc_subinterval hτ.1.le le_rfl hcore)
      ((ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo (hβ.1.trans hτ.1).le hηL.le)
        hcoeff).mono fun _ ht => ⟨ht.2.1, ht.2.2.1, ht.2.2.2.2⟩)
    have hprefixClosed := hIcc hprefix
    exact Analysis.firstUnit_raw_momentum_data_impossible
      hphase.first_mem.1.le hαβ.le hβη hηL.le hγ.1.le hγ.2.le
      hpAC hqAC hu hv hδm.aestronglyMeasurable hδ hode hfirst hchargedSector hcore
      (Analysis.firstUnit_core_residual_condition
        ((ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hβ.1.le hηL.le) hcoeff).mono
          fun _ ht => ht.2.2.2.2)
        (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hαβ.le le_rfl)
          (hprefixVisible τ hτ.2.le hprefix))
        (fun t ht => (htail t ht).trans (by norm_num)))
      hfinal hphase.first_zero hphase.second_zero hunitClosed hfloor
      (Analysis.ae_restrict_Icc_subinterval le_rfl hγτ.le hprefixClosed)
      (Analysis.ae_restrict_Icc_subinterval le_rfl hτ.1.le hprefixClosed) hqnonneg
      (hIcc (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hηL.le) hbad))
      hfold hp0 hq0 (by linarith only [hpL]) hqL hR hL hS hh hT' hz
      hC0 hT hgeometry.1 hgeometry.2 hhz hβsin

end ActualPair

end AmbidextrousSofa
