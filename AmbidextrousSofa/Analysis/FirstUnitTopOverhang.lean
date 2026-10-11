module

public import AmbidextrousSofa.Analysis.FirstUnitProjection
public import AmbidextrousSofa.Analysis.TiltedTopOverhang

@[expose] public section

/-!
# Positive top overhang throughout the first-unit width range

At the smaller widths, a collapsed top starts the reflected active arc
with second momentum at most one. Its actual clipped-energy barrier
therefore gives unit companion curvature on the entire quarter. The
literal minimum contact then contradicts the negative initial companion
kernel. Together with the reflected late-unit argument at larger widths,
this removes the collapsed top from the whole remaining tilted range. The
exact top projection then places the low-wing zero strictly right of the
low middle endpoint, where the niche therefore vanishes.
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

include hU hm haffine hρ hρ0 hρK heq in
theorem FirstUnitSetting.companion_unit_of_collapsed_top {C h : ℝ}
    (P : FirstUnitSetting U m ρ C h) (hC1 : C ≤ 2 / 3)
    (htop : (MovingSofaOptimality.vminus U (Real.pi / 2)).1 = C) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      leftCompanionWingDensity m ρ (t + Real.pi / 2) ≤ 1 := by
  have D := fullTiltedSupportQuarterPair_reflected_dynamics
    hU hm haffine hρ hρ0 hρK heq P.hl P.hr P.C_pos P.hsmall P.hheight P.hhigh P.hκ
  have hvalues := fullTiltedSupportQuarterPair_reflected_initial_values
    hU hm haffine hρ hρ0 hρK heq P.hl P.hmpos P.hheight
  have hactive := (ae_restrict_iff' measurableSet_Ioo).mp (D.ae_unit_of_second_le_one
    (hvalues.1 ▸ (hU.isCap.inStrip (capRoof_mem hU.isCap.isCompact
      (horizontalLeft_mem hU.isCap.nonempty hU.isCap.isCompact))).2)
    (by rw [hvalues.2, htop]; linarith only [hC1]))
  have hzero := (ae_restrict_iff' measurableSet_Ioo).mp
    (fullTiltedSupportQuarterPair_reflected_zero_after_active
      hU hm haffine hρ hρ0 hρK heq P.hl P.hr P.C_pos P.hsmall P.hheight P.hhigh)
  -- The reflected first density is at most one on the whole quarter.
  have hwhole : ∀ᵐ r, r ∈ Ioo (0 : ℝ) (Real.pi / 2) → reflectedFirstWingDensity m ρ r ≤ 1 := by
    filter_upwards [hactive, hzero, volume.ae_ne (fullReflectedActiveEnd m)]
      with r ha hz hne hr
    rcases lt_or_gt_of_ne hne with hrb | hbr
    · exact ha ⟨hr.1, hrb⟩
    · rw [(hz ⟨hbr, hr.2⟩).1]
      norm_num
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae
    ((volume.measurePreserving_sub_left (Real.pi / 2)).quasiMeasurePreserving.ae hwhole)]
    with t ht hu
  simpa only [reflectedFirstWingDensity, sub_sub_cancel] using
    hu ⟨by linarith only [ht.2], by linarith only [ht.1]⟩

include hU hm haffine hρ hρ0 hρK heq in
/-- First-unit curvature and the actual spatial maximum give strictly
positive top overhang at every remaining width. The overhang is `C` plus
the low-wing zero, and the niche vanishes at the low middle endpoint. -/
theorem FirstUnitSetting.top_overhang {C h : ℝ} (P : FirstUnitSetting U m ρ C h) :
    0 < (MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C ∧
      (MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C =
        C + companionZero (leftCompanionCap U (-C)) ∧
      sweptNiche U (Real.pi / 2) (-C) = 0 := by
  set z := companionZero (leftCompanionCap U (-C))
  have hC := P.C_pos
  have haff : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c := P.middle ▸ haffine
  have hprojection := P.top_projection_eq hU hm haffine hρ hρ0 hρK heq
  obtain ⟨ha, hb, hV, hVh, hVtop, hVL⟩ :=
    hU.low_wing_cut P.hl P.hr hC P.hmpos P.hheight P.hlow haffine
  have hT : 0 < (MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C := by
    by_cases hwide : 2 / 3 ≤ C
    · exact hU.tilted_top_overhang_pos P.hl P.hr hwide P.hC1 P.hh0 P.hh1 P.hheight haff P.hlow
        P.hhigh
    by_contra hnot
    -- A collapsed top forces `vminus = C` and a low-wing zero left of `-C`.
    have hz : z ≤ -C := by linarith only [le_max_left (C + z) 0, hprojection, not_lt.mp hnot]
    have hT0 : (MovingSofaOptimality.vminus U (Real.pi / 2)).1 = C := by
      linarith only [le_max_right (C + z) 0, hprojection, not_lt.mp hnot]
    obtain ⟨-, -, t, ht, -, -, -, hwall⟩ :=
      hV.exists_companionZero_contact (by rw [hVh]; linarith only [P.hh0]) hVL
    have hcut := hU.leftCompanion_density_of_regular_companion haffine
      (restrict_withDensity_of_subset heq (measurableSet_regularCompanionDomain m)
        (regularCompanionDomain_subset_regularCurvatureDomain m))
    rw [P.left_quarter] at hcut
    have hkernel := hV.secondWall_le_height_sub_one_of_unit_prefix
      (measurable_leftCompanionWingDensity hρ m)
      (fun s => (leftCompanionWingDensity_bounds hρ0 hρK s).1)
      (fun s => (leftCompanionWingDensity_bounds hρ0 hρK s).2) hcut ht
      (fun s hs => ⟨hs.1, by linarith only [hs.2, ht.2]⟩)
      (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl ht.2.le)
        (P.companion_unit_of_collapsed_top hU hm haffine hρ hρ0 hρK heq (not_le.mp hwide).le
          hT0))
    simp only [hVtop, hVh] at hkernel
    -- The companion wall is monotone in the abscissa, so its zero contact sits below `-C`.
    obtain ⟨hs, hc⟩ := quarter_sin_cos_pos ht
    have hwallle : secondWall (leftCompanionCap U (-C)) t z
        ≤ secondWall (leftCompanionCap U (-C)) t (-C) :=
      div_le_div_of_nonneg_right (by linarith only [mul_le_mul_of_nonneg_right hz hs.le]) hc.le
    linarith only [hwallle, hwall, hkernel, P.hh0]
  have hz : -C < z :=
    lt_of_not_ge fun hz => hT.ne' (hprojection.trans (max_eq_right (by linarith only [hz])))
  exact ⟨hT, hprojection.trans (max_eq_left (by linarith only [hz])),
    hU.isCap.sweptNiche_eq_zero_of_le_low_wing_zero ha hb (by linarith only [hC]) haff
      (by linarith only [hC]) hz.le⟩

end ActualPair

end AmbidextrousSofa
