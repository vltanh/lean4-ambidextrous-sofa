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
this removes the collapsed top from the whole remaining tilted range.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem fullTiltedSupportQuarterPair_companion_unit_of_collapsed_top_small_width
    {U : Set Plane} (hU : IsFullCapMaximizer U)
    {C m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ}
    (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 0 < C) (hC1 : C ≤ 2 / 3) (hmpos : 0 < m) (hsmall : C + m < 1)
    (hheight : capHeight U = 1) (hhigh : capRoof U C = 1)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (htop : (MovingSofaOptimality.vminus U (Real.pi / 2)).1 = C) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      leftCompanionWingDensity m ρ (t + Real.pi / 2) ≤ 1 := by
  have D := fullTiltedSupportQuarterPair_reflected_dynamics
    hU hm haffine hρ hρ0 hρK heq hl hr hC0 hsmall hheight hhigh hκ
  have hvalues := fullTiltedSupportQuarterPair_reflected_initial_values
    hU hm haffine hρ hρ0 hρK heq hl hmpos hheight
  have hactive := (ae_restrict_iff' measurableSet_Ioo).mp (D.ae_unit_of_second_le_one
    (hvalues.1 ▸ (hU.isCap.inStrip (capRoof_mem hU.isCap.isCompact
      (horizontalLeft_mem hU.isCap.nonempty hU.isCap.isCompact))).2)
    (by rw [hvalues.2, htop]; linarith only [hC1]))
  have hzero := (ae_restrict_iff' measurableSet_Ioo).mp
    (fullTiltedSupportQuarterPair_reflected_zero_after_active
      hU hm haffine hρ hρ0 hρK heq hl hr hC0 hsmall hheight hhigh)
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

/-- First-unit curvature and the actual spatial maximum give strictly
positive top overhang at every remaining width. -/
theorem IsFullCapMaximizer.firstUnit_top_overhang_pos
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh0 : 0 < h) (hh1 : h < 17 / 50)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1)
    {ρ : ℝ → ℝ} {K : ℝ} (hρ : Measurable ρ)
    (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1) :
    0 < (MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C := by
  by_cases hwide : 2 / 3 ≤ C
  · exact hU.tilted_top_overhang_pos hl hr hwide hC1 hh0 hh1 hheight haffine hlow hhigh
  have hC : 0 < C := by linarith only [hC0]
  have hprojection := hU.firstUnit_top_projection_eq
    hl hr hC0 hC1 hh0 hh1 hheight haffine hlow hhigh hρ hρ0 hρK heq hunit
  by_contra hnot
  -- A collapsed top forces `vminus = C` and a low-wing zero left of `-C`.
  have hz : companionZero (leftCompanionCap U (-C)) ≤ -C := by
    linarith only [le_max_left (C + companionZero (leftCompanionCap U (-C))) 0, hprojection,
      not_lt.mp hnot]
  have hT0 : (MovingSofaOptimality.vminus U (Real.pi / 2)).1 = C := by
    linarith only [le_max_right (C + companionZero (leftCompanionCap U (-C))) 0, hprojection,
      not_lt.mp hnot]
  have hm := positive_affine_slope_of_middle_heights hC hh0 haffine hlow hhigh
  have hsmall : C + m < 1 := by
    rw [show m = h / (2 * C) by
      rw [eq_div_iff (mul_pos two_pos hC).ne']
      linarith only [haffine (-C) ⟨le_rfl, by linarith only [hC]⟩,
        haffine C ⟨by linarith only [hC], le_rfl⟩, hlow, hhigh]]
    exact canonical_width_add_slope_lt_one hC0.le hC1 hh1
  have haff : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c := fun x hx => haffine x (by
    rw [middleHalfInterval, hl, hr] at hx; constructor <;> linarith only [hx.1, hx.2])
  have hproj : horizontalProjection U = Icc (-2 * C) (2 * C) := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex, hl, hr]
  have ha : -C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith only [hC]
  have hb : C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith only [hC]
  have hV := hU.isCap.leftCompanionCap ha
  have hVtop := hU.isCap.top_leftCompanionCap_of_positive_affine ha hb (by linarith only [hC]) hm
    haffine
  rw [hlow] at hVtop
  have hVL : 0 < capRoof (leftCompanionCap U (-C)) (horizontalLeft (leftCompanionCap U (-C))) := by
    rw [horizontalLeft_leftCompanionCap hU.isCap ha,
      hU.isCap.capRoof_leftCompanionCap ha ⟨le_rfl, by rw [hl]; linarith only [hC]⟩]
    exact (hU.endpoint_heights_pos_of_affine hheight ⟨m, c, haff⟩).2
  obtain ⟨-, -, t, ht, -, -, -, hwall⟩ :=
    hV.exists_companionZero_contact (hVtop.1 ▸ sub_lt_self 1 hh0) hVL
  have hcut := hU.leftCompanion_density_of_regular_companion haff
    (restrict_withDensity_of_subset heq (measurableSet_regularCompanionDomain m)
      (regularCompanionDomain_subset_regularCurvatureDomain m))
  rw [show horizontalLeft U + capWidth U / 4 = -C by rw [capWidth, hl, hr]; ring] at hcut
  have hkernel := hV.secondWall_le_height_sub_one_of_unit_prefix
    (measurable_leftCompanionWingDensity hρ m)
    (fun s => (leftCompanionWingDensity_bounds hρ0 hρK s).1)
    (fun s => (leftCompanionWingDensity_bounds hρ0 hρK s).2) hcut ht
    (fun s hs => ⟨hs.1, by linarith only [hs.2, ht.2]⟩)
    (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl ht.2.le)
      (fullTiltedSupportQuarterPair_companion_unit_of_collapsed_top_small_width hU hm.le haff
        hρ hρ0 hρK heq hl hr hC (not_le.mp hwide).le hm hsmall hheight hhigh hκ hT0))
  simp only [hVtop] at hkernel
  -- The companion wall is monotone in the abscissa, so its zero contact sits below `-C`.
  have hs := (Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith only [ht.2, Real.pi_pos])).le
  have hwallle : secondWall (leftCompanionCap U (-C)) t (companionZero (leftCompanionCap U (-C)))
      ≤ secondWall (leftCompanionCap U (-C)) t (-C) :=
    div_le_div_of_nonneg_right (by linarith only [mul_le_mul_of_nonneg_right hz hs])
      (Real.cos_pos_of_mem_Ioo ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩).le
  linarith only [hwallle, hwall, hkernel, hh0]

theorem IsFullCapMaximizer.firstUnit_dry_left_and_overhang_bounds
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh0 : 0 < h) (hh1 : h < 17 / 50)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1)
    {ρ : ℝ → ℝ} {K : ℝ} (hρ : Measurable ρ)
    (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1) :
    let T := (MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C
    0 < T ∧ sweptNiche U (Real.pi / 2) (-C) = 0 ∧
      T = C + companionZero (leftCompanionCap U (-C)) ∧
      T ≤ Real.sqrt (h * (2 - h)) ∧
      T ≤ Real.sqrt (1 - capRoof U (horizontalLeft U) ^ 2) - C ∧ T < 1 - C := by
  intro T
  have hT : 0 < T := hU.firstUnit_top_overhang_pos
    hl hr hC0 hC1 hh0 hh1 hheight haffine hlow hhigh hρ hρ0 hρK heq hκ hunit
  have hprojection : T = max (C + companionZero (leftCompanionCap U (-C))) 0 :=
    hU.firstUnit_top_projection_eq hl hr hC0 hC1 hh0 hh1 hheight haffine hlow hhigh
      hρ hρ0 hρK heq hunit
  have hC : 0 < C := by linarith only [hC0]
  have hproj : horizontalProjection U = Icc (-2 * C) (2 * C) := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex, hl, hr]
  have ha : -C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith only [hC]
  have hb : C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith only [hC]
  have hV := hU.isCap.leftCompanionCap ha
  have hVL : 0 < capRoof (leftCompanionCap U (-C)) (horizontalLeft (leftCompanionCap U (-C))) := by
    rw [horizontalLeft_leftCompanionCap hU.isCap ha,
      hU.isCap.capRoof_leftCompanionCap ha ⟨le_rfl, by rw [hl]; linarith only [hC]⟩]
    linarith only [(hU.tilted_left_endpoint_height_bounds hl hr hC hC1 hh0.le hh1 hheight haffine
      hlow hhigh).1]
  have hz : -C < companionZero (leftCompanionCap U (-C)) := by
    by_contra! hz
    rw [max_eq_right (by linarith only [hz])] at hprojection
    linarith only [hprojection, hT]
  have hTeq : T = C + companionZero (leftCompanionCap U (-C)) :=
    hprojection.trans (max_eq_left (by linarith only [hz]))
  have hzlow := hV.companionZero_le_point (hlow ▸ hU.isCap.rightRoof_mem_leftCompanionCap ha)
  have hzleft := hV.companionZero_le_point (⟨capRoof_mem hU.isCap.isCompact
    (horizontalLeft_mem hU.isCap.nonempty hU.isCap.isCompact), le_rfl,
      by rw [hl]; linarith only [hC]⟩ :
      (horizontalLeft U, capRoof U (horizontalLeft U)) ∈ leftCompanionCap U (-C))
  simp only [rightCircleAbscissa, circleHeight, show 1 - (1 - h) ^ 2 = h * (2 - h) by ring]
    at hzlow hzleft
  refine ⟨hT, hU.isCap.sweptNiche_eq_zero_of_le_low_wing_zero ha hb (by linarith only [hC])
    haffine (by linarith only [hC]) hz.le, hTeq, by linarith only [hTeq, hzlow],
    by linarith only [hTeq, hzleft, hl], ?_⟩
  linarith only [hTeq, hl, horizontalLeft_leftCompanionCap hU.isCap ha,
    hV.companionZero_lt_left_add_one (by
      rw [(hU.isCap.top_leftCompanionCap_of_positive_affine ha hb (by linarith only [hC])
        (positive_affine_slope_of_middle_heights hC hh0 haffine hlow hhigh) haffine).1, hlow]
      linarith only [hh0]) hVL]

end AmbidextrousSofa
