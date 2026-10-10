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
  let F := fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
  have D := fullTiltedSupportQuarterPair_reflected_dynamics
    hU hm haffine hρ hρ0 hρK heq hl hr hC0 hsmall hheight hhigh hκ
  have hvalues := fullTiltedSupportQuarterPair_reflected_initial_values
    hU hm haffine hρ hρ0 hρK heq hl hmpos hheight
  have heL : capRoof U (horizontalLeft U) ≤ 1 :=
    (hU.isCap.inStrip (capRoof_mem hU.isCap.isCompact
      (horizontalLeft_mem hU.isCap.nonempty hU.isCap.isCompact))).2
  have hactive := D.ae_unit_of_second_le_one
    (by rw [hvalues.1]; exact heL)
    (by rw [hvalues.2, htop]; linarith only [hC1])
  have hactiveGlobal := (ae_restrict_iff' measurableSet_Ioo).mp hactive
  have hzeroGlobal := (ae_restrict_iff' measurableSet_Ioo).mp
    (fullTiltedSupportQuarterPair_reflected_zero_after_active
      hU hm haffine hρ hρ0 hρK heq hl hr hC0 hsmall hheight hhigh)
  have hwhole : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      reflectedFirstWingDensity m ρ r ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae hactiveGlobal, ae_restrict_of_ae hzeroGlobal,
      ae_restrict_of_ae (volume.ae_ne (fullReflectedActiveEnd m))] with r hr ha hz hne
    by_cases hrb : r < fullReflectedActiveEnd m
    · exact ha ⟨hr.1, hrb⟩
    · have hbr : fullReflectedActiveEnd m < r :=
        lt_of_le_of_ne (le_of_not_gt hrb) (Ne.symm hne)
      rw [(hz ⟨hbr, hr.2⟩).1]
      norm_num
  have hwholeGlobal := (ae_restrict_iff' measurableSet_Ioo).mp hwhole
  have hshift := (volume.measurePreserving_sub_left (Real.pi / 2)).quasiMeasurePreserving.ae
    hwholeGlobal
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hshift]
    with t ht hu
  have hrt : Real.pi / 2 - t ∈ Ioo (0 : ℝ) (Real.pi / 2) := by
    constructor <;> linarith only [ht.1, ht.2]
  simpa only [reflectedFirstWingDensity, sub_sub_cancel] using hu hrt

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
  have hTle := le_of_not_gt hnot
  have hz : companionZero (leftCompanionCap U (-C)) ≤ -C := by
    have hmax := le_max_left (C + companionZero (leftCompanionCap U (-C))) 0
    rw [← hprojection] at hmax
    linarith only [hmax, hTle]
  have hT0 : (MovingSofaOptimality.vminus U (Real.pi / 2)).1 = C := by
    have hnonneg := le_max_right (C + companionZero (leftCompanionCap U (-C))) 0
    rw [← hprojection] at hnonneg
    linarith only [hnonneg, hTle]
  have hm := positive_affine_slope_of_middle_heights hC hh0 haffine hlow hhigh
  have hleftEq := haffine (-C) ⟨le_rfl, by linarith only [hC]⟩
  have hrightEq := haffine C ⟨by linarith only [hC], le_rfl⟩
  rw [hlow] at hleftEq
  rw [hhigh] at hrightEq
  have hmEq : m = h / (2 * C) := (eq_div_iff
    (show 2 * C ≠ 0 by linarith only [hC])).mpr
      (by nlinarith only [hleftEq, hrightEq])
  have hsmall : C + m < 1 := by
    rw [hmEq]
    exact canonical_width_add_slope_lt_one hC0.le hC1 hh1
  have hproj : horizontalProjection U = Icc (-2 * C) (2 * C) := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex, hl, hr]
  have ha : -C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith only [hC]
  have hb : C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith only [hC]
  have hab : -C < C := by linarith only [hC]
  have hW : capWidth U = 4 * C := by unfold capWidth; rw [hl, hr]; ring
  have hJL : horizontalLeft U + capWidth U / 4 = -C := by rw [hl, hW]; ring
  have hmid : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]
    congr 1 <;> ring
  have haff : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c := by simpa only [hmid] using haffine
  let V := leftCompanionCap U (-C)
  have hV : IsDownwardCap V := hU.isCap.leftCompanionCap ha
  have hVtop := hU.isCap.top_leftCompanionCap_of_positive_affine ha hb hab hm haffine
  have hVH : capHeight V < 1 := by
    dsimp only [V]
    rw [hVtop.1, hlow]
    linarith only [hh0]
  have hVL : 0 < capRoof V (horizontalLeft V) := by
    dsimp only [V]
    rw [horizontalLeft_leftCompanionCap hU.isCap ha,
      hU.isCap.capRoof_leftCompanionCap ha ⟨le_rfl, by rw [hl]; linarith only [hC]⟩]
    exact (hU.endpoint_heights_pos_of_affine hheight ⟨m, c, haff⟩).2
  obtain ⟨p, hp, t, ht, _hpy, _hzero, _hpwall, hwall⟩ :=
    hV.exists_companionZero_contact hVH hVL
  have hcompanion := fullTiltedSupportQuarterPair_companion_unit_of_collapsed_top_small_width
    hU hm.le haff hρ hρ0 hρK heq hl hr hC (lt_of_not_ge hwide).le hm hsmall hheight
    hhigh hκ hT0
  have hcut := hU.leftCompanion_density_of_regular_companion haff
    (restrict_withDensity_of_subset heq (measurableSet_regularCompanionDomain m)
      (regularCompanionDomain_subset_regularCurvatureDomain m))
  rw [hJL] at hcut
  have hkernel := hV.secondWall_le_height_sub_one_of_unit_prefix
    (measurable_leftCompanionWingDensity hρ m)
    (fun s => (leftCompanionWingDensity_bounds hρ0 hρK s).1)
    (fun s => (leftCompanionWingDensity_bounds hρ0 hρK s).2) hcut ht
    (by intro s hs; exact ⟨hs.1, by linarith only [hs.2, ht.2]⟩)
    (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl ht.2.le) hcompanion)
  change secondWall (leftCompanionCap U (-C)) t
    (MovingSofaOptimality.vplus (leftCompanionCap U (-C)) (Real.pi / 2)).1 ≤
      capHeight (leftCompanionCap U (-C)) - 1 at hkernel
  rw [hVtop.2, hVtop.1, hlow] at hkernel
  have hs : 0 ≤ Real.sin t := (Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])).le
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  have hwallle : secondWall V t (companionZero V) ≤ secondWall V t (-C) := by
    unfold secondWall
    apply div_le_div_of_nonneg_right _ hc.le
    have hmul := mul_le_mul_of_nonneg_right hz hs
    linarith only [hmul]
  rw [hwall] at hwallle
  change secondWall V t (-C) ≤ 1 - h - 1 at hkernel
  linarith only [hwallle, hkernel, hh0]

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
  let T := (MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C
  let V := leftCompanionCap U (-C)
  have hT : 0 < T := hU.firstUnit_top_overhang_pos
    hl hr hC0 hC1 hh0 hh1 hheight haffine hlow hhigh hρ hρ0 hρK heq hκ hunit
  have hprojection := hU.firstUnit_top_projection_eq
    hl hr hC0 hC1 hh0 hh1 hheight haffine hlow hhigh hρ hρ0 hρK heq hunit
  have hz : -C < companionZero V := by
    by_contra hnot
    have hmax : max (C + companionZero V) 0 = 0 :=
      max_eq_right (by linarith only [le_of_not_gt hnot])
    change T = max (C + companionZero V) 0 at hprojection
    rw [hmax] at hprojection
    linarith only [hT, hprojection]
  have hTeq : T = C + companionZero V := by
    change T = max (C + companionZero V) 0 at hprojection
    rw [max_eq_left (by linarith only [hz])] at hprojection
    exact hprojection
  have hC : 0 < C := by linarith only [hC0]
  have hm := positive_affine_slope_of_middle_heights hC hh0 haffine hlow hhigh
  have hproj : horizontalProjection U = Icc (-2 * C) (2 * C) := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex, hl, hr]
  have ha : -C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith only [hC]
  have hb : C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith only [hC]
  have hab : -C < C := by linarith only [hC]
  have hV : IsDownwardCap V := hU.isCap.leftCompanionCap ha
  have hdry := hU.isCap.sweptNiche_eq_zero_of_le_low_wing_zero ha hb hab haffine hab.le hz.le
  have hlowPoint : (-C, 1 - h) ∈ V := by
    simpa only [V, hlow] using hU.isCap.rightRoof_mem_leftCompanionCap ha
  have hzlow := hV.companionZero_le_point hlowPoint
  have hcircle : circleHeight (1 - h) = Real.sqrt (h * (2 - h)) := by
    unfold circleHeight
    congr 1
    ring
  have hTlow : T ≤ Real.sqrt (h * (2 - h)) := by
    dsimp only [rightCircleAbscissa] at hzlow
    rw [hcircle] at hzlow
    linarith only [hTeq, hzlow]
  have hlmem : horizontalLeft U ∈ horizontalProjection U := by
    rw [hproj, hl]
    exact ⟨le_rfl, by linarith only [hC]⟩
  have hleftPoint : (horizontalLeft U, capRoof U (horizontalLeft U)) ∈ V := by
    exact ⟨capRoof_mem hU.isCap.isCompact hlmem, le_rfl,
      by rw [hl]; linarith only [hC]⟩
  have hzleft := hV.companionZero_le_point hleftPoint
  have hTleft : T ≤ Real.sqrt (1 - capRoof U (horizontalLeft U) ^ 2) - C := by
    dsimp only [rightCircleAbscissa, circleHeight] at hzleft
    rw [hl] at hzleft ⊢
    linarith only [hTeq, hzleft]
  have hVtop := hU.isCap.top_leftCompanionCap_of_positive_affine ha hb hab hm haffine
  have hVH : capHeight V < 1 := by
    dsimp only [V]
    rw [hVtop.1, hlow]
    linarith only [hh0]
  have hmid : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]
    congr 1 <;> ring
  have haff : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c := by simpa only [hmid] using haffine
  have hVL : 0 < capRoof V (horizontalLeft V) := by
    dsimp only [V]
    rw [horizontalLeft_leftCompanionCap hU.isCap ha,
      hU.isCap.capRoof_leftCompanionCap ha ⟨le_rfl, by rw [hl]; linarith only [hC]⟩]
    exact (hU.endpoint_heights_pos_of_affine hheight ⟨m, c, haff⟩).2
  have hzaxis := hV.companionZero_lt_left_add_one hVH hVL
  have hTaxis : T < 1 - C := by
    rw [show horizontalLeft V = -2 * C by
      dsimp only [V]
      rw [horizontalLeft_leftCompanionCap hU.isCap ha, hl]] at hzaxis
    linarith only [hTeq, hzaxis]
  exact ⟨hT, hdry, hTeq, hTlow, hTleft, hTaxis⟩

end AmbidextrousSofa
