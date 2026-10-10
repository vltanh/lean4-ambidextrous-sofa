module

public import AmbidextrousSofa.Analysis.TiltedReflectedLateUnit
public import AmbidextrousSofa.Analysis.CompanionEndpointKernel

@[expose] public section

/-!
# Positive actual top overhang and the dry low middle endpoint

If the top overhang vanished, the exact selected-source projection would
put the low-wing zero at or to the left of the low middle endpoint. Its
actual minimizing contact occurs in the companion unit-curvature prefix.
The initial companion kernel is then strictly negative at the low middle
endpoint, contradicting that contact. The two endpoint circles give the
remaining overhang bounds directly from the same minimum.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

/-- The density, reflected crossing, zero contact, and projection are
all obtained from the actual maximum. No overhang or occupation premise
is supplied to this strict positivity statement. -/
theorem IsFullCapMaximizer.tilted_top_overhang_pos
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 2 / 3 ≤ C) (hC1 : C ≤ 37 / 50) (hh0 : 0 < h) (hh1 : h < 17 / 50)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1) :
    0 < (MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C := by
  have hC : 0 < C := by linarith only [hC0]
  have hprojection := hU.tilted_top_projection_eq
    hl hr hC0 hC1 hh0 hh1 hheight haffine hlow hhigh
  by_contra hnot
  have hTle := le_of_not_gt hnot
  have hz : companionZero (leftCompanionCap U (-C)) ≤ -C := by
    have hmax : C + companionZero (leftCompanionCap U (-C)) ≤
        max (C + companionZero (leftCompanionCap U (-C))) 0 := le_max_left _ _
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
    exact canonical_width_add_slope_lt_one (by linarith only [hC0]) hC1 hh1
  have hproj : horizontalProjection U = Icc (-2 * C) (2 * C) := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex,
      hl, hr]
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
  have heL := (hU.tilted_left_endpoint_height_bounds hl hr hC hC1 hh0.le hh1 hheight
    haffine hlow hhigh).1
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
    linarith only [heL]
  obtain ⟨p, hp, t, ht, _hpy, hzero, _hpwall, hwall⟩ :=
    hV.exists_companionZero_contact hVH hVL
  have hpx : -2 * C ≤ p.1 := by
    have h := (hV.fst_mem_Icc hp).1
    simpa only [V, horizontalLeft_leftCompanionCap hU.isCap ha, hl] using h
  have hsinC : Real.sin t ≤ C := by
    change companionZero V ≤ -C at hz
    linarith only [hzero, hz, hpx]
  have htprefix : t < Real.pi / 2 - 11 / 15 := by
    by_contra hlate
    have hmono := Real.cos_le_cos_of_nonneg_of_le_pi
      (show 0 ≤ Real.pi / 2 - t by linarith only [ht.2])
      (show (11 / 15 : ℝ) ≤ Real.pi by linarith only [Real.pi_gt_three])
      (show Real.pi / 2 - t ≤ 11 / 15 by linarith only [le_of_not_gt hlate])
    rw [Real.cos_pi_div_two_sub] at hmono
    linarith only [hmono, hsinC, hC1,
      Analysis.cos_eleven_fifteenths_gt_thirty_seven_fiftieths]
  obtain ⟨ρ, hρ, hbounds, hcoarse, heq, _⟩ :=
    hU.curvature_density_corner_controls hheight haff
  have hρ0 : ∀ s, 0 ≤ ρ s := fun s => (hbounds s).1
  have hunit := fullTiltedSupportQuarterPair_companion_unit_prefix_of_collapsed_top
    hU hm.le haff hρ hρ0 hcoarse heq hl hr hC0 hC1 hm hsmall hh0 hh1 hheight hhigh hlow
    (fun s => (hbounds s).2) hT0
  have hcut := hU.leftCompanion_density_of_regular_companion haff
    (restrict_withDensity_of_subset heq (measurableSet_regularCompanionDomain m)
      (regularCompanionDomain_subset_regularCurvatureDomain m))
  rw [hJL] at hcut
  have hkernel := hV.secondWall_le_height_sub_one_of_unit_prefix
    (measurable_leftCompanionWingDensity hρ m)
    (fun s => (leftCompanionWingDensity_bounds hρ0 hcoarse s).1)
    (fun s => (leftCompanionWingDensity_bounds hρ0 hcoarse s).2) hcut ht
    (by intro s hs; exact ⟨hs.1, by linarith only [hs.2, ht.2]⟩)
    (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl htprefix.le) hunit)
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

/-- RT.9--RT.12 for the actual full maximum: the low middle endpoint is
dry, the top extends strictly to its right, and both literal endpoint
circles bound that overhang. -/
theorem IsFullCapMaximizer.tilted_dry_left_and_overhang_bounds
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 2 / 3 ≤ C) (hC1 : C ≤ 37 / 50) (hh0 : 0 < h) (hh1 : h < 17 / 50)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1) :
    let T := (MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C
    0 < T ∧ sweptNiche U (Real.pi / 2) (-C) = 0 ∧
      T = C + companionZero (leftCompanionCap U (-C)) ∧
      T ≤ Real.sqrt (h * (2 - h)) ∧
      T ≤ Real.sqrt (1 - capRoof U (horizontalLeft U) ^ 2) - C ∧ T < 1 - C := by
  let T := (MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C
  let V := leftCompanionCap U (-C)
  have hT : 0 < T := hU.tilted_top_overhang_pos
    hl hr hC0 hC1 hh0 hh1 hheight haffine hlow hhigh
  have hprojection := hU.tilted_top_projection_eq
    hl hr hC0 hC1 hh0 hh1 hheight haffine hlow hhigh
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
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex,
      hl, hr]
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
  have heL := (hU.tilted_left_endpoint_height_bounds hl hr hC hC1 hh0.le hh1 hheight
    haffine hlow hhigh).1
  have hVL : 0 < capRoof V (horizontalLeft V) := by
    dsimp only [V]
    rw [horizontalLeft_leftCompanionCap hU.isCap ha,
      hU.isCap.capRoof_leftCompanionCap ha ⟨le_rfl, by rw [hl]; linarith only [hC]⟩]
    linarith only [heL]
  have hzaxis := hV.companionZero_lt_left_add_one hVH hVL
  have hTaxis : T < 1 - C := by
    rw [show horizontalLeft V = -2 * C by
      dsimp only [V]
      rw [horizontalLeft_leftCompanionCap hU.isCap ha, hl]] at hzaxis
    linarith only [hTeq, hzaxis]
  exact ⟨hT, hdry, hTeq, hTlow, hTleft, hTaxis⟩

end AmbidextrousSofa
