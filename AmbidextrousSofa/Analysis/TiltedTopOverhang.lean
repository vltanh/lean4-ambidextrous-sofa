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

/-- The low companion cut of a tilted full maximum has a lower top and a positive left roof. -/
private theorem tilted_companion_cut {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 2 / 3 ≤ C) (hC1 : C ≤ 37 / 50) (hh0 : 0 < h) (hh1 : h < 17 / 50)
    (hheight : capHeight U = 1) (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1) :
    0 < m ∧ -C ∈ horizontalProjection U ∧ C ∈ horizontalProjection U ∧
      IsDownwardCap (leftCompanionCap U (-C)) ∧
      horizontalLeft (leftCompanionCap U (-C)) = -2 * C ∧ capHeight (leftCompanionCap U (-C)) < 1 ∧
      0 < capRoof (leftCompanionCap U (-C)) (horizontalLeft (leftCompanionCap U (-C))) := by
  have hC : 0 < C := by linarith
  have hm := positive_affine_slope_of_middle_heights hC hh0 haffine hlow hhigh
  have hproj : horizontalProjection U = Icc (-2 * C) (2 * C) := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex, hl, hr]
  have ha : -C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith
  have hb : C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith
  have hleft := horizontalLeft_leftCompanionCap hU.isCap ha
  refine ⟨hm, ha, hb, hU.isCap.leftCompanionCap ha, hleft.trans hl, ?_, ?_⟩
  · rw [(hU.isCap.top_leftCompanionCap_of_positive_affine ha hb (by linarith) hm haffine).1, hlow]
    linarith
  · rw [hleft, hU.isCap.capRoof_leftCompanionCap ha ⟨le_rfl, by rw [hl]; linarith⟩]
    linarith [(hU.tilted_left_endpoint_height_bounds hl hr hC hC1 hh0.le hh1 hheight
      haffine hlow hhigh).1]

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
  have hC : 0 < C := by linarith
  obtain ⟨hm, ha, hb, hV, hlV, hVH, hVL⟩ :=
    tilted_companion_cut hU hl hr hC0 hC1 hh0 hh1 hheight haffine hlow hhigh
  have h1 := le_max_left (C + companionZero (leftCompanionCap U (-C))) 0
  have h2 := le_max_right (C + companionZero (leftCompanionCap U (-C))) 0
  rw [← hU.tilted_top_projection_eq hl hr hC0 hC1 hh0 hh1 hheight haffine hlow hhigh] at h1 h2
  by_contra! hTle
  have hz : companionZero (leftCompanionCap U (-C)) ≤ -C := by linarith only [h1, hTle]
  -- Without overhang, the slope is small and the companion density has a unit prefix.
  have hmEq : m = h / (2 * C) := by
    rw [eq_div_iff (by positivity)]
    linarith only [hlow, hhigh, haffine (-C) ⟨le_rfl, neg_le_self hC.le⟩,
      haffine C ⟨neg_le_self hC.le, le_rfl⟩]
  have hsmall : C + m < 1 := by
    rw [hmEq]; exact canonical_width_add_slope_lt_one (by linarith only [hC0]) hC1 hh1
  have hmid : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]; congr 1 <;> ring
  have haff : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c := hmid ▸ haffine
  obtain ⟨ρ, hρ, hbounds, hcoarse, heq, -⟩ := hU.curvature_density_corner_controls hheight haff
  have hρ0 : ∀ s, 0 ≤ ρ s := fun s => (hbounds s).1
  have hunit := fullTiltedSupportQuarterPair_companion_unit_prefix_of_collapsed_top
    hU hm.le haff hρ hρ0 hcoarse heq hl hr hC0 hC1 hm hsmall hh0 hh1 hheight hhigh hlow
    (fun s => (hbounds s).2) (by linarith only [h2, hTle])
  -- The zero contact angle lies in that prefix.
  obtain ⟨p, hp, t, ht, -, hzero, -, hwall⟩ := hV.exists_companionZero_contact hVH hVL
  have hpx := hlV ▸ (hV.fst_mem_Icc hp).1
  have htprefix : t < Real.pi / 2 - 11 / 15 := by
    by_contra! hlate
    have hmono := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith only [ht.2])
      (by linarith only [Real.pi_gt_three]) (by linarith only [hlate] : Real.pi / 2 - t ≤ 11 / 15)
    rw [Real.cos_pi_div_two_sub] at hmono
    linarith only [hmono, hzero, hpx, hz, hC1,
      Analysis.cos_eleven_fifteenths_gt_thirty_seven_fiftieths]
  have hcut := hU.leftCompanion_density_of_regular_companion haff
    (restrict_withDensity_of_subset heq (measurableSet_regularCompanionDomain m)
      (regularCompanionDomain_subset_regularCurvatureDomain m))
  rw [show horizontalLeft U + capWidth U / 4 = -C by unfold capWidth; rw [hl, hr]; ring] at hcut
  have hkernel := hV.secondWall_le_height_sub_one_of_unit_prefix
    (measurable_leftCompanionWingDensity hρ m)
    (fun s => (leftCompanionWingDensity_bounds hρ0 hcoarse s).1)
    (fun s => (leftCompanionWingDensity_bounds hρ0 hcoarse s).2) hcut ht
    (fun s hs => ⟨hs.1, by linarith only [hs.2, ht.2]⟩)
    (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl htprefix.le) hunit)
  have hVtop := hU.isCap.top_leftCompanionCap_of_positive_affine ha hb (neg_lt_self hC) hm haffine
  simp only [hVtop.1, hVtop.2, hlow] at hkernel
  -- Then the companion wall at `-C` is both nonnegative and at most `-h`.
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith only [ht.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  have hwallle : secondWall (leftCompanionCap U (-C)) t (companionZero (leftCompanionCap U (-C)))
      ≤ secondWall (leftCompanionCap U (-C)) t (-C) :=
    div_le_div_of_nonneg_right (by linarith only [mul_le_mul_of_nonneg_right hz hs]) hc.le
  linarith only [hwallle, hwall, hkernel, hh0]

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
  intro T
  have hT : 0 < T := hU.tilted_top_overhang_pos hl hr hC0 hC1 hh0 hh1 hheight haffine hlow hhigh
  have hprojection : T = max (C + companionZero (leftCompanionCap U (-C))) 0 :=
    hU.tilted_top_projection_eq hl hr hC0 hC1 hh0 hh1 hheight haffine hlow hhigh
  have hz : -C < companionZero (leftCompanionCap U (-C)) := by
    by_contra! hz
    rw [max_eq_right (by linarith only [hz])] at hprojection
    linarith only [hT, hprojection]
  have hTeq : T = C + companionZero (leftCompanionCap U (-C)) := by
    rwa [max_eq_left (by linarith only [hz])] at hprojection
  obtain ⟨-, ha, hb, hV, hlV, hVH, hVL⟩ :=
    tilted_companion_cut hU hl hr hC0 hC1 hh0 hh1 hheight haffine hlow hhigh
  -- Both endpoint circles bound the companion zero.
  have hzlow := hV.companionZero_le_point (p := (-C, 1 - h))
    (by simpa only [hlow] using hU.isCap.rightRoof_mem_leftCompanionCap ha)
  have hzleft := hV.companionZero_le_point (p := (horizontalLeft U, capRoof U (horizontalLeft U)))
    ⟨capRoof_mem hU.isCap.isCompact (horizontalLeft_mem hU.isCap.nonempty hU.isCap.isCompact),
      le_rfl, by rw [hl]; linarith only [hC0]⟩
  simp only [rightCircleAbscissa, circleHeight] at hzlow hzleft
  refine ⟨hT, hU.isCap.sweptNiche_eq_zero_of_le_low_wing_zero ha hb (by linarith only [hC0])
    haffine (by linarith only [hC0]) hz.le, hTeq, ?_, by linarith only [hTeq, hzleft, hl], ?_⟩
  · rw [show h * (2 - h) = 1 - (1 - h) ^ 2 by ring]
    linarith only [hTeq, hzlow]
  · linarith only [hTeq, hlV, hV.companionZero_lt_left_add_one hVH hVL]

end AmbidextrousSofa
