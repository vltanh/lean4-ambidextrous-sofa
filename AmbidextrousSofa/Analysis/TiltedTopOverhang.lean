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
endpoint, contradicting that contact. The low endpoint circle bounds the
overhang directly from the same minimum.
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
    (hC0 : 2 / 3 ≤ C) (hC1 : C ≤ 37 / 50) (hh0 : 0 < h) (hh1 : h < 1 / 3)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1) :
    0 < (MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C := by
  have hC : 0 < C := by linarith
  obtain ⟨hm, ha, hb, hV, hlV, hVH, hVL⟩ :=
    hU.tilted_companion_cut hl hr hC0 hC1 hh0 hh1 hheight haffine hlow hhigh
  have h1 := le_max_left (C + companionZero (leftCompanionCap U (-C))) 0
  have h2 := le_max_right (C + companionZero (leftCompanionCap U (-C))) 0
  rw [← hU.tilted_top_projection_eq hl hr hC0 hC1 hh0 hh1 hheight haffine hlow hhigh] at h1 h2
  by_contra! hTle
  have hz : companionZero (leftCompanionCap U (-C)) ≤ -C := by linarith only [h1, hTle]
  -- Without overhang, the slope is small and the companion density has a unit prefix.
  have hsmall : C + m < 1 := by
    by_contra! hcm
    linarith only [mul_nonneg (sub_nonneg.2 hC0) (sub_nonneg.2 hC1), hC1, hh1, hlow, hhigh,
      haffine (-C) ⟨le_rfl, neg_le_self hC.le⟩, haffine C ⟨neg_le_self hC.le, le_rfl⟩,
      mul_le_mul_of_nonneg_left hcm hC.le]
  have haff : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c := (centered_quarter_points hl hr).2.2 ▸ haffine
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
  have hcut := hU.isCap.leftCompanion_density_of_regular_companion
    (zero_lt_two.trans hU.two_lt_width) haff
    (fun hm => hU.horizontalProjection_middle_supportFace hm haff) heq
    (regularCompanionDomain_subset_regularCurvatureDomain m)
  rw [show horizontalLeft U + capWidth U / 4 = -C from (centered_quarter_points hl hr).1] at hcut
  have hkernel := hV.secondWall_le_height_sub_one_of_unit_prefix
    (measurable_leftCompanionWingDensity hρ m)
    (fun s => (leftCompanionWingDensity_bounds hρ0 hcoarse s).1)
    (fun s => (leftCompanionWingDensity_bounds hρ0 hcoarse s).2) hcut ht
    (fun s hs => ⟨hs.1, by linarith only [hs.2, ht.2]⟩)
    (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl htprefix.le) hunit)
  have hVtop := hU.isCap.top_leftCompanionCap_of_positive_affine ha hb (neg_lt_self hC) hm haffine
  simp only [hVtop.1, hVtop.2, hlow] at hkernel
  -- Then the companion wall at `-C` is both nonnegative and at most `-h`.
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ht
  have hwallle : secondWall (leftCompanionCap U (-C)) t (companionZero (leftCompanionCap U (-C)))
      ≤ secondWall (leftCompanionCap U (-C)) t (-C) :=
    div_le_div_of_nonneg_right (by linarith only [mul_le_mul_of_nonneg_right hz hs.le]) hc.le
  linarith only [hwallle, hwall, hkernel, hh0]

/-- For the actual full maximum the low middle endpoint is dry, the top extends strictly to its
right, and the low endpoint circle bounds that overhang. -/
theorem IsFullCapMaximizer.tilted_dry_left_and_overhang_bounds
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 2 / 3 ≤ C) (hC1 : C ≤ 37 / 50) (hh0 : 0 < h) (hh1 : h < 1 / 3)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1) :
    let T := (MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C
    0 < T ∧ sweptNiche U (Real.pi / 2) (-C) = 0 ∧ T ≤ Real.sqrt (h * (2 - h)) := by
  intro T
  have hT : 0 < T := hU.tilted_top_overhang_pos hl hr hC0 hC1 hh0 hh1 hheight haffine hlow hhigh
  have hprojection : T = max (C + companionZero (leftCompanionCap U (-C))) 0 :=
    hU.tilted_top_projection_eq hl hr hC0 hC1 hh0 hh1 hheight haffine hlow hhigh
  have hz : -C < companionZero (leftCompanionCap U (-C)) := by
    by_contra! hz
    rw [max_eq_right (by linarith only [hz])] at hprojection
    linarith only [hT, hprojection]
  rw [max_eq_left (by linarith only [hz])] at hprojection
  obtain ⟨-, ha, hb, hV, -⟩ :=
    hU.tilted_companion_cut hl hr hC0 hC1 hh0 hh1 hheight haffine hlow hhigh
  -- The low endpoint circle bounds the companion zero.
  have hzlow := hV.companionZero_le_point (p := (-C, 1 - h))
    (by simpa only [hlow] using hU.isCap.rightRoof_mem_leftCompanionCap ha)
  simp only [rightCircleAbscissa, circleHeight] at hzlow
  refine ⟨hT, hU.isCap.sweptNiche_eq_zero_of_le_low_wing_zero ha hb (by linarith only [hC0])
    haffine (by linarith only [hC0]) hz.le, ?_⟩
  rw [show h * (2 - h) = 1 - (1 - h) ^ 2 by ring]
  linarith only [hprojection, hzlow]

end AmbidextrousSofa
