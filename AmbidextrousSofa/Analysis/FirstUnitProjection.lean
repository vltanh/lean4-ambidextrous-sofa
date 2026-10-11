module

public import AmbidextrousSofa.Analysis.FirstUnitNiche
public import AmbidextrousSofa.Analysis.TiltedTopProjection

@[expose] public section

/-!
# Exact positive projection for every first-unit tilted width

The first-unit tangent starts at abscissa `2C-1`. Therefore every first
wall at `x ≤ 1-2C` decreases strictly to zero at the top angle whenever
`C > 1/2`. This supplies the low-width positive-interval argument. The
selected positive projection and dry floor/top balance then give the
same exact top-overhang identity on the full remaining width range.
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
theorem fullTiltedSupportQuarterPair_first_wall_pos_left {C h x t : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 1 / 2 < C) (hmpos : 0 < m) (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h)
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ s ≤ 1)
    (hx : x ≤ 1 - 2 * C) (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    0 < firstWall U t x := by
  have hsin (s : ℝ) (hs : s ∈ Icc t (Real.pi / 2)) : Real.sin s ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (ht.1.trans_le hs.1)
      (by linarith only [hs.2, Real.pi_pos])).ne'
  have hcont : ContinuousOn (fun s => firstWall U s x) (Icc t (Real.pi / 2)) :=
    ((hU.isCap.imported_isConvexBody.continuous_supp.sub continuous_const).sub
      (continuous_const.mul Real.continuous_cos)).continuousOn.div
        Real.continuous_sin.continuousOn hsin
  have hanti := strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont fun s hs => by
    rw [interior_Icc] at hs
    have hsq : s ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨ht.1.trans hs.1, hs.2⟩
    have hlo := (fullTiltedSupportQuarterPair_first_tangent_order
      hU hm haffine hρ hρ0 hρK heq hunit).1 ⟨le_rfl, by positivity⟩ (Ioo_subset_Icc_self hsq)
      hsq.1.le
    simp only [(fullTiltedSupportQuarterPair_tangent_traces
      hU hm haffine hρ hρ0 hρK heq hl hr hmpos hheight hlow).1,
      fullTiltedSupportQuarterPair_first_tangency hU hm haffine hρ hρ0 hρK heq
        ⟨hsq.1.le, hsq.2⟩] at hlo
    rw [(hU.isCap.hasDerivAt_firstWall_of_open_first_density hρ hρ0 hρK heq
      (firstQuarter_subset_regularCurvatureDomain_of_nonneg hm) hsq x).deriv]
    exact div_neg_of_neg_of_pos (by linarith only [hlo, hC, hx])
      (sq_pos_of_ne_zero (hsin s ⟨hs.1.le, hs.2.le⟩))
  simpa only [firstWall_pi_div_two, show support U (0, 1) = 1 from hheight, sub_self] using
    hanti (left_mem_Icc.mpr ht.2.le) (right_mem_Icc.mpr ht.2.le) ht.2

include hU hm haffine hρ hρ0 hρK heq in
theorem fullTiltedSupportQuarterPair_positive_middle_iff {C h x : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 1 / 2 < C) (hmpos : 0 < m) (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1) (hh : 0 < h)
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ s ≤ 1)
    (hx : x ∈ Ioo (-C) C) :
    0 < sweptNiche U (Real.pi / 2) x ↔ companionZero (leftCompanionCap U (-C)) < x := by
  have haff : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c := fun x hx => haffine x (by
    rw [middleHalfInterval, hl, hr]; constructor <;> linarith only [hx.1, hx.2])
  have hproj : horizontalProjection U = Icc (-2 * C) (2 * C) := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex, hl, hr]
  have ha : -C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith only [hC]
  have hb : C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith only [hC]
  have hV := hU.isCap.leftCompanionCap ha
  have hVL : 0 < capRoof (leftCompanionCap U (-C)) (horizontalLeft (leftCompanionCap U (-C))) := by
    rw [horizontalLeft_leftCompanionCap hU.isCap ha,
      hU.isCap.capRoof_leftCompanionCap ha ⟨le_rfl, by rw [hl]; linarith only [hC]⟩]
    exact (hU.endpoint_heights_pos_of_affine hheight ⟨m, c, haffine⟩).2
  refine ⟨fun hpos => not_le.mp fun hz => hpos.ne'
    (hU.isCap.sweptNiche_eq_zero_of_le_low_wing_zero ha hb (by linarith only [hC]) haff
      hx.2.le hz),
    fun hz => ?_⟩
  by_cases hsplit : x ≤ 1 - 2 * C
  · obtain ⟨t, ht, hsecond⟩ :=
      hV.exists_secondWall_pos_of_companionZero_lt (by
        rw [(hU.isCap.top_leftCompanionCap_of_positive_affine ha hb (by linarith only [hC])
          hmpos haff).1, hlow]; linarith only [hh]) hVL hz
    have hsecondU := hsecond.trans_le (secondWall_mono (leftCompanionCap_subset U (-C))
      hV.nonempty hU.isCap.isCompact (Real.cos_pos_of_mem_Ioo
        ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩) x)
    exact (lt_min (fullTiltedSupportQuarterPair_first_wall_pos_left hU hm haffine hρ hρ0 hρK
      heq hl hr hC hmpos hheight hlow hunit hsplit ht) hsecondU).trans_le
        (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCap.isCompact le_rfl x) ht)
  · exact hU.isCap.sweptNiche_pos_of_top_point_right
      (hhigh ▸ capRoof_mem hU.isCap.isCompact hb) hx.2 (by rw [hl]; linarith only [hsplit])

include hU hm haffine hρ hρ0 hρK heq in
theorem fullTiltedSupportQuarterPair_positive_middle_eq {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 1 / 2 < C) (hmpos : 0 < m) (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1) (hh : 0 < h)
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ s ≤ 1) :
    Ioo (-C) C ∩ {x : ℝ | 0 < sweptNiche U (Real.pi / 2) x} =
      Ioo (max (-C) (companionZero (leftCompanionCap U (-C)))) C := by
  ext x
  have := fun hx : x ∈ Ioo (-C) C => fullTiltedSupportQuarterPair_positive_middle_iff
    hU hm haffine hρ hρ0 hρK heq hl hr hC hmpos hheight hlow hhigh hh hunit hx
  simp only [mem_inter_iff, mem_Ioo, mem_ofPred_eq, max_lt_iff] at this ⊢
  tauto

end ActualPair

/-- Exact top projection on the full tilted width range after the actual
first density has been shown to be at most one. The selected finite
source and floor balances are constructed within the proof. -/
theorem IsFullCapMaximizer.firstUnit_top_projection_eq
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
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1) :
    (MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C =
      max (C + companionZero (leftCompanionCap U (-C))) 0 := by
  set z := companionZero (leftCompanionCap U (-C))
  set b := (MovingSofaOptimality.vminus U (Real.pi / 2)).1
  have hC : 0 < C := by linarith only [hC0]
  have hm := positive_affine_slope_of_middle_heights hC hh0 haffine hlow hhigh
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
  have hhighPoint : (C, 1) ∈ U := hhigh ▸ capRoof_mem hU.isCap.isCompact hb
  have htop := hU.isCap.top_points_after_positive_affine ha hb (by linarith only [hC]) hm hheight
    haffine hhigh
  have hCb : C ≤ b := (htop (C, 1) hhighPoint rfl).2
  have htopPoint : (b, 1) ∈ U := by
    simpa only [b, ← (top_vminus_snd_eq_capHeight U).trans hheight, Prod.mk.eta] using
      (MovingSofaOptimality.vminus_mem_edge hU.isCap.imported_isConvexBody (Real.pi / 2)).1
  have hbR : b ≤ 2 * C := hr ▸ (hU.isCap.fst_mem_Icc htopPoint).2
  have hzaxis : z < 1 - 2 * C := by
    have := hV.companionZero_lt_left_add_one (by
      rw [(hU.isCap.top_leftCompanionCap_of_positive_affine ha hb (by linarith only [hC]) hm
        haffine).1, hlow]; linarith only [hh0]) hVL
    rw [horizontalLeft_leftCompanionCap hU.isCap ha, hl] at this
    linarith only [this]
  have hJL : horizontalLeft U + capWidth U / 4 = -C := by rw [capWidth, hl, hr]; ring
  have hJR : horizontalRight U - capWidth U / 4 = C := by rw [capWidth, hl, hr]; ring
  have hJ : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]; ring_nf
  have hmid : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c := hJ ▸ haffine
  -- The positive middle has length at least `C - max (-C) z`, and the
  -- top-free outer windows bound it by `3C - b`.
  have hlength : C - max (-C) z ≤
      volume.real (Icc (-C) C ∩ {x : ℝ | 0 < sweptNiche U (Real.pi / 2) x}) := by
    rw [← Real.volume_real_Ioo_of_le
      (max_lt (by linarith only [hC]) (by linarith only [hzaxis, hC0])).le,
      ← fullTiltedSupportQuarterPair_positive_middle_eq
        hU hm.le hmid hρ hρ0 hρK heq hl hr hC0 hm hheight hlow hhigh hh0 hunit]
    exact measureReal_mono (inter_subset_inter_left _ Ioo_subset_Icc_self)
      ((measure_mono inter_subset_left).trans_lt measure_Icc_lt_top).ne
  have hmoment := hU.positive_middle_measure_le_outer_without_top hheight ⟨m, c, hmid⟩
    hhighPoint htopPoint
  rw [hJ, hJL, hJR, hl, hr] at hmoment
  have hbound : b - C ≤ C + max (-C) z := by
    linarith only [hlength, hmoment, real_left_window_without_top_le
      (show -2 * C ≤ -C by linarith only [hC]) (show -2 * C ≤ C by linarith only [hC])
      (show -C ≤ b by linarith only [hC, hCb]),
      real_right_window_without_top_le (show C ≤ 2 * C by linarith only [hC]) hbR le_rfl,
      min_le_left (-C) C, le_max_right C b]
  rcases le_or_gt z (-C) with hz | hz
  · rw [max_eq_left hz] at hbound
    rw [max_eq_right (by linarith only [hz])]
    linarith only [hbound, hCb]
  rw [max_eq_right hz.le] at hbound
  rw [max_eq_left (by linarith only [hz])]
  refine le_antisymm hbound (not_lt.mp fun hgap => ?_)
  -- A dry interval left of `z` longer than the top would contradict the dry/top balance.
  have hdry := hU.dry_interval_length_le_top_width (a := -C + (C + z - (b - C)) / 4)
    (b := z - (C + z - (b - C)) / 4) (by linarith only [hz, hCb])
    (by rw [hJL]; linarith only [hgap]) (by rw [hJR]; linarith only [hgap, hzaxis, hC0]) hCb htop
    (fun x hx θ hθ => hU.isCap.secondWallNumerator_neg_of_lt_low_wing_zero ha hb
      (by linarith only [hC]) haffine hhigh (by linarith only [hx.2, hgap, hzaxis, hC0])
      (by change x < z; linarith only [hx.2, hgap]) (by rw [hl]; linarith only [hx.2, hgap, hzaxis])
      hθ)
  linarith only [hdry, hgap]

end AmbidextrousSofa
