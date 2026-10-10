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
open scoped Topology

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
set_option quotPrecheck false in
local notation "B" => firstTangentPoint (F).f (F).fD

include hU hm haffine hρ hρ0 hρK heq in
theorem fullTiltedSupportQuarterPair_first_wall_pos_left {C h x t : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 1 / 2 < C) (hmpos : 0 < m) (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h)
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ s ≤ 1)
    (hx : x ≤ 1 - 2 * C) (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    0 < firstWall U t x := by
  have horder := (fullTiltedSupportQuarterPair_first_tangent_order
    hU hm haffine hρ hρ0 hρK heq hunit).1
  have hB0 := (fullTiltedSupportQuarterPair_tangent_traces
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hheight hlow).1
  have hsin (s : ℝ) (hs : s ∈ Icc t (Real.pi / 2)) : Real.sin s ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (ht.1.trans_le hs.1)
      (by linarith only [hs.2, Real.pi_pos])).ne'
  have hnum : Continuous (fun s => angleSupport U s - 1 - x * Real.cos s) :=
    (hU.isCap.imported_isConvexBody.continuous_supp.sub continuous_const).sub
      (continuous_const.mul Real.continuous_cos)
  have hcont : ContinuousOn (fun s => firstWall U s x) (Icc t (Real.pi / 2)) :=
    hnum.continuousOn.div Real.continuous_sin.continuousOn hsin
  have hanti : StrictAntiOn (fun s => firstWall U s x) (Icc t (Real.pi / 2)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont
    intro s hs
    have hs' : s ∈ Ioo t (Real.pi / 2) := by simpa only [interior_Icc] using hs
    have hsq : s ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨ht.1.trans hs'.1, hs'.2⟩
    have hd := hU.isCap.hasDerivAt_firstWall_of_open_first_density
      hρ hρ0 hρK heq (firstQuarter_subset_regularCurvatureDomain_of_nonneg hm) hsq x
    rw [hd.deriv]
    have hmatch := fullTiltedSupportQuarterPair_first_tangency
      hU hm haffine hρ hρ0 hρK heq ⟨hsq.1.le, hsq.2⟩
    have hlo := horder ⟨le_rfl, by positivity⟩ (Ioo_subset_Icc_self hsq) hsq.1.le
    dsimp only at hlo
    rw [hB0] at hlo
    rw [← hmatch]
    exact div_neg_of_neg_of_pos (by linarith only [hlo, hC, hx])
      (sq_pos_of_ne_zero (hsin s ⟨hs'.1.le, hs'.2.le⟩))
  have hstrict := hanti (left_mem_Icc.mpr ht.2.le) (right_mem_Icc.mpr ht.2.le) ht.2
  have hterminal : firstWall U (Real.pi / 2) x = 0 := by
    simp only [firstWall, unitNormal, Real.cos_pi_div_two, Real.sin_pi_div_two,
      mul_zero, sub_zero, div_one]
    change capHeight U - 1 = 0
    rw [hheight, sub_self]
  dsimp only at hstrict
  rwa [hterminal] at hstrict

include hU hm haffine hρ hρ0 hρK heq in
theorem fullTiltedSupportQuarterPair_positive_middle_iff {C h x : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 1 / 2 < C) (hmpos : 0 < m) (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1) (hh : 0 < h)
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ s ≤ 1)
    (hx : x ∈ Ioo (-C) C) :
    0 < sweptNiche U (Real.pi / 2) x ↔ companionZero (leftCompanionCap U (-C)) < x := by
  have hmid : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]
    congr 1 <;> ring
  have haff := haffine
  rw [hmid] at haff
  have hproj : horizontalProjection U = Icc (-2 * C) (2 * C) := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex,
      hl, hr]
  have ha : -C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith only [hC]
  have hb : C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith only [hC]
  have hab : -C < C := by linarith only [hC]
  have hV := hU.isCap.leftCompanionCap ha
  have hVheight : capHeight (leftCompanionCap U (-C)) < 1 := by
    rw [(hU.isCap.top_leftCompanionCap_of_positive_affine ha hb hab hmpos haff).1, hlow]
    linarith only [hh]
  have hleft := (hU.endpoint_heights_pos_of_affine hheight ⟨m, c, haffine⟩).2
  have hVleft : 0 < capRoof (leftCompanionCap U (-C))
      (horizontalLeft (leftCompanionCap U (-C))) := by
    rw [horizontalLeft_leftCompanionCap hU.isCap ha,
      hU.isCap.capRoof_leftCompanionCap ha ⟨le_rfl, by rw [hl]; linarith only [hC]⟩]
    exact hleft
  have hhighPoint : (C, 1) ∈ U := by
    simpa only [hhigh] using capRoof_mem hU.isCap.isCompact hb
  constructor
  · intro hpositive
    by_contra hnot
    rw [hU.isCap.sweptNiche_eq_zero_of_le_low_wing_zero ha hb hab haff hx.2.le
      (le_of_not_gt hnot)] at hpositive
    exact lt_irrefl 0 hpositive
  · intro hz
    by_cases hsplit : x ≤ 1 - 2 * C
    · obtain ⟨t, ht, hsecond⟩ := hV.exists_secondWall_pos_of_companionZero_lt
        hVheight hVleft hz
      have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
        ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
      have hsecondU := hsecond.trans_le
        (secondWall_mono (leftCompanionCap_subset U (-C)) hV.nonempty hU.isCap.isCompact hc x)
      have hfirst := fullTiltedSupportQuarterPair_first_wall_pos_left
        hU hm haffine hρ hρ0 hρK heq hl hr hC hmpos hheight hlow hunit hsplit ht
      exact (lt_min hfirst hsecondU).trans_le (cornerWall_le_sweptNiche
        (sweptWallValues_bddAbove hU.isCap.isCompact le_rfl x) ht)
    · exact hU.isCap.sweptNiche_pos_of_top_point_right hhighPoint hx.2
        (by rw [hl]; linarith only [lt_of_not_ge hsplit])

include hU hm haffine hρ hρ0 hρK heq in
theorem fullTiltedSupportQuarterPair_positive_middle_eq {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 1 / 2 < C) (hmpos : 0 < m) (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1) (hh : 0 < h)
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ s ≤ 1) :
    Ioo (-C) C ∩ {x : ℝ | 0 < sweptNiche U (Real.pi / 2) x} =
      Ioo (max (-C) (companionZero (leftCompanionCap U (-C)))) C := by
  ext x
  constructor
  · rintro ⟨hx, hp⟩
    exact ⟨max_lt hx.1 ((fullTiltedSupportQuarterPair_positive_middle_iff
      hU hm haffine hρ hρ0 hρK heq hl hr hC hmpos hheight hlow hhigh hh hunit hx).mp hp), hx.2⟩
  · intro hx
    have hxJ : x ∈ Ioo (-C) C := ⟨(le_max_left _ _).trans_lt hx.1, hx.2⟩
    exact ⟨hxJ, (fullTiltedSupportQuarterPair_positive_middle_iff
      hU hm haffine hρ hρ0 hρK heq hl hr hC hmpos hheight hlow hhigh hh hunit hxJ).mpr
        ((le_max_right _ _).trans_lt hx.1)⟩

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
  let z := companionZero (leftCompanionCap U (-C))
  let b := (MovingSofaOptimality.vminus U (Real.pi / 2)).1
  have hC : 0 < C := by linarith only [hC0]
  have hm := positive_affine_slope_of_middle_heights hC hh0 haffine hlow hhigh
  have hproj : horizontalProjection U = Icc (-2 * C) (2 * C) := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex, hl, hr]
  have ha : -C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith only [hC]
  have hb : C ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith only [hC]
  have hab : -C < C := by linarith only [hC]
  have hhighPoint : (C, 1) ∈ U := by
    simpa only [hhigh] using capRoof_mem hU.isCap.isCompact hb
  have htop := hU.isCap.top_points_after_positive_affine ha hb hab hm hheight haffine hhigh
  have hCb : C ≤ b := (htop (C, 1) hhighPoint rfl).2
  have htopPoint : (b, 1) ∈ U := by
    have hpoint := (MovingSofaOptimality.vminus_mem_edge hU.isCap.imported_isConvexBody (Real.pi / 2)).1
    have hy := (top_vminus_snd_eq_capHeight U).trans hheight
    simpa only [b, ← hy, Prod.mk.eta] using hpoint
  have hbR : b ≤ 2 * C := by
    simpa only [hr] using (hU.isCap.fst_mem_Icc htopPoint).2
  have hleft := (hU.tilted_left_endpoint_height_bounds hl hr hC hC1 hh0.le hh1 hheight
    haffine hlow hhigh).1
  have hleft0 : 0 < capRoof U (horizontalLeft U) := by linarith only [hleft]
  have hV := hU.isCap.leftCompanionCap ha
  have hVheight : capHeight (leftCompanionCap U (-C)) < 1 := by
    rw [(hU.isCap.top_leftCompanionCap_of_positive_affine ha hb hab hm haffine).1, hlow]
    linarith only [hh0]
  have hVleft : 0 < capRoof (leftCompanionCap U (-C))
      (horizontalLeft (leftCompanionCap U (-C))) := by
    rw [horizontalLeft_leftCompanionCap hU.isCap ha,
      hU.isCap.capRoof_leftCompanionCap ha ⟨le_rfl, by rw [hl]; linarith only [hC]⟩]
    exact hleft0
  have hzaxis : z < 1 - 2 * C := by
    have hz := hV.companionZero_lt_left_add_one hVheight hVleft
    rw [horizontalLeft_leftCompanionCap hU.isCap ha, hl] at hz
    dsimp only [z]
    linarith only [hz]
  have hzC : z < C := by linarith only [hzaxis, hC0]
  have hW : capWidth U = 4 * C := by unfold capWidth; rw [hl, hr]; ring
  have hJL : horizontalLeft U + capWidth U / 4 = -C := by rw [hl, hW]; ring
  have hJR : horizontalRight U - capWidth U / 4 = C := by rw [hr, hW]; ring
  have hJ : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    change Icc (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) = _
    rw [hJL, hJR]
  have hmid : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c := by simpa only [hJ] using haffine
  have hprojection := fullTiltedSupportQuarterPair_positive_middle_eq
    hU hm.le hmid hρ hρ0 hρK heq hl hr hC0 hm hheight hlow hhigh hh0 hunit
  have hqC : max (-C) z < C := max_lt hab hzC
  have hpositiveLength : C - max (-C) z ≤
      volume.real (middleHalfInterval (horizontalLeft U) (horizontalRight U) ∩
        {x : ℝ | 0 < sweptNiche U (Real.pi / 2) x}) := by
    have hsub : Ioo (max (-C) z) C ⊆
        middleHalfInterval (horizontalLeft U) (horizontalRight U) ∩
          {x : ℝ | 0 < sweptNiche U (Real.pi / 2) x} := by
      intro x hx
      rw [← hprojection] at hx
      exact ⟨by rw [hJ]; exact ⟨hx.1.1.le, hx.1.2.le⟩, hx.2⟩
    have hfinite : volume (middleHalfInterval (horizontalLeft U) (horizontalRight U) ∩
        {x : ℝ | 0 < sweptNiche U (Real.pi / 2) x}) ≠ ⊤ := by
      apply (lt_of_le_of_lt (measure_mono inter_subset_left) ?_).ne
      rw [hJ, Real.volume_Icc]
      exact ENNReal.ofReal_lt_top
    simpa only [Real.volume_real_Ioo_of_le hqC.le] using measureReal_mono hsub hfinite
  have hmoment := hU.positive_middle_measure_le_outer_without_top hheight ⟨m, c, hmid⟩
    hhighPoint htopPoint
  have hmoment' : volume.real (middleHalfInterval (horizontalLeft U) (horizontalRight U) ∩
      {x : ℝ | 0 < sweptNiche U (Real.pi / 2) x}) ≤
      volume.real (Icc (-2 * C) (-C) \ Ioo C b) +
        volume.real (Icc C (2 * C) \ Ioo C b) := by
    rw [hJL, hJR] at hmoment
    simpa only [hl, hr] using hmoment
  have houterL := real_left_window_without_top_le
    (show -2 * C ≤ -C by linarith only [hC])
    (show -2 * C ≤ C by linarith only [hC]) (show -C ≤ b by linarith only [hCb, hC])
  have houterR := real_right_window_without_top_le
    (show C ≤ 2 * C by linarith only [hC]) hbR (le_refl C)
  have hbound := hpositiveLength.trans (hmoment'.trans (add_le_add houterL houterR))
  rw [min_eq_left hab.le, max_eq_right hCb] at hbound
  have hmax : C + max (-C) z = max (C + z) 0 := by
    by_cases hz : -C ≤ z
    · rw [max_eq_right hz, max_eq_left (by linarith only [hz])]
    · rw [max_eq_left (le_of_not_ge hz), max_eq_right (by linarith only [le_of_not_ge hz])]
      ring
  apply le_antisymm
  · change b - C ≤ max (C + z) 0
    rw [← hmax]
    linarith only [hbound]
  · change max (C + z) 0 ≤ b - C
    by_cases hz : z ≤ -C
    · rw [max_eq_right (by linarith only [hz])]
      linarith only [hCb]
    · have hzleft : -C < z := lt_of_not_ge hz
      rw [max_eq_left (by linarith only [hzleft])]
      by_contra hnot
      have hgap : 0 < (C + z) - (b - C) := sub_pos.mpr (lt_of_not_ge hnot)
      let ε := ((C + z) - (b - C)) / 4
      have hε : 0 < ε := by dsimp only [ε]; positivity
      have habdry : -C + ε ≤ z - ε := by dsimp only [ε]; linarith only [hzleft, hCb]
      have hdry := hU.dry_interval_length_le_top_width habdry
        (by rw [hJL]; linarith only [hε])
        (by rw [hJR]; linarith only [hzC, hε]) hCb htop
        (fun x hx θ hθ => hU.isCap.secondWallNumerator_neg_of_lt_low_wing_zero
          ha hb hab haffine hhigh (by linarith only [hx.2, hzC, hε])
          (by change x < z; linarith only [hx.2, hε])
          (by rw [hl]; linarith only [hx.2, hzaxis, hε]) hθ)
      dsimp only [ε] at hdry
      linarith only [hdry, hgap]


end AmbidextrousSofa
