module

public import AmbidextrousSofa.Analysis.DryTopBalance
public import AmbidextrousSofa.Analysis.SelectedHorizontalMoment
public import AmbidextrousSofa.Analysis.TerminalTopProjection
public import AmbidextrousSofa.Analysis.TiltedEndpointBounds

@[expose] public section

/-!
# The exact actual top projection for a tilted full maximum

The positive middle interval is fixed by the actual low-wing circle
minimum. The selected horizontal source inequality gives one comparison
with the top width. For the reverse comparison, compact dry intervals
carry finite inner floor mass, which the selected finite balance charges
to the literal top leaf. Both selected limits are constructed internally.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem IsFullCapMaximizer.tilted_left_endpoint_height_bounds
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 0 < C) (hC1 : C ≤ 37 / 50) (hh0 : 0 ≤ h) (hh1 : h < 17 / 50)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1) :
    3 / 20 < capRoof U (horizontalLeft U) ∧
      capRoof U (horizontalLeft U) < 3 / 4 := by
  have hEP := (hU.tilted_endpoint_laws hl hr hheight haffine hlow hhigh).2
  have hn := hU.isCap.middle_niche_le_box_height_of_endpoints hl hr hC0.le
    (by linarith only [hC1])
  have hH := Analysis.tiltedBoxHeight_lt_thirty_three_hundredths hC0.le hC1
  change sweptNiche U (Real.pi / 2) (-C) ≤ Analysis.tiltedBoxHeight C ∧
    sweptNiche U (Real.pi / 2) C ≤ Analysis.tiltedBoxHeight C at hn
  have hz := sweptNiche_nonneg U (Real.pi / 2) C
  have hw := sweptNiche_nonneg U (Real.pi / 2) (-C)
  constructor <;> linarith only [hEP, hn.1, hn.2, hH, hz, hw, hh0, hh1]

theorem positive_affine_slope_of_middle_heights {U : Set Plane} {C h m c : ℝ}
    (hC : 0 < C) (hh : 0 < h)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1) : 0 < m := by
  have hleft := haffine (-C) ⟨le_rfl, by linarith only [hC]⟩
  have hright := haffine C ⟨by linarith only [hC], le_rfl⟩
  rw [hlow] at hleft
  rw [hhigh] at hright
  by_contra hnot
  have hprod := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot) hC.le
  nlinarith only [hleft, hright, hprod, hh]

/-- Every actual top point lies to the right of the high affine endpoint,
and its right endpoint is the literal `vminus` trace at the top normal. -/
theorem IsDownwardCap.top_points_after_positive_affine
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (hm : 0 < m) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc a b, capRoof U x = m * x + c)
    (hhigh : capRoof U b = 1) :
    ∀ p ∈ U, p.2 = 1 → p.1 ∈ Icc b (MovingSofaOptimality.vminus U (Real.pi / 2)).1 := by
  intro p hp hpy
  have hroof : p.2 ≤ m * p.1 + c :=
    (le_capRoof hU.isCompact (show (p.1, p.2) ∈ U by simpa only [Prod.mk.eta] using hp)).trans
      (hU.capRoof_le_affine_of_affine_segment ha hb hab haffine p.1 ⟨p, hp, rfl⟩)
  have hline : m * b + c = 1 := (haffine b ⟨hab.le, le_rfl⟩).symm.trans hhigh
  have hlo : b ≤ p.1 := by
    apply (mul_le_mul_left hm).mp
    linarith only [hroof, hline, hpy]
  have hedge : p ∈ MovingSofaOptimality.edge U (Real.pi / 2) := by
    refine ⟨hp, ?_⟩
    change coordDot p (unitNormal (Real.pi / 2)) = angleSupport U (Real.pi / 2)
    simp only [coordDot, unitNormal, angleSupport, Real.cos_pi_div_two, Real.sin_pi_div_two,
      mul_zero, mul_one, zero_add, hpy, ← capHeight, hheight]
  have hxp : p.1 ∈ Icc (MovingSofaOptimality.vplus U (Real.pi / 2)).1
      (MovingSofaOptimality.vminus U (Real.pi / 2)).1 := by
    rw [← hU.horizontalProjection_edge (by simp : 0 ≤ Real.sin (Real.pi / 2))]
    exact ⟨p, hedge, rfl⟩
  exact ⟨hlo, hxp.2⟩

/-- RT.3 for the literal low-wing zero and literal right top endpoint.
There is no source-occupation or projection premise in this statement. -/
theorem IsFullCapMaximizer.tilted_top_projection_eq
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 2 / 3 ≤ C) (hC1 : C ≤ 37 / 50) (hh0 : 0 < h) (hh1 : h < 17 / 50)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1) :
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
  have hprojection := hU.isCap.positive_middle_eq_low_wing_interval hl hr hC0 hm haffine hhigh
    (by rw [hlow]; linarith only [hh0]) hleft0
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
    simpa only [hJL, hJR, hl, hr] using hmoment
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
