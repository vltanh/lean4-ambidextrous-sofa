module

public import AmbidextrousSofa.Analysis.DryTopBalance
public import AmbidextrousSofa.Analysis.SelectedHorizontalMoment
public import AmbidextrousSofa.Analysis.TerminalTopProjection
public import AmbidextrousSofa.Analysis.TiltedEndpointBounds

@[expose] public section

/-!
# The exact actual top projection for a tilted full maximum

The low companion cut has a lower top and a positive left roof, and the
positive middle interval is fixed by the actual low-wing circle minimum.
The selected horizontal source inequality gives one comparison with the
top width. For the reverse comparison, compact dry intervals carry
finite inner floor mass, which the selected finite balance charges to
the literal top leaf. Both selected limits are constructed internally.
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
  have hn := hU.isCap.middle_niche_le_box_height_of_endpoints hl hr hC0.le (by linarith)
  have hH := Analysis.tiltedBoxHeight_lt_thirty_three_hundredths hC0.le hC1
  rw [Analysis.tiltedBoxHeight] at hH
  constructor <;> linarith only [hEP, hn.1, hn.2, hH, hh0, hh1,
    sweptNiche_nonneg U (Real.pi / 2) C, sweptNiche_nonneg U (Real.pi / 2) (-C)]

theorem positive_affine_slope_of_middle_heights {U : Set Plane} {C h m c : ℝ}
    (hC : 0 < C) (hh : 0 < h)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1) : 0 < m := by
  nlinarith [haffine (-C) ⟨le_rfl, by linarith⟩, haffine C ⟨by linarith, le_rfl⟩]

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
  have hroof : p.2 ≤ m * p.1 + c := (le_capRoof hU.isCompact hp).trans
    (hU.capRoof_le_affine_of_affine_segment ha hb hab haffine p.1 ⟨p, hp, rfl⟩)
  have hlo : b ≤ p.1 :=
    le_of_mul_le_mul_left (by linarith only [hroof, hpy, hhigh, haffine b ⟨hab.le, le_rfl⟩]) hm
  have hedge : p ∈ MovingSofaOptimality.edge U (Real.pi / 2) := by
    refine ⟨hp, ?_⟩
    change coordDot p (unitNormal (Real.pi / 2)) = angleSupport U (Real.pi / 2)
    simp only [coordDot, unitNormal, angleSupport, Real.cos_pi_div_two, Real.sin_pi_div_two,
      mul_zero, mul_one, zero_add, hpy]
    exact hheight.symm
  have hxp : p.1 ∈ Icc (MovingSofaOptimality.vplus U (Real.pi / 2)).1
      (MovingSofaOptimality.vminus U (Real.pi / 2)).1 := by
    rw [← hU.horizontalProjection_edge (by simp : 0 ≤ Real.sin (Real.pi / 2))]
    exact ⟨p, hedge, rfl⟩
  exact ⟨hlo, hxp.2⟩

/-- The low companion cut of a tilted full maximum has a lower top and a positive left roof. -/
theorem IsFullCapMaximizer.tilted_companion_cut
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
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
  obtain ⟨ha, hb, -⟩ := hU.isCap.tilted_centered_middle hl hr hC
  have hleft := horizontalLeft_leftCompanionCap hU.isCap ha
  refine ⟨hm, ha, hb, hU.isCap.leftCompanionCap ha, hleft.trans hl, ?_, ?_⟩
  · rw [(hU.isCap.top_leftCompanionCap_of_positive_affine ha hb (by linarith) hm haffine).1, hlow]
    linarith
  · rw [hleft, hU.isCap.capRoof_leftCompanionCap ha ⟨le_rfl, by rw [hl]; linarith⟩]
    linarith [(hU.tilted_left_endpoint_height_bounds hl hr hC hC1 hh0.le hh1 hheight
      haffine hlow hhigh).1]

/-- The top projection for the literal low-wing zero and literal right top endpoint.
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
  set z := companionZero (leftCompanionCap U (-C))
  set b := (MovingSofaOptimality.vminus U (Real.pi / 2)).1
  have hC : 0 < C := by linarith
  obtain ⟨hm, ha, hb, hV, hlV, hVH, hVL⟩ :=
    hU.tilted_companion_cut hl hr hC0 hC1 hh0 hh1 hheight haffine hlow hhigh
  have hab : -C < C := by linarith
  have hhighPoint : (C, 1) ∈ U := hhigh ▸ capRoof_mem hU.isCap.isCompact hb
  have htop := hU.isCap.top_points_after_positive_affine ha hb hab hm hheight haffine hhigh
  have hCb : C ≤ b := (htop (C, 1) hhighPoint rfl).2
  have htopPoint : (b, 1) ∈ U := by
    rw [← (top_vminus_snd_eq_capHeight U).trans hheight]
    exact (MovingSofaOptimality.vminus_mem_edge hU.isCap.imported_isConvexBody _).1
  have hbR : b ≤ 2 * C := hr ▸ (hU.isCap.fst_mem_Icc htopPoint).2
  have hzaxis : z < 1 - 2 * C := by linarith only [hV.companionZero_lt_left_add_one hVH hVL, hlV]
  have hzC : z < C := by linarith only [hzaxis, hC0]
  have hJL : horizontalLeft U + capWidth U / 4 = -C := by unfold capWidth; rw [hl, hr]; ring
  have hJR : horizontalRight U - capWidth U / 4 = C := by unfold capWidth; rw [hl, hr]; ring
  have hJ := (hU.isCap.tilted_centered_middle hl hr hC).2.2
  -- The middle is positive from the low-wing zero to `C`; the selected moment bounds the length
  -- of the positive part by the outer windows outside the top.
  have hpos : C - max (-C) z ≤
      volume.real (Icc (-C) C ∩ {x : ℝ | 0 < sweptNiche U (Real.pi / 2) x}) := by
    rw [← Real.volume_real_Ioo_of_le (max_lt hab hzC).le]
    exact measureReal_mono (fun x hx => ⟨⟨(le_max_left _ _).trans hx.1.le, hx.2.le⟩,
      hU.isCap.sweptNiche_pos_of_low_wing_zero_lt hl hr hC0 hhigh hVH hVL hx⟩)
      ((measure_mono inter_subset_left).trans_lt measure_Icc_lt_top).ne
  have hmoment := hU.positive_middle_measure_le_outer_without_top hheight ⟨m, c, hJ ▸ haffine⟩
    hhighPoint htopPoint
  rw [hJ, hJL, hJR, hl, hr] at hmoment
  have hbound := hpos.trans (hmoment.trans (add_le_add
    (real_left_window_without_top_le (by linarith only [hC]) (by linarith only [hC])
      (by linarith only [hC, hCb]))
    (real_right_window_without_top_le (by linarith only [hC]) hbR le_rfl)))
  rw [min_eq_left hab.le, max_eq_right hCb] at hbound
  have hmax : max (C + z) 0 = C + max (-C) z := by
    rw [← max_add_add_left, add_neg_cancel, max_comm]
  refine le_antisymm (by linarith only [hbound, hmax]) (max_le ?_ (by linarith only [hCb]))
  -- A dry interval longer than the top would contradict the selected finite balance.
  by_contra! hnot
  set ε := ((C + z) - (b - C)) / 4 with hε
  have hdry := hU.dry_interval_length_le_top_width (a := -C + ε) (b := z - ε)
    (by linarith only [hε, hnot, hCb]) (by rw [hJL]; linarith only [hε, hnot])
    (by rw [hJR]; linarith only [hε, hnot, hzC]) hCb htop
    (fun x hx θ hθ => hU.isCap.secondWallNumerator_neg_of_lt_low_wing_zero
      ha hb hab haffine hhigh (by linarith only [hx.2, hε, hnot, hzC])
      (by linarith only [hx.2, hε, hnot])
      (by rw [hl]; linarith only [hx.2, hε, hnot, hzaxis]) hθ)
  linarith only [hdry, hε, hnot]

end AmbidextrousSofa
