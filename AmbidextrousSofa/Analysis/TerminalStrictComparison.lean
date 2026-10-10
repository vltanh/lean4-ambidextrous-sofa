module

public import AmbidextrousSofa.Analysis.TerminalCompanionComparison
public import AmbidextrousSofa.Analysis.TerminalExposure
public import AmbidextrousSofa.Analysis.CanonicalOneTurn

@[expose] public section

/-!
# Strict terminal exposure from the actual companion moments

The weighted companion estimate is compared with the literal outgoing
wall. Its strict circle margin covers the complete actual terminal
reserve interval. Continuity then extends strict exposure beyond the
reserve endpoint, contradicting the actual inward-cut exposure bound
at a largest-angle maximizer.

Curvature regularity and the early weighted-excess estimate remain
explicit analytic inputs. In particular this file does not assert the
proper charged-wing density theorem or discard its exceptional atoms.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem terminal_circle_reserve_localization {C c s z : ℝ}
    (hC : C ≤ 37 / 50) (hc : 0 < c) (hcut : 73 * c ^ 2 ≤ 9)
    (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1) (hz : z ≤ c / 2) :
    C + z < s := by
  have hcsmall := terminal_cosine_lt_forty_four_one_twenty_fifths hc hcut
  have hslow : (187 / 200 : ℝ) < s := by
    by_contra hbad
    have hsq := (sq_le_sq₀ hs.le (by norm_num : (0 : ℝ) ≤ 187 / 200)).2
      (le_of_not_gt hbad)
    nlinarith only [hsq, hcs, hcut]
  linarith only [hC, hz, hcsmall, hslow]

/-- Strict comparison is for the actual outgoing wall and the complete
visited niche, including every historical companion angle. -/
theorem IsDownwardCap.sweptNiche_lt_terminalWall_of_weighted_excess
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ}
    {K α C T_L T_R z : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hleft : horizontalLeft U = -2 * C)
    (hinitial : companionInitialOffset U = C - T_L)
    (htail : (terminalTailPoint U α).1 = C + T_R)
    (hC0 : (1 / 2 : ℝ) ≤ C) (hC1 : C ≤ 37 / 50)
    (hcut : 73 * Real.cos α ^ 2 ≤ 9)
    (hH : Real.sin α < (terminalTailPoint U α).2)
    (hTL : 0 ≤ T_L) (hTR : 0 ≤ T_R)
    (htop : T_L + 2 * T_R ≤ terminalTailInset U α)
    (hsub : Ioc (Real.pi / 2)
      (Real.arcsin (C + terminalTailReserve U α) + Real.pi / 2) ⊆ S)
    (hexcess : terminalWeightedExcess (fun t => ρ (t + Real.pi / 2))
      (Real.arcsin (C - T_L)) ≤ (39 / 4400 : ℝ) * Real.cos α)
    (hz0 : 0 ≤ z) (hz1 : z ≤ terminalTailReserve U α) :
    sweptNiche U α (-C + z) < firstWall U α (-C + z) := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0
    (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hαL⟩
  have hcs : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := by
    linarith only [Real.sin_sq_add_cos_sq α]
  obtain ⟨_hd0, hdc, _hw0, _hwbound, hwhalf⟩ := hU.terminalTailInset_bounds hα0 hαL hH
  have hcsmall := terminal_cosine_lt_forty_four_one_twenty_fifths hc hcut
  have hA : 0 < companionInitialOffset U := by
    rw [hinitial]
    linarith only [htop, hTR, hdc, hcsmall, hC0]
  have hcoord : (-C + z) - horizontalLeft U = C + z := by
    rw [hleft]
    ring
  have hAB : companionInitialOffset U ≤ (-C + z) - horizontalLeft U := by
    rw [hinitial, hcoord]
    linarith only [hTL, hz0]
  have hBα : (-C + z) - horizontalLeft U < Real.sin α := by
    rw [hcoord]
    exact terminal_circle_reserve_localization hC1 hc hcut hs hcs
      (hz1.trans hwhalf.le)
  have hsubz : Ioc (Real.pi / 2)
      (Real.arcsin ((-C + z) - horizontalLeft U) + Real.pi / 2) ⊆ S := by
    rw [hcoord]
    exact (Ioc_subset_Ioc le_rfl (add_le_add_left
      (Real.arcsin_le_arcsin (add_le_add_right hz1 C)) _)).trans hsub
  have hniche := hU.sweptNiche_le_circle_of_density hρ hρ0 hρK heq
    hα0 hαL hA hAB hBα hsubz
  rw [hinitial, hcoord] at hniche
  have hH1 : (terminalTailPoint U α).2 ≤ 1 :=
    (hU.inStrip (hU.terminalTailPoint_mem α)).2
  have hmargin := terminal_circle_margin_of_height hC0 hC1 hc hcut hs hcs hH hH1
    hTL hTR htop hz0 hz1
  have hwall : firstWall U α (-C + z) =
      Real.cos α / Real.sin α * (2 * C + T_R - terminalTailInset U α - z) := by
    rw [firstWall_eq_terminalTail U hs.ne' hc.ne']
    unfold terminalTailZero
    rw [htail]
    congr 1
    ring
  change (39 / 4400 : ℝ) * Real.cos α <
    Real.cos α / Real.sin α * (2 * C + T_R - terminalTailInset U α - z) -
      (circleHeight (C - T_L) - circleHeight (C + z)) at hmargin
  rw [hwall]
  linarith only [hniche, hexcess, hmargin]

/-- A continuous strict gap on a complete closed initial interval
persists beyond its right endpoint. Consequently its measure is
strictly larger than the length of that interval. -/
theorem volume_real_strict_region_gt_of_initial_interval
    {f g : ℝ → ℝ} {l r w : ℝ} (hf : Continuous f) (hg : Continuous g)
    (hw : 0 ≤ w) (hwr : l + w < r)
    (hstrict : ∀ x ∈ Icc l (l + w), f x < g x) :
    w < volume.real (Icc l r ∩ {x | f x < g x}) := by
  have hgap : {x | f x < g x} ∈ 𝓝 (l + w) :=
    (isOpen_lt hf hg).mem_nhds (hstrict (l + w) ⟨by linarith only [hw], le_rfl⟩)
  obtain ⟨a, b, hab, hlocal⟩ := mem_nhds_iff_exists_Ioo_subset.mp hgap
  obtain ⟨q, hq0, hq1⟩ := exists_between (lt_min hab.2 hwr)
  have hlq : l ≤ q := by linarith only [hq0, hw]
  have hsub : Icc l q ⊆ Icc l r ∩ {x | f x < g x} := by
    intro x hx
    refine ⟨⟨hx.1, hx.2.trans (hq1.trans_le (min_le_right _ _)).le⟩, ?_⟩
    by_cases hxw : x ≤ l + w
    · exact hstrict x ⟨hx.1, hxw⟩
    · exact hlocal ⟨hab.1.trans (lt_of_not_ge hxw),
        hx.2.trans_lt (hq1.trans_le (min_le_left _ _))⟩
  have hmeasure := measureReal_mono (μ := volume) hsub
    (measure_ne_top_of_subset inter_subset_left measure_Icc_lt_top.ne)
  rw [Real.volume_real_Icc_of_le hlq] at hmeasure
  linarith only [hq0, hmeasure]

/-- The contradiction uses the proved inward-cut exposure inequality
for the actual maximizer. It does not assume an occupation measure. -/
theorem IsJointCapMaximizer.false_of_companion_weighted_excess_of_tail_regime
    {U : Set Plane} {α m c C T_L T_R K : ℝ} {S : Set ℝ} {ρ : ℝ → ℝ}
    (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hinitial : companionInitialOffset U = C - T_L)
    (htail : (terminalTailPoint U α).1 = C + T_R)
    (hC0 : (1 / 2 : ℝ) ≤ C) (hC1 : C ≤ 37 / 50)
    (hcut : 73 * Real.cos α ^ 2 ≤ 9)
    (hTL : 0 ≤ T_L) (hTR : 0 ≤ T_R)
    (htop : T_L + 2 * T_R ≤ terminalTailInset U α)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hsub : Ioc (Real.pi / 2)
      (Real.arcsin (C + terminalTailReserve U α) + Real.pi / 2) ⊆ S)
    (hexcess : terminalWeightedExcess (fun t => ρ (t + Real.pi / 2))
      (Real.arcsin (C - T_L)) ≤ (39 / 4400 : ℝ) * Real.cos α) : False := by
  have hH := (hU.terminalTailPoint_bounds_of_tail_regime hregime hαL hheight haffine).2.1
  obtain ⟨_hd0, _hdc, hw0, _hwbound, hwhalf⟩ :=
    hU.isCap.terminalTailInset_bounds hU.angle_pos hαL hH
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hU.angle_pos, Real.pi_pos], hαL⟩
  have hcsmall := terminal_cosine_lt_forty_four_one_twenty_fifths hc hcut
  have hwr : -C + terminalTailReserve U α < C := by
    linarith only [hwhalf, hcsmall, hC0]
  have hstrict : ∀ x ∈ Icc (-C) (-C + terminalTailReserve U α),
      sweptNiche U α x < firstWall U α x := by
    intro x hx
    have h := hU.isCap.sweptNiche_lt_terminalWall_of_weighted_excess hρ hρ0 hρK heq
      hU.angle_pos hαL hleft hinitial htail hC0 hC1 hcut hH hTL hTR htop hsub hexcess
      (z := x + C) (by linarith only [hx.1]) (by linarith only [hx.2])
    simpa only [show -C + (x + C) = x by ring] using h
  have hlarge := volume_real_strict_region_gt_of_initial_interval
    (hU.isCap.continuous_sweptNiche_terminalAngle hU.angle_mem)
    (continuous_firstWall U α) hw0.le hwr hstrict
  have hsmall := hU.terminal_strict_exposure_measure_le_reserve_of_tail_regime hregime hαL hheight haffine
  rw [middleHalfInterval_eq_centered hleft hright] at hsmall
  exact (not_lt_of_ge hsmall) hlarge

theorem IsJointCapMaximizer.false_of_companion_weighted_excess
    {U : Set Plane} {α m c C T_L T_R K : ℝ} {S : Set ℝ} {ρ : ℝ → ℝ}
    (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hinitial : companionInitialOffset U = C - T_L)
    (htail : (terminalTailPoint U α).1 = C + T_R)
    (hC0 : (1 / 2 : ℝ) ≤ C) (hC1 : C ≤ 37 / 50)
    (hcut : 73 * Real.cos α ^ 2 ≤ 9)
    (hTL : 0 ≤ T_L) (hTR : 0 ≤ T_R)
    (htop : T_L + 2 * T_R ≤ terminalTailInset U α)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hsub : Ioc (Real.pi / 2)
      (Real.arcsin (C + terminalTailReserve U α) + Real.pi / 2) ⊆ S)
    (hexcess : terminalWeightedExcess (fun t => ρ (t + Real.pi / 2))
      (Real.arcsin (C - T_L)) ≤ (39 / 4400 : ℝ) * Real.cos α) : False := by
  exact IsJointCapMaximizer.false_of_companion_weighted_excess_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hαL hheight haffine) hαL hheight haffine hleft hright
    hinitial htail hC0 hC1 hcut hTL hTR htop hρ hρ0 hρK heq hsub hexcess

end AmbidextrousSofa
