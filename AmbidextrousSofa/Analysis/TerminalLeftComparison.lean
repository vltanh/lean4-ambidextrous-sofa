import AmbidextrousSofa.Analysis.LeftCompanionDensity
import AmbidextrousSofa.Analysis.TerminalStrictComparison

/-!
# Terminal comparison for the actual left charged wing

The left cut controls the positive visited niche of the original cap.
Its density is constructed from the proper selected polygons, and its
literal supporting endpoints satisfy both coordinate moments. The
circle estimate therefore applies in every sign of the middle slope,
including the positive slope with its low initial endpoint.

The final theorem states the remaining analytic obligation precisely:
the actual early weighted excess must exceed the exact terminal margin
at any maximum with the displayed terminal and top geometry. Density
regularity is a conclusion of the construction, not an extra premise.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

/-- In nonpositive tilt the left cut retains the original top endpoint
and hence both original companion initial coordinates. -/
theorem IsDownwardCap.leftCompanion_initial_data_of_nonpos_affine
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (hm : m ≤ 0)
    (haffine : ∀ x ∈ Icc a b, capRoof U x = m * x + c) :
    Imported.vplus (leftCompanionCap U a) (Real.pi / 2) =
        Imported.vplus U (Real.pi / 2) ∧
      companionInitialOffset (leftCompanionCap U a) = companionInitialOffset U ∧
      companionInitialDeficit (leftCompanionCap U a) = companionInitialDeficit U := by
  have htop := hU.vplus_leftCompanionCap_eq_of_affine ha hb hab haffine
    (by simp only [Real.sin_pi_div_two]; norm_num : 0 < Real.sin (Real.pi / 2))
    (by simpa only [Real.cos_pi_div_two, Real.sin_pi_div_two, mul_one, zero_add] using hm)
  refine ⟨htop, ?_, ?_⟩
  · unfold companionInitialOffset
    rw [htop, horizontalLeft_leftCompanionCap hU ha]
  · unfold companionInitialDeficit
    rw [← top_vplus_snd_eq_capHeight (leftCompanionCap U a), htop,
      top_vplus_snd_eq_capHeight U]

theorem Ioc_companion_arcsin_subset {B : ℝ} (hB : B < 1) :
    Ioc (Real.pi / 2) (Real.arcsin B + Real.pi / 2) ⊆
      Ioo (Real.pi / 2) Real.pi := by
  intro t ht
  exact ⟨ht.1, ht.2.trans_lt (by linarith only [Real.arcsin_lt_pi_div_two.mpr hB])⟩

/-- The actual selected density supplies both literal endpoint moments
through every compact subarc of the proper companion semicircle. -/
theorem IsJointCapMaximizer.exists_leftCompanion_moment_density
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2)
    (haffine : ∀ z ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U z = m * z + c) :
    let V := leftCompanionCap U (horizontalLeft U + capWidth U / 4)
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ 8 * (|horizontalLeft U| + |horizontalRight U| + 1) + 24) ∧
      (upperCurvature V).restrict (Ioo (Real.pi / 2) Real.pi) =
        (volume.restrict (Ioo (Real.pi / 2) Real.pi)).withDensity
          (fun t => ENNReal.ofReal (ρ t)) ∧
      ∀ t : ℝ, 0 ≤ t → t < Real.pi / 2 →
        shiftedCompanionX V t - (horizontalLeft U + companionInitialOffset V) =
            (∫ r in 0..t, (1 - ρ (r + Real.pi / 2)) * Real.cos r) ∧
          shiftedCompanionY V t + companionInitialDeficit V =
            ∫ r in 0..t, (1 - ρ (r + Real.pi / 2)) * Real.sin r := by
  dsimp only
  obtain ⟨ρ, hρ, hbounds, _hzero, heq⟩ := hU.leftCompanion_curvature_density hproper haffine
  have hwidth : 0 < capWidth U := by linarith only [hU.width_bounds.1, one_lt_M]
  obtain ⟨ha, _hb, _hab⟩ := hU.isCap.middleChord_endpoints hwidth
  have hV := hU.isCap.leftCompanionCap ha
  have hleft := horizontalLeft_leftCompanionCap hU.isCap ha
  refine ⟨ρ, hρ, hbounds, heq, ?_⟩
  intro t ht0 htL
  have hsub : Ioc (Real.pi / 2) (t + Real.pi / 2) ⊆ Ioo (Real.pi / 2) Real.pi := by
    intro r hr
    exact ⟨hr.1, hr.2.trans_lt (by linarith only [htL])⟩
  have h := hV.shiftedCompanion_eq_initial_add_integral_of_density hρ
    (fun r => (hbounds r).1) (fun r => (hbounds r).2) heq ht0 hsub
  simpa only [hleft] using h

/-- The exact circle margin controls the original outgoing wall using
the actual cut density. All historical companion angles remain in the
visited niche on the left side of the conclusion. -/
theorem IsDownwardCap.sweptNiche_lt_terminalWall_of_leftCompanion_weighted_excess
    {U : Set Plane} (hU : IsDownwardCap U) {ρ : ℝ → ℝ}
    {K α C T_L T_R m c z : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature (leftCompanionCap U (-C))).restrict (Ioo (Real.pi / 2) Real.pi) =
      (volume.restrict (Ioo (Real.pi / 2) Real.pi)).withDensity
        (fun t => ENNReal.ofReal (ρ t)))
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hinitial : companionInitialOffset (leftCompanionCap U (-C)) = C - T_L)
    (htail : (terminalTailPoint U α).1 = C + T_R)
    (hC0 : (1 / 2 : ℝ) ≤ C) (hC1 : C ≤ 37 / 50)
    (hcut : 73 * Real.cos α ^ 2 ≤ 9)
    (hH : Real.sin α < (terminalTailPoint U α).2)
    (hTL : 0 ≤ T_L) (hTR : 0 ≤ T_R)
    (htop : T_L + 2 * T_R ≤ terminalTailInset U α)
    (hexcess : terminalWeightedExcess (fun t => ρ (t + Real.pi / 2))
      (Real.arcsin (C - T_L)) ≤ (39 / 4400 : ℝ) * Real.cos α)
    (hz0 : 0 ≤ z) (hz1 : z ≤ terminalTailReserve U α) :
    sweptNiche U α (-C + z) < firstWall U α (-C + z) := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0
    (by linarith only [hαL, Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [hα0, Real.pi_pos], hαL⟩
  have hcs : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := by
    linarith only [Real.sin_sq_add_cos_sq α]
  obtain ⟨_hd0, hdc, _hw0, _hwbound, hwhalf⟩ := hU.terminalTailInset_bounds hα0 hαL hH
  have hcsmall := terminal_cosine_lt_forty_four_one_twenty_fifths hc hcut
  have ha : -C ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hleft, hright]
    constructor <;> linarith only [hC0]
  have hb : C ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hleft, hright]
    constructor <;> linarith only [hC0]
  have hab : -C < C := by linarith only [hC0]
  have hxb : -C + z ≤ C := by linarith only [hz1, hwhalf, hcsmall, hC0]
  have hA : 0 < companionInitialOffset (leftCompanionCap U (-C)) := by
    rw [hinitial]
    linarith only [htop, hTR, hdc, hcsmall, hC0]
  have hcoord : (-C + z) - horizontalLeft U = C + z := by rw [hleft]; ring
  have hAB : companionInitialOffset (leftCompanionCap U (-C)) ≤ (-C + z) - horizontalLeft U := by
    rw [hinitial, hcoord]
    linarith only [hTL, hz0]
  have hBα : (-C + z) - horizontalLeft U < Real.sin α := by
    rw [hcoord]
    exact terminal_circle_reserve_localization hC1 hc hcut hs hcs (hz1.trans hwhalf.le)
  have hniche := hU.sweptNiche_le_circle_of_leftCompanion_density ha hb hab haffine hxb
    hρ hρ0 hρK heq hα0 hαL hA hAB hBα
    (Ioc_companion_arcsin_subset (hBα.trans_le (Real.sin_le_one α)))
  rw [hinitial, hcoord] at hniche
  have hH1 : (terminalTailPoint U α).2 ≤ 1 := (hU.inStrip (hU.terminalTailPoint_mem α)).2
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

theorem IsJointCapMaximizer.false_of_leftCompanion_weighted_excess
    {U : Set Plane} {α m c C T_L T_R K : ℝ} {ρ : ℝ → ℝ}
    (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hinitial : companionInitialOffset (leftCompanionCap U (-C)) = C - T_L)
    (htail : (terminalTailPoint U α).1 = C + T_R)
    (hC0 : (1 / 2 : ℝ) ≤ C) (hC1 : C ≤ 37 / 50)
    (hcut : 73 * Real.cos α ^ 2 ≤ 9)
    (hTL : 0 ≤ T_L) (hTR : 0 ≤ T_R)
    (htop : T_L + 2 * T_R ≤ terminalTailInset U α)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature (leftCompanionCap U (-C))).restrict (Ioo (Real.pi / 2) Real.pi) =
      (volume.restrict (Ioo (Real.pi / 2) Real.pi)).withDensity
        (fun t => ENNReal.ofReal (ρ t)))
    (hexcess : terminalWeightedExcess (fun t => ρ (t + Real.pi / 2))
      (Real.arcsin (C - T_L)) ≤ (39 / 4400 : ℝ) * Real.cos α) : False := by
  have hH := (hU.terminalTailPoint_bounds hLargest hαL hheight haffine).2.1
  obtain ⟨_hd0, _hdc, hw0, _hwbound, hwhalf⟩ :=
    hU.isCap.terminalTailInset_bounds hU.angle_pos hαL hH
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [hU.angle_pos, Real.pi_pos], hαL⟩
  have hcsmall := terminal_cosine_lt_forty_four_one_twenty_fifths hc hcut
  have hwr : -C + terminalTailReserve U α < C := by linarith only [hwhalf, hcsmall, hC0]
  have haff : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c := by
    simpa only [middleHalfInterval_eq_centered hleft hright] using haffine
  have hstrict : ∀ x ∈ Icc (-C) (-C + terminalTailReserve U α),
      sweptNiche U α x < firstWall U α x := by
    intro x hx
    have h := hU.isCap.sweptNiche_lt_terminalWall_of_leftCompanion_weighted_excess
      hρ hρ0 hρK heq hU.angle_pos hαL hleft hright haff hinitial htail hC0 hC1 hcut hH
      hTL hTR htop hexcess (z := x + C)
      (by linarith only [hx.1]) (by linarith only [hx.2])
    simpa only [show -C + (x + C) = x by ring] using h
  have hlarge := volume_real_strict_region_gt_of_initial_interval
    (hU.isCap.continuous_sweptNiche_terminalAngle hU.angle_mem)
    (continuous_firstWall U α) hw0.le hwr hstrict
  have hsmall := hU.terminal_strict_exposure_measure_le_reserve hLargest hαL hheight haffine
  rw [middleHalfInterval_eq_centered hleft hright] at hsmall
  exact (not_lt_of_ge hsmall) hlarge

/-- A genuine proper maximum with the terminal and top geometry must
have excessive early weighted curvature on its actual left charged
wing. The density in this conclusion is constructed inside the theorem. -/
theorem IsJointCapMaximizer.exists_leftCompanion_density_excess_gt
    {U : Set Plane} {α m c C T_L T_R : ℝ}
    (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hinitial : companionInitialOffset (leftCompanionCap U (-C)) = C - T_L)
    (htail : (terminalTailPoint U α).1 = C + T_R)
    (hC0 : (1 / 2 : ℝ) ≤ C) (hC1 : C ≤ 37 / 50)
    (hcut : 73 * Real.cos α ^ 2 ≤ 9)
    (hTL : 0 ≤ T_L) (hTR : 0 ≤ T_R)
    (htop : T_L + 2 * T_R ≤ terminalTailInset U α) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ 8 * (|horizontalLeft U| + |horizontalRight U| + 1) + 24) ∧
      (upperCurvature (leftCompanionCap U (-C))).restrict (Ioo (Real.pi / 2) Real.pi) =
        (volume.restrict (Ioo (Real.pi / 2) Real.pi)).withDensity
          (fun t => ENNReal.ofReal (ρ t)) ∧
      (39 / 4400 : ℝ) * Real.cos α <
        terminalWeightedExcess (fun t => ρ (t + Real.pi / 2)) (Real.arcsin (C - T_L)) := by
  obtain ⟨ρ, hρ, hbounds, _hzero, heq⟩ := hU.leftCompanion_curvature_density hαL haffine
  have hquarter : horizontalLeft U + capWidth U / 4 = -C := by
    unfold capWidth
    rw [hleft, hright]
    ring
  rw [hquarter] at heq
  refine ⟨ρ, hρ, hbounds, heq, ?_⟩
  by_contra hbad
  exact hU.false_of_leftCompanion_weighted_excess hLargest hαL hheight haffine
    hleft hright hinitial htail hC0 hC1 hcut hTL hTR htop hρ
    (fun t => (hbounds t).1) (fun t => (hbounds t).2) heq (le_of_not_gt hbad)

end AmbidextrousSofa
