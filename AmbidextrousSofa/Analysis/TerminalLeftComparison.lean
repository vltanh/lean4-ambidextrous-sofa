module

public import AmbidextrousSofa.Analysis.LeftCompanionDensity
public import AmbidextrousSofa.Analysis.TerminalStrictComparison

@[expose] public section

/-!
# Terminal comparison for the actual left charged wing

The left cut controls the positive visited niche of the original cap, so
the circle estimate applies in every sign of the middle slope, including
the positive slope with its low initial endpoint. With the exact circle
margin it makes the outgoing wall strictly exposed beyond the reserve,
which the exposure bound forbids. Hence the early weighted excess of the
cut density must exceed the exact terminal margin at any maximum with the
displayed terminal and top geometry.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

/-- The exact circle margin controls the original outgoing wall using
the actual cut density, on the whole initial reserve interval. This
contradicts the bound of the strict terminal exposure by the reserve. -/
theorem IsJointCapMaximizer.false_of_leftCompanion_weighted_excess_of_tail_regime
    {U : Set Plane} {α m c C T_L T_R K : ℝ} {ρ : ℝ → ℝ}
    (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
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
  obtain ⟨hs, hc⟩ := terminal_sin_cos_pos hU.angle_pos hαL
  have hH := (hU.terminalTailPoint_bounds_of_tail_regime hregime hαL hheight haffine).2.1
  have hH1 := (hU.isCap.inStrip (hU.isCap.terminalTailPoint_mem α)).2
  obtain ⟨-, hdc, hw0, -, hwhalf⟩ := hU.isCap.terminalTailInset_bounds hU.angle_pos hαL hH
  have hcsmall := terminal_cosine_lt_forty_four_one_twenty_fifths hc hcut
  have hP := horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex
  have ha : -C ∈ horizontalProjection U := by
    rw [hP, hleft, hright]; constructor <;> linarith only [hC0]
  have hb : C ∈ horizontalProjection U := by
    rw [hP, hleft, hright]; constructor <;> linarith only [hC0]
  have haff : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c := by
    simpa only [middleHalfInterval_eq_centered hleft hright] using haffine
  have hstrict : ∀ x ∈ Icc (-C) (-C + terminalTailReserve U α),
      sweptNiche U α x < firstWall U α x := by
    rintro x ⟨hx0, hx1⟩
    obtain ⟨z, rfl⟩ : ∃ z, x = -C + z := ⟨x + C, by ring⟩
    have hz0 : 0 ≤ z := by linarith only [hx0]
    have hz1 : z ≤ terminalTailReserve U α := by linarith only [hx1]
    have hcoord : -C + z - horizontalLeft U = C + z := by rw [hleft]; ring
    have hBα : C + z < Real.sin α := terminal_circle_reserve_localization hC1 hc hcut hs
      (Real.cos_sq_add_sin_sq α) (hz1.trans hwhalf.le)
    have harcsin := Real.arcsin_lt_pi_div_two.mpr (hBα.trans_le (Real.sin_le_one α))
    have hniche := hU.isCap.sweptNiche_le_circle_of_leftCompanion_density ha hb
      (by linarith only [hC0]) haff (by linarith only [hz1, hwhalf, hcsmall, hC0]) hρ hρ0 hρK
      heq hU.angle_pos hαL (by rw [hinitial]; linarith only [htop, hTR, hdc, hcsmall, hC0])
      (by rw [hinitial, hcoord]; linarith only [hTL, hz0]) (hcoord ▸ hBα)
      fun t ht => ⟨ht.1, ht.2.trans_lt (by rw [hcoord]; linarith only [harcsin])⟩
    rw [hinitial, hcoord] at hniche
    have hmargin := terminal_circle_margin_of_height hC0 hC1 hc hcut hs (Real.cos_sq_add_sin_sq α)
      hH hH1 hTL hTR htop hz0 hz1
    rw [firstWall_eq_terminalTail U hs.ne' hc.ne', terminalTailZero, htail]
    unfold terminalTailInset
    linarith only [hniche, hexcess, hmargin]
  have hsmall := hU.terminal_strict_exposure_measure_le_reserve_of_tail_regime hregime hαL hheight
    haffine
  rw [middleHalfInterval_eq_centered hleft hright] at hsmall
  exact hsmall.not_gt (volume_real_strict_region_gt_of_initial_interval
    (hU.isCap.continuous_sweptNiche_terminalAngle hU.angle_mem) (continuous_firstWall U α) hw0.le
    (by linarith only [hwhalf, hcsmall, hC0]) hstrict)

end AmbidextrousSofa
