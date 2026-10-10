module

public import AmbidextrousSofa.Analysis.ClosedSupportPair
public import AmbidextrousSofa.Analysis.CornerSignPhases
public import AmbidextrousSofa.Analysis.HorizontalNicheGraphs
public import AmbidextrousSofa.Measure.SignedRoofIntegralAC

@[expose] public section

/-!
# The actual horizontal signed niche integral

The closed support pair belongs to the same actual cap and uses its own
Lebesgue density. Strict tangency separation supplies the ordered sign
phases. Their three actual graph identities and the absolutely continuous
integration theorem then give the clipped signed niche integral.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem horizontalSupportQuarterPair_tangencies
    {U : Set Plane} (hU : IsDownwardCap U) {ρ : ℝ → ℝ} {K t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    let F := horizontalSupportQuarterPair hU hρ hρ0 hρK heq
    firstTangentPoint F.f F.fD t = firstTangency U t ∧
      secondTangentPoint F.g F.gD t = secondTangency U t ∧
      innerCornerPoint F.f F.g t = attachedCorner U t := by
  have hr := horizontal_density_quarter_restrictions heq
  have hfD := hU.closedSupportDerivative_eq_supportTangent hρ hρ0 hρK hr.1
    (d := 0) (by simpa only [zero_add] using (Subset.rfl :
      Ioo (0 : ℝ) (Real.pi / 2) ⊆ Ioo 0 (Real.pi / 2))) ht.1.le ht.2
  have hgD := hU.closedSupportDerivative_eq_supportTangent hρ hρ0 hρK hr.2
    (d := Real.pi / 2) (by intro s hs; exact ⟨hs.1, by linarith [hs.2]⟩) ht.1.le ht.2
  simp only [add_zero] at hfD
  dsimp only [horizontalSupportQuarterPair, supportQuarterPair]
  constructor
  · apply Prod.ext
    · change (angleSupport U t - 1) * Real.cos t -
        closedSupportDerivative U ρ 0 t * Real.sin t = (firstTangency U t).1
      rw [hfD, firstTangency_fst_eq_support]
    · change (angleSupport U t - 1) * Real.sin t +
        closedSupportDerivative U ρ 0 t * Real.cos t = (firstTangency U t).2
      rw [hfD, firstTangency_snd_eq_support]
  constructor
  · rw [secondTangentPoint, companionSupportPoint_coordinates]
    apply Prod.ext
    · dsimp only [Prod.fst]
      rw [hgD, secondTangency_fst_eq_support]
      ring
    · dsimp only [Prod.snd]
      rw [hgD, secondTangency_snd_eq_support]
      ring
  · apply Prod.ext
    · exact (attachedCorner_fst_eq_support U t).symm
    · exact (attachedCorner_snd_eq_support U t).symm

/-- The actual endpoint traces and strict tangency gap force the two
ordered sign switches. No choice of contact phases is an input. -/
theorem IsFullCapMaximizer.horizontalSupportQuarterPair_sign_switches
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {K : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
      ρ t ≤ 1 ∧ ρ (t + Real.pi / 2) ≤ 1) :
    let F := horizontalSupportQuarterPair hU.isCap hρ hρ0 hρK heq
    ∃ b d : ℝ, b ∈ Ioo 0 (Real.pi / 2) ∧ d ∈ Ioo b (Real.pi / 2) ∧
      supportP F.fD F.g b = 0 ∧ supportQ F.gD F.f d = 0 ∧
      (∀ t ∈ Icc 0 b, 0 ≤ supportP F.fD F.g t) ∧
      (∀ t ∈ Icc b (Real.pi / 2), supportP F.fD F.g t ≤ 0) ∧
      (∀ t ∈ Icc 0 d, 0 ≤ supportQ F.gD F.f t) ∧
      (∀ t ∈ Icc d (Real.pi / 2), supportQ F.gD F.f t ≤ 0) := by
  let F := horizontalSupportQuarterPair hU.isCap hρ hρ0 hρK heq
  have hcal := horizontalSupportQuarterPair_corner_calculus hU.isCap hρ hρ0 hρK heq
  rcases hU.horizontalSupportQuarterPair_traces hρ hρ0 hρK heq hheight hmiddle with
    ⟨hf0, hg0, hfL, hgL, hfD0, hgD0, hfDL, hgDL⟩
  have hpos := hU.endpoint_heights_pos_of_affine hheight
    ⟨0, 1, by intro x hx; simpa only [zero_mul, zero_add] using hmiddle x hx⟩
  have hw := hU.two_lt_width
  have hp0 : 0 < supportP F.fD F.g 0 := by
    dsimp only [supportP]
    rw [hfD0, hg0]
    linarith [hpos.1]
  have hpL : supportP F.fD F.g (Real.pi / 2) < 0 := by
    dsimp only [supportP]
    rw [hfDL, hgL]
    dsimp only [capWidth] at hw ⊢
    linarith
  have hq0 : 0 < supportQ F.gD F.f 0 := by
    dsimp only [supportQ]
    rw [hgD0, hf0]
    dsimp only [capWidth] at hw ⊢
    linarith
  have hqL : supportQ F.gD F.f (Real.pi / 2) < 0 := by
    dsimp only [supportQ]
    rw [hgDL, hfL]
    linarith [hpos.2]
  have hsep : ∀ t ∈ Ioo 0 (Real.pi / 2),
      0 < supportQ F.gD F.f t ∨ supportP F.fD F.g t < 0 := by
    intro t ht
    have hv := horizontalSupportQuarterPair_velocities hU.isCap hρ hρ0 hρK heq ht
    rcases hU.corner_velocity_pos_or_pos_of_unit_density hρ hρ0 hρK heq hunit ht with hq | hr
    · left
      rw [hv.2]
      exact hq
    · right
      rw [hv.1]
      linarith
  exact exists_ordered_corner_sign_switches (by linarith [Real.pi_pos])
    hcal.1 hcal.2.1 hcal.2.2 hunit hp0 hpL hq0 hqL hsep

/-- The niche integral in the full cap score is the signed support
expression with its literal clipped momenta. All graph, sign, density,
and endpoint hypotheses are discharged from the actual horizontal cap. -/
theorem IsFullCapMaximizer.twice_middle_niche_eq_signed_support
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {K : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
      ρ t ≤ 1 ∧ ρ (t + Real.pi / 2) ≤ 1) :
    let F := horizontalSupportQuarterPair hU.isCap hρ hρ0 hρK heq
    2 * (∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
      sweptNiche U (Real.pi / 2) x) =
      -(∫ t in (0 : ℝ)..(Real.pi / 2), cornerDensity F.f F.g F.fD F.gD t) +
      (∫ t in (0 : ℝ)..(Real.pi / 2), min (supportP F.fD F.g t) 0 ^ 2) +
      ∫ t in (0 : ℝ)..(Real.pi / 2), max (supportQ F.gD F.f t) 0 ^ 2 := by
  let F := horizontalSupportQuarterPair hU.isCap hρ hρ0 hρK heq
  have hr := horizontal_density_quarter_restrictions heq
  obtain ⟨b, d, hb, hd, hpb, hqd, hpplus, hpminus, hqplus, hqminus⟩ :=
    hU.horizontalSupportQuarterPair_sign_switches hheight hmiddle hρ hρ0 hρK heq hunit
  have hf : Continuous F.f := hU.isCap.imported_isConvexBody.continuous_supp
  have hg : Continuous F.g := hU.isCap.imported_isConvexBody.continuous_supp.comp
    (continuous_id.add_const (Real.pi / 2))
  have hfD : Continuous F.fD := hU.isCap.continuous_closedSupportDerivative hρ hρ0 hρK 0
  have hgD : Continuous F.gD :=
    hU.isCap.continuous_closedSupportDerivative hρ hρ0 hρK (Real.pi / 2)
  have hac := supportQuarterPair_absolutelyContinuous hU.isCap hU.isCap
    hρ hρ0 hρK hρ hρ0 hρK hr.1 hr.2
  have hderiv := supportQuarterPair_ae_derivatives hU.isCap hU.isCap
    hρ hρ0 hρK hρ hρ0 hρK hr.1 hr.2
  have hfDD : IntervalIntegrable (fun t => ρ t - F.f t) volume 0 (Real.pi / 2) :=
    (intervalIntegrable_bounded_real_density hρ hρ0 hρK _ _).sub (hf.intervalIntegrable _ _)
  have hgDD : IntervalIntegrable (fun t => ρ (t + Real.pi / 2) - F.g t)
      volume 0 (Real.pi / 2) :=
    (intervalIntegrable_bounded_real_density
      (hρ.comp (measurable_id.add_const (Real.pi / 2)))
      (fun t => hρ0 (t + Real.pi / 2)) (fun t => hρK (t + Real.pi / 2)) _ _).sub
      (hg.intervalIntegrable _ _)
  rcases hU.horizontalSupportQuarterPair_traces hρ hρ0 hρK heq hheight hmiddle with
    ⟨hf0, hg0, hfL, hgL, hfD0, hgD0, hfDL, hgDL⟩
  have hgraphD : ∀ t ∈ Ioo 0 d,
      sweptNiche U (Real.pi / 2) (secondTangentPoint F.g F.gD t).1 =
        (secondTangentPoint F.g F.gD t).2 := by
    intro t ht
    have htL : t ∈ Ioo 0 (Real.pi / 2) := ⟨ht.1, ht.2.trans hd.2⟩
    have hpoints := horizontalSupportQuarterPair_tangencies hU.isCap hρ hρ0 hρK heq htL
    rw [hpoints.2.1]
    apply hU.sweptNiche_secondTangency_of_unit_density hheight hmiddle
      hρ hρ0 hρK heq (hunit.mono fun _ h => h.2) htL
    have hsign := hqplus t ⟨ht.1.le, ht.2.le⟩
    rwa [(horizontalSupportQuarterPair_velocities hU.isCap hρ hρ0 hρK heq htL).2] at hsign
  have hgraphC : ∀ t ∈ Ioo b d,
      sweptNiche U (Real.pi / 2) (innerCornerPoint F.f F.g t).1 =
        (innerCornerPoint F.f F.g t).2 := by
    intro t ht
    have htL : t ∈ Ioo 0 (Real.pi / 2) := ⟨hb.1.trans ht.1, ht.2.trans hd.2⟩
    have hpoints := horizontalSupportQuarterPair_tangencies hU.isCap hρ hρ0 hρK heq htL
    have hv := horizontalSupportQuarterPair_velocities hU.isCap hρ hρ0 hρK heq htL
    rw [hpoints.2.2]
    apply hU.sweptNiche_corner_of_unit_density hheight hmiddle hρ hρ0 hρK heq hunit htL
    · have hsign := hqplus t ⟨htL.1.le, ht.2.le⟩
      rwa [hv.2] at hsign
    · have hsign := hpminus t ⟨ht.1.le, htL.2.le⟩
      rw [hv.1] at hsign
      linarith
  have hgraphB : ∀ t ∈ Ioo b (Real.pi / 2),
      sweptNiche U (Real.pi / 2) (firstTangentPoint F.f F.fD t).1 =
        (firstTangentPoint F.f F.fD t).2 := by
    intro t ht
    have htL : t ∈ Ioo 0 (Real.pi / 2) := ⟨hb.1.trans ht.1, ht.2⟩
    have hpoints := horizontalSupportQuarterPair_tangencies hU.isCap hρ hρ0 hρK heq htL
    rw [hpoints.1]
    apply hU.sweptNiche_firstTangency_of_unit_density hheight hmiddle
      hρ hρ0 hρK heq (hunit.mono fun _ h => h.1) htL
    have hsign := hpminus t ⟨ht.1.le, ht.2.le⟩
    rw [(horizontalSupportQuarterPair_velocities hU.isCap hρ hρ0 hρK heq htL).1] at hsign
    linarith
  have hN : Continuous (sweptNiche U (Real.pi / 2)) := by
    have hpb : partialBarrier U (Real.pi / 2) = sweptNiche U (Real.pi / 2) :=
      funext hU.isCap.partialBarrier_pi_div_two
    rw [← hpb]
    exact hU.isCap.continuous_partialBarrier_pi_div_two
  have hsigned := signedRoof_integral_of_graphs_ac hb.1.le hd.1.le hd.2.le
    hN hf hg hfD hgD
    hac.1 hac.2.1 hac.2.2.1 hac.2.2.2 hderiv hfDD hgDD
    hfL hg0 hpb hqd hgraphD hgraphC hgraphB
  have hpcont : Continuous (supportP F.fD F.g) := (hfD.sub hg).add continuous_const
  have hqcont : Continuous (supportQ F.gD F.f) := (hgD.add hf).sub continuous_const
  have hpclip := integral_min_sq_of_sign_switch hb.1.le hb.2.le hpcont hpplus hpminus
  have hqclip := integral_max_sq_of_sign_switch (hb.1.trans hd.1).le hd.2.le
    hqcont hqplus hqminus
  rw [← hpclip, ← hqclip] at hsigned
  rw [hgD0, hfDL, neg_neg, neg_neg] at hsigned
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hmidle : horizontalLeft U + capWidth U / 4 ≤
      horizontalRight U - capWidth U / 4 := by
    dsimp only [capWidth]
    linarith
  have hinterval : (∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
      sweptNiche U (Real.pi / 2) x) =
      ∫ x in (horizontalLeft U + capWidth U / 4)..(horizontalRight U - capWidth U / 4),
        sweptNiche U (Real.pi / 2) x := by
    change (∫ x in Icc (horizontalLeft U + capWidth U / 4)
      (horizontalRight U - capWidth U / 4), sweptNiche U (Real.pi / 2) x) = _
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hmidle]
  rw [hinterval]
  exact hsigned

end AmbidextrousSofa
