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
    (d := 0) (by rw [zero_add]) ht.1.le ht.2
  have hgD := hU.closedSupportDerivative_eq_supportTangent hρ hρ0 hρK hr.2
    (d := Real.pi / 2) (fun s hs => ⟨hs.1, by linarith [hs.2]⟩) ht.1.le ht.2
  rw [add_zero] at hfD
  simp only [horizontalSupportQuarterPair, supportQuarterPair, firstTangentPoint,
    secondTangentPoint, innerCornerPoint, Reference.supportPoint,
    companionSupportPoint_coordinates, Prod.ext_iff, hfD, hgD, firstTangency_fst_eq_support,
    firstTangency_snd_eq_support, secondTangency_fst_eq_support, secondTangency_snd_eq_support,
    attachedCorner_fst_eq_support, attachedCorner_snd_eq_support, and_true, true_and]
  constructor <;> ring

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
  rcases hU.horizontalSupportQuarterPair_traces hρ hρ0 hρK heq hheight hmiddle with
    ⟨hf0, hg0, hfL, hgL, hfD0, hgD0, hfDL, hgDL⟩
  have hw := hU.two_lt_width
  have hwr : capWidth U = horizontalRight U - horizontalLeft U := rfl
  have hpos := hU.endpoint_heights_pos_of_affine hheight ⟨0, 1, by simpa using hmiddle⟩
  have hvel {t} (ht : t ∈ Ioo 0 (Real.pi / 2)) :=
    horizontalSupportQuarterPair_velocities hU.isCap hρ hρ0 hρK heq ht
  have htan {t} (ht : t ∈ Ioo 0 (Real.pi / 2)) :=
    horizontalSupportQuarterPair_tangencies hU.isCap hρ hρ0 hρK heq ht
  -- the endpoint traces and the strict tangency gap force two ordered sign switches
  have hcal := horizontalSupportQuarterPair_corner_calculus hU.isCap hρ hρ0 hρK heq
  obtain ⟨b, d, hb, hd, hpb, hqd, hpplus, hpminus, hqplus, hqminus⟩ :=
    exists_ordered_corner_sign_switches (by linarith [Real.pi_pos]) hcal.1 hcal.2.1 hcal.2.2
      hunit (by rw [supportP, hfD0, hg0]; linarith [hpos.1]) (by rw [supportP, hfDL, hgL]; linarith)
      (by rw [supportQ, hgD0, hf0]; linarith) (by rw [supportQ, hgDL, hfL]; linarith [hpos.2])
      fun t ht => by
        rw [(hvel ht).1, (hvel ht).2, neg_lt_zero]
        exact hU.corner_velocity_pos_or_pos_of_unit_density hρ hρ0 hρK heq hunit ht
  -- the three graph identities of the niche
  have hgraphD : ∀ t ∈ Ioo 0 d,
      sweptNiche U (Real.pi / 2) (secondTangentPoint F.g F.gD t).1 =
        (secondTangentPoint F.g F.gD t).2 := fun t ht => by
    have htL : t ∈ Ioo 0 (Real.pi / 2) := ⟨ht.1, ht.2.trans hd.2⟩
    rw [(htan htL).2.1]
    refine hU.sweptNiche_secondTangency_of_unit_density hheight hmiddle hρ hρ0 hρK heq
      (hunit.mono fun _ h => h.2) htL ?_
    rw [← (hvel htL).2]
    exact hqplus t ⟨ht.1.le, ht.2.le⟩
  have hgraphC : ∀ t ∈ Ioo b d,
      sweptNiche U (Real.pi / 2) (innerCornerPoint F.f F.g t).1 =
        (innerCornerPoint F.f F.g t).2 := fun t ht => by
    have htL : t ∈ Ioo 0 (Real.pi / 2) := ⟨hb.1.trans ht.1, ht.2.trans hd.2⟩
    have hp := hpminus t ⟨ht.1.le, htL.2.le⟩
    have hq := hqplus t ⟨htL.1.le, ht.2.le⟩
    rw [(hvel htL).1] at hp
    rw [(hvel htL).2] at hq
    rw [(htan htL).2.2]
    exact hU.sweptNiche_corner_of_unit_density hheight hmiddle hρ hρ0 hρK heq hunit htL hq
      (by linarith)
  have hgraphB : ∀ t ∈ Ioo b (Real.pi / 2),
      sweptNiche U (Real.pi / 2) (firstTangentPoint F.f F.fD t).1 =
        (firstTangentPoint F.f F.fD t).2 := fun t ht => by
    have htL : t ∈ Ioo 0 (Real.pi / 2) := ⟨hb.1.trans ht.1, ht.2⟩
    have hp := hpminus t ⟨ht.1.le, ht.2.le⟩
    rw [(hvel htL).1] at hp
    rw [(htan htL).1]
    exact hU.sweptNiche_firstTangency_of_unit_density hheight hmiddle hρ hρ0 hρK heq
      (hunit.mono fun _ h => h.1) htL (by linarith)
  have hf : Continuous F.f := hU.isCap.imported_isConvexBody.continuous_supp
  have hg : Continuous F.g := hU.isCap.imported_isConvexBody.continuous_supp.comp
    (continuous_id.add_const (Real.pi / 2))
  have hfD : Continuous F.fD := hU.isCap.continuous_closedSupportDerivative hρ hρ0 hρK 0
  have hgD : Continuous F.gD :=
    hU.isCap.continuous_closedSupportDerivative hρ hρ0 hρK (Real.pi / 2)
  have hac := supportQuarterPair_absolutelyContinuous hU.isCap hU.isCap
    hρ hρ0 hρK hρ hρ0 hρK hr.1 hr.2
  have hN : Continuous (sweptNiche U (Real.pi / 2)) :=
    funext hU.isCap.partialBarrier_pi_div_two ▸ hU.isCap.continuous_partialBarrier_pi_div_two
  have hsigned := signedRoof_integral_of_graphs_ac hb.1.le hd.1.le hd.2.le hN hf hg hfD hgD
    hac.1 hac.2.1 hac.2.2.1 hac.2.2.2
    (supportQuarterPair_ae_derivatives hU.isCap hU.isCap hρ hρ0 hρK hρ hρ0 hρK hr.1 hr.2)
    ((intervalIntegrable_bounded_real_density hρ hρ0 hρK _ _).sub (hf.intervalIntegrable _ _))
    ((intervalIntegrable_bounded_real_density (hρ.comp (measurable_id.add_const _))
      (fun t => hρ0 _) (fun t => hρK _) _ _).sub (hg.intervalIntegrable _ _))
    hfL hg0 hpb hqd hgraphD hgraphC hgraphB
  rw [← integral_min_sq_of_sign_switch (p := supportP F.fD F.g) hb.1.le hb.2.le
      ((hfD.sub hg).add continuous_const) hpplus hpminus,
    ← integral_max_sq_of_sign_switch (q := supportQ F.gD F.f) (hb.1.trans hd.1).le hd.2.le
      ((hgD.add hf).sub continuous_const) hqplus hqminus, hgD0, hfDL, neg_neg, neg_neg] at hsigned
  rwa [middleHalfInterval, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]

end AmbidextrousSofa
