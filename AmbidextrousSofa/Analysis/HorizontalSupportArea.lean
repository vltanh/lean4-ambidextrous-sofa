module

public import AmbidextrousSofa.Analysis.ClosedSupportPair
public import AmbidextrousSofa.Measure.SupportAreaAC

@[expose] public section

/-!
# Actual horizontal cap area in the closed support pair

The pair, its derivatives, its realized roof points, its top segment, and
its axis traces are all those of the actual full maximum. The area identity
uses its bounded measurable curvature density and retains the top and axis
face contributions until the final cancellation.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsFullCapMaximizer.volumeReal_eq_horizontalSupportQuarterPair_energy
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {K : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1) :
    let F := horizontalSupportQuarterPair hU.isCap hρ hρ0 hρK heq
    volume.real U = 1 / 2 * ∫ t in (0 : ℝ)..(Real.pi / 2),
      (F.f t ^ 2 - F.fD t ^ 2) + (F.g t ^ 2 - F.gD t ^ 2) := by
  let F := horizontalSupportQuarterPair hU.isCap hρ hρ0 hρK heq
  have hr := horizontal_density_quarter_restrictions heq
  have hac := supportQuarterPair_absolutelyContinuous hU.isCap hU.isCap
    hρ hρ0 hρK hρ hρ0 hρK hr.1 hr.2
  have hd := supportQuarterPair_ae_derivatives hU.isCap hU.isCap
    hρ hρ0 hρK hρ hρ0 hρK hr.1 hr.2
  have hp := supportQuarterPair_points_mem hU.isCap hU.isCap
    hρ hρ0 hρK hρ hρ0 hρK hr.1 hr.2
  have htr := hU.horizontalSupportQuarterPair_traces hρ hρ0 hρK heq hheight hmiddle
  change F.f 0 = horizontalRight U ∧ F.g 0 = 1 ∧
    F.f (Real.pi / 2) = 1 ∧ F.g (Real.pi / 2) = -horizontalLeft U ∧
    F.fD 0 = capRoof U (horizontalRight U) ∧
    F.gD 0 = -(horizontalLeft U + capWidth U / 4) ∧
    F.fD (Real.pi / 2) = -(horizontalRight U - capWidth U / 4) ∧
    F.gD (Real.pi / 2) = -capRoof U (horizontalLeft U) at htr
  rcases htr with ⟨hf0, hg0, hfL, hgL, hfD0, hgD0, hfDL, hgDL⟩
  have hfi : IntervalIntegrable (fun t => ρ t - F.f t) volume 0 (Real.pi / 2) := by
    simpa only [F, horizontalSupportQuarterPair, supportQuarterPair, add_zero] using
      hU.isCap.intervalIntegrable_shifted_density_sub_support hρ hρ0 hρK 0 (Real.pi / 2) 0
  have hgi : IntervalIntegrable (fun t => ρ (t + Real.pi / 2) - F.g t)
      volume 0 (Real.pi / 2) :=
    hU.isCap.intervalIntegrable_shifted_density_sub_support hρ hρ0 hρK
      0 (Real.pi / 2) (Real.pi / 2)
  apply hU.isCap.volumeReal_eq_support_energy_ac
    hac.1 hac.2.1 hac.2.2.1 hac.2.2.2
    (hd.mono (fun _ h => h.1)) (hd.mono (fun _ h => h.2.1))
    (hd.mono (fun _ h => h.2.2.1)) (hd.mono (fun _ h => h.2.2.2))
    hfi hgi hp.1 hp.2 (fun _ _ => rfl) (fun _ _ => rfl)
    (by change horizontalLeft U = -F.g (Real.pi / 2); rw [hgL, neg_neg]) hf0.symm hfL hg0
  · change -F.gD 0 ≤ -F.fD (Real.pi / 2)
    rw [hgD0, hfDL, neg_neg, neg_neg]
    have hwidth : 0 ≤ capWidth U := hU.isCap.capWidth_nonneg
    dsimp only [capWidth] at hwidth ⊢
    linarith
  · intro x hx
    change x ∈ Icc (-F.gD 0) (-F.fD (Real.pi / 2)) at hx
    rw [hgD0, hfDL, neg_neg, neg_neg] at hx
    exact hmiddle x hx

end AmbidextrousSofa
