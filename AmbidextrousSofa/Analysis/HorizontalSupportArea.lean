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
  intro F
  have hr := horizontal_density_quarter_restrictions heq
  have hac := supportQuarterPair_absolutelyContinuous hU.isCap hU.isCap
    hρ hρ0 hρK hρ hρ0 hρK hr.1 hr.2
  have hd := supportQuarterPair_ae_derivatives hU.isCap hU.isCap
    hρ hρ0 hρK hρ hρ0 hρK hr.1 hr.2
  have hp := supportQuarterPair_points_mem hU.isCap hU.isCap
    hρ hρ0 hρK hρ hρ0 hρK hr.1 hr.2
  obtain ⟨hf0, hg0, hfL, hgL, -, hgD0, hfDL, -⟩ :=
    hU.horizontalSupportQuarterPair_traces hρ hρ0 hρK heq hheight hmiddle
  have hface : Icc (-F.gD 0) (-F.fD (Real.pi / 2)) =
      middleHalfInterval (horizontalLeft U) (horizontalRight U) := by
    rw [hgD0, hfDL, neg_neg, neg_neg]; rfl
  refine hU.isCap.volumeReal_eq_support_energy_ac hac.1 hac.2.1 hac.2.2.1 hac.2.2.2
    (hd.mono fun _ h => h.1) (hd.mono fun _ h => h.2.1) (hd.mono fun _ h => h.2.2.1)
    (hd.mono fun _ h => h.2.2.2) ((intervalIntegrable_bounded_real_density hρ hρ0 hρK _ _).sub
      (hU.isCap.imported_isConvexBody.continuous_supp.intervalIntegrable _ _))
    (hU.isCap.intervalIntegrable_shift_density hρ hρ0 hρK _ _ _) hp.1 hp.2
    (fun _ _ => rfl) (fun _ _ => rfl) (by rw [hgL, neg_neg]) hf0.symm hfL hg0 ?_
    (hface ▸ hmiddle)
  rw [hgD0, hfDL, neg_neg, neg_neg]
  linarith [hU.isCap.capWidth_nonneg,
    show capWidth U = horizontalRight U - horizontalLeft U from rfl]

end AmbidextrousSofa
