module

public import AmbidextrousSofa.Analysis.PartialSharpSourceDensity
public import AmbidextrousSofa.Analysis.LeftCompanionDensity

@[expose] public section

/-!
# Actual sharp curvature densities for proper maxima

Lebesgue differentiation turns the proved local source interval bounds
into domination of the actual curvature on an open wing by the sharp
source coefficient. The literal selected sequence of the proper maximum
discharges every regularity premise. All sharp coefficients are
evaluated at the original cap's actual corner velocity. No occupation
equality is assumed.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- The selected sequence belongs to this actual joint maximum and is
constructed here. The terminal normal stays outside the open wing. -/
theorem IsJointCapMaximizer.curvature_restrict_le_source_density_on_proper_open_wing
    {K : Set Plane} {α m c A B : ℝ} (hK : IsJointCapMaximizer K α)
    (hproper : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (hA : 0 ≤ A) (hB : B ≤ Real.pi) (htop : Real.pi / 2 ∉ Ioo A B)
    (hterminal : α ∉ Ioo A B)
    (hperp : ∀ t ∈ Ioo A B, Real.cos t + m * Real.sin t ≠ 0) :
    (upperCurvature K).restrict (Ioo A B) ≤
      (volume.restrict (Ioo A B)).withDensity
        (fun t => ENNReal.ofReal (sourceKappa (upperCornerVelocity K t))) := by
  obtain ⟨level, coefficient, U, hlevel, hc, hrate, hU, hHausdorff⟩ :=
    hK.exists_symmetric_selected_sequence hproper
  refine restrict_Ioo_le_withDensity_of_local_bound (by positivity)
    (hK.curvature_restrict_le_on_proper_open_wing hproper haffine hA hB htop hterminal hperp) ?_
  filter_upwards [ae_sigmaAt_companionSourceAngle_eq_zero K] with t hcomp ht ε hε
  obtain ⟨δ, hδ, -, hlocal⟩ := PartialGrid.curvature_local_source_bound hK.isCap hU hHausdorff
    hlevel hc hrate (by positivity) (fun n => (hU n).inBox)
    (by linarith only [hK.width_bounds.1, one_lt_M]) haffine hA hB htop hterminal hperp ht hcomp hε
  exact ⟨δ, hδ, hlocal⟩

end AmbidextrousSofa
