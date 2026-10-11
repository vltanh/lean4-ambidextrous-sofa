module

public import AmbidextrousSofa.Analysis.PartialShadowSecants
public import AmbidextrousSofa.Analysis.PartialAtomIntervalLimit

@[expose] public section

/-!
# The actual proper same-sign curvature laws

The selected polygons and their moving neighboring-wall margins belong
to the original proper maximizer. Summation keeps every unsampled atom
and both vanishing errors. Lebesgue differentiation, in the form shared
with the full-turn case, then gives the zero and half-density bounds in
the two same-sign quadrants. The actual terminal normal is excluded from
the regular domain throughout.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- Both support directions avoid the actual exceptional normals. -/
def regularProperCornerDomain (α m : ℝ) : Set ℝ :=
  Ioo (0 : ℝ) (Real.pi / 2) ∩ (regularProperCurvatureDomain α m ∩
    (fun t : ℝ => t + Real.pi / 2) ⁻¹' regularProperCurvatureDomain α m)

theorem isOpen_regularProperCornerDomain (α m : ℝ) :
    IsOpen (regularProperCornerDomain α m) :=
  have hreg := isOpen_regularProperCurvatureDomain α m
  isOpen_Ioo.inter (hreg.inter (hreg.preimage (continuous_id.add_const (Real.pi / 2))))

/-- In the convention `p = -secondCornerVelocity` and
`q = firstCornerVelocity`, these are the `++` and `--` source laws.
Both densities represent curvature of the original proper cap, which
supplies its own selected sequence. -/
theorem IsJointCapMaximizer.ae_proper_curvature_same_sign_quadrants
    {K : Set Plane} {α m c C : ℝ} (hK : IsJointCapMaximizer K α)
    (hproper : α < Real.pi / 2) {ρ : ℝ → ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature K).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    ∀ᵐ t ∂volume.restrict (regularProperCornerDomain α m),
      (0 < firstCornerVelocity K t ∧ secondCornerVelocity K t < 0 →
        ρ t = 0 ∧ ρ (t + Real.pi / 2) ≤ 1 / 2) ∧
      (firstCornerVelocity K t < 0 ∧ 0 < secondCornerVelocity K t →
        ρ (t + Real.pi / 2) = 0 ∧ ρ t ≤ 1 / 2) := by
  obtain ⟨level, coefficient, U, hlevel, hc, hrate, hU, hHausdorff⟩ :=
    hK.exists_symmetric_selected_sequence hproper
  have hzero {t} (ht : t ∈ regularProperCurvatureDomain α m) :=
    sigmaAt_eq_zero_of_density hρ hρ0 heq ht
  refine ae_curvature_same_sign_quadrants_of_local_bound (isOpen_regularProperCurvatureDomain α m)
    hρ hρ0 hρC heq fun positive t ε ht hpaired hmargin hε => ?_
  obtain ⟨δ, hδ, hfinite⟩ := PartialGrid.eventually_shadow_atoms_le hK.isCap hU hHausdorff hlevel
    hc (isCompact_Icc.prod isCompact_Icc) (fun n => (hU n).inBox) positive
    (mem_regularCurvatureDomain_iff.mp ht.1).2.2.1 (hzero hpaired.2.1) (hzero hpaired.2.2)
    hmargin hε
  refine ⟨δ, hδ, fun d hd hdδ hreg => ?_⟩
  simpa only [add_sub_cancel_left] using
    PartialGrid.curvature_Ioc_le_of_eventual_sampled_atom_bound hK.isCap hU hHausdorff hlevel hc
      hrate (fun n => (hU n).inBox) (by linarith only [hK.width_bounds.1, one_lt_M]) haffine
      (add_nonneg (sameSignCoefficient_nonneg positive t) hε.le) (by linarith) hreg (hzero ht)
      (hzero (hreg ⟨by linarith, le_rfl⟩))
      (hfinite.mono fun n hn j hj => hn j (abs_lt.mpr ⟨by linarith [hj.1], by linarith [hj.2]⟩))

end AmbidextrousSofa
