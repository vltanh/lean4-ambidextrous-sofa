import AmbidextrousSofa.Analysis.PartialSourceMass
import AmbidextrousSofa.Analysis.LocalSourceDensity

/-!
# Sharp limits of the actual rescaled proper sources

The proper history uses a rescaled angular mesh, with both neighboring
walls retained at each sampled interior source. Its actual curvature
atom enters the neighboring-wall estimate. Solving that self-bound gives
the same finite sharp coefficient as in the full history.

Moving support secants converge along the rescaled samples. Consequently
their normalized sharp coefficients converge to the actual corner
velocity coefficient, uniformly near each non-atomic companion normal.
No terminal source is included among these interior samples.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace PartialGrid

open AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

theorem IsSelectedPolygon.curvature_scaled_atom_refined
    {target U : Set Plane} {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U) (hc : 0 ≤ coefficient)
    (j : AngularGrid.SourceIndex (dyadic level)) :
    (upperCurvature U {fullAngle α (dyadic level) (scaledSource α (dyadic level) j)}).toReal ≤
      finiteCurvatureDensity (cornerSecant U α level j) (mesh α level) +
        middleOuterMass U α (dyadic level) (scaledSource α (dyadic level) j) +
        selectionDefect target U α level coefficient (scaledSource α (dyadic level) j) := by
  have horder : horizontalLeft U + capWidth U / 4 ≤ horizontalRight U - capWidth U / 4 := by
    unfold capWidth
    linarith only [horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact]
  have hsource := integral_scaled_innerDensity_le hU.isCap α hαL level j horder
  have hatom := hU.curvature_atom_le_mass hc (scaledSource α (dyadic level) j)
  have he := add_nonneg
    (middleOuterMass_nonneg hU.isCap α (dyadic level) (scaledSource α (dyadic level) j))
    (selectionDefect_nonneg target U α level hc (scaledSource α (dyadic level) j))
  have hraw : (upperCurvature U
      {fullAngle α (dyadic level) (scaledSource α (dyadic level) j)}).toReal ≤
      Real.tan (mesh α level) * (|cornerSecant U α level j| + Real.tan (mesh α level / 2)) +
        max (2 * Real.tan (mesh α level / 2) -
          (upperCurvature U {fullAngle α (dyadic level) (scaledSource α (dyadic level) j)}).toReal) 0 +
        (middleOuterMass U α (dyadic level) (scaledSource α (dyadic level) j) +
          selectionDefect target U α level coefficient (scaledSource α (dyadic level) j)) := by
    change innerSourceMass U α hαL (dyadic level) (scaledSource α (dyadic level) j) ≤ _ at hsource
    linarith only [hsource, hatom]
  have h := solve_curvature_self_bound he hraw
  simpa only [finiteCurvatureDensity, add_assoc] using h

/-- The full normal of the sampled proper source may move at every
stage. Its secant still converges to the literal target velocity. -/
theorem cornerSecant_tendsto
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    (α : TerminalAngle) {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop)
    (j : ∀ n, AngularGrid.SourceIndex (dyadic (level n))) {t : ℝ}
    (hangle : Tendsto (fun n =>
      fullAngle α (dyadic (level n)) (scaledSource α (dyadic (level n)) (j n))) atTop (𝓝 t))
    (htop : t ≠ Real.pi / 2)
    (ht : Imported.sigmaAt K (companionSourceAngle t) = 0) :
    Tendsto (fun n => cornerSecant (U n) α (level n) (j n)) atTop
      (𝓝 (upperCornerVelocity K t)) := by
  have hmesh := (mesh_tendsto α).comp hlevel
  by_cases hleft : t < Real.pi / 2
  · have hsec := h.firstCornerSecant_tendsto hU hK hB hbox hangle hmesh
      (fun n => mesh_sin_pos α (level n)) (fun n => (mesh_cos_pos α (level n)).le)
      (by simpa only [companionSourceAngle, if_pos hleft] using ht)
    have heq : ∀ᶠ n in atTop, cornerSecant (U n) α (level n) (j n) =
        firstCornerSecant (U n)
          (fullAngle α (dyadic (level n)) (scaledSource α (dyadic (level n)) (j n)))
          (mesh α (level n)) := by
      filter_upwards [hangle.eventually (isOpen_Iio.mem_nhds hleft)] with n hn
      cases hj : j n with
      | inl s =>
        simp only [hj, cornerSecant, fullAngle, scaledSource, AngularGrid.fullAngle, scaledInterior]
      | inr s =>
        have hs := scaleAngle_mem_open α (interiorPoint_mem (dyadic (level n)) s)
        have hbad : (scaleAngle α s.val : ℝ) + Real.pi / 2 < Real.pi / 2 := by
          simpa only [hj, fullAngle, scaledSource, AngularGrid.fullAngle, scaledInterior] using hn
        exact False.elim (by linarith only [hs.1, hbad])
    simpa only [upperCornerVelocity, if_pos hleft] using hsec.congr' heq.symm
  · have hright : Real.pi / 2 < t := lt_of_le_of_ne (le_of_not_gt hleft) htop.symm
    have hsec := h.secondCornerSecant_tendsto hU hK hB hbox
      (hangle.sub_const (Real.pi / 2)) hmesh
      (fun n => mesh_sin_pos α (level n)) (fun n => (mesh_cos_pos α (level n)).le)
      (by simpa only [companionSourceAngle, if_neg hleft] using ht)
    have heq : ∀ᶠ n in atTop, cornerSecant (U n) α (level n) (j n) =
        secondCornerSecant (U n)
          (fullAngle α (dyadic (level n)) (scaledSource α (dyadic (level n)) (j n)) - Real.pi / 2)
          (mesh α (level n)) := by
      filter_upwards [hangle.eventually (isOpen_Ioi.mem_nhds hright)] with n hn
      cases hj : j n with
      | inl s =>
        have hs := (scaleAngle_mem_open α (interiorPoint_mem (dyadic (level n)) s)).2.trans_le
          α.property.2
        have hbad : Real.pi / 2 < (scaleAngle α s.val : ℝ) := by
          simpa only [hj, fullAngle, scaledSource, AngularGrid.fullAngle, scaledInterior] using hn
        exact False.elim ((not_lt_of_ge hs.le) hbad)
      | inr s =>
        simp only [hj, cornerSecant, fullAngle, scaledSource, AngularGrid.fullAngle,
          scaledInterior, add_sub_cancel_right]
    simpa only [upperCornerVelocity, if_neg hleft] using hsec.congr' heq.symm

theorem sampledCurvatureDensity_tendsto
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    (α : TerminalAngle) {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop)
    (j : ∀ n, AngularGrid.SourceIndex (dyadic (level n))) {t : ℝ}
    (hangle : Tendsto (fun n =>
      fullAngle α (dyadic (level n)) (scaledSource α (dyadic (level n)) (j n))) atTop (𝓝 t))
    (htop : t ≠ Real.pi / 2)
    (ht : Imported.sigmaAt K (companionSourceAngle t) = 0) :
    Tendsto (fun n => finiteCurvatureDensity (cornerSecant (U n) α (level n) (j n))
      (mesh α (level n)) / mesh α (level n)) atTop
        (𝓝 (sourceKappa (upperCornerVelocity K t))) :=
  finiteCurvatureDensity_div_tendsto
    (cornerSecant_tendsto h hU hK hB hbox α hlevel j hangle htop ht)
    ((mesh_tendsto α).comp hlevel) (fun n => mesh_pos α (level n))

theorem eventually_sampledCurvatureDensity_lt
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    (α : TerminalAngle) {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop)
    {t ε : ℝ} (htop : t ≠ Real.pi / 2)
    (ht : Imported.sigmaAt K (companionSourceAngle t) = 0) (hε : 0 < ε) :
    ∃ δ > 0, ∀ᶠ n in atTop, ∀ j : AngularGrid.SourceIndex (dyadic (level n)),
      |fullAngle α (dyadic (level n)) (scaledSource α (dyadic (level n)) j) - t| < δ →
        finiteCurvatureDensity (cornerSecant (U n) α (level n) j) (mesh α (level n)) /
          mesh α (level n) < sourceKappa (upperCornerVelocity K t) + ε := by
  apply eventually_uniform_upper_of_moving_tendsto
    (fun n j => fullAngle α (dyadic (level n)) (scaledSource α (dyadic (level n)) j))
    (fun n j => finiteCurvatureDensity (cornerSecant (U n) α (level n) j) (mesh α (level n)) /
      mesh α (level n)) ?_ hε
  intro ns hns j hangle
  exact sampledCurvatureDensity_tendsto (h.comp hns) (fun n => hU (ns n)) hK hB
    (fun n => hbox (ns n)) α (hlevel.comp hns) j hangle htop ht

end PartialGrid

end AmbidextrousSofa
