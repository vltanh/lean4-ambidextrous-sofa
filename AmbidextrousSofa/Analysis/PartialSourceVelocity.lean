module

public import AmbidextrousSofa.Analysis.PartialSourceMass
public import AmbidextrousSofa.Analysis.LocalSourceDensity

@[expose] public section

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
  have hsource := integral_scaled_innerDensity_le hU.isCap α hαL level j hU.isCap.quarter_le
  have hatom := hU.curvature_atom_le_mass hc (scaledSource α (dyadic level) j)
  rw [add_assoc]
  exact solve_curvature_self_bound (add_nonneg (middleOuterMass_nonneg hU.isCap α _ _)
    (selectionDefect_nonneg target U α level hc _)) (by unfold innerSourceMass at hatom; linarith)

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
    (ht : MovingSofaOptimality.sigmaAt K (companionSourceAngle t) = 0) :
    Tendsto (fun n => cornerSecant (U n) α (level n) (j n)) atTop
      (𝓝 (upperCornerVelocity K t)) := by
  have hmesh : Tendsto (fun n => mesh α (level n)) atTop (𝓝 0) := (mesh_tendsto α).comp hlevel
  by_cases hleft : t < Real.pi / 2
  · simp only [upperCornerVelocity, hleft, ↓reduceIte]
    refine (h.firstCornerSecant_tendsto hU hK hB hbox hangle hmesh
      (fun n => mesh_sin_pos α (level n)) (fun n => (mesh_cos_pos α (level n)).le)
      (by simpa only [companionSourceAngle, hleft, ↓reduceIte] using ht)).congr' ?_
    filter_upwards [hangle.eventually (isOpen_Iio.mem_nhds hleft)] with n hn
    rcases hj : j n with s | s <;> simp only [hj, cornerSecant, fullAngle, scaledSource,
      AngularGrid.fullAngle, scaledInterior] at hn ⊢
    linarith [(scaleAngle_mem_open α (interiorPoint_mem (dyadic (level n)) s)).1]
  · simp only [upperCornerVelocity, hleft, ↓reduceIte]
    refine (h.secondCornerSecant_tendsto hU hK hB hbox (hangle.sub_const (Real.pi / 2)) hmesh
      (fun n => mesh_sin_pos α (level n)) (fun n => (mesh_cos_pos α (level n)).le)
      (by simpa only [companionSourceAngle, hleft, ↓reduceIte] using ht)).congr' ?_
    filter_upwards [hangle.eventually (isOpen_Ioi.mem_nhds
      (htop.symm.lt_of_le (not_lt.mp hleft)))] with n hn
    rcases hj : j n with s | s <;> simp only [hj, cornerSecant, fullAngle, scaledSource,
      AngularGrid.fullAngle, scaledInterior, add_sub_cancel_right] at hn ⊢
    linarith [(scaleAngle_mem_open α (interiorPoint_mem (dyadic (level n)) s)).2, α.property.2]

theorem sampledCurvatureDensity_tendsto
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    (α : TerminalAngle) {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop)
    (j : ∀ n, AngularGrid.SourceIndex (dyadic (level n))) {t : ℝ}
    (hangle : Tendsto (fun n =>
      fullAngle α (dyadic (level n)) (scaledSource α (dyadic (level n)) (j n))) atTop (𝓝 t))
    (htop : t ≠ Real.pi / 2)
    (ht : MovingSofaOptimality.sigmaAt K (companionSourceAngle t) = 0) :
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
    (ht : MovingSofaOptimality.sigmaAt K (companionSourceAngle t) = 0) (hε : 0 < ε) :
    ∃ δ > 0, ∀ᶠ n in atTop, ∀ j : AngularGrid.SourceIndex (dyadic (level n)),
      |fullAngle α (dyadic (level n)) (scaledSource α (dyadic (level n)) j) - t| < δ →
        finiteCurvatureDensity (cornerSecant (U n) α (level n) j) (mesh α (level n)) /
          mesh α (level n) < sourceKappa (upperCornerVelocity K t) + ε :=
  eventually_uniform_upper_of_moving_tendsto _ _ (fun ns hns j hangle =>
    sampledCurvatureDensity_tendsto (h.comp hns) (fun n => hU (ns n)) hK hB
      (fun n => hbox (ns n)) α (hlevel.comp hns) j hangle htop ht) hε

end PartialGrid

end AmbidextrousSofa
