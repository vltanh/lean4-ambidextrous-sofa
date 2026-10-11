module

public import AmbidextrousSofa.Analysis.OpenGraphFlux

@[expose] public section

/-!
# First-family flux of visible core and tangent pieces

A visible core chord and a disjoint first-tangency piece are open graph
pieces whose maximizing angles lie in `(s, t)`. Projected onto the
direction `θ - π / 2`, their first-family source mass is charged in full
and the companion mass only with the factor `t - s`. The tangent piece may
be a plateau; its zero projection is then retained exactly. All measures
and selected polygons in the comparison are the literal ones belonging to
the prescribed full maximum.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- A literal visible core chord. Every maximizing angle over its open
spatial projection lies in the stated parameter interval. -/
structure FirstSourceCorePiece {U : Set Plane} (hU : IsDownwardCap U)
    (Z : ℝ → Plane) (s t : ℝ) : Prop where
  reversed : (Z t).1 < (Z s).1
  middle_left : horizontalLeft U + capWidth U / 4 ≤ (Z t).1
  middle_right : (Z s).1 ≤ horizontalRight U - capWidth U / 4
  contact_s : sweptNiche U (Real.pi / 2) (Z s).1 = (Z s).2
  contact_t : sweptNiche U (Real.pi / 2) (Z t).1 = (Z t).2
  positive : ∀ x ∈ Ioo (Z t).1 (Z s).1, 0 < sweptNiche U (Real.pi / 2) x
  localizes : ∀ x ∈ Ioo (Z t).1 (Z s).1, ∀ v ∈ Icc (0 : ℝ) (Real.pi / 2),
    fullWallClip hU.toCompactCap x v = sweptNiche U (Real.pi / 2) x → v ∈ Ioo s t

/-- Two disjoint literal graph pieces. The first tangent may be a
plateau; its zero projection is then retained exactly. -/
structure FirstSourceChargedPieces {U : Set Plane} (hU : IsDownwardCap U)
    (B Z : ℝ → Plane) (s t : ℝ) : Prop where
  core : FirstSourceCorePiece hU Z s t
  tangent_order : (B s).1 ≤ (B t).1
  separation : (Z s).1 ≤ (B s).1
  middle_right : (B t).1 ≤ horizontalRight U - capWidth U / 4
  contact_s : sweptNiche U (Real.pi / 2) (B s).1 = (B s).2
  contact_t : sweptNiche U (Real.pi / 2) (B t).1 = (B t).2
  positive : ∀ x ∈ Ioo (B s).1 (B t).1, 0 < sweptNiche U (Real.pi / 2) x
  localizes : ∀ x ∈ Ioo (B s).1 (B t).1, ∀ v ∈ Icc (0 : ℝ) (Real.pi / 2),
    fullWallClip hU.toCompactCap x v = sweptNiche U (Real.pi / 2) x → v ∈ Ioo s t

/-- The flux bound in the direction `θ - π / 2`, at the contact points of both pieces. -/
theorem IsFullCapMaximizer.first_source_flux_of_charged_pieces
    {U : Set Plane} (hU : IsFullCapMaximizer U) {m c s t θ : ℝ} {B Z : ℝ → Plane}
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hθ : θ ∈ Icc s t)
    (hregular : Icc s t ⊆ regularCurvatureDomain m)
    (hshift : Icc (s + Real.pi / 2) (t + Real.pi / 2) ⊆ regularCurvatureDomain m)
    (H : FirstSourceChargedPieces hU.isCap B Z s t) :
    Real.sin θ * ((Z s).1 - (Z t).1) - Real.cos θ * ((Z s).2 - (Z t).2) +
      (Real.sin θ * ((B t).1 - (B s).1) - Real.cos θ * ((B t).2 - (B s).2)) ≤
      (upperCurvature U).real (Ioc s t) +
        (t - s) * ((upperCurvature U).real (Ioc s t) +
          (upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2))) := by
  have hst := hθ.1.trans hθ.2
  have h := hU.nicheGraphProjection_add_le_curvature_of_open_pieces hheight haffine hst hregular
    (by linarith only [hst]) hshift (sub_nonneg.2 hst)
    (fun _ j hj => (AngularGrid.localized_quarter_source _ hθ j hj).2) H.core.middle_left
    H.core.reversed.le H.separation H.tangent_order H.middle_right
    (fun x hx => hx.elim (H.core.positive x) (H.positive x))
    (fun x hx => hx.elim (H.core.localizes x) (H.localizes x))
  simp only [nicheGraphProjection, H.core.contact_s, H.core.contact_t, H.contact_s,
    H.contact_t, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two] at h
  linarith

end AmbidextrousSofa
