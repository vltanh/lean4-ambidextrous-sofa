module

public import AmbidextrousSofa.Analysis.PartialInactiveNormals
public import AmbidextrousSofa.Analysis.FacetPinning

@[expose] public section

/-!
# Pinning the middle facet of an actual partial maximizer

The literal partial-barrier insertion theorem rules out an extension of
any tilted affine middle facet into a charged wing. Every normal of an
interior point of that facet has strictly negative middle-wall slack, so
raising such a point preserves the whole terminal first wall as well as
the visited history and produces a strict exterior roof gain.

Consequently the actual supporting face projects onto exactly the moving
middle interval, for either sign of the nonzero slope. This argument uses
neither partial source measures nor full-turn optimality.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem IsJointCapMaximizer.not_affine_wing_triple {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) {u x v m c : ℝ}
    (hu : u ∈ horizontalProjection U) (hv : v ∈ horizontalProjection U)
    (hux : u < x) (hxv : x < v) (hm : m ≠ 0)
    (hfa : capRoof U (horizontalLeft U + capWidth U / 4) =
      m * (horizontalLeft U + capWidth U / 4) + c)
    (hfb : capRoof U (horizontalRight U - capWidth U / 4) =
      m * (horizontalRight U - capWidth U / 4) + c)
    (hfu : capRoof U u = m * u + c) (hfx : capRoof U x = m * x + c)
    (hfv : capRoof U v = m * v + c)
    (hxWing : x ∈ Icc (horizontalLeft U)
        (horizontalLeft U + capWidth U / 4) ∪
      Icc (horizontalRight U - capWidth U / 4) (horizontalRight U)) : False := by
  have h1 := capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip
  obtain ⟨θ, hθ, hsupport, hslack⟩ := hU.exists_noninactive_normal_on_wing hxWing
    (hfx ▸ affine_lt_one_between hux hxv hm (hfu ▸ h1 u) (hfv ▸ h1 v))
  exact hslack.not_gt (hU.isCap.middleWallSlack_neg_of_affine_triple
    hu hv hux hxv hm hfa hfb hfu hfx hfv hθ hsupport)

/-- A literal supporting face, not an assigned facet, is pinned to the
entire moving middle interval of any prescribed tilted joint cap-and-angle maximum. -/
theorem IsJointCapMaximizer.horizontalProjection_middle_supportFace
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) {m c : ℝ} (hm : m ≠ 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    horizontalProjection (supportFace U (-m, 1)) =
      middleHalfInterval (horizontalLeft U) (horizontalRight U) := by
  obtain ⟨ha, hb, hab⟩ :=
    hU.isCap.middleChord_endpoints (by linarith [one_lt_M, hU.width_bounds.1])
  have hfa := haffine (horizontalLeft U + capWidth U / 4) ⟨le_rfl, hab.le⟩
  have hfb := haffine (horizontalRight U - capWidth U / 4) ⟨hab.le, le_rfl⟩
  have hceiling := hU.isCap.capRoof_le_affine_of_affine_segment ha hb hab haffine
  have hsupport := hU.isCap.support_of_affine_segment ha hb hab haffine
  -- two contacts `u < v` whose midpoint lies in a charged wing are impossible
  have key {u v : ℝ} (hu : u ∈ horizontalProjection U) (hv : v ∈ horizontalProjection U)
      (huv : u < v) (hfu : capRoof U u = m * u + c) (hfv : capRoof U v = m * v + c) :=
    hU.not_affine_wing_triple hu hv (by linarith : u < (u + v) / 2) (by linarith) hm hfa hfb hfu
      (hU.isCap.capRoof_eq_affine_between_contacts hu hv huv hfu hfv hceiling _
        ⟨by linarith, by linarith⟩) hfv
  refine Subset.antisymm ?_ fun x hx => ⟨(x, capRoof U x), ⟨capRoof_mem hU.isCap.isCompact
    ((convex_horizontalProjection hU.isCap.convex).ordConnected.out ha hb hx), ?_⟩, rfl⟩
  · rintro _ ⟨p, ⟨hpU, hp : coordDot p (-m, 1) = _⟩, rfl⟩
    have hpProj : p.1 ∈ horizontalProjection U := ⟨p, hpU, rfl⟩
    have hpRoof : capRoof U p.1 = m * p.1 + c := by
      have := le_capRoof (x := p.1) (y := p.2) hU.isCap.isCompact hpU
      simp only [coordDot, hsupport] at hp
      exact le_antisymm (hceiling p.1 hpProj) (by linarith)
    obtain ⟨hl, hr⟩ := hU.isCap.horizontalProjection_eq_Icc ▸ hpProj
    by_contra hout
    rcases lt_or_ge p.1 (horizontalLeft U + capWidth U / 4) with hpa | hap
    · exact key hpProj ha hpa hpRoof hfa (.inl ⟨by linarith, by linarith⟩)
    have hbp : horizontalRight U - capWidth U / 4 < p.1 :=
      lt_of_not_ge fun hpb => hout ⟨hap, hpb⟩
    exact key hb hpProj hbp hfb hpRoof (.inr ⟨by linarith, by linarith⟩)
  · show coordDot _ _ = _
    simp only [coordDot, hsupport, haffine x hx]
    ring

end AmbidextrousSofa
