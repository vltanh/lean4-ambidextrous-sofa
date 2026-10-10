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
  have hu1 : m * u + c ≤ 1 := by
    rw [← hfu]; exact capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip u
  have hv1 : m * v + c ≤ 1 := by
    rw [← hfv]; exact capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip v
  have hlow : capRoof U x < 1 := by
    rw [hfx]; exact affine_lt_one_between hux hxv hm hu1 hv1
  obtain ⟨θ, hθ, hsupport, hnonnegative⟩ :=
    hU.exists_noninactive_normal_on_wing hxWing hlow
  have hnegative := hU.isCap.middleWallSlack_neg_of_affine_triple
    hu hv hux hxv hm hfa hfb hfu hfx hfv hθ hsupport
  exact (not_lt_of_ge hnonnegative) hnegative

/-- A literal supporting face, not an assigned facet, is pinned to the
entire moving middle interval of any prescribed tilted joint cap-and-angle maximum. -/
theorem IsJointCapMaximizer.horizontalProjection_middle_supportFace
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) {m c : ℝ} (hm : m ≠ 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    horizontalProjection (supportFace U (-m, 1)) =
      middleHalfInterval (horizontalLeft U) (horizontalRight U) := by
  let a := horizontalLeft U + capWidth U / 4
  let b := horizontalRight U - capWidth U / 4
  have hwidth : 0 < capWidth U := lt_of_lt_of_le
    (by linarith [one_lt_M] : 0 < M) hU.width_bounds.1
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints hwidth
  have hfa : capRoof U a = m * a + c := haffine a ⟨le_rfl, hab.le⟩
  have hfb : capRoof U b = m * b + c := haffine b ⟨hab.le, le_rfl⟩
  have hceiling := hU.isCap.capRoof_le_affine_of_affine_segment ha hb hab haffine
  have hsupport := hU.isCap.support_of_affine_segment ha hb hab haffine
  have hproj : horizontalProjection U =
      Icc (horizontalLeft U) (horizontalRight U) :=
    horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex
  apply Set.Subset.antisymm
  · rintro x ⟨p, hp, rfl⟩
    have hpU : p ∈ U := hp.1
    have hpProj : p.1 ∈ horizontalProjection U := ⟨p, hpU, rfl⟩
    have hpLine : p.2 = m * p.1 + c := by
      have heq := hp.2
      change p.1 * (-m) + p.2 * 1 = support U (-m, 1) at heq
      rw [hsupport] at heq
      nlinarith
    have hpRoof : capRoof U p.1 = m * p.1 + c := by
      apply le_antisymm (hceiling p.1 hpProj)
      rw [← hpLine]
      exact le_capRoof hU.isCap.isCompact (by simpa only [Prod.mk.eta] using hpU)
    by_contra hout
    change ¬(a ≤ p.1 ∧ p.1 ≤ b) at hout
    rcases lt_or_ge p.1 a with hpa | hap
    · let x₀ := (p.1 + a) / 2
      have hpx : p.1 < x₀ := by dsimp [x₀]; linarith
      have hxa : x₀ < a := by dsimp [x₀]; linarith
      have hfx : capRoof U x₀ = m * x₀ + c :=
        hU.isCap.capRoof_eq_affine_between_contacts hpProj ha hpa hpRoof hfa hceiling
          x₀ ⟨hpx.le, hxa.le⟩
      have hxWing : x₀ ∈ Icc (horizontalLeft U) a := by
        have hpl := hpProj
        rw [hproj] at hpl
        exact ⟨hpl.1.trans hpx.le, hxa.le⟩
      exact hU.not_affine_wing_triple hpProj ha hpx hxa hm
        hfa hfb hpRoof hfx hfa (Or.inl hxWing)
    · have hbp : b < p.1 := lt_of_not_ge (fun hpb => hout ⟨hap, hpb⟩)
      let x₀ := (b + p.1) / 2
      have hbx : b < x₀ := by dsimp [x₀]; linarith
      have hxp : x₀ < p.1 := by dsimp [x₀]; linarith
      have hfx : capRoof U x₀ = m * x₀ + c :=
        hU.isCap.capRoof_eq_affine_between_contacts hb hpProj hbp hfb hpRoof hceiling
          x₀ ⟨hbx.le, hxp.le⟩
      have hxWing : x₀ ∈ Icc b (horizontalRight U) := by
        have hpr := hpProj
        rw [hproj] at hpr
        exact ⟨hbx.le, hxp.le.trans hpr.2⟩
      exact hU.not_affine_wing_triple hb hpProj hbx hxp hm
        hfa hfb hfb hfx hpRoof (Or.inr hxWing)
  · intro x hx
    have hxU : x ∈ horizontalProjection U :=
      (convex_horizontalProjection hU.isCap.convex).ordConnected.out ha hb hx
    refine ⟨(x, capRoof U x), ⟨capRoof_mem hU.isCap.isCompact hxU, ?_⟩, rfl⟩
    rw [hsupport, haffine x hx]
    dsimp [coordDot]
    ring

end AmbidextrousSofa
