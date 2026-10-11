module

public import AmbidextrousSofa.Analysis.InactiveNormals
public import AmbidextrousSofa.Analysis.TopFacetEndpoints

@[expose] public section

/-!
# Pinning the actual nonhorizontal middle facet

The inner wall of a tilted middle facet is strictly inactive on the whole
charged middle interval. A relative-interior point of the same facet has
only normals perpendicular to that facet. If such a point were in a
charged wing, the actual insertion theorem would improve the score.

Consequently the supporting face of a nonhorizontal affine middle at a
global full-cap maximum projects onto exactly the middle interval. This
is an equality of actual support faces, including their endpoints.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem coordDot_affine_graph_normal (m c x θ : ℝ) :
    coordDot (x, m * x + c) (unitNormal θ) =
      x * (Real.cos θ + m * Real.sin θ) + c * Real.sin θ := by
  simp only [coordDot, unitNormal]
  ring

theorem IsDownwardCap.capRoof_le_affine_of_affine_segment {U : Set Plane}
    (hU : IsDownwardCap U) {a b m c : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ x ∈ Icc a b, capRoof U x = m * x + c) :
    ∀ x ∈ horizontalProjection U, capRoof U x ≤ m * x + c := by
  intro x hx
  have hchord := roofChord_eq_affine hab (haffine a ⟨le_rfl, hab.le⟩)
    (haffine b ⟨hab.le, le_rfl⟩) x
  rcases le_total x a with hxa | hax
  · exact hchord ▸ ConcaveOn.le_roofChord_of_le hU.concaveOn_capRoof hx hb hab hxa
  rcases le_total b x with hbx | hxb
  · exact hchord ▸ ConcaveOn.le_roofChord_of_ge hU.concaveOn_capRoof ha hx hab hbx
  · exact (haffine x ⟨hax, hxb⟩).le

theorem IsDownwardCap.support_of_affine_segment {U : Set Plane}
    (hU : IsDownwardCap U) {a b m c : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ x ∈ Icc a b, capRoof U x = m * x + c) :
    support U (-m, 1) = c := by
  refine support_eq_of_mem hU.isCompact (fun p hp => ?_) (capRoof_mem hU.isCompact ha) ?_
  · have := le_capRoof hU.isCompact (show (p.1, p.2) ∈ U from hp)
    have := hU.capRoof_le_affine_of_affine_segment ha hb hab haffine p.1 ⟨p, hp, rfl⟩
    simp only [coordDot]
    linarith
  · simp only [coordDot, haffine a ⟨le_rfl, hab.le⟩]
    ring

/-- The entire middle interval has strictly negative inner-wall slack for
every normal of an interior point of a nonhorizontal affine roof facet. -/
theorem IsDownwardCap.middleWallSlack_neg_of_affine_triple
    {U : Set Plane} (hU : IsDownwardCap U) {a b u x v m c θ : ℝ}
    (hu : u ∈ horizontalProjection U) (hv : v ∈ horizontalProjection U)
    (hux : u < x) (hxv : x < v) (hm : m ≠ 0)
    (hfa : capRoof U a = m * a + c) (hfb : capRoof U b = m * b + c)
    (hfu : capRoof U u = m * u + c) (hfx : capRoof U x = m * x + c)
    (hfv : capRoof U v = m * v + c) (hθ : θ ∈ Icc 0 Real.pi)
    (hsupport : coordDot (x, capRoof U x) (unitNormal θ) = angleSupport U θ) :
    middleWallSlack U a b θ < 0 := by
  -- A supporting normal at an interior point of the facet is perpendicular to it.
  have hu' := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hu) (unitNormal θ)
  have hv' := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hv) (unitNormal θ)
  rw [hfu, coordDot_affine_graph_normal] at hu'
  rw [hfv, coordDot_affine_graph_normal] at hv'
  rw [hfx, coordDot_affine_graph_normal] at hsupport
  rw [← angleSupport, ← hsupport] at hu' hv'
  have hperp : Real.cos θ + m * Real.sin θ = 0 :=
    le_antisymm (by nlinarith only [hv', hxv]) (by nlinarith only [hu', hux])
  have hs0 := Real.sin_nonneg_of_mem_Icc hθ
  have hs1 : Real.sin θ < 1 := (Real.sin_le_one θ).lt_of_ne fun hs => hm <| by
    simpa [hs, Real.cos_eq_zero_iff_sin_eq.mpr (.inl hs)] using hperp
  rw [hperp, mul_zero, zero_add] at hsupport
  have ha1 : m * a + c ≤ 1 := hfa ▸ capRoof_le_one hU.isCompact hU.inStrip a
  have hb1 : m * b + c ≤ 1 := hfb ▸ capRoof_le_one hU.isCompact hU.inStrip b
  rw [middleWallSlack, show Real.cos θ = -m * Real.sin θ by linarith]
  refine sub_neg.mpr (lt_min ?_ ?_)
  · linarith [mul_le_mul_of_nonneg_right ha1 hs0]
  · linarith [mul_le_mul_of_nonneg_right hb1 hs0]

theorem affine_lt_one_between {u x v m c : ℝ} (hux : u < x) (hxv : x < v)
    (hm : m ≠ 0) (hu : m * u + c ≤ 1) (hv : m * v + c ≤ 1) :
    m * x + c < 1 := by
  rcases hm.lt_or_gt with hm | hm <;> nlinarith

/-- A tilted affine roof facet cannot have a relative-interior point in
either charged wing of a global maximum. -/
theorem IsFullCapMaximizer.not_affine_wing_triple {U : Set Plane}
    (hU : IsFullCapMaximizer U) {u x v m c : ℝ}
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
  have hu1 : m * u + c ≤ 1 := hfu ▸ capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip u
  have hv1 : m * v + c ≤ 1 := hfv ▸ capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip v
  obtain ⟨θ, hθ, hsupport, hnonneg⟩ := hU.exists_noninactive_normal_on_wing hxWing
    (hfx ▸ affine_lt_one_between hux hxv hm hu1 hv1)
  exact (hU.isCap.middleWallSlack_neg_of_affine_triple hu hv hux hxv hm hfa hfb hfu hfx hfv hθ
    hsupport).not_ge hnonneg

theorem IsDownwardCap.capRoof_eq_affine_between_contacts {U : Set Plane}
    (hU : IsDownwardCap U) {u v m c : ℝ}
    (hu : u ∈ horizontalProjection U) (hv : v ∈ horizontalProjection U)
    (huv : u < v) (hfu : capRoof U u = m * u + c)
    (hfv : capRoof U v = m * v + c)
    (hceiling : ∀ x ∈ horizontalProjection U, capRoof U x ≤ m * x + c) :
    ∀ x ∈ Icc u v, capRoof U x = m * x + c := fun x hx =>
  le_antisymm (hceiling x ((convex_horizontalProjection hU.convex).ordConnected.out hu hv hx))
    (roofChord_eq_affine huv hfu hfv x ▸ ConcaveOn.roofChord_le hU.concaveOn_capRoof hu hv huv hx)

/-- A literal supporting face, not an assigned facet, is pinned to the
entire moving middle interval of any prescribed tilted full maximum. -/
theorem IsFullCapMaximizer.horizontalProjection_middle_supportFace
    {U : Set Plane} (hU : IsFullCapMaximizer U) {m c : ℝ} (hm : m ≠ 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    horizontalProjection (supportFace U (-m, 1)) =
      middleHalfInterval (horizontalLeft U) (horizontalRight U) := by
  obtain ⟨ha, hb, hab⟩ :=
    hU.isCap.middleChord_endpoints (by linarith [hU.width_bounds.1, one_lt_M])
  set a := horizontalLeft U + capWidth U / 4
  set b := horizontalRight U - capWidth U / 4
  have hfa : capRoof U a = m * a + c := haffine a ⟨le_rfl, hab.le⟩
  have hfb : capRoof U b = m * b + c := haffine b ⟨hab.le, le_rfl⟩
  have hceiling := hU.isCap.capRoof_le_affine_of_affine_segment ha hb hab haffine
  have hsupport := hU.isCap.support_of_affine_segment ha hb hab haffine
  -- A face point outside the middle gives a facet interior point in a wing.
  have hwing (u v : ℝ) (hu : u ∈ horizontalProjection U) (hv : v ∈ horizontalProjection U)
      (huv : u < v) (hfu : capRoof U u = m * u + c) (hfv : capRoof U v = m * v + c)
      (hw : (u + v) / 2 ∈ Icc (horizontalLeft U) a ∪ Icc b (horizontalRight U)) : False :=
    hU.not_affine_wing_triple hu hv (by linarith) (by linarith) hm hfa hfb hfu
      (hU.isCap.capRoof_eq_affine_between_contacts hu hv huv hfu hfv hceiling _
        ⟨by linarith, by linarith⟩) hfv hw
  refine Subset.antisymm ?_ fun x hx => ⟨(x, capRoof U x), ⟨capRoof_mem hU.isCap.isCompact
    ((convex_horizontalProjection hU.isCap.convex).ordConnected.out ha hb hx), ?_⟩, rfl⟩
  · rintro _ ⟨p, ⟨hpU, hpface⟩, rfl⟩
    have hpProj : p.1 ∈ horizontalProjection U := ⟨p, hpU, rfl⟩
    have hp := le_capRoof hU.isCap.isCompact (show (p.1, p.2) ∈ U from hpU)
    simp only [mem_ofPred_eq, coordDot, hsupport] at hpface
    have hpRoof : capRoof U p.1 = m * p.1 + c :=
      le_antisymm (hceiling p.1 hpProj) (by linarith)
    have hpl := horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact
      hU.isCap.convex ▸ hpProj
    by_contra hout
    rcases lt_or_ge p.1 a with hpa | hap
    · exact hwing _ _ hpProj ha hpa hpRoof hfa (.inl ⟨by linarith [hpl.1], by linarith⟩)
    · have hbp : b < p.1 := lt_of_not_ge fun hpb => hout ⟨hap, hpb⟩
      exact hwing _ _ hb hpProj hbp hfb hpRoof (.inr ⟨by linarith, by linarith [hpl.2]⟩)
  · rw [mem_ofPred_eq, hsupport, haffine x hx]
    simp only [coordDot]
    ring

end AmbidextrousSofa
