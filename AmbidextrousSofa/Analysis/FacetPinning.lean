import AmbidextrousSofa.Analysis.InactiveNormals
import AmbidextrousSofa.Analysis.TopFacetEndpoints

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
  dsimp [coordDot, unitNormal]
  ring

theorem IsDownwardCap.capRoof_le_affine_of_affine_segment {U : Set Plane}
    (hU : IsDownwardCap U) {a b m c : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ x ∈ Icc a b, capRoof U x = m * x + c) :
    ∀ x ∈ horizontalProjection U, capRoof U x ≤ m * x + c := by
  have hfa := haffine a ⟨le_rfl, hab.le⟩
  have hfb := haffine b ⟨hab.le, le_rfl⟩
  intro x hx
  rcases le_total x a with hxa | hax
  · have h := hU.concaveOn_capRoof.le_roofChord_of_le hx hb hab hxa
    rwa [roofChord_eq_affine hab hfa hfb] at h
  · rcases le_total b x with hbx | hxb
    · have h := hU.concaveOn_capRoof.le_roofChord_of_ge ha hx hab hbx
      rwa [roofChord_eq_affine hab hfa hfb] at h
    · exact (haffine x ⟨hax, hxb⟩).le

theorem IsDownwardCap.support_of_affine_segment {U : Set Plane}
    (hU : IsDownwardCap U) {a b m c : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ x ∈ Icc a b, capRoof U x = m * x + c) :
    support U (-m, 1) = c := by
  apply support_eq_of_mem hU.isCompact (q := (a, capRoof U a)) ?_
    (capRoof_mem hU.isCompact ha) ?_
  · intro p hp
    have hpRoof := le_capRoof hU.isCompact
      (show (p.1, p.2) ∈ U by simpa only [Prod.mk.eta] using hp)
    have hpLine := hU.capRoof_le_affine_of_affine_segment ha hb hab haffine
      p.1 ⟨p, hp, rfl⟩
    change p.1 * (-m) + p.2 * 1 ≤ c
    nlinarith
  · rw [haffine a ⟨le_rfl, hab.le⟩]
    dsimp [coordDot]
    ring

/-- A supporting normal at an interior point of three collinear roof
points must be perpendicular to their line. -/
theorem IsDownwardCap.support_normal_perpendicular_of_affine_triple
    {U : Set Plane} (hU : IsDownwardCap U) {u x v m c θ : ℝ}
    (hu : u ∈ horizontalProjection U) (hv : v ∈ horizontalProjection U)
    (hux : u < x) (hxv : x < v)
    (hfu : capRoof U u = m * u + c) (hfx : capRoof U x = m * x + c)
    (hfv : capRoof U v = m * v + c)
    (hsupport : coordDot (x, capRoof U x) (unitNormal θ) = angleSupport U θ) :
    Real.cos θ + m * Real.sin θ = 0 := by
  let d := Real.cos θ + m * Real.sin θ
  have huSupport := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hu)
    (unitNormal θ)
  have hvSupport := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hv)
    (unitNormal θ)
  change coordDot (u, capRoof U u) (unitNormal θ) ≤ angleSupport U θ at huSupport
  change coordDot (v, capRoof U v) (unitNormal θ) ≤ angleSupport U θ at hvSupport
  rw [hfu, coordDot_affine_graph_normal] at huSupport
  rw [hfv, coordDot_affine_graph_normal] at hvSupport
  rw [hfx, coordDot_affine_graph_normal] at hsupport
  rw [← hsupport] at huSupport hvSupport
  change u * d + c * Real.sin θ ≤ x * d + c * Real.sin θ at huSupport
  change v * d + c * Real.sin θ ≤ x * d + c * Real.sin θ at hvSupport
  have hd0 : 0 ≤ d := nonneg_of_mul_nonneg_right
    (by nlinarith : 0 ≤ (x - u) * d) (sub_pos.mpr hux)
  have hd1 : d ≤ 0 := nonpos_of_mul_nonpos_right
    (by nlinarith : (v - x) * d ≤ 0) (sub_pos.mpr hxv)
  exact le_antisymm hd1 hd0

theorem sin_lt_one_of_tilted_perpendicular {m θ : ℝ} (hm : m ≠ 0)
    (hperp : Real.cos θ + m * Real.sin θ = 0) : Real.sin θ < 1 := by
  by_contra h
  have hs : Real.sin θ = 1 := le_antisymm (Real.sin_le_one θ) (le_of_not_gt h)
  have hc : Real.cos θ = 0 := by
    have hcircle := Real.sin_sq_add_cos_sq θ
    rw [hs] at hcircle
    nlinarith [sq_nonneg (Real.cos θ)]
  apply hm
  simpa only [hs, hc, mul_one, zero_add] using hperp

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
  have hperp := hU.support_normal_perpendicular_of_affine_triple
    hu hv hux hxv hfu hfx hfv hsupport
  have hs0 := Real.sin_nonneg_of_mem_Icc hθ
  have hs1 := sin_lt_one_of_tilted_perpendicular hm hperp
  have hsupportC : angleSupport U θ = c * Real.sin θ := by
    rw [hfx, coordDot_affine_graph_normal, hperp, mul_zero, zero_add] at hsupport
    exact hsupport.symm
  have hc : Real.cos θ = -m * Real.sin θ := by linarith
  have hformula (z : ℝ) : angleSupport U θ - 1 - z * Real.cos θ =
      (m * z + c) * Real.sin θ - 1 := by
    rw [hsupportC, hc]
    ring
  have ha1 : m * a + c ≤ 1 := by
    rw [← hfa]; exact capRoof_le_one hU.isCompact hU.inStrip a
  have hb1 : m * b + c ≤ 1 := by
    rw [← hfb]; exact capRoof_le_one hU.isCompact hU.inStrip b
  have haNeg : angleSupport U θ - 1 - a * Real.cos θ < 0 := by
    rw [hformula]
    nlinarith [mul_le_mul_of_nonneg_right ha1 hs0]
  have hbNeg : angleSupport U θ - 1 - b * Real.cos θ < 0 := by
    rw [hformula]
    nlinarith [mul_le_mul_of_nonneg_right hb1 hs0]
  unfold middleWallSlack
  rcases le_total (a * Real.cos θ) (b * Real.cos θ) with h | h
  · rwa [min_eq_left h]
  · rwa [min_eq_right h]

theorem affine_lt_one_between {u x v m c : ℝ} (hux : u < x) (hxv : x < v)
    (hm : m ≠ 0) (hu : m * u + c ≤ 1) (hv : m * v + c ≤ 1) :
    m * x + c < 1 := by
  rcases lt_or_gt_of_ne hm with hm | hm
  · have h := mul_lt_mul_of_neg_left hux hm
    linarith
  · have h := mul_lt_mul_of_pos_left hxv hm
    linarith

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

theorem IsDownwardCap.capRoof_eq_affine_between_contacts {U : Set Plane}
    (hU : IsDownwardCap U) {u v m c : ℝ}
    (hu : u ∈ horizontalProjection U) (hv : v ∈ horizontalProjection U)
    (huv : u < v) (hfu : capRoof U u = m * u + c)
    (hfv : capRoof U v = m * v + c)
    (hceiling : ∀ x ∈ horizontalProjection U, capRoof U x ≤ m * x + c) :
    ∀ x ∈ Icc u v, capRoof U x = m * x + c := by
  intro x hx
  have hxU : x ∈ horizontalProjection U :=
    (convex_horizontalProjection hU.convex).ordConnected.out hu hv hx
  apply le_antisymm (hceiling x hxU)
  have h := hU.concaveOn_capRoof.roofChord_le hu hv huv hx
  rwa [roofChord_eq_affine huv hfu hfv] at h

/-- A literal supporting face, not an assigned facet, is pinned to the
entire moving middle interval of any prescribed tilted full maximum. -/
theorem IsFullCapMaximizer.horizontalProjection_middle_supportFace
    {U : Set Plane} (hU : IsFullCapMaximizer U) {m c : ℝ} (hm : m ≠ 0)
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
