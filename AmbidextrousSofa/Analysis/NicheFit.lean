module

public import AmbidextrousSofa.Analysis.NicheBoxBounds
public import AmbidextrousSofa.Analysis.EndpointPositivity
public import AmbidextrousSofa.Analysis.OneTurnSurvivor

@[expose] public section

/-!
# From middle niche control to the actual one-turn body

Convexity of the wing niche and concavity of the cap roof propagate
the two middle endpoint inequalities to both outer endpoints. For a
canonical full maximum, the exact pressure sum and the rational box
estimate convert the middle height bound by half the endpoint-height sum
into strict roof clearance. This leaves precisely that source-derived
middle height estimate supplied later by `SelectedNicheHeight` through the
actual finite erosion moments. `CanonicalOneTurn` applies this module with
that estimate discharged.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem IsFullCapMaximizer.sweptNiche_le_roof_of_middle_height_bound
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hleft : capRoof U (-C) = 1 - h) (hright : capRoof U C = 1)
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 37 / 50) (hh0 : 0 ≤ h) (hh1 : h ≤ 17 / 50)
    (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hmid : ∀ x ∈ Icc (-C) C, sweptNiche U (Real.pi / 2) x ≤
      (capRoof U (horizontalRight U) + capRoof U (horizontalLeft U)) / 2) :
    ∀ x ∈ horizontalProjection U, sweptNiche U (Real.pi / 2) x ≤ capRoof U x := by
  have hsum := hU.endpoint_height_sum_of_affine hheight haffine
  have hends := hU.isCap.middle_niche_le_two_fifths_of_endpoints hl hr (by linarith)
  have hconv := hU.isCap.convexOn_sweptNiche_wings_of_roof_endpoints hl hr hleft hright hC0 hC1 hh1
  have hconc := hU.isCap.concaveOn_capRoof
  rw [hU.isCap.horizontalProjection_eq_Icc, hl,
    hr] at hconc ⊢
  rw [hl, hr, show -2 * C + (2 * C - -2 * C) / 4 = -C by ring,
    show 2 * C - (2 * C - -2 * C) / 4 = C by ring, hleft, hright] at hsum
  rw [hl, hr] at hmid
  -- Concavity of the roof between the middle endpoints clears the middle interval.
  have hclear (x : ℝ) (hx : x ∈ Icc (-C) C) : sweptNiche U (Real.pi / 2) x ≤ capRoof U x := by
    have := hconc.min_le_of_mem_Icc ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hx
    rw [hleft, hright, min_eq_left (by linarith)] at this
    linarith [hmid x hx, hends.1, hends.2]
  -- On a convex wing of the niche, the concave clearance is at least its endpoint minimum.
  have wing {a b x : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ Icc (-2 * C) (2 * C))
      (hconvex : ConvexOn ℝ (Icc a b) (sweptNiche U (Real.pi / 2)))
      (ha : sweptNiche U (Real.pi / 2) a ≤ capRoof U a)
      (hb : sweptNiche U (Real.pi / 2) b ≤ capRoof U b) (hx : x ∈ Icc a b) :
      sweptNiche U (Real.pi / 2) x ≤ capRoof U x :=
    sub_nonneg.mp ((le_min (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)).trans
      (((hconc.subset hsub (convex_Icc a b)).sub hconvex).min_le_of_mem_Icc
        (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hx))
  have hroof0 := capRoof_nonneg hU.isCap.isCompact fun p hp => (hU.isCap.inStrip hp).1
  intro x hx
  rcases le_or_gt x (-C) with hxL | hxL
  · exact wing (by linarith) (Icc_subset_Icc le_rfl (by linarith)) hconv.1
      ((hU.isCap.sweptNiche_eq_zero_of_le_left hl.ge).trans_le (hroof0 _))
      (hclear _ ⟨le_rfl, by linarith⟩) ⟨hx.1, hxL⟩
  rcases le_or_gt C x with hxR | hxR
  · exact wing (by linarith) (Icc_subset_Icc (by linarith) le_rfl) hconv.2
      (hclear _ ⟨by linarith, le_rfl⟩)
      ((hU.isCap.sweptNiche_eq_zero_of_right_le hr.le).trans_le (hroof0 _)) ⟨hxR, hx.2⟩
  exact hclear x ⟨hxL.le, hxR.le⟩

end AmbidextrousSofa
