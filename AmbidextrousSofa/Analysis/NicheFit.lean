import AmbidextrousSofa.Analysis.NicheBoxBounds
import AmbidextrousSofa.Analysis.EndpointPositivity
import AmbidextrousSofa.Analysis.OneTurnSurvivor

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

theorem ConcaveOn.const_le_of_endpoints {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ s f) {a b x d : ℝ} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a < b) (hfa : d ≤ f a) (hfb : d ≤ f b) (hx : x ∈ Icc a b) :
    d ≤ f x := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hweightA : 0 ≤ (b - x) / (b - a) := div_nonneg (sub_nonneg.mpr hx.2) hba.le
  have hweightB : 0 ≤ (x - a) / (b - a) := div_nonneg (sub_nonneg.mpr hx.1) hba.le
  have hsum : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
    field_simp [hba.ne'] <;> ring
  have hconstant := congrArg (fun t : ℝ => t * d) hsum
  have hleft := mul_le_mul_of_nonneg_left hfa hweightA
  have hright := mul_le_mul_of_nonneg_left hfb hweightB
  have hchord := hf.roofChord_le ha hb hab hx
  rw [roofChord_eq_interpolation f hab] at hchord
  nlinarith

theorem IsDownwardCap.sweptNiche_le_roof_of_middle_and_convex_wings
    {U : Set Plane} (hU : IsDownwardCap U) {C : ℝ} (hC : 0 < C)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hconvL : ConvexOn ℝ (Icc (-2 * C) (-C)) (sweptNiche U (Real.pi / 2)))
    (hconvR : ConvexOn ℝ (Icc C (2 * C)) (sweptNiche U (Real.pi / 2)))
    (hmid : ∀ x ∈ Icc (-C) C, sweptNiche U (Real.pi / 2) x ≤ capRoof U x) :
    ∀ x ∈ horizontalProjection U, sweptNiche U (Real.pi / 2) x ≤ capRoof U x := by
  have hprojection : horizontalProjection U = Icc (-2 * C) (2 * C) := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
  have hzeroL : sweptNiche U (Real.pi / 2) (-2 * C) = 0 := by
    rw [← hl]
    exact hU.sweptNiche_eq_zero_of_le_left le_rfl
  have hzeroR : sweptNiche U (Real.pi / 2) (2 * C) = 0 := by
    rw [← hr]
    exact hU.sweptNiche_eq_zero_of_right_le le_rfl
  have hroof0 := capRoof_nonneg hU.isCompact (fun p hp => (hU.inStrip hp).1)
  intro x hx
  rw [hprojection] at hx
  by_cases hxL : x ≤ -C
  · have hconc := (hU.concaveOn_capRoof.subset (s := Icc (-2 * C) (-C))
        (by intro z hz; rw [hprojection]; exact ⟨hz.1, by linarith [hz.2]⟩)
        (convex_Icc (-2 * C) (-C))).sub hconvL
    have hleft : 0 ≤ (capRoof U - sweptNiche U (Real.pi / 2)) (-2 * C) := by
      change 0 ≤ capRoof U (-2 * C) - sweptNiche U (Real.pi / 2) (-2 * C)
      rw [hzeroL, sub_zero]
      exact hroof0 _
    have hright : 0 ≤ (capRoof U - sweptNiche U (Real.pi / 2)) (-C) :=
      sub_nonneg.mpr (hmid (-C) ⟨le_rfl, by linarith⟩)
    exact sub_nonneg.mp (hconc.const_le_of_endpoints
      ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
      hleft hright ⟨hx.1, hxL⟩)
  · by_cases hxR : C ≤ x
    · have hconc := (hU.concaveOn_capRoof.subset (s := Icc C (2 * C))
          (by intro z hz; rw [hprojection]; exact ⟨by linarith [hz.1], hz.2⟩)
          (convex_Icc C (2 * C))).sub hconvR
      have hleft : 0 ≤ (capRoof U - sweptNiche U (Real.pi / 2)) C :=
        sub_nonneg.mpr (hmid C ⟨by linarith, le_rfl⟩)
      have hright : 0 ≤ (capRoof U - sweptNiche U (Real.pi / 2)) (2 * C) := by
        change 0 ≤ capRoof U (2 * C) - sweptNiche U (Real.pi / 2) (2 * C)
        rw [hzeroR, sub_zero]
        exact hroof0 _
      exact sub_nonneg.mp (hconc.const_le_of_endpoints
        ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
        hleft hright ⟨hxR, hx.2⟩)
    · exact hmid x ⟨(lt_of_not_ge hxL).le, (lt_of_not_ge hxR).le⟩

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
  have hC : 0 < C := by linarith
  have hprojection : horizontalProjection U = Icc (-2 * C) (2 * C) := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex, hl, hr]
  have hminus : horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 = -C := by
    rw [hl, hr]
    ring
  have hplus : horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 = C := by
    rw [hl, hr]
    ring
  have hsum := hU.endpoint_height_sum_of_affine hheight haffine
  rw [hminus, hplus, hleft, hright] at hsum
  have hends := hU.isCap.middle_niche_le_two_fifths_of_endpoints hl hr (by linarith)
  have hroof : ∀ x ∈ Icc (-C) C, 1 - h ≤ capRoof U x := by
    intro x hx
    apply hU.isCap.concaveOn_capRoof.const_le_of_endpoints
      (a := -C) (b := C)
    · rw [hprojection]; constructor <;> linarith
    · rw [hprojection]; constructor <;> linarith
    · linarith
    · rw [hleft]
    · rw [hright]; linarith
    · exact hx
  have hclear : ∀ x ∈ Icc (-C) C, sweptNiche U (Real.pi / 2) x ≤ capRoof U x := by
    intro x hx
    have hnx := hmid x hx
    have hrx := hroof x hx
    linarith [hends.1, hends.2]
  have hconv := hU.isCap.convexOn_sweptNiche_wings_of_roof_endpoints
    hl hr hleft hright hC0 hC1 hh1
  exact hU.isCap.sweptNiche_le_roof_of_middle_and_convex_wings
    hC hl hr hconv.1 hconv.2 hclear

end AmbidextrousSofa
