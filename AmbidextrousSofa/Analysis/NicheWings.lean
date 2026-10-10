import AmbidextrousSofa.Analysis.CornerConfinement
import AmbidextrousSofa.Analysis.Chord

/-!
# Convexity and endpoint values of the actual wing niche

On either side of all attached corners the swept niche is the supremum
of the corresponding affine walls and zero. Its convexity is proved
directly from the defining supremum. Outside the cap projection one
inner wall is nonpositive at every angle, so the actual niche vanishes.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem firstWall_affine (U : Set Plane) (θ x y : ℝ) {a b : ℝ} (hab : a + b = 1) :
    firstWall U θ (a * x + b * y) = a * firstWall U θ x + b * firstWall U θ y := by
  have hconstant := congrArg
    (fun t : ℝ => t * ((support U (unitNormal θ) - 1) / Real.sin θ)) hab
  unfold firstWall
  linear_combination -hconstant

theorem secondWall_affine (U : Set Plane) (θ x y : ℝ) {a b : ℝ} (hab : a + b = 1) :
    secondWall U θ (a * x + b * y) = a * secondWall U θ x + b * secondWall U θ y := by
  have hconstant := congrArg
    (fun t : ℝ => t * ((support U (companionNormal θ) - 1) / Real.cos θ)) hab
  unfold secondWall
  linear_combination -hconstant

theorem IsDownwardCap.convexOn_sweptNiche_right_of_corners {U : Set Plane}
    (hU : IsDownwardCap U) {r : ℝ}
    (hcorner : ∀ θ ∈ Ioo (0 : ℝ) (Real.pi / 2), (attachedCorner U θ).1 ≤ r) :
    ConvexOn ℝ (Ici r) (sweptNiche U (Real.pi / 2)) := by
  refine ⟨convex_Ici r, ?_⟩
  intro x hx y hy a b ha hb hab
  change sweptNiche U (Real.pi / 2) (a * x + b * y) ≤
    a * sweptNiche U (Real.pi / 2) x + b * sweptNiche U (Real.pi / 2) y
  have hz : r ≤ a * x + b * y := by
    have hax := mul_le_mul_of_nonneg_left hx ha
    have hby := mul_le_mul_of_nonneg_left hy hb
    have hsum := congrArg (fun t : ℝ => t * r) hab
    nlinarith
  apply sweptNiche_le_of_forall (by linarith [Real.pi_pos])
    (add_nonneg (mul_nonneg ha (sweptNiche_nonneg _ _ _))
      (mul_nonneg hb (sweptNiche_nonneg _ _ _)))
  intro θ hθ
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hxwall : firstWall U θ x ≤ sweptNiche U (Real.pi / 2) x := by
    rw [← cornerWall_eq_firstWall_of_corner_le hs hc ((hcorner θ hθ).trans hx)]
    exact cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact le_rfl x) hθ
  have hywall : firstWall U θ y ≤ sweptNiche U (Real.pi / 2) y := by
    rw [← cornerWall_eq_firstWall_of_corner_le hs hc ((hcorner θ hθ).trans hy)]
    exact cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact le_rfl y) hθ
  rw [cornerWall_eq_firstWall_of_corner_le hs hc ((hcorner θ hθ).trans hz),
    firstWall_affine U θ x y hab]
  exact add_le_add (mul_le_mul_of_nonneg_left hxwall ha) (mul_le_mul_of_nonneg_left hywall hb)

theorem IsDownwardCap.convexOn_sweptNiche_left_of_corners {U : Set Plane}
    (hU : IsDownwardCap U) {l : ℝ}
    (hcorner : ∀ θ ∈ Ioo (0 : ℝ) (Real.pi / 2), l ≤ (attachedCorner U θ).1) :
    ConvexOn ℝ (Iic l) (sweptNiche U (Real.pi / 2)) := by
  refine ⟨convex_Iic l, ?_⟩
  intro x hx y hy a b ha hb hab
  change sweptNiche U (Real.pi / 2) (a * x + b * y) ≤
    a * sweptNiche U (Real.pi / 2) x + b * sweptNiche U (Real.pi / 2) y
  have hz : a * x + b * y ≤ l := by
    have hax := mul_le_mul_of_nonneg_left hx ha
    have hby := mul_le_mul_of_nonneg_left hy hb
    have hsum := congrArg (fun t : ℝ => t * l) hab
    nlinarith
  apply sweptNiche_le_of_forall (by linarith [Real.pi_pos])
    (add_nonneg (mul_nonneg ha (sweptNiche_nonneg _ _ _))
      (mul_nonneg hb (sweptNiche_nonneg _ _ _)))
  intro θ hθ
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hxwall : secondWall U θ x ≤ sweptNiche U (Real.pi / 2) x := by
    rw [← cornerWall_eq_secondWall_of_le_corner hs hc (hx.trans (hcorner θ hθ))]
    exact cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact le_rfl x) hθ
  have hywall : secondWall U θ y ≤ sweptNiche U (Real.pi / 2) y := by
    rw [← cornerWall_eq_secondWall_of_le_corner hs hc (hy.trans (hcorner θ hθ))]
    exact cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact le_rfl y) hθ
  rw [cornerWall_eq_secondWall_of_le_corner hs hc (hz.trans (hcorner θ hθ)),
    secondWall_affine U θ x y hab]
  exact add_le_add (mul_le_mul_of_nonneg_left hxwall ha) (mul_le_mul_of_nonneg_left hywall hb)

theorem IsDownwardCap.sweptNiche_eq_zero_of_right_le {U : Set Plane}
    (hU : IsDownwardCap U) {x : ℝ} (hx : horizontalRight U ≤ x) :
    sweptNiche U (Real.pi / 2) x = 0 := by
  apply le_antisymm _ (sweptNiche_nonneg _ _ _)
  apply sweptNiche_le_of_forall (by linarith [Real.pi_pos]) le_rfl
  intro θ hθ
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hf : support U (unitNormal θ) ≤ x * Real.cos θ + Real.sin θ := by
    apply support_le_of_forall hU.nonempty
    intro p hp
    have hproj : p.1 ∈ horizontalProjection U := ⟨p, hp, rfl⟩
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex] at hproj
    have hpx := mul_le_mul_of_nonneg_right (hproj.2.trans hx) hc.le
    have hpy := mul_le_mul_of_nonneg_right (hU.inStrip hp).2 hs.le
    dsimp only [coordDot, unitNormal]
    nlinarith
  apply (min_le_left (firstWall U θ x) (secondWall U θ x)).trans
  rw [firstWall, div_le_iff₀ hs]
  nlinarith [Real.sin_le_one θ]

theorem IsDownwardCap.sweptNiche_eq_zero_of_le_left {U : Set Plane}
    (hU : IsDownwardCap U) {x : ℝ} (hx : x ≤ horizontalLeft U) :
    sweptNiche U (Real.pi / 2) x = 0 := by
  apply le_antisymm _ (sweptNiche_nonneg _ _ _)
  apply sweptNiche_le_of_forall (by linarith [Real.pi_pos]) le_rfl
  intro θ hθ
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hg : support U (companionNormal θ) ≤ -x * Real.sin θ + Real.cos θ := by
    apply support_le_of_forall hU.nonempty
    intro p hp
    have hproj : p.1 ∈ horizontalProjection U := ⟨p, hp, rfl⟩
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex] at hproj
    have hpx := mul_le_mul_of_nonneg_right (hx.trans hproj.1) hs.le
    have hpy := mul_le_mul_of_nonneg_right (hU.inStrip hp).2 hc.le
    dsimp only [coordDot, companionNormal]
    nlinarith
  apply (min_le_right (firstWall U θ x) (secondWall U θ x)).trans
  rw [secondWall, div_le_iff₀ hc]
  nlinarith [Real.cos_le_one θ]

theorem IsDownwardCap.convexOn_sweptNiche_wings_of_roof_endpoints
    {U : Set Plane} (hU : IsDownwardCap U) {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hleft : capRoof U (-C) = 1 - h) (hright : capRoof U C = 1)
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50) :
    ConvexOn ℝ (Icc (-2 * C) (-C)) (sweptNiche U (Real.pi / 2)) ∧
      ConvexOn ℝ (Icc C (2 * C)) (sweptNiche U (Real.pi / 2)) := by
  have hcorners : ∀ θ ∈ Ioo (0 : ℝ) (Real.pi / 2),
      (attachedCorner U θ).1 ∈ Ioo (-C) C := by
    intro θ hθ
    exact hU.attachedCorner_fst_mem_middle_of_roof_endpoints hl hr hleft hright hC0 hC1 hh hθ
  exact ⟨(hU.convexOn_sweptNiche_left_of_corners (fun θ hθ => (hcorners θ hθ).1.le)).subset
      (fun _ hx => hx.2) (convex_Icc _ _),
    (hU.convexOn_sweptNiche_right_of_corners (fun θ hθ => (hcorners θ hθ).2.le)).subset
      (fun _ hx => hx.1) (convex_Icc _ _)⟩

end AmbidextrousSofa
