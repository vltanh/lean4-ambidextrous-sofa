module

public import AmbidextrousSofa.Analysis.CornerConfinement
public import AmbidextrousSofa.Analysis.Chord

@[expose] public section

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

/-- Where every inner corner is one affine wall `w θ`, the niche is convex. -/
private theorem IsDownwardCap.convexOn_sweptNiche_of_walls {U : Set Plane}
    (hU : IsDownwardCap U) {s : Set ℝ} (hs : Convex ℝ s) (w : ℝ → ℝ → ℝ)
    (hw : ∀ θ x y (a b : ℝ), a + b = 1 → w θ (a • x + b • y) = a • w θ x + b • w θ y)
    (hcorner : ∀ θ ∈ Ioo (0 : ℝ) (Real.pi / 2), ∀ x ∈ s, cornerWall U θ x = w θ x) :
    ConvexOn ℝ s (sweptNiche U (Real.pi / 2)) := by
  refine ⟨hs, fun x hx y hy a b ha hb hab => sweptNiche_le_of_forall (by positivity)
    (add_nonneg (mul_nonneg ha (sweptNiche_nonneg _ _ _)) (mul_nonneg hb (sweptNiche_nonneg _ _ _)))
    fun θ hθ => ?_⟩
  rw [hcorner θ hθ _ (hs hx hy ha hb hab), hw θ x y a b hab, ← hcorner θ hθ x hx,
    ← hcorner θ hθ y hy]
  gcongr <;> exact cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact le_rfl _) hθ

theorem IsDownwardCap.convexOn_sweptNiche_right_of_corners {U : Set Plane}
    (hU : IsDownwardCap U) {r : ℝ}
    (hcorner : ∀ θ ∈ Ioo (0 : ℝ) (Real.pi / 2), (attachedCorner U θ).1 ≤ r) :
    ConvexOn ℝ (Ici r) (sweptNiche U (Real.pi / 2)) :=
  hU.convexOn_sweptNiche_of_walls (convex_Ici r) (firstWall U)
    (fun θ x y a b hab => by
      simp only [firstWall, smul_eq_mul]
      linear_combination (1 - support U (unitNormal θ)) / Real.sin θ * hab)
    fun θ hθ _ hx => cornerWall_eq_firstWall_of_corner_le (sin_cos_pos_of_mem_quarter hθ).1
      (sin_cos_pos_of_mem_quarter hθ).2 ((hcorner θ hθ).trans hx)

theorem IsDownwardCap.convexOn_sweptNiche_left_of_corners {U : Set Plane}
    (hU : IsDownwardCap U) {l : ℝ}
    (hcorner : ∀ θ ∈ Ioo (0 : ℝ) (Real.pi / 2), l ≤ (attachedCorner U θ).1) :
    ConvexOn ℝ (Iic l) (sweptNiche U (Real.pi / 2)) :=
  hU.convexOn_sweptNiche_of_walls (convex_Iic l) (secondWall U)
    (fun θ x y a b hab => by
      simp only [secondWall, smul_eq_mul]
      linear_combination (1 - support U (companionNormal θ)) / Real.cos θ * hab)
    fun θ hθ _ hx => cornerWall_eq_secondWall_of_le_corner (sin_cos_pos_of_mem_quarter hθ).1
      (sin_cos_pos_of_mem_quarter hθ).2 (hx.trans (hcorner θ hθ))

theorem IsDownwardCap.sweptNiche_eq_zero_of_right_le {U : Set Plane}
    (hU : IsDownwardCap U) {x : ℝ} (hx : horizontalRight U ≤ x) :
    sweptNiche U (Real.pi / 2) x = 0 := by
  refine le_antisymm (sweptNiche_le_of_forall (by positivity) le_rfl fun θ hθ => ?_)
    (sweptNiche_nonneg _ _ _)
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter hθ
  have hf : support U (unitNormal θ) ≤ x * Real.cos θ + 1 :=
    support_le_of_forall hU.nonempty fun p hp => by
      have : p.1 ≤ horizontalRight U :=
        le_csSup (isCompact_horizontalProjection hU.isCompact).bddAbove ⟨p, hp, rfl⟩
      simp only [coordDot, unitNormal]
      linarith [mul_le_mul_of_nonneg_right (this.trans hx) hc.le,
        mul_le_mul_of_nonneg_right (hU.inStrip hp).2 hs.le, Real.sin_le_one θ]
  exact (min_le_left _ _).trans (div_nonpos_of_nonpos_of_nonneg (by linarith) hs.le)

theorem IsDownwardCap.sweptNiche_eq_zero_of_le_left {U : Set Plane}
    (hU : IsDownwardCap U) {x : ℝ} (hx : x ≤ horizontalLeft U) :
    sweptNiche U (Real.pi / 2) x = 0 := by
  refine le_antisymm (sweptNiche_le_of_forall (by positivity) le_rfl fun θ hθ => ?_)
    (sweptNiche_nonneg _ _ _)
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter hθ
  have hg : support U (companionNormal θ) ≤ 1 - x * Real.sin θ :=
    support_le_of_forall hU.nonempty fun p hp => by
      have : horizontalLeft U ≤ p.1 :=
        csInf_le (isCompact_horizontalProjection hU.isCompact).bddBelow ⟨p, hp, rfl⟩
      simp only [coordDot, companionNormal]
      linarith [mul_le_mul_of_nonneg_right (hx.trans this) hs.le,
        mul_le_mul_of_nonneg_right (hU.inStrip hp).2 hc.le, Real.cos_le_one θ]
  exact (min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg (by linarith) hc.le)

theorem IsDownwardCap.convexOn_sweptNiche_wings_of_roof_endpoints
    {U : Set Plane} (hU : IsDownwardCap U) {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hleft : capRoof U (-C) = 1 - h) (hright : capRoof U C = 1)
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50) :
    ConvexOn ℝ (Icc (-2 * C) (-C)) (sweptNiche U (Real.pi / 2)) ∧
      ConvexOn ℝ (Icc C (2 * C)) (sweptNiche U (Real.pi / 2)) := by
  have hcorners θ (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2)) :=
    hU.attachedCorner_fst_mem_middle_of_roof_endpoints hl hr hleft hright hC0 hC1 hh hθ
  exact ⟨(hU.convexOn_sweptNiche_left_of_corners fun θ hθ => (hcorners θ hθ).1.le).subset
      (fun _ hx => hx.2) (convex_Icc _ _),
    (hU.convexOn_sweptNiche_right_of_corners fun θ hθ => (hcorners θ hθ).2.le).subset
      (fun _ hx => hx.1) (convex_Icc _ _)⟩

end AmbidextrousSofa
