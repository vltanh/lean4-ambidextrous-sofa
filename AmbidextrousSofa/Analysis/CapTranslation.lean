module

public import AmbidextrousSofa.Measure.CapScore
public import AmbidextrousSofa.Measure.RigidInvariance

@[expose] public section

/-!
# Horizontal translation of actual cap scores

Every roof, support wall, and moving integration window is translated by
the same amount. Product Lebesgue translation invariance therefore leaves
the full or partial spatial score unchanged. This permits compact-domain
normalization without imposing symmetry on a competitor.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def horizontalTranslate (U : Set Plane) (c : ℝ) : Set Plane :=
  (fun p => p + (c, 0)) '' U

theorem mem_horizontalTranslate_iff (U : Set Plane) (c : ℝ) (p : Plane) :
    p ∈ horizontalTranslate U c ↔ (p.1 - c, p.2) ∈ U := by
  obtain ⟨x, y⟩ := p
  simp [horizontalTranslate, image_add_right, sub_eq_add_neg]

theorem IsDownwardCap.horizontalTranslate {U : Set Plane} (hU : IsDownwardCap U) (c : ℝ) :
    IsDownwardCap (AmbidextrousSofa.horizontalTranslate U c) := by
  refine ⟨hU.nonempty.image _, hU.isCompact.image (by fun_prop), ?_, ?_,
    fun p hp y hy0 hyp => (mem_horizontalTranslate_iff _ _ _).2
      (hU.downward _ ((mem_horizontalTranslate_iff _ _ _).1 hp) y hy0 hyp)⟩
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ a b ha hb hab
    refine ⟨a • p + b • q, hU.convex hp hq ha hb hab, ?_⟩
    ext <;> simp
    linear_combination (-c) * hab
  · rintro _ ⟨q, hq, rfl⟩
    simpa [unitStrip] using hU.inStrip hq

theorem capRoof_horizontalTranslate (U : Set Plane) (c x : ℝ) :
    capRoof (horizontalTranslate U c) x = capRoof U (x - c) :=
  capRoof_eq_of_verticalFiber_eq (Set.ext fun y => mem_horizontalTranslate_iff U c (x, y))

theorem support_horizontalTranslate {U : Set Plane} (hU : IsDownwardCap U) (c : ℝ) (v : Plane) :
    support (horizontalTranslate U c) v = support U v + c * v.1 := by
  simp [horizontalTranslate, support_translate hU.isCompact hU.nonempty, coordDot, -image_add_right]

theorem horizontalRight_horizontalTranslate {U : Set Plane} (hU : IsDownwardCap U) (c : ℝ) :
    horizontalRight (horizontalTranslate U c) = horizontalRight U + c := by
  simp [← support_horizontal_right, support_horizontalTranslate hU]

theorem horizontalLeft_horizontalTranslate {U : Set Plane} (hU : IsDownwardCap U) (c : ℝ) :
    horizontalLeft (horizontalTranslate U c) = horizontalLeft U + c := by
  have h := support_horizontalTranslate hU c (-1, 0)
  simp only [support_horizontal_left (hU.horizontalTranslate c).isCompact
    (hU.horizontalTranslate c).nonempty, support_horizontal_left hU.isCompact hU.nonempty] at h
  linarith

theorem capWidth_horizontalTranslate {U : Set Plane} (hU : IsDownwardCap U) (c : ℝ) :
    capWidth (horizontalTranslate U c) = capWidth U := by
  simp [capWidth, horizontalRight_horizontalTranslate hU, horizontalLeft_horizontalTranslate hU]

theorem firstWall_horizontalTranslate {U : Set Plane} (hU : IsDownwardCap U) (c t x : ℝ) :
    firstWall (horizontalTranslate U c) t x = firstWall U t (x - c) := by
  simp only [firstWall, support_horizontalTranslate hU, unitNormal]
  ring

theorem cornerWall_horizontalTranslate {U : Set Plane} (hU : IsDownwardCap U) (c t x : ℝ) :
    cornerWall (horizontalTranslate U c) t x = cornerWall U t (x - c) := by
  simp only [cornerWall, firstWall_horizontalTranslate hU, secondWall,
    support_horizontalTranslate hU, companionNormal]
  congr 1
  ring

theorem partialBarrier_horizontalTranslate {U : Set Plane} (hU : IsDownwardCap U) (c α x : ℝ) :
    partialBarrier (horizontalTranslate U c) α x = partialBarrier U α (x - c) := by
  simp only [partialBarrier, sweptNiche, sweptWallValues, cornerWall_horizontalTranslate hU,
    firstWall_horizontalTranslate hU]

theorem middleHalfInterval_add (l r c : ℝ) :
    middleHalfInterval (l + c) (r + c) = (fun x => x + c) '' middleHalfInterval l r := by
  rw [middleHalfInterval, middleHalfInterval, image_add_const_Icc]
  congr 1 <;> ring

theorem setIntegral_horizontal_shift (f : ℝ → ℝ) (D : Set ℝ) (c : ℝ) :
    (∫ x in (fun y => y + c) '' D, f (x - c)) = ∫ x in D, f x := by
  simpa only [add_sub_cancel_right] using
    (measurePreserving_add_right (volume : Measure ℝ) c).setIntegral_image_emb
      (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding (fun x => f (x - c)) D

/-- Translation invariance includes the proper terminal wall and holds for
every real terminal parameter in the definition. -/
theorem capScore_horizontalTranslate {U : Set Plane} (hU : IsDownwardCap U) (c α : ℝ) :
    capScore (horizontalTranslate U c) α = capScore U α := by
  rw [capScore_eq_integrals, capScore_eq_integrals,
    horizontalLeft_horizontalTranslate hU, horizontalRight_horizontalTranslate hU,
    middleHalfInterval_add, ← image_add_const_Icc, ← image_sdiff (add_left_injective c)]
  simp only [capRoof_horizontalTranslate, partialBarrier_horizontalTranslate hU,
    setIntegral_horizontal_shift]

/-- Translate a cap so its actual projection is centered at the origin. -/
def centeredCap (U : Set Plane) : Set Plane :=
  horizontalTranslate U (-(horizontalLeft U + horizontalRight U) / 2)

theorem IsDownwardCap.centeredCap {U : Set Plane} (hU : IsDownwardCap U) :
    IsDownwardCap (AmbidextrousSofa.centeredCap U) := hU.horizontalTranslate _

theorem horizontalLeft_centeredCap {U : Set Plane} (hU : IsDownwardCap U) :
    horizontalLeft (centeredCap U) = -capWidth U / 2 := by
  rw [centeredCap, horizontalLeft_horizontalTranslate hU, capWidth]
  ring

theorem horizontalRight_centeredCap {U : Set Plane} (hU : IsDownwardCap U) :
    horizontalRight (centeredCap U) = capWidth U / 2 := by
  rw [centeredCap, horizontalRight_horizontalTranslate hU, capWidth]
  ring

theorem capScore_centeredCap {U : Set Plane} (hU : IsDownwardCap U) (α : ℝ) :
    capScore (centeredCap U) α = capScore U α := capScore_horizontalTranslate hU _ α

theorem centeredCap_subset_box_of_width_le {U : Set Plane} (hU : IsDownwardCap U)
    {B : ℝ} (hwidth : capWidth U ≤ 2 * B) :
    centeredCap U ⊆ Icc (-B, 0) (B, 1) := by
  intro p hp
  have hx : p.1 ∈ horizontalProjection (centeredCap U) := ⟨p, hp, rfl⟩
  rw [hU.centeredCap.horizontalProjection_eq_Icc, horizontalLeft_centeredCap hU,
    horizontalRight_centeredCap hU] at hx
  have hy := hU.centeredCap.inStrip hp
  exact ⟨⟨by linarith [hx.1], hy.1⟩, by linarith [hx.2], hy.2⟩

end AmbidextrousSofa
