import AmbidextrousSofa.Measure.CapScore
import AmbidextrousSofa.Measure.RigidInvariance

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
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa only [Prod.fst_add, Prod.snd_add, add_sub_cancel_right, add_zero] using hq
  · intro hp
    refine ⟨(p.1 - c, p.2), hp, ?_⟩
    apply Prod.ext <;> simp

theorem IsDownwardCap.horizontalTranslate {U : Set Plane} (hU : IsDownwardCap U) (c : ℝ) :
    IsDownwardCap (horizontalTranslate U c) := by
  refine ⟨hU.nonempty.image _, hU.isCompact.image (by fun_prop), ?_, ?_, ?_⟩
  · rintro p ⟨p, hp, rfl⟩ q ⟨q, hq, rfl⟩ a b ha hb hab
    refine ⟨a • p + b • q, hU.convex hp hq ha hb hab, ?_⟩
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.fst_smul, smul_eq_mul]
      have hc : (a + b) * c = c := by rw [hab, one_mul]
      nlinarith [hc]
    · simp only [Prod.snd_add, Prod.snd_smul, smul_eq_mul, add_zero]
  · rintro p ⟨q, hq, rfl⟩
    simpa only [unitStrip, mem_setOf_eq, Prod.snd_add, add_zero] using hU.inStrip hq
  · intro p hp y hy0 hyp
    rw [mem_horizontalTranslate_iff] at hp ⊢
    exact hU.downward (p.1 - c, p.2) hp y hy0 hyp

theorem verticalFiber_horizontalTranslate (U : Set Plane) (c x : ℝ) :
    verticalFiber (horizontalTranslate U c) x = verticalFiber U (x - c) := by
  ext y
  exact mem_horizontalTranslate_iff U c (x, y)

theorem horizontalProjection_horizontalTranslate_iff (U : Set Plane) (c x : ℝ) :
    x ∈ horizontalProjection (horizontalTranslate U c) ↔ x - c ∈ horizontalProjection U := by
  rw [← verticalFiber_nonempty_iff, ← verticalFiber_nonempty_iff,
    verticalFiber_horizontalTranslate]

theorem capRoof_horizontalTranslate (U : Set Plane) (c x : ℝ) :
    capRoof (horizontalTranslate U c) x = capRoof U (x - c) := by
  simp only [capRoof, horizontalProjection_horizontalTranslate_iff, verticalFiber_horizontalTranslate]

theorem horizontalRight_horizontalTranslate {U : Set Plane} (hU : IsDownwardCap U) (c : ℝ) :
    horizontalRight (horizontalTranslate U c) = horizontalRight U + c := by
  rw [← support_horizontal_right, horizontalTranslate, support_translate hU.isCompact hU.nonempty,
    support_horizontal_right]
  simp [coordDot]

theorem horizontalLeft_horizontalTranslate {U : Set Plane} (hU : IsDownwardCap U) (c : ℝ) :
    horizontalLeft (horizontalTranslate U c) = horizontalLeft U + c := by
  have h := support_translate hU.isCompact hU.nonempty (c, 0) (-1, 0)
  rw [support_horizontal_left (hU.horizontalTranslate c).isCompact
      (hU.horizontalTranslate c).nonempty,
    support_horizontal_left hU.isCompact hU.nonempty] at h
  simp only [coordDot, mul_neg_one, zero_mul, add_zero] at h
  linarith

theorem capWidth_horizontalTranslate {U : Set Plane} (hU : IsDownwardCap U) (c : ℝ) :
    capWidth (horizontalTranslate U c) = capWidth U := by
  unfold capWidth
  rw [horizontalRight_horizontalTranslate hU, horizontalLeft_horizontalTranslate hU]
  ring

theorem firstWall_horizontalTranslate {U : Set Plane} (hU : IsDownwardCap U) (c t x : ℝ) :
    firstWall (horizontalTranslate U c) t x = firstWall U t (x - c) := by
  unfold firstWall horizontalTranslate
  rw [support_translate hU.isCompact hU.nonempty]
  unfold coordDot unitNormal
  congr 1
  ring

theorem secondWall_horizontalTranslate {U : Set Plane} (hU : IsDownwardCap U) (c t x : ℝ) :
    secondWall (horizontalTranslate U c) t x = secondWall U t (x - c) := by
  unfold secondWall horizontalTranslate
  rw [support_translate hU.isCompact hU.nonempty]
  unfold coordDot companionNormal
  congr 1
  ring

theorem cornerWall_horizontalTranslate {U : Set Plane} (hU : IsDownwardCap U) (c t x : ℝ) :
    cornerWall (horizontalTranslate U c) t x = cornerWall U t (x - c) := by
  rw [cornerWall, firstWall_horizontalTranslate hU, secondWall_horizontalTranslate hU]
  rfl

theorem sweptNiche_horizontalTranslate {U : Set Plane} (hU : IsDownwardCap U) (c α x : ℝ) :
    sweptNiche (horizontalTranslate U c) α x = sweptNiche U α (x - c) := by
  unfold sweptNiche sweptWallValues
  simp only [cornerWall_horizontalTranslate hU]

theorem partialBarrier_horizontalTranslate {U : Set Plane} (hU : IsDownwardCap U) (c α x : ℝ) :
    partialBarrier (horizontalTranslate U c) α x = partialBarrier U α (x - c) := by
  rw [partialBarrier, sweptNiche_horizontalTranslate hU, firstWall_horizontalTranslate hU]
  rfl

theorem middleHalfInterval_add (l r c : ℝ) :
    middleHalfInterval (l + c) (r + c) = (fun x => x + c) '' middleHalfInterval l r := by
  unfold middleHalfInterval
  rw [image_add_const_Icc]
  congr 1 <;> ring

theorem setIntegral_horizontal_shift (f : ℝ → ℝ) (D : Set ℝ) (c : ℝ) :
    (∫ x in (fun y => y + c) '' D, f (x - c)) = ∫ x in D, f x := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) c).setIntegral_image_emb
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding (fun x => f (x - c)) D
  simpa only [add_sub_cancel_right] using h

/-- Translation invariance includes the proper terminal wall and holds for
every real terminal parameter in the definition. -/
theorem capScore_horizontalTranslate {U : Set Plane} (hU : IsDownwardCap U) (c α : ℝ) :
    capScore (horizontalTranslate U c) α = capScore U α := by
  rw [capScore_eq_integrals, capScore_eq_integrals,
    horizontalLeft_horizontalTranslate hU, horizontalRight_horizontalTranslate hU,
    middleHalfInterval_add, ← image_add_const_Icc]
  rw [← image_sdiff (add_right_injective c)]
  simp only [capRoof_horizontalTranslate, partialBarrier_horizontalTranslate hU,
    setIntegral_horizontal_shift]

/-- Translate a cap so its actual projection is centered at the origin. -/
def centeredCap (U : Set Plane) : Set Plane :=
  horizontalTranslate U (-(horizontalLeft U + horizontalRight U) / 2)

theorem IsDownwardCap.centeredCap {U : Set Plane} (hU : IsDownwardCap U) :
    IsDownwardCap (centeredCap U) := hU.horizontalTranslate _

theorem horizontalLeft_centeredCap {U : Set Plane} (hU : IsDownwardCap U) :
    horizontalLeft (centeredCap U) = -capWidth U / 2 := by
  rw [centeredCap, horizontalLeft_horizontalTranslate hU]
  unfold capWidth
  ring

theorem horizontalRight_centeredCap {U : Set Plane} (hU : IsDownwardCap U) :
    horizontalRight (centeredCap U) = capWidth U / 2 := by
  rw [centeredCap, horizontalRight_horizontalTranslate hU]
  unfold capWidth
  ring

theorem capScore_centeredCap {U : Set Plane} (hU : IsDownwardCap U) (α : ℝ) :
    capScore (centeredCap U) α = capScore U α := capScore_horizontalTranslate hU _ α

theorem centeredCap_subset_box_of_width_le {U : Set Plane} (hU : IsDownwardCap U)
    {B : ℝ} (hwidth : capWidth U ≤ 2 * B) :
    centeredCap U ⊆ Icc (-B, 0) (B, 1) := by
  intro p hp
  have hx : p.1 ∈ Icc (horizontalLeft (centeredCap U)) (horizontalRight (centeredCap U)) := by
    rw [← horizontalProjection_eq_Icc hU.centeredCap.nonempty hU.centeredCap.isCompact
      hU.centeredCap.convex]
    exact ⟨p, hp, rfl⟩
  rw [horizontalLeft_centeredCap hU, horizontalRight_centeredCap hU] at hx
  have hy := hU.centeredCap.inStrip hp
  exact ⟨⟨by linarith [hx.1], hy.1⟩, ⟨by linarith [hx.2], hy.2⟩⟩

end AmbidextrousSofa
