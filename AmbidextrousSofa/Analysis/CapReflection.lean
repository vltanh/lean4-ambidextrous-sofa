module

public import AmbidextrousSofa.Analysis.FiniteScore
public import AmbidextrousSofa.Analysis.GlobalCapMaximum

@[expose] public section

/-!
# Horizontal reflection of full cap scores

The actual map `(x,y) ↦ (-x,y)` exchanges the two upper normal families
and reverses the full quarter-angle parameter. It exchanges the charged
wings and preserves the whole full-angle cap score. The statement here is
for the full barrier; no proper terminal wall is discarded.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def horizontalReflection (p : Plane) : Plane := (-p.1, p.2)

def horizontalMirror (U : Set Plane) : Set Plane := horizontalReflection '' U

theorem horizontalReflection_involutive : Function.Involutive horizontalReflection := by
  intro p
  apply Prod.ext <;> simp [horizontalReflection]

theorem continuous_horizontalReflection : Continuous horizontalReflection := by
  unfold horizontalReflection
  fun_prop

theorem mem_horizontalMirror_iff (U : Set Plane) (p : Plane) :
    p ∈ horizontalMirror U ↔ horizontalReflection p ∈ U := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa only [horizontalReflection_involutive] using hq
  · intro hp
    exact ⟨horizontalReflection p, hp, horizontalReflection_involutive p⟩

theorem horizontalMirror_involutive (U : Set Plane) :
    horizontalMirror (horizontalMirror U) = U := by
  ext p
  simp only [mem_horizontalMirror_iff, horizontalReflection_involutive]

theorem horizontalReflection_combo (p q : Plane) (a b : ℝ) :
    horizontalReflection (a • p + b • q) =
      a • horizontalReflection p + b • horizontalReflection q := by
  apply Prod.ext <;> simp [horizontalReflection, smul_eq_mul] <;> ring

theorem IsDownwardCap.horizontalMirror {U : Set Plane} (hU : IsDownwardCap U) :
    IsDownwardCap (AmbidextrousSofa.horizontalMirror U) := by
  refine ⟨hU.nonempty.image _, hU.isCompact.image continuous_horizontalReflection, ?_, ?_, ?_⟩
  · rintro p ⟨p, hp, rfl⟩ q ⟨q, hq, rfl⟩ a b ha hb hab
    exact ⟨a • p + b • q, hU.convex hp hq ha hb hab, horizontalReflection_combo p q a b⟩
  · rintro p ⟨q, hq, rfl⟩
    exact hU.inStrip hq
  · intro p hp y hy0 hyp
    rw [mem_horizontalMirror_iff] at hp ⊢
    exact hU.downward (horizontalReflection p) hp y hy0 hyp

theorem verticalFiber_horizontalMirror (U : Set Plane) (x : ℝ) :
    verticalFiber (horizontalMirror U) x = verticalFiber U (-x) := by
  ext y
  exact mem_horizontalMirror_iff U (x, y)

theorem horizontalProjection_horizontalMirror_iff (U : Set Plane) (x : ℝ) :
    x ∈ horizontalProjection (horizontalMirror U) ↔ -x ∈ horizontalProjection U := by
  rw [← verticalFiber_nonempty_iff, ← verticalFiber_nonempty_iff,
    verticalFiber_horizontalMirror]

theorem capRoof_horizontalMirror (U : Set Plane) (x : ℝ) :
    capRoof (horizontalMirror U) x = capRoof U (-x) := by
  simp only [capRoof, horizontalProjection_horizontalMirror_iff, verticalFiber_horizontalMirror]

theorem support_horizontalMirror (U : Set Plane) (v : Plane) :
    support (horizontalMirror U) v = support U (horizontalReflection v) := by
  unfold support horizontalMirror
  rw [image_image]
  congr 1
  apply congrArg (fun f : Plane → ℝ => f '' U)
  funext p
  simp only [Function.comp_apply, coordDot, horizontalReflection]
  ring

theorem horizontalRight_horizontalMirror {U : Set Plane} (hU : IsDownwardCap U) :
    horizontalRight (horizontalMirror U) = -horizontalLeft U := by
  rw [← support_horizontal_right, support_horizontalMirror]
  exact support_horizontal_left hU.isCompact hU.nonempty

theorem horizontalLeft_horizontalMirror {U : Set Plane} (hU : IsDownwardCap U) :
    horizontalLeft (horizontalMirror U) = -horizontalRight U := by
  have h := horizontalRight_horizontalMirror hU.horizontalMirror
  rw [horizontalMirror_involutive] at h
  linarith

theorem capWidth_horizontalMirror {U : Set Plane} (hU : IsDownwardCap U) :
    capWidth (horizontalMirror U) = capWidth U := by
  unfold capWidth
  rw [horizontalRight_horizontalMirror hU, horizontalLeft_horizontalMirror hU]
  ring

theorem firstWall_horizontalMirror (U : Set Plane) (t x : ℝ) :
    firstWall (horizontalMirror U) t x = secondWall U (Real.pi / 2 - t) (-x) := by
  simp only [firstWall, secondWall, support_horizontalMirror, unitNormal,
    companionNormal, horizontalReflection, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub]
  congr 1
  ring

theorem secondWall_horizontalMirror (U : Set Plane) (t x : ℝ) :
    secondWall (horizontalMirror U) t x = firstWall U (Real.pi / 2 - t) (-x) := by
  simp only [firstWall, secondWall, support_horizontalMirror, unitNormal,
    companionNormal, horizontalReflection, neg_neg, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub]
  congr 1
  ring

theorem cornerWall_horizontalMirror (U : Set Plane) (t x : ℝ) :
    cornerWall (horizontalMirror U) t x = cornerWall U (Real.pi / 2 - t) (-x) := by
  rw [cornerWall, firstWall_horizontalMirror, secondWall_horizontalMirror, min_comm]
  rfl

theorem sweptNiche_horizontalMirror (U : Set Plane) (x : ℝ) :
    sweptNiche (horizontalMirror U) (Real.pi / 2) x =
      sweptNiche U (Real.pi / 2) (-x) := by
  have hvalues : sweptWallValues (horizontalMirror U) (Real.pi / 2) x =
      sweptWallValues U (Real.pi / 2) (-x) := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨Real.pi / 2 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩,
        (cornerWall_horizontalMirror U t x).symm⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨Real.pi / 2 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
      rw [cornerWall_horizontalMirror, show Real.pi / 2 - (Real.pi / 2 - t) = t by ring]
  simp only [sweptNiche, hvalues]

theorem partialBarrier_horizontalMirror {U : Set Plane} (hU : IsDownwardCap U) (x : ℝ) :
    partialBarrier (horizontalMirror U) (Real.pi / 2) x =
      partialBarrier U (Real.pi / 2) (-x) := by
  rw [hU.horizontalMirror.partialBarrier_pi_div_two, hU.partialBarrier_pi_div_two,
    sweptNiche_horizontalMirror]

theorem intervalSpatialScore_reflect (roof niche : ℝ → ℝ) (l r : ℝ) :
    intervalSpatialScore (fun x => roof (-x)) (fun x => niche (-x)) (-r) (-l) =
      intervalSpatialScore roof niche l r := by
  unfold intervalSpatialScore
  rw [intervalIntegral.integral_comp_neg, intervalIntegral.integral_comp_neg,
    intervalIntegral.integral_comp_neg]
  simp only [neg_neg]
  rw [show -(-r + (-l - -r) / 4) = r - (r - l) / 4 by ring,
    show -(-l - (-l - -r) / 4) = l + (r - l) / 4 by ring]
  ring

theorem capScore_horizontalMirror {U : Set Plane} (hU : IsDownwardCap U) :
    capScore (horizontalMirror U) (Real.pi / 2) = capScore U (Real.pi / 2) := by
  rw [hU.horizontalMirror.capScore_eq_intervalSpatialScore, hU.capScore_eq_intervalSpatialScore,
    horizontalLeft_horizontalMirror hU, horizontalRight_horizontalMirror hU]
  have hroof : capRoof (horizontalMirror U) = fun x => capRoof U (-x) :=
    funext (capRoof_horizontalMirror U)
  have hniche : partialBarrier (horizontalMirror U) (Real.pi / 2) =
      fun x => partialBarrier U (Real.pi / 2) (-x) := funext (partialBarrier_horizontalMirror hU)
  rw [hroof, hniche, intervalSpatialScore_reflect]

theorem IsFullCapMaximizer.horizontalMirror {U : Set Plane} (hU : IsFullCapMaximizer U) :
    IsFullCapMaximizer (AmbidextrousSofa.horizontalMirror U) :=
  hU.of_score_le hU.isCap.horizontalMirror (capScore_horizontalMirror hU.isCap).ge

theorem capHeight_horizontalMirror (U : Set Plane) :
    capHeight (horizontalMirror U) = capHeight U := by
  rw [capHeight, support_horizontalMirror]
  simp only [horizontalReflection, neg_zero]
  rfl

end AmbidextrousSofa
