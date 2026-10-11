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

theorem horizontalReflection_involutive : Function.Involutive horizontalReflection :=
  fun _ => by simp [horizontalReflection]

theorem mem_horizontalMirror_iff (U : Set Plane) (p : Plane) :
    p ∈ horizontalMirror U ↔ horizontalReflection p ∈ U :=
  mem_image_iff_of_inverse horizontalReflection_involutive.leftInverse
    horizontalReflection_involutive.rightInverse

theorem horizontalMirror_involutive (U : Set Plane) :
    horizontalMirror (horizontalMirror U) = U := by
  ext p
  simp only [mem_horizontalMirror_iff, horizontalReflection_involutive p]

theorem IsDownwardCap.horizontalMirror {U : Set Plane} (hU : IsDownwardCap U) :
    IsDownwardCap (AmbidextrousSofa.horizontalMirror U) := by
  refine ⟨hU.nonempty.image _, hU.isCompact.image (by unfold horizontalReflection; fun_prop),
    ?_, ?_, fun p hp y hy0 hyp => (mem_horizontalMirror_iff _ _).2
      (hU.downward _ ((mem_horizontalMirror_iff _ _).1 hp) y hy0 hyp)⟩
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ a b ha hb hab
    exact ⟨a • p + b • q, hU.convex hp hq ha hb hab,
      by ext <;> simp [horizontalReflection, add_comm]⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact (hU.inStrip hq : q ∈ unitStrip)

theorem capRoof_horizontalMirror (U : Set Plane) (x : ℝ) :
    capRoof (horizontalMirror U) x = capRoof U (-x) := by
  have h : verticalFiber (horizontalMirror U) x = verticalFiber U (-x) :=
    Set.ext fun y => mem_horizontalMirror_iff U (x, y)
  rw [capRoof, capRoof, ← verticalFiber_nonempty_iff, ← verticalFiber_nonempty_iff, h]

theorem support_horizontalMirror (U : Set Plane) (v : Plane) :
    support (horizontalMirror U) v = support U (horizontalReflection v) := by
  simp [support, horizontalMirror, image_image, coordDot, horizontalReflection]

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
  rw [capWidth, capWidth, horizontalRight_horizontalMirror hU, horizontalLeft_horizontalMirror hU]
  ring

theorem cornerWall_horizontalMirror (U : Set Plane) (t x : ℝ) :
    cornerWall (horizontalMirror U) t x = cornerWall U (Real.pi / 2 - t) (-x) := by
  simp only [cornerWall, firstWall, secondWall, support_horizontalMirror, unitNormal,
    companionNormal, horizontalReflection, neg_neg, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub]
  rw [min_comm]
  congr 1 <;> ring

theorem sweptNiche_horizontalMirror (U : Set Plane) (x : ℝ) :
    sweptNiche (horizontalMirror U) (Real.pi / 2) x =
      sweptNiche U (Real.pi / 2) (-x) := by
  simp only [sweptNiche, sweptWallValues, cornerWall_horizontalMirror]
  rw [← image_image (fun θ => cornerWall U θ (-x)) (fun θ => Real.pi / 2 - θ),
    image_const_sub_Ioo]
  simp

theorem intervalSpatialScore_reflect (roof niche : ℝ → ℝ) (l r : ℝ) :
    intervalSpatialScore (fun x => roof (-x)) (fun x => niche (-x)) (-r) (-l) =
      intervalSpatialScore roof niche l r := by
  simp only [intervalSpatialScore, intervalIntegral.integral_comp_neg, neg_neg]
  ring_nf

theorem capScore_horizontalMirror {U : Set Plane} (hU : IsDownwardCap U) :
    capScore (horizontalMirror U) (Real.pi / 2) = capScore U (Real.pi / 2) := by
  rw [hU.horizontalMirror.capScore_eq_intervalSpatialScore, hU.capScore_eq_intervalSpatialScore,
    horizontalLeft_horizontalMirror hU, horizontalRight_horizontalMirror hU,
    ← intervalSpatialScore_reflect (capRoof U)]
  congr 1 <;> funext x
  · exact capRoof_horizontalMirror U x
  · rw [hU.horizontalMirror.partialBarrier_pi_div_two, hU.partialBarrier_pi_div_two,
      sweptNiche_horizontalMirror]

theorem IsFullCapMaximizer.horizontalMirror {U : Set Plane} (hU : IsFullCapMaximizer U) :
    IsFullCapMaximizer (AmbidextrousSofa.horizontalMirror U) :=
  hU.of_score_le hU.isCap.horizontalMirror (capScore_horizontalMirror hU.isCap).ge

theorem capHeight_horizontalMirror (U : Set Plane) :
    capHeight (horizontalMirror U) = capHeight U := by
  simp [capHeight, support_horizontalMirror, horizontalReflection]

end AmbidextrousSofa
