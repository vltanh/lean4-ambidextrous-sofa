import AmbidextrousSofa.Geometry.RigidMotion

/-!
# The original passage domain under a fixed rigid image

Both original paths are rebased by the same coordinate change. Equality
of their initial rotations is preserved even when their real angle lifts
are different. The inverse image identity also recovers the original
body from a classification in normalized coordinates.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem image_rigidMap_image (S : Set Plane) (θ φ : ℝ) (v w : Plane) :
    rigidMap θ v '' (rigidMap φ w '' S) =
      rigidMap (θ + φ) (rotate θ w + v) '' S := by
  rw [← image_comp]
  congr 1
  funext p
  simp only [Function.comp_apply, rigidMap, rotate_add_vector, rotate_rotate, add_assoc]

theorem image_inverse_rigidMap_image (S : Set Plane) (θ : ℝ) (v : Plane) :
    rigidMap (-θ) (-rotate (-θ) v) '' (rigidMap θ v '' S) = S := by
  rw [image_rigidMap_image]
  simp only [neg_add_cancel, add_neg_cancel, rigidMap, rotate_zero, add_zero, image_id']

theorem SameInitialOrientation.rebase {lower upper : RigidMotionPath}
    (h : SameInitialOrientation lower upper) (θ : ℝ) (v : Plane) :
    SameInitialOrientation (lower.rebase θ v) (upper.rebase θ v) := by
  change rotate (lower.angle 0 - θ) = rotate (upper.angle 0 - θ)
  funext p
  calc
    rotate (lower.angle 0 - θ) p = rotate (lower.angle 0) (rotate (-θ) p) := by
      rw [rotate_rotate, sub_eq_add_neg]
    _ = rotate (upper.angle 0) (rotate (-θ) p) := congrFun h _
    _ = rotate (upper.angle 0 - θ) p := by rw [rotate_rotate, sub_eq_add_neg]

theorem IsAmbidextrous.rigidImage {S : Set Plane} (hS : IsAmbidextrous S)
    (θ : ℝ) (v : Plane) : IsAmbidextrous (rigidMap θ v '' S) := by
  obtain ⟨lower, upper, horient, hlower, hupper⟩ := hS.passages
  exact ⟨hS.nonempty.image _, hS.isCompact.image (continuous_rigidMap θ v),
    hS.isConnected.image _ (continuous_rigidMap θ v).continuousOn,
    lower.rebase θ v, upper.rebase θ v, horient.rebase θ v,
    hlower.rebase θ v, hupper.rebase θ v⟩

theorem isAmbidextrous_rigidImage_iff (S : Set Plane) (θ : ℝ) (v : Plane) :
    IsAmbidextrous (rigidMap θ v '' S) ↔ IsAmbidextrous S := by
  constructor
  · intro h
    simpa only [image_inverse_rigidMap_image] using h.rigidImage (-θ) (-rotate (-θ) v)
  · intro h
    exact h.rigidImage θ v

end AmbidextrousSofa
