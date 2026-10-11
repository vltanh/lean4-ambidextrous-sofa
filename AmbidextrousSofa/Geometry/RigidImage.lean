module

public import AmbidextrousSofa.Geometry.RigidMotion

@[expose] public section

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
    rigidMap θ v '' (rigidMap φ w '' S) = rigidMap (θ + φ) (rotate θ w + v) '' S := by
  simp only [image_image, rigidMap, rotate_add_vector, rotate_rotate, add_assoc]; rfl

theorem image_inverse_rigidMap_image (S : Set Plane) (θ : ℝ) (v : Plane) :
    rigidMap (-θ) (-rotate (-θ) v) '' (rigidMap θ v '' S) = S := by
  simp [image_rigidMap_image]

theorem SameInitialOrientation.rebase {lower upper : RigidMotionPath}
    (h : SameInitialOrientation lower upper) (θ : ℝ) (v : Plane) :
    SameInitialOrientation (lower.rebase θ v) (upper.rebase θ v) := funext fun p => by
  simpa only [RigidMotionPath.rebase, rotate_rotate, ← sub_eq_add_neg] using
    congrFun h (rotate (-θ) p)

theorem IsAmbidextrous.rigidImage {S : Set Plane} (hS : IsAmbidextrous S)
    (θ : ℝ) (v : Plane) : IsAmbidextrous (rigidMap θ v '' S) := by
  obtain ⟨lower, upper, horient, hlower, hupper⟩ := hS.passages
  exact ⟨hS.nonempty.image _, hS.isCompact.image (continuous_rigidMap θ v),
    hS.isConnected.image _ (continuous_rigidMap θ v).continuousOn,
    lower.rebase θ v, upper.rebase θ v, horient.rebase θ v,
    hlower.rebase θ v, hupper.rebase θ v⟩

end AmbidextrousSofa
