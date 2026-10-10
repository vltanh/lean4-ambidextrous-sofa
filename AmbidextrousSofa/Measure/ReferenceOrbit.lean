import AmbidextrousSofa.Geometry.RigidImage
import AmbidextrousSofa.Measure.ActualReferenceRecovery

/-!
# Recovering the reference rigid orbit from normalized equality

A normalized horizontal translate is inverted explicitly. The result is
an equality of the original sets under a rotation and a translation.
Every such image of the displayed reference retains both actual passages
and has the same exact area.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem eq_rigidImage_of_normalized_horizontalTranslate
    {S T : Set Plane} {θ b : ℝ} {v : Plane}
    (h : rigidMap θ v '' S = horizontalTranslate T b) :
    S = rigidMap (-θ) (rotate (-θ) ((b, 0) - v)) '' T := by
  have hinv := congrArg
    (fun E : Set Plane => rigidMap (-θ) (-rotate (-θ) v) '' E) h
  rw [image_inverse_rigidMap_image] at hinv
  have htranslate : horizontalTranslate T b = rigidMap 0 (b, 0) '' T := by
    simp only [horizontalTranslate, rigidMap, rotate_zero]
  rw [htranslate, image_rigidMap_image] at hinv
  have hshift : rotate (-θ) (b, 0) + -rotate (-θ) v =
      rotate (-θ) ((b, 0) - v) := by
    rw [rotate_sub_vector]
    abel
  simpa only [add_zero, hshift] using hinv

theorem Reference.isAmbidextrous_rigidImage_referenceSofa (θ : ℝ) (v : Plane) :
    IsAmbidextrous (rigidMap θ v '' Reference.referenceSofa) :=
  Reference.isAmbidextrous_referenceSofa.rigidImage θ v

theorem Reference.volumeReal_rigidImage_referenceSofa (θ : ℝ) (v : Plane) :
    volume.real (rigidMap θ v '' Reference.referenceSofa) = M := by
  rw [volumeReal_image_rigidMap, Reference.volumeReal_referenceSofa]

end AmbidextrousSofa
