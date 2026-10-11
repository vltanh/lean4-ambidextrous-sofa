module

public import AmbidextrousSofa.Geometry.RigidImage
public import AmbidextrousSofa.Measure.ActualReferenceRecovery

@[expose] public section

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
  rw [← image_inverse_rigidMap_image S θ v, h, horizontalTranslate, image_image]
  exact image_congr fun p _ => by simp only [rigidMap, rotate_add_vector, rotate_sub_vector]; abel

theorem Reference.isAmbidextrous_rigidImage_referenceSofa (θ : ℝ) (v : Plane) :
    IsAmbidextrous (rigidMap θ v '' Reference.referenceSofa) :=
  Reference.isAmbidextrous_referenceSofa.rigidImage θ v

theorem Reference.volumeReal_rigidImage_referenceSofa (θ : ℝ) (v : Plane) :
    volume.real (rigidMap θ v '' Reference.referenceSofa) = M :=
  (volumeReal_image_rigidMap θ v _).trans Reference.volumeReal_referenceSofa

end AmbidextrousSofa
