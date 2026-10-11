module

public import AmbidextrousSofa.Geometry.RigidMotion
public import AmbidextrousSofa.Geometry.Reflection

@[expose] public section

/-!
# Product Lebesgue area under rigid changes of coordinates

Rotation invariance follows from the determinant-one linear-map formula for
Haar measure. Translation and reflection are treated as actual coordinate
maps. These statements hold for all sets, and in particular do not require a
new measurability hypothesis on the original physical sofa.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem volume_image_translate (v : Plane) (S : Set Plane) :
    volume ((fun p => p + v) '' S) = volume S := by
  rw [image_add_right, measure_preimage_add_right]

theorem volumeReal_image_rigidMap (θ : ℝ) (v : Plane) (S : Set Plane) :
    volume.real (rigidMap θ v '' S) = volume.real S := by
  change volume.real (((· + v) ∘ rotate θ) '' S) = _
  rw [image_comp, Measure.real, volume_image_translate, ← coe_rotationLinearMap,
    Measure.addHaar_image_linearMap]
  simp [Measure.real]

theorem volumeReal_image_reflect (S : Set Plane) :
    volume.real (reflect '' S) = volume.real S := by
  let F : Plane →ₗ[ℝ] Plane :=
    Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ) !![1, 0; 0, -1]
  have hF : reflect = (· + (0, 1)) ∘ F := by
    funext p
    simp [F, reflect, Matrix.toLin_finTwoProd_apply, sub_eq_neg_add]
  rw [hF, image_comp, Measure.real, volume_image_translate, Measure.addHaar_image_linearMap]
  simp [F, LinearMap.det_toLin, Measure.real]

/-- Normalize the original motion domain without changing its actual area.
The chosen transform is one incoming placement of the lower passage. -/
theorem IsAmbidextrous.exists_normalized {S : Set Plane} (hS : IsAmbidextrous S) :
    ∃ (θ : ℝ) (v : Plane) (lower upper : RigidMotionPath),
      let T := rigidMap θ v '' S
      IsAmbidextrous T ∧ T ⊆ unitStrip ∧ volume.real T = volume.real S ∧
        lower.angle 0 = 0 ∧ upper.angle 0 = 0 ∧
        Passage T lowerHall incomingArm lowerOutgoingArm lower ∧
        Passage T upperHall incomingArm upperOutgoingArm upper := by
  obtain ⟨θ, v, lower, upper, hT, hstrip, hl0, hu0, hl, hu⟩ := hS.exists_normalized_passages
  exact ⟨θ, v, lower, upper, hT, hstrip, volumeReal_image_rigidMap θ v S, hl0, hu0, hl, hu⟩

end AmbidextrousSofa
