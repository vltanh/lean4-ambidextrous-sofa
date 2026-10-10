import AmbidextrousSofa.Geometry.RigidMotion
import AmbidextrousSofa.Geometry.Reflection

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

theorem measurePreserving_rotate (θ : ℝ) :
    MeasurePreserving (rotate θ) (volume : Measure Plane) volume := by
  refine ⟨(continuous_rotate θ).measurable, ?_⟩
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure Plane) (f := rotationLinearMap θ) (by simp)
  simpa only [coe_rotationLinearMap, det_rotationLinearMap, inv_one, abs_one,
    ENNReal.ofReal_one, one_smul] using h

theorem volume_image_rotate (θ : ℝ) (S : Set Plane) :
    volume (rotate θ '' S) = volume S := by
  have h := Measure.addHaar_image_linearMap (volume : Measure Plane)
    (rotationLinearMap θ) S
  simpa only [coe_rotationLinearMap, det_rotationLinearMap, abs_one,
    ENNReal.ofReal_one, one_mul] using h

theorem volume_image_translate (v : Plane) (S : Set Plane) :
    volume ((fun p => p + v) '' S) = volume S := by
  rw [image_add_right, measure_preimage_add_right]

theorem measurePreserving_rigidMap (θ : ℝ) (v : Plane) :
    MeasurePreserving (rigidMap θ v) (volume : Measure Plane) volume :=
  (measurePreserving_add_right volume v).comp (measurePreserving_rotate θ)

theorem volume_image_rigidMap (θ : ℝ) (v : Plane) (S : Set Plane) :
    volume (rigidMap θ v '' S) = volume S := by
  change volume (((fun p => p + v) ∘ rotate θ) '' S) = volume S
  rw [Set.image_comp, volume_image_translate, volume_image_rotate]

theorem volumeReal_image_rigidMap (θ : ℝ) (v : Plane) (S : Set Plane) :
    volume.real (rigidMap θ v '' S) = volume.real S := by
  simp only [Measure.real, volume_image_rigidMap]

def verticalFlipLinearMap : Plane →ₗ[ℝ] Plane :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![1, 0; 0, -1]

theorem verticalFlipLinearMap_apply (p : Plane) :
    verticalFlipLinearMap p = (p.1, -p.2) := by
  simp [verticalFlipLinearMap, Matrix.toLin_finTwoProd_apply]

theorem det_verticalFlipLinearMap :
    LinearMap.det verticalFlipLinearMap = -1 := by
  simp [verticalFlipLinearMap, LinearMap.det_toLin]

theorem volume_image_reflect (S : Set Plane) : volume (reflect '' S) = volume S := by
  have hflip : volume (verticalFlipLinearMap '' S) = volume S := by
    simpa only [det_verticalFlipLinearMap, abs_neg, abs_one, ENNReal.ofReal_one,
      one_mul] using
      Measure.addHaar_image_linearMap (volume : Measure Plane) verticalFlipLinearMap S
  have hreflect : reflect = (fun p : Plane => p + (0, 1)) ∘ verticalFlipLinearMap := by
    funext p
    rw [Function.comp_apply, verticalFlipLinearMap_apply]
    apply Prod.ext <;> simp [reflect] <;> ring
  rw [hreflect, Set.image_comp, volume_image_translate, hflip]

theorem volumeReal_image_reflect (S : Set Plane) :
    volume.real (reflect '' S) = volume.real S := by
  simp only [Measure.real, volume_image_reflect]

/-- Normalize the original motion domain without changing its actual area.
The chosen transform is one incoming placement of the lower passage. -/
theorem IsAmbidextrous.exists_normalized {S : Set Plane} (hS : IsAmbidextrous S) :
    ∃ (θ : ℝ) (v : Plane) (lower upper : RigidMotionPath),
      let T := rigidMap θ v '' S
      IsAmbidextrous T ∧ T ⊆ unitStrip ∧ volume.real T = volume.real S ∧
        lower.angle 0 = 0 ∧ upper.angle 0 = 0 ∧
        Passage T lowerHall incomingArm lowerOutgoingArm lower ∧
        Passage T upperHall incomingArm upperOutgoingArm upper := by
  obtain ⟨θ, v, lower, upper, hT, hstrip, hl0, hu0, hl, hu⟩ :=
    hS.exists_normalized_passages
  exact ⟨θ, v, lower, upper, hT, hstrip, volumeReal_image_rigidMap θ v S,
    hl0, hu0, hl, hu⟩

end AmbidextrousSofa
