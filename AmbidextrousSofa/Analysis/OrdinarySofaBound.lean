import AmbidextrousSofa.Imported.Main
import AmbidextrousSofa.Measure.RigidInvariance

/-!
# The retained ordinary one-turn bound

The auxiliary tilted and terminal exclusions use the rational ordinary
moving-sofa bound `22199 / 10000`. Its complete mathematical source
dependency is adapted under `Imported`, including the existence of the
Gerver parameters and their rational area enclosure. No ordinary-optimality
axiom or conditional area certificate is introduced here.

The bridge below identifies the actual coordinate corridors, rotations,
area and continuous real-angle motions. An arbitrary initial orientation
is removed by an actual rigid change of body coordinates, preserving area.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem imported_rot_eq_rotate (θ : ℝ) (p : Plane) : Imported.rot θ p = rotate θ p := rfl

theorem imported_area_eq_volumeReal (S : Set Plane) : Imported.area S = volume.real S := rfl

theorem imported_horizSide_eq_incomingArm : Imported.horizSide = incomingArm := rfl

theorem imported_vertSide_eq_lowerOutgoingArm : Imported.vertSide = lowerOutgoingArm := rfl

theorem imported_hallway_eq_lowerHall : Imported.hallway = lowerHall := rfl

/-- Both existential Gerver parameter conditions are discharged by their
proved source existence theorem. The resulting bound quantifies over the
entire imported ordinary moving-sofa domain. -/
theorem imported_movingSofa_area_le {S : Set Plane} (hS : Imported.IsMovingSofa S) :
    volume.real S ≤ (22199 : ℝ) / 10000 := by
  obtain ⟨P, hP, hbox⟩ := Imported.definition8_1_2_exists
  have hupper : Imported.area (Imported.gerverSofa P) ≤ (22199 : ℝ) / 10000 := by
    have h := (Imported.gerverSofa_area_mem hP hbox).2
    norm_num at h ⊢
    exact h
  by_cases h22 : (2.2 : ℝ) ≤ Imported.area S
  · exact (Imported.gm_area_le hP hbox hS h22).trans hupper
  · change Imported.area S ≤ (22199 : ℝ) / 10000
    linarith

/-- A normalized actual lower passage is exactly a movement in the
imported ordinary definition, with its own unrestricted terminal angle. -/
theorem Passage.imported_isMovement {S : Set Plane} {path : RigidMotionPath}
    (h : Passage S lowerHall incomingArm lowerOutgoingArm path)
    (hzero : path.angle 0 = 0) :
    Imported.IsMovement S (-path.angle 1) path.angle path.shift := by
  refine ⟨path.continuous_angle, path.continuous_shift, hzero, ?_, ?_, ?_, ?_⟩
  · simp only [neg_neg]
  · intro p hp
    change path.placement 0 p ∈ incomingArm
    exact h.start ⟨p, hp, rfl⟩
  · intro t ht p hp
    change path.placement t p ∈ lowerHall
    exact h.inside t ht ⟨p, hp, rfl⟩
  · intro p hp
    change path.placement 1 p ∈ lowerOutgoingArm
    exact h.finish ⟨p, hp, rfl⟩

theorem Passage.imported_isMovingSofa_of_angle_zero {S : Set Plane}
    {path : RigidMotionPath}
    (h : Passage S lowerHall incomingArm lowerOutgoingArm path)
    (hcompact : IsCompact S) (hconnected : IsConnected S) (hzero : path.angle 0 = 0) :
    Imported.IsMovingSofa S :=
  ⟨-path.angle 1, hcompact.isClosed, hconnected,
    path.angle, path.shift, h.imported_isMovement hzero⟩

/-- The rational ordinary bound applies to a genuine continuous passage
without imposing an initial-angle normalization on its original body. -/
theorem volumeReal_le_ordinaryBound_of_lowerPassage {S : Set Plane}
    {path : RigidMotionPath} (hcompact : IsCompact S) (hconnected : IsConnected S)
    (hpassage : Passage S lowerHall incomingArm lowerOutgoingArm path) :
    volume.real S ≤ (22199 : ℝ) / 10000 := by
  let T := rigidMap (path.angle 0) 0 '' S
  have hTcompact : IsCompact T := hcompact.image (continuous_rigidMap _ _)
  have hTconnected : IsConnected T :=
    hconnected.image _ (continuous_rigidMap _ _).continuousOn
  have hTpassage : Passage T lowerHall incomingArm lowerOutgoingArm
      (path.rebase (path.angle 0) 0) := hpassage.rebase _ _
  have hT := hTpassage.imported_isMovingSofa_of_angle_zero hTcompact hTconnected
    (path.rebase_angle_zero 0)
  have hbound := imported_movingSofa_area_le hT
  have harea : volume.real T = volume.real S := volumeReal_image_rigidMap _ _ S
  rwa [harea] at hbound

theorem IsAmbidextrous.volumeReal_le_ordinaryBound {S : Set Plane}
    (hS : IsAmbidextrous S) : volume.real S ≤ (22199 : ℝ) / 10000 := by
  obtain ⟨lower, upper, horient, hlower, hupper⟩ := hS.passages
  exact volumeReal_le_ordinaryBound_of_lowerPassage hS.isCompact hS.isConnected hlower

end AmbidextrousSofa
