module

public import MovingSofaOptimality.Main
public import AmbidextrousSofa.Measure.RigidInvariance

@[expose] public section

/-!
# The retained ordinary one-turn bound

The auxiliary tilted and terminal exclusions use the rational ordinary
moving-sofa bound `2.2199`. Its complete mathematical source
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

/-- Both existential Gerver parameter conditions are discharged by their
proved source existence theorem. The resulting bound quantifies over the
entire imported ordinary moving-sofa domain. -/
theorem imported_movingSofa_area_le {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    volume.real S ≤ (2.2199 : ℝ) := by
  obtain ⟨P, hP, hbox⟩ := MovingSofaOptimality.definition8_1_2_exists
  have h := (MovingSofaOptimality.gerverSofa_area_mem hP hbox).2
  change MovingSofaOptimality.area S ≤ _
  by_cases h22 : (2.2 : ℝ) ≤ MovingSofaOptimality.area S
  · linarith [MovingSofaOptimality.gm_area_le hP hbox hS h22]
  · linarith

/-- A normalized actual lower passage is exactly a movement in the
imported ordinary definition, with its own unrestricted terminal angle. -/
theorem Passage.imported_isMovement {S : Set Plane} {path : RigidMotionPath}
    (h : Passage S lowerHall incomingArm lowerOutgoingArm path)
    (hzero : path.angle 0 = 0) :
    MovingSofaOptimality.IsMovement S (-path.angle 1) path.angle path.shift :=
  ⟨path.continuous_angle, path.continuous_shift, hzero, (neg_neg _).symm,
    fun p hp => h.start ⟨p, hp, rfl⟩, fun t ht p hp => h.inside t ht ⟨p, hp, rfl⟩,
    fun p hp => h.finish ⟨p, hp, rfl⟩⟩

/-- The rational ordinary bound applies to a genuine continuous passage
without imposing an initial-angle normalization on its original body. -/
theorem volumeReal_le_ordinaryBound_of_lowerPassage {S : Set Plane}
    {path : RigidMotionPath} (hcompact : IsCompact S) (hconnected : IsConnected S)
    (hpassage : Passage S lowerHall incomingArm lowerOutgoingArm path) :
    volume.real S ≤ (2.2199 : ℝ) := by
  rw [← volumeReal_image_rigidMap (path.angle 0) 0 S]
  exact imported_movingSofa_area_le ⟨_, (hcompact.image (continuous_rigidMap _ _)).isClosed,
    hconnected.image _ (continuous_rigidMap _ _).continuousOn, _, _,
    (hpassage.rebase _ 0).imported_isMovement (path.rebase_angle_zero 0)⟩

end AmbidextrousSofa
