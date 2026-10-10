module

public import AmbidextrousSofa.Geometry.Plane

@[expose] public section

/-!
# The original two-passage domain

Paths use continuous real angle lifts and continuous translations on `[0, 1]`.
Their two translations and their terminal rotations are independent. There is
no monotonicity, contact-chart, symmetry, or full-turn assumption.

Common incoming orientation means equality of the initial rotation maps, so
angle lifts differing by a full period are permitted. Relating this coordinate
presentation to arbitrary continuous paths in the group of proper Euclidean
isometries is an explicit later obligation in the roadmap.
-/

noncomputable section

namespace AmbidextrousSofa

/-- Time is only constrained on this compact interval. -/
def motionInterval : Set ℝ := Set.Icc 0 1

/-- A continuous path of coordinate rigid placements. -/
structure RigidMotionPath where
  angle : ℝ → ℝ
  shift : ℝ → Plane
  continuous_angle : ContinuousOn angle motionInterval
  continuous_shift : ContinuousOn shift motionInterval

def RigidMotionPath.placement (path : RigidMotionPath) (t : ℝ) : Plane → Plane :=
  rigidMap (path.angle t) (path.shift t)

/-- A whole-body corridor passage, with incoming and outgoing endpoint conditions. -/
structure Passage (S hall incoming outgoing : Set Plane) (path : RigidMotionPath) : Prop where
  inside : ∀ t ∈ motionInterval, path.placement t '' S ⊆ hall
  start : path.placement 0 '' S ⊆ incoming
  finish : path.placement 1 '' S ⊆ outgoing

/-- Equality of rotations, without requiring identical real angle lifts. -/
def SameInitialOrientation (lower upper : RigidMotionPath) : Prop :=
  rotate (lower.angle 0) = rotate (upper.angle 0)

/-- The original compact connected two-motion domain in coordinate form. -/
structure IsAmbidextrous (S : Set Plane) : Prop where
  nonempty : S.Nonempty
  isCompact : IsCompact S
  isConnected : IsConnected S
  passages : ∃ lower upper : RigidMotionPath,
    SameInitialOrientation lower upper ∧
      Passage S lowerHall incomingArm lowerOutgoingArm lower ∧
      Passage S upperHall incomingArm upperOutgoingArm upper

/-- Restricting the physical body preserves a fixed passage. -/
theorem Passage.mono {S T hall incoming outgoing : Set Plane} {path : RigidMotionPath}
    (h : Passage T hall incoming outgoing path) (hST : S ⊆ T) :
    Passage S hall incoming outgoing path := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rintro _ ⟨p, hp, rfl⟩
    exact h.inside t ht ⟨p, hST hp, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact h.start ⟨p, hST hp, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact h.finish ⟨p, hST hp, rfl⟩

/-- A nonempty compact connected subset inherits the same two passages. -/
theorem IsAmbidextrous.of_subset {S T : Set Plane} (hT : IsAmbidextrous T)
    (hST : S ⊆ T) (hne : S.Nonempty) (hc : IsCompact S) (hconn : IsConnected S) :
    IsAmbidextrous S := by
  obtain ⟨lower, upper, horient, hlower, hupper⟩ := hT.passages
  exact ⟨hne, hc, hconn, lower, upper, horient, hlower.mono hST, hupper.mono hST⟩

end AmbidextrousSofa
