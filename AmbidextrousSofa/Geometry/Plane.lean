module

public import Mathlib

@[expose] public section

/-!
# Coordinate plane and the two unit corridors

The plane is represented by a pair of real coordinates, with its product
topology and product Lebesgue measure. The product norm is not the Euclidean
norm. Rotations are therefore defined by their coordinate formula, and the
Euclidean squared-length identity is proved explicitly below.

The lower corridor is the union of the incoming horizontal arm and the
downward outgoing arm. The upper corridor is its reflection in `y = 1 / 2`.
-/

noncomputable section

namespace AmbidextrousSofa

abbrev Plane := ℝ × ℝ

/-- Counterclockwise rotation in Euclidean coordinates. -/
def rotate (θ : ℝ) (p : Plane) : Plane :=
  (Real.cos θ * p.1 - Real.sin θ * p.2,
    Real.sin θ * p.1 + Real.cos θ * p.2)

/-- A proper rigid placement: rotate, then translate. -/
def rigidMap (θ : ℝ) (v p : Plane) : Plane := rotate θ p + v

/-- Euclidean squared length, independent of the product norm instance. -/
def squaredLength (p : Plane) : ℝ := p.1 ^ 2 + p.2 ^ 2

@[simp]
theorem rotate_zero (p : Plane) : rotate 0 p = p := by
  simp [rotate]

@[simp]
theorem rigidMap_zero_zero (p : Plane) : rigidMap 0 0 p = p := by
  simp [rigidMap]

/-- The coordinate rotation preserves Euclidean squared length. -/
theorem squaredLength_rotate (θ : ℝ) (p : Plane) :
    squaredLength (rotate θ p) = squaredLength p := by
  calc
    squaredLength (rotate θ p) =
        (Real.cos θ ^ 2 + Real.sin θ ^ 2) * (p.1 ^ 2 + p.2 ^ 2) := by
      unfold squaredLength rotate
      ring
    _ = squaredLength p := by
      simp only [Real.cos_sq_add_sin_sq, one_mul, squaredLength]

/-- Reflection in the center line of the incoming strip. -/
def reflect (p : Plane) : Plane := (p.1, 1 - p.2)

@[simp]
theorem reflect_reflect (p : Plane) : reflect (reflect p) = p := by
  apply Prod.ext
  · rfl
  · change 1 - (1 - p.2) = p.2
    ring

def unitStrip : Set Plane := {p | 0 ≤ p.2 ∧ p.2 ≤ 1}

def incomingArm : Set Plane := {p | p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}

def lowerOutgoingArm : Set Plane := {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 ≤ 1}

def upperOutgoingArm : Set Plane := {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2}

def lowerHall : Set Plane := incomingArm ∪ lowerOutgoingArm

def upperHall : Set Plane := incomingArm ∪ upperOutgoingArm

@[simp]
theorem reflect_mem_unitStrip (p : Plane) :
    reflect p ∈ unitStrip ↔ p ∈ unitStrip := by
  change (0 ≤ 1 - p.2 ∧ 1 - p.2 ≤ 1) ↔ (0 ≤ p.2 ∧ p.2 ≤ 1)
  constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> linarith

@[simp]
theorem reflect_mem_incomingArm (p : Plane) :
    reflect p ∈ incomingArm ↔ p ∈ incomingArm := by
  change (p.1 ≤ 1 ∧ 0 ≤ 1 - p.2 ∧ 1 - p.2 ≤ 1) ↔
    (p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1)
  constructor
  · rintro ⟨hx, h0, h1⟩
    exact ⟨hx, by linarith, by linarith⟩
  · rintro ⟨hx, h0, h1⟩
    exact ⟨hx, by linarith, by linarith⟩

@[simp]
theorem reflect_mem_lowerOutgoingArm (p : Plane) :
    reflect p ∈ lowerOutgoingArm ↔ p ∈ upperOutgoingArm := by
  change (0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 1 - p.2 ≤ 1) ↔
    (0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2)
  constructor
  · rintro ⟨hx0, hx1, hy⟩
    exact ⟨hx0, hx1, by linarith⟩
  · rintro ⟨hx0, hx1, hy⟩
    exact ⟨hx0, hx1, by linarith⟩

/-- The upper hall really is the reflection of the lower hall. -/
theorem reflect_mem_lowerHall (p : Plane) :
    reflect p ∈ lowerHall ↔ p ∈ upperHall := by
  change (reflect p ∈ incomingArm ∨ reflect p ∈ lowerOutgoingArm) ↔
    (p ∈ incomingArm ∨ p ∈ upperOutgoingArm)
  rw [reflect_mem_incomingArm, reflect_mem_lowerOutgoingArm]

theorem upperHall_eq_preimage_lowerHall : upperHall = reflect ⁻¹' lowerHall := by
  ext p
  exact (reflect_mem_lowerHall p).symm

end AmbidextrousSofa
