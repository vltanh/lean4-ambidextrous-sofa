module

public import AmbidextrousSofa.Geometry.Support
public import AmbidextrousSofa.Geometry.HullCompact
public import AmbidextrousSofa.Geometry.Motions

@[expose] public section

/-!
# Actual hallway constraints and support tightening

The inner corner is excluded by a disjunction, while both outer walls must
hold. Tightening the two support offsets preserves every original retained
point; it does not assert that the entire convex hull fits the hallway.
The actual outgoing strip is tightened separately and remains a whole-body
condition. These are the pointwise geometric steps GA.1--GA.2 and GA.5.
-/

noncomputable section

namespace AmbidextrousSofa

def companionNormal (θ : ℝ) : Plane := (-Real.sin θ, Real.cos θ)

theorem continuous_companionNormal : Continuous companionNormal := by
  unfold companionNormal; fun_prop

theorem companionNormal_eq_unitNormal (θ : ℝ) :
    companionNormal θ = unitNormal (θ + Real.pi / 2) := by
  apply Prod.ext <;> simp [companionNormal, unitNormal, Real.sin_add, Real.cos_add]

/-- The two quarter families of directions cover the upper half-plane. -/
theorem exists_upper_polar {v : Plane} (hv : 0 ≤ v.2) :
    ∃ r : ℝ, 0 ≤ r ∧ ∃ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      v = r • unitNormal t ∨ v = r • companionNormal t := by
  have hz : v = ‖(⟨v.1, v.2⟩ : ℂ)‖ • unitNormal (Complex.arg ⟨v.1, v.2⟩) := by
    ext <;> simp [unitNormal, Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg]
  have h0 : 0 ≤ Complex.arg ⟨v.1, v.2⟩ := Complex.arg_nonneg_iff.2 hv
  have hπ := Complex.arg_le_pi ⟨v.1, v.2⟩
  refine ⟨_, norm_nonneg (⟨v.1, v.2⟩ : ℂ), ?_⟩
  rcases le_total (Complex.arg ⟨v.1, v.2⟩) (Real.pi / 2) with h | h
  · exact ⟨_, ⟨h0, h⟩, Or.inl hz⟩
  · refine ⟨Complex.arg ⟨v.1, v.2⟩ - Real.pi / 2, ⟨by linarith, by linarith⟩,
      Or.inr ?_⟩
    rwa [companionNormal_eq_unitNormal, sub_add_cancel]

/-- A two-wall L-hallway in a prescribed frame. -/
def frameHall (u v : Plane) (a b : ℝ) : Set Plane :=
  {p | coordDot p u ≤ a + 1 ∧ coordDot p v ≤ b + 1 ∧
    (a ≤ coordDot p u ∨ b ≤ coordDot p v)}

/-- The frame hallway with both outer walls at the actual support values. -/
def canonicalHall (K : Set Plane) (u v : Plane) : Set Plane :=
  frameHall u v (support K u - 1) (support K v - 1)

theorem mem_canonicalHall (K : Set Plane) (u v p : Plane) :
    p ∈ canonicalHall K u v ↔
      coordDot p u ≤ support K u ∧ coordDot p v ≤ support K v ∧
        (support K u - 1 ≤ coordDot p u ∨ support K v - 1 ≤ coordDot p v) := by
  simp only [canonicalHall, frameHall, Set.mem_ofPred_eq, sub_add_cancel]

/-- Tightening preserves S, without inferring feasibility of its convex hull: both original
offsets dominate their support-tightened values. -/
theorem subset_hullCanonicalHall_of_subset_frameHall {S : Set Plane}
    (hS : IsCompact S) (hne : S.Nonempty) {u v : Plane} {a b : ℝ}
    (h : S ⊆ frameHall u v a b) : S ⊆ canonicalHall (actualHull S) u v := by
  have hu : support S u ≤ a + 1 := support_le_of_forall hne (fun _ hp => (h hp).1)
  have hv : support S v ≤ b + 1 := support_le_of_forall hne (fun _ hp => (h hp).2.1)
  intro p hp
  rw [mem_canonicalHall, support_actualHull hS hne, support_actualHull hS hne]
  exact ⟨coordDot_le_support hS hp u, coordDot_le_support hS hp v,
    (h hp).2.2.imp (fun _ => by linarith) (fun _ => by linarith)⟩

/-- The coordinate placement associated to support tightening. -/
def canonicalPlacement (K : Set Plane) (θ : ℝ) (p : Plane) : Plane :=
  (coordDot p (unitNormal θ) + 1 - support K (unitNormal θ),
    coordDot p (companionNormal θ) + 1 - support K (companionNormal θ))

theorem canonicalPlacement_eq_rigidMap (K : Set Plane) (θ : ℝ) (p : Plane) :
    canonicalPlacement K θ p =
      rigidMap (-θ) (1 - support K (unitNormal θ),
        1 - support K (companionNormal θ)) p := by
  apply Prod.ext <;>
    simp only [canonicalPlacement, rigidMap, rotate, coordDot, unitNormal,
      companionNormal, Prod.fst_add, Prod.snd_add, Real.cos_neg, Real.sin_neg] <;> ring

/-- A genuine translated rotation has exactly the frame-hall constraints. -/
theorem rigidMap_mem_lowerHall_iff (θ : ℝ) (a p : Plane) :
    rigidMap (-θ) a p ∈ lowerHall ↔
      p ∈ frameHall (unitNormal θ) (companionNormal θ) (-a.1) (-a.2) := by
  simp only [lowerHall, incomingArm, lowerOutgoingArm, frameHall, Set.mem_union,
    Set.mem_ofPred_eq, rigidMap, rotate, coordDot, unitNormal, companionNormal, Prod.fst_add,
    Prod.snd_add, Real.cos_neg, Real.sin_neg]
  grind

theorem canonicalPlacement_mem_lowerHall_iff (K : Set Plane) (θ : ℝ) (p : Plane) :
    canonicalPlacement K θ p ∈ lowerHall ↔
      p ∈ canonicalHall K (unitNormal θ) (companionNormal θ) := by
  rw [canonicalPlacement_eq_rigidMap, rigidMap_mem_lowerHall_iff, canonicalHall, neg_sub, neg_sub]

/-- Each frame visited by the original motion confines the body to the translated frame
hallway. -/
theorem Passage.subset_frameHall_at {S : Set Plane} {path : RigidMotionPath}
    (h : Passage S lowerHall incomingArm lowerOutgoingArm path) {t : ℝ}
    (ht : t ∈ motionInterval) :
    S ⊆ frameHall (unitNormal (-path.angle t)) (companionNormal (-path.angle t))
      (-(path.shift t).1) (-(path.shift t).2) := fun p hp =>
  (rigidMap_mem_lowerHall_iff _ (path.shift t) p).mp <| by
    simpa only [neg_neg, RigidMotionPath.placement] using
      h.inside t ht (Set.mem_image_of_mem (path.placement t) hp)

/-- Each frame visited by the original motion supplies the corresponding hull constraint. -/
theorem Passage.subset_canonicalHall_at {S : Set Plane} {path : RigidMotionPath}
    (h : Passage S lowerHall incomingArm lowerOutgoingArm path)
    (hS : IsCompact S) (hne : S.Nonempty) {t : ℝ} (ht : t ∈ motionInterval) :
    S ⊆ canonicalHall (actualHull S) (unitNormal (-path.angle t))
      (companionNormal (-path.angle t)) :=
  subset_hullCanonicalHall_of_subset_frameHall hS hne (h.subset_frameHall_at ht)

/-- The outgoing endpoint really supplies a whole-body unit strip. -/
theorem Passage.terminal_frameStrip {S : Set Plane} {path : RigidMotionPath}
    (h : Passage S lowerHall incomingArm lowerOutgoingArm path) :
    ∀ p ∈ S, -(path.shift 1).1 ≤ coordDot p (unitNormal (-path.angle 1)) ∧
      coordDot p (unitNormal (-path.angle 1)) ≤ -(path.shift 1).1 + 1 := fun p hp => by
  obtain ⟨h0, h1, -⟩ := h.finish (Set.mem_image_of_mem _ hp)
  simp only [RigidMotionPath.placement, rigidMap, rotate, Prod.fst_add, coordDot, unitNormal,
    Real.cos_neg, Real.sin_neg] at h0 h1 ⊢
  constructor <;> linarith

/-- The real outgoing arm yields its own whole-body support strip. -/
theorem Passage.terminal_support_lower {S : Set Plane} {path : RigidMotionPath}
    (h : Passage S lowerHall incomingArm lowerOutgoingArm path)
    (hne : S.Nonempty) {p : Plane} (hp : p ∈ S) :
    support S (unitNormal (-path.angle 1)) - 1 ≤
      coordDot p (unitNormal (-path.angle 1)) := by
  have key := h.terminal_frameStrip
  linarith [support_le_of_forall hne (fun q hq => (key q hq).2), (key p hp).1]

end AmbidextrousSofa
