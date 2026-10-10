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
  unfold companionNormal
  fun_prop

theorem companionNormal_eq_unitNormal (θ : ℝ) :
    companionNormal θ = unitNormal (θ + Real.pi / 2) := by
  apply Prod.ext <;> simp [companionNormal, unitNormal, Real.sin_add, Real.cos_add]

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
  simp only [canonicalHall, frameHall, Set.mem_setOf_eq, sub_add_cancel]

theorem mem_lowerHall_iff (p : Plane) :
    p ∈ lowerHall ↔ p.1 ≤ 1 ∧ p.2 ≤ 1 ∧ (0 ≤ p.1 ∨ 0 ≤ p.2) := by
  change ((p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1) ∨
    (0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 ≤ 1)) ↔ _
  constructor
  · rintro (⟨hx, hy0, hy1⟩ | ⟨hx0, hx1, hy1⟩)
    · exact ⟨hx, hy1, Or.inr hy0⟩
    · exact ⟨hx1, hy1, Or.inl hx0⟩
  · rintro ⟨hx1, hy1, hx0 | hy0⟩
    · exact Or.inr ⟨hx0, hx1, hy1⟩
    · exact Or.inl ⟨hx1, hy0, hy1⟩

/-- Both original offsets dominate their support-tightened values. -/
theorem support_offsets_le_of_subset_frameHall {S : Set Plane} (hne : S.Nonempty)
    {u v : Plane} {a b : ℝ} (h : S ⊆ frameHall u v a b) :
    support S u - 1 ≤ a ∧ support S v - 1 ≤ b := by
  have hu : support S u ≤ a + 1 := support_le_of_forall hne (fun _ hp => (h hp).1)
  have hv : support S v ≤ b + 1 := support_le_of_forall hne (fun _ hp => (h hp).2.1)
  constructor <;> linarith

/-- Tightening preserves S, without inferring feasibility of its convex hull. -/
theorem subset_canonicalHall_of_subset_frameHall {S : Set Plane}
    (hS : IsCompact S) (hne : S.Nonempty) {u v : Plane} {a b : ℝ}
    (h : S ⊆ frameHall u v a b) : S ⊆ canonicalHall S u v := by
  have hoff := support_offsets_le_of_subset_frameHall hne h
  intro p hp
  apply (mem_canonicalHall S u v p).mpr
  refine ⟨coordDot_le_support hS hp u, coordDot_le_support hS hp v, ?_⟩
  rcases (h hp).2.2 with hu | hv
  · exact Or.inl (hoff.1.trans hu)
  · exact Or.inr (hoff.2.trans hv)

theorem canonicalHall_actualHull {S : Set Plane} (hS : IsCompact S)
    (hne : S.Nonempty) (u v : Plane) :
    canonicalHall (actualHull S) u v = canonicalHall S u v := by
  simp only [canonicalHall, support_actualHull hS hne]

theorem subset_hullCanonicalHall_of_subset_frameHall {S : Set Plane}
    (hS : IsCompact S) (hne : S.Nonempty) {u v : Plane} {a b : ℝ}
    (h : S ⊆ frameHall u v a b) : S ⊆ canonicalHall (actualHull S) u v := by
  rw [canonicalHall_actualHull hS hne]
  exact subset_canonicalHall_of_subset_frameHall hS hne h

/-- A whole-body strip gives the lower wall at the tightened support offset. -/
theorem support_strip_lower_of_mem {S : Set Plane} (hne : S.Nonempty)
    {u : Plane} {a : ℝ} (hstrip : ∀ q ∈ S, a ≤ coordDot q u ∧ coordDot q u ≤ a + 1)
    {p : Plane} (hp : p ∈ S) : support S u - 1 ≤ coordDot p u := by
  have hu : support S u ≤ a + 1 :=
    support_le_of_forall hne (fun q hq => (hstrip q hq).2)
  have hlower := (hstrip p hp).1
  linarith

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

theorem canonicalPlacement_mem_lowerHall_iff (K : Set Plane) (θ : ℝ) (p : Plane) :
    canonicalPlacement K θ p ∈ lowerHall ↔
      p ∈ canonicalHall K (unitNormal θ) (companionNormal θ) := by
  rw [mem_lowerHall_iff, mem_canonicalHall]
  change (_ ≤ 1 ∧ _ ≤ 1 ∧ (0 ≤ _ ∨ 0 ≤ _)) ↔ _
  simp only [canonicalPlacement]
  constructor
  · rintro ⟨hu, hv, hfirst | hsecond⟩
    · exact ⟨by linarith, by linarith, Or.inl (by linarith)⟩
    · exact ⟨by linarith, by linarith, Or.inr (by linarith)⟩
  · rintro ⟨hu, hv, hfirst | hsecond⟩
    · exact ⟨by linarith, by linarith, Or.inl (by linarith)⟩
    · exact ⟨by linarith, by linarith, Or.inr (by linarith)⟩

/-- A genuine translated rotation has exactly the frame-hall constraints. -/
theorem rigidMap_mem_lowerHall_iff (θ : ℝ) (a p : Plane) :
    rigidMap (-θ) a p ∈ lowerHall ↔
      p ∈ frameHall (unitNormal θ) (companionNormal θ) (-a.1) (-a.2) := by
  rw [mem_lowerHall_iff]
  have hcoords : rigidMap (-θ) a p =
      (coordDot p (unitNormal θ) + a.1, coordDot p (companionNormal θ) + a.2) := by
    apply Prod.ext <;>
      simp only [rigidMap, rotate, coordDot, unitNormal, companionNormal,
        Prod.fst_add, Prod.snd_add, Real.cos_neg, Real.sin_neg] <;> ring
  rw [hcoords]
  change (_ ≤ 1 ∧ _ ≤ 1 ∧ (0 ≤ _ ∨ 0 ≤ _)) ↔
    (_ ≤ -a.1 + 1 ∧ _ ≤ -a.2 + 1 ∧ (-a.1 ≤ _ ∨ -a.2 ≤ _))
  constructor
  · rintro ⟨hu, hv, hfirst | hsecond⟩
    · exact ⟨by linarith, by linarith, Or.inl (by linarith)⟩
    · exact ⟨by linarith, by linarith, Or.inr (by linarith)⟩
  · rintro ⟨hu, hv, hfirst | hsecond⟩
    · exact ⟨by linarith, by linarith, Or.inl (by linarith)⟩
    · exact ⟨by linarith, by linarith, Or.inr (by linarith)⟩

/-- Each frame visited by the original motion supplies the corresponding hull constraint. -/
theorem Passage.subset_canonicalHall_at {S : Set Plane} {path : RigidMotionPath}
    (h : Passage S lowerHall incomingArm lowerOutgoingArm path)
    (hS : IsCompact S) (hne : S.Nonempty) {t : ℝ} (ht : t ∈ motionInterval) :
    S ⊆ canonicalHall (actualHull S) (unitNormal (-path.angle t))
      (companionNormal (-path.angle t)) := by
  apply subset_hullCanonicalHall_of_subset_frameHall hS hne
    (a := -(path.shift t).1) (b := -(path.shift t).2)
  intro p hp
  apply (rigidMap_mem_lowerHall_iff (-path.angle t) (path.shift t) p).mp
  simpa only [neg_neg, RigidMotionPath.placement] using
    h.inside t ht (Set.mem_image_of_mem (path.placement t) hp)

/-- The real outgoing arm yields its own whole-body support strip. -/
theorem Passage.terminal_support_lower {S : Set Plane} {path : RigidMotionPath}
    (h : Passage S lowerHall incomingArm lowerOutgoingArm path)
    (hne : S.Nonempty) {p : Plane} (hp : p ∈ S) :
    support S (unitNormal (-path.angle 1)) - 1 ≤
      coordDot p (unitNormal (-path.angle 1)) := by
  apply support_strip_lower_of_mem hne
    (a := -(path.shift 1).1) (p := p) ?_ hp
  intro q hq
  have hfinish := h.finish (Set.mem_image_of_mem (path.placement 1) hq)
  change 0 ≤ (rigidMap (path.angle 1) (path.shift 1) q).1 ∧
    (rigidMap (path.angle 1) (path.shift 1) q).1 ≤ 1 ∧
    (rigidMap (path.angle 1) (path.shift 1) q).2 ≤ 1 at hfinish
  simp only [rigidMap, rotate, Prod.fst_add] at hfinish
  simp only [coordDot, unitNormal, Real.cos_neg, Real.sin_neg]
  constructor <;> nlinarith [hfinish.1, hfinish.2.1]

end AmbidextrousSofa
