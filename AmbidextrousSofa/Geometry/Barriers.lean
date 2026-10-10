module

public import AmbidextrousSofa.Geometry.Hallway

@[expose] public section

/-!
# Whole-angle niches and the actual terminal wall

The definitions retain both attached inner rays and their full open angular
interval. The terminal first wall is included separately. At a full quarter
turn it is nonpositive for a cap in the unit strip and is therefore redundant.
No analogous omission is made at a proper terminal angle.
-/

noncomputable section

namespace AmbidextrousSofa

def firstWall (K : Set Plane) (θ x : ℝ) : ℝ :=
  (support K (unitNormal θ) - 1 - x * Real.cos θ) / Real.sin θ

def secondWall (K : Set Plane) (θ x : ℝ) : ℝ :=
  (support K (companionNormal θ) - 1 + x * Real.sin θ) / Real.cos θ

def cornerWall (K : Set Plane) (θ x : ℝ) : ℝ := min (firstWall K θ x) (secondWall K θ x)

/-- All visited interior angles, rather than a sampled or contact-only family. -/
def sweptWallValues (K : Set Plane) (α x : ℝ) : Set ℝ :=
  (fun θ => cornerWall K θ x) '' Set.Ioo 0 α

def sweptNiche (K : Set Plane) (α x : ℝ) : ℝ := max (sSup (sweptWallValues K α x)) 0

/-- The true partial barrier includes the entire outgoing first wall. -/
def partialBarrier (K : Set Plane) (α x : ℝ) : ℝ :=
  max (sweptNiche K α x) (firstWall K α x)

theorem sweptWallValues_nonempty (K : Set Plane) {α : ℝ} (hα : 0 < α) (x : ℝ) :
    (sweptWallValues K α x).Nonempty := by
  refine ⟨cornerWall K (α / 2) x, α / 2, ?_, rfl⟩
  constructor <;> linarith

theorem sweptNiche_nonneg (K : Set Plane) (α x : ℝ) : 0 ≤ sweptNiche K α x :=
  le_max_right _ _

theorem partialBarrier_nonneg (K : Set Plane) (α x : ℝ) : 0 ≤ partialBarrier K α x :=
  (sweptNiche_nonneg K α x).trans (le_max_left _ _)

theorem firstWall_le_iff {K : Set Plane} {θ x y : ℝ} (hs : 0 < Real.sin θ) :
    firstWall K θ x ≤ y ↔ support K (unitNormal θ) - 1 ≤ coordDot (x, y) (unitNormal θ) := by
  rw [firstWall, div_le_iff₀ hs]
  simp only [coordDot, unitNormal]
  constructor <;> intro h <;> linarith

theorem secondWall_le_iff {K : Set Plane} {θ x y : ℝ} (hc : 0 < Real.cos θ) :
    secondWall K θ x ≤ y ↔
      support K (companionNormal θ) - 1 ≤ coordDot (x, y) (companionNormal θ) := by
  rw [secondWall, div_le_iff₀ hc]
  simp only [coordDot, companionNormal]
  constructor <;> intro h <;> nlinarith

/-- The two alternatives of the inner corner are exactly a minimum of wall heights. -/
theorem cornerWall_le_iff {K : Set Plane} {θ x y : ℝ}
    (hs : 0 < Real.sin θ) (hc : 0 < Real.cos θ) :
    cornerWall K θ x ≤ y ↔
      (support K (unitNormal θ) - 1 ≤ coordDot (x, y) (unitNormal θ) ∨
        support K (companionNormal θ) - 1 ≤ coordDot (x, y) (companionNormal θ)) := by
  rw [cornerWall, min_le_iff, firstWall_le_iff hs, secondWall_le_iff hc]

theorem cornerWall_le_of_mem_canonicalHall {K : Set Plane} {θ : ℝ} {p : Plane}
    (hs : 0 < Real.sin θ) (hc : 0 < Real.cos θ)
    (hp : p ∈ canonicalHall K (unitNormal θ) (companionNormal θ)) :
    cornerWall K θ p.1 ≤ p.2 := by
  apply (cornerWall_le_iff hs hc).mpr
  simpa only [Prod.mk.eta] using ((mem_canonicalHall K _ _ p).mp hp).2.2

/-- A retained physical point bounds every swept value at its own abscissa. -/
theorem sweptNiche_le_of_forall {K : Set Plane} {α x y : ℝ} (hα : 0 < α)
    (hy : 0 ≤ y) (h : ∀ θ ∈ Set.Ioo 0 α, cornerWall K θ x ≤ y) :
    sweptNiche K α x ≤ y := by
  apply max_le _ hy
  exact csSup_le (sweptWallValues_nonempty K hα x) (Set.forall_mem_image.mpr h)

theorem cornerWall_le_sweptNiche {K : Set Plane} {α θ x : ℝ}
    (hbounded : BddAbove (sweptWallValues K α x)) (hθ : θ ∈ Set.Ioo 0 α) :
    cornerWall K θ x ≤ sweptNiche K α x :=
  (le_csSup hbounded (Set.mem_image_of_mem _ hθ)).trans (le_max_left _ _)

theorem partialBarrier_le_iff (K : Set Plane) (α x y : ℝ) :
    partialBarrier K α x ≤ y ↔ sweptNiche K α x ≤ y ∧ firstWall K α x ≤ y :=
  max_le_iff

/-- The full-turn terminal first wall is the actual top-support excess. -/
theorem firstWall_pi_div_two (K : Set Plane) (x : ℝ) :
    firstWall K (Real.pi / 2) x = support K (0, 1) - 1 := by
  simp [firstWall, unitNormal]

theorem IsDownwardCap.partialBarrier_pi_div_two {U : Set Plane}
    (hU : IsDownwardCap U) (x : ℝ) :
    partialBarrier U (Real.pi / 2) x = sweptNiche U (Real.pi / 2) x := by
  apply max_eq_left
  rw [firstWall_pi_div_two]
  have htop := hU.support_upward_le_one
  have hn := sweptNiche_nonneg U (Real.pi / 2) x
  linarith

/-- Passage through every listed frame plus the true outgoing strip bounds the whole barrier. -/
theorem partialBarrier_le_of_angular_constraints {K : Set Plane} {α : ℝ} {p : Plane}
    (hα : 0 < α) (hαL : α ≤ Real.pi / 2) (hp0 : 0 ≤ p.2)
    (hinside : ∀ θ ∈ Set.Ioo 0 α,
      p ∈ canonicalHall K (unitNormal θ) (companionNormal θ))
    (hterminal : support K (unitNormal α) - 1 ≤ coordDot p (unitNormal α)) :
    partialBarrier K α p.1 ≤ p.2 := by
  apply (partialBarrier_le_iff K α p.1 p.2).mpr
  constructor
  · apply sweptNiche_le_of_forall hα hp0
    intro θ hθ
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1
      (by linarith [hθ.2, hαL, Real.pi_pos])
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.trans_le hαL⟩
    exact cornerWall_le_of_mem_canonicalHall hs hc (hinside θ hθ)
  · apply (firstWall_le_iff (Real.sin_pos_of_pos_of_lt_pi hα
      (by linarith [hαL, Real.pi_pos]))).mpr
    simpa only [Prod.mk.eta] using hterminal

/-- Upward support invariance identifies the cap walls with the actual hull walls. -/
theorem firstWall_upperCap {K : Set Plane} (hK : IsCompact K) (hne : K.Nonempty)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) {θ : ℝ} (hs : 0 ≤ Real.sin θ) (x : ℝ) :
    firstWall (upperCap K) θ x = firstWall K θ x := by
  unfold firstWall
  rw [support_upperCap hK hne hK0 hs]

theorem secondWall_upperCap {K : Set Plane} (hK : IsCompact K) (hne : K.Nonempty)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) {θ : ℝ} (hc : 0 ≤ Real.cos θ) (x : ℝ) :
    secondWall (upperCap K) θ x = secondWall K θ x := by
  unfold secondWall
  rw [support_upperCap hK hne hK0 hc]

end AmbidextrousSofa
