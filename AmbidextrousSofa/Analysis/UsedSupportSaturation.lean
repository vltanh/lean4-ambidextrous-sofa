import AmbidextrousSofa.Analysis.PartialTopInsertion
import AmbidextrousSofa.Analysis.Circumscription
import AmbidextrousSofa.Analysis.FacetPinning

/-!
# Saturation by precisely the visited upper supports

The defining normal index is the disjoint union of two copies of the
closed visited interval. The general halfplane construction used here
allows arbitrary index types; no finite sampling is substituted for that
interval. Saturation retains the original projection box and every used
support, including the whole terminal first wall and the initial top wall.

At an actual joint maximum its exterior roof agrees pointwise with the
original roof, including the wing endpoints. If the original middle roof
is affine, intersecting the saturation with that affine ceiling recovers
the original cap exactly. These are identities of actual sets and support
functions, without any terminal-curvature assumption.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def usedNormal (α : ℝ) : Icc (0 : ℝ) α ⊕ Icc (0 : ℝ) α → Plane :=
  Sum.elim (fun t => unitNormal t) (fun t => companionNormal t)

def usedSupportSaturation (U : Set Plane) (α : ℝ) : Set Plane :=
  FinitePolygon.circumscription U (usedNormal α)

theorem mem_usedSupportSaturation_iff (U : Set Plane) (α : ℝ) (p : Plane) :
    p ∈ usedSupportSaturation U α ↔
      p.1 ∈ Icc (horizontalLeft U) (horizontalRight U) ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧
      ∀ t ∈ Icc 0 α, coordDot p (unitNormal t) ≤ support U (unitNormal t) ∧
        coordDot p (companionNormal t) ≤ support U (companionNormal t) := by
  rw [usedSupportSaturation, FinitePolygon.circumscription, FinitePolygon.mem_upperPolygon_iff]
  constructor
  · rintro ⟨hx, hy, hn⟩
    refine ⟨hx, hy, ?_⟩
    intro t ht
    exact ⟨hn (Sum.inl ⟨t, ht⟩), hn (Sum.inr ⟨t, ht⟩)⟩
  · rintro ⟨hx, hy, hn⟩
    refine ⟨hx, hy, ?_⟩
    intro i
    rcases i with t | t
    · exact (hn t t.property).1
    · exact (hn t t.property).2

theorem usedNormal_vertical_nonneg {α : ℝ} (hα : α ≤ Real.pi / 2)
    (i : Icc (0 : ℝ) α ⊕ Icc (0 : ℝ) α) : 0 ≤ (usedNormal α i).2 := by
  rcases i with t | t
  · exact Real.sin_nonneg_of_nonneg_of_le_pi t.property.1
      (by linarith [t.property.2, Real.pi_pos])
  · exact Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [t.property.1, Real.pi_pos], t.property.2.trans hα⟩

theorem IsDownwardCap.subset_usedSupportSaturation {U : Set Plane}
    (hU : IsDownwardCap U) (α : ℝ) : U ⊆ usedSupportSaturation U α :=
  FinitePolygon.subset_circumscription hU (usedNormal α)

theorem IsDownwardCap.isDownwardCap_usedSupportSaturation {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα : α ≤ Real.pi / 2) :
    IsDownwardCap (usedSupportSaturation U α) :=
  FinitePolygon.isDownwardCap_circumscription hU (usedNormal α) (usedNormal_vertical_nonneg hα)

theorem IsDownwardCap.horizontalProjection_usedSupportSaturation {U : Set Plane}
    (hU : IsDownwardCap U) (α : ℝ) :
    horizontalProjection (usedSupportSaturation U α) = horizontalProjection U :=
  FinitePolygon.horizontalProjection_circumscription hU (usedNormal α)

theorem IsDownwardCap.support_usedSupportSaturation_first {U : Set Plane}
    (hU : IsDownwardCap U) {α t : ℝ} (ht : t ∈ Icc 0 α) :
    support (usedSupportSaturation U α) (unitNormal t) = support U (unitNormal t) :=
  FinitePolygon.support_circumscription hU (usedNormal α) (Sum.inl ⟨t, ht⟩)

theorem IsDownwardCap.support_usedSupportSaturation_second {U : Set Plane}
    (hU : IsDownwardCap U) {α t : ℝ} (ht : t ∈ Icc 0 α) :
    support (usedSupportSaturation U α) (companionNormal t) = support U (companionNormal t) :=
  FinitePolygon.support_circumscription hU (usedNormal α) (Sum.inr ⟨t, ht⟩)

theorem IsDownwardCap.capHeight_usedSupportSaturation {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα : 0 ≤ α) :
    capHeight (usedSupportSaturation U α) = capHeight U := by
  have h := hU.support_usedSupportSaturation_second (show (0 : ℝ) ∈ Icc 0 α from ⟨le_rfl, hα⟩)
  simpa only [companionNormal, Real.sin_zero, Real.cos_zero, neg_zero, capHeight] using h

theorem IsDownwardCap.firstWall_usedSupportSaturation {U : Set Plane}
    (hU : IsDownwardCap U) {α t : ℝ} (ht : t ∈ Icc 0 α) (x : ℝ) :
    firstWall (usedSupportSaturation U α) t x = firstWall U t x := by
  rw [firstWall, firstWall, hU.support_usedSupportSaturation_first ht]

theorem IsDownwardCap.secondWall_usedSupportSaturation {U : Set Plane}
    (hU : IsDownwardCap U) {α t : ℝ} (ht : t ∈ Icc 0 α) (x : ℝ) :
    secondWall (usedSupportSaturation U α) t x = secondWall U t x := by
  rw [secondWall, secondWall, hU.support_usedSupportSaturation_second ht]

theorem IsDownwardCap.partialBarrier_usedSupportSaturation {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) (x : ℝ) :
    partialBarrier (usedSupportSaturation U α) α x = partialBarrier U α x := by
  have hV := hU.isDownwardCap_usedSupportSaturation hα
  have hsweep : sweptNiche (usedSupportSaturation U α) α x = sweptNiche U α x := by
    apply sweptNiche_eq_of_clippedCorner_eq hV.isCompact hU.isCompact hα0 hα
    intro t ht
    rw [cornerWall, cornerWall,
      hU.firstWall_usedSupportSaturation ⟨ht.1.le, ht.2.le⟩,
      hU.secondWall_usedSupportSaturation ⟨ht.1.le, ht.2.le⟩]
  rw [partialBarrier, partialBarrier, hsweep,
    hU.firstWall_usedSupportSaturation ⟨hα0.le, le_rfl⟩]

/-- The charged roof can only increase, while both integration windows and
the complete partial barrier are unchanged. -/
theorem IsDownwardCap.capScore_le_usedSupportSaturation {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) :
    capScore U α ≤ capScore (usedSupportSaturation U α) α := by
  have hV := hU.isDownwardCap_usedSupportSaturation hα
  have hproj := hU.horizontalProjection_usedSupportSaturation α
  have hleft : horizontalLeft (usedSupportSaturation U α) = horizontalLeft U := congrArg sInf hproj
  have hright : horizontalRight (usedSupportSaturation U α) = horizontalRight U := congrArg sSup hproj
  have hroof : ∀ x, capRoof U x ≤ capRoof (usedSupportSaturation U α) x :=
    hU.capRoof_mono hV (hU.subset_usedSupportSaturation α)
  have hw := hU.capWidth_nonneg
  have hfirst := intervalIntegral.integral_mono_on
    (show horizontalLeft U ≤ horizontalLeft U + capWidth U / 4 by linarith)
    (hU.intervalIntegrable_capRoof _ _) (hV.intervalIntegrable_capRoof _ _)
    (fun x _ => hroof x)
  have hlast := intervalIntegral.integral_mono_on
    (show horizontalRight U - capWidth U / 4 ≤ horizontalRight U by linarith)
    (hU.intervalIntegrable_capRoof _ _) (hV.intervalIntegrable_capRoof _ _)
    (fun x _ => hroof x)
  have hbarrier : partialBarrier (usedSupportSaturation U α) α = partialBarrier U α :=
    funext (hU.partialBarrier_usedSupportSaturation hα0 hα)
  rw [hU.capScore_eq_intervalSpatialScore, hV.capScore_eq_intervalSpatialScore,
    hleft, hright, hbarrier]
  change (∫ x in (horizontalLeft U)..(horizontalLeft U + capWidth U / 4), capRoof U x) +
      (∫ x in (horizontalRight U - capWidth U / 4)..(horizontalRight U), capRoof U x) -
      (∫ x in (horizontalLeft U + capWidth U / 4)..(horizontalRight U - capWidth U / 4),
        partialBarrier U α x) ≤
    (∫ x in (horizontalLeft U)..(horizontalLeft U + capWidth U / 4),
        capRoof (usedSupportSaturation U α) x) +
      (∫ x in (horizontalRight U - capWidth U / 4)..(horizontalRight U),
        capRoof (usedSupportSaturation U α) x) -
      (∫ x in (horizontalLeft U + capWidth U / 4)..(horizontalRight U - capWidth U / 4),
        partialBarrier U α x)
  linarith

theorem IsJointCapMaximizer.usedSupportSaturation {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) : IsJointCapMaximizer (usedSupportSaturation U α) α :=
  hU.of_score_le (hU.isCap.isDownwardCap_usedSupportSaturation hU.angle_mem.2) hU.angle_mem
    (hU.isCap.capScore_le_usedSupportSaturation hU.angle_pos hU.angle_mem.2)

theorem IsJointCapMaximizer.capScore_usedSupportSaturation {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) : capScore (usedSupportSaturation U α) α = capScore U α :=
  hU.usedSupportSaturation.score_eq hU

/-- A strict increase even at a wing endpoint would give a positive
interval integral by roof continuity. Maximality therefore pins all these
actual roof values, not merely their almost-everywhere classes. -/
theorem IsJointCapMaximizer.capRoof_usedSupportSaturation_on_charged
    {U : Set Plane} {α x : ℝ} (hU : IsJointCapMaximizer U α)
    (hx : x ∈ Icc (horizontalLeft U) (horizontalLeft U + capWidth U / 4) ∪
      Icc (horizontalRight U - capWidth U / 4) (horizontalRight U)) :
    capRoof (usedSupportSaturation U α) x = capRoof U x := by
  have hV := hU.isCap.isDownwardCap_usedSupportSaturation hU.angle_mem.2
  have hsub := hU.isCap.subset_usedSupportSaturation α
  have hwidth : 0 < capWidth U := by linarith [hU.width_bounds.1, one_lt_M]
  apply le_antisymm _ (hU.isCap.capRoof_mono hV hsub x)
  by_contra h
  have hstrict := hU.isCap.capScore_lt_of_charged_roof_gain hV hsub
    (hU.isCap.horizontalProjection_usedSupportSaturation α) hwidth
    (fun y _ => hU.isCap.partialBarrier_usedSupportSaturation hU.angle_pos hU.angle_mem.2 y)
    hx (lt_of_not_ge h)
  exact (not_lt_of_ge (hU.score_le_same_angle hV)) hstrict

/-- Exact PD.15: an affine-middle maximizer is the used-support saturation
cut by its own affine middle ceiling. -/
theorem IsJointCapMaximizer.eq_usedSupportSaturation_capCut
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    U = capCut (usedSupportSaturation U α) (fun x => m * x + c) := by
  let a := horizontalLeft U + capWidth U / 4
  let b := horizontalRight U - capWidth U / 4
  have hwidth : 0 < capWidth U := by linarith [hU.width_bounds.1, one_lt_M]
  have hab : a < b := by dsimp [a, b]; unfold capWidth at *; linarith
  have ha : a ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex]
    dsimp [a]
    unfold capWidth at *
    constructor <;> linarith
  have hb : b ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex]
    dsimp [b]
    unfold capWidth at *
    constructor <;> linarith
  have hline := hU.isCap.capRoof_le_affine_of_affine_segment ha hb hab haffine
  have hV := hU.isCap.isDownwardCap_usedSupportSaturation hU.angle_mem.2
  have hproj := hU.isCap.horizontalProjection_usedSupportSaturation α
  apply Subset.antisymm
  · intro p hp
    refine ⟨hU.isCap.subset_usedSupportSaturation α hp, ?_⟩
    exact (le_capRoof hU.isCap.isCompact (by simpa only [Prod.mk.eta] using hp)).trans
      (hline p.1 ⟨p, hp, rfl⟩)
  · intro p hp
    have hxV : p.1 ∈ horizontalProjection (usedSupportSaturation U α) := ⟨p, hp.1, rfl⟩
    have hxU : p.1 ∈ horizontalProjection U := by rwa [hproj] at hxV
    apply (hU.isCap.mem_iff_projection_and_roof p).mpr
    refine ⟨hxU, (hV.inStrip hp.1).1, ?_⟩
    by_cases hxJ : p.1 ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U)
    · rw [haffine p.1 hxJ]
      exact hp.2
    · have hxI : p.1 ∈ Icc (horizontalLeft U) (horizontalRight U) := by
        rwa [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex] at hxU
      have hxWing : p.1 ∈ Icc (horizontalLeft U) a ∪ Icc b (horizontalRight U) := by
        rcases le_total p.1 a with hxa | hax
        · exact Or.inl ⟨hxI.1, hxa⟩
        · have hbx : b ≤ p.1 := le_of_lt (lt_of_not_ge (fun hxb => hxJ ⟨hax, hxb⟩))
          exact Or.inr ⟨hbx, hxI.2⟩
      rw [← hU.capRoof_usedSupportSaturation_on_charged hxWing]
      exact le_capRoof hV.isCompact (by simpa only [Prod.mk.eta] using hp.1)

end AmbidextrousSofa
