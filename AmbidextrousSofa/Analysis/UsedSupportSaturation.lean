module

public import AmbidextrousSofa.Analysis.PartialTopInsertion
public import AmbidextrousSofa.Analysis.Circumscription
public import AmbidextrousSofa.Analysis.FacetPinning

@[expose] public section

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
  simp only [usedSupportSaturation, FinitePolygon.circumscription,
    FinitePolygon.mem_upperPolygon_iff, Sum.forall, Subtype.forall, usedNormal, Sum.elim_inl,
    Sum.elim_inr, imp_and, forall_and]

theorem IsDownwardCap.isDownwardCap_usedSupportSaturation {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα : α ≤ Real.pi / 2) :
    IsDownwardCap (usedSupportSaturation U α) :=
  FinitePolygon.isDownwardCap_circumscription hU (usedNormal α) fun i => by
    rcases i with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, Real.pi_pos])
    · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2.trans hα⟩

theorem IsDownwardCap.partialBarrier_usedSupportSaturation {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) (x : ℝ) :
    partialBarrier (usedSupportSaturation U α) α x = partialBarrier U α x := by
  have h1 {t} (ht : t ∈ Icc 0 α) : support (usedSupportSaturation U α) (unitNormal t) =
      support U (unitNormal t) :=
    FinitePolygon.support_circumscription hU (usedNormal α) (Sum.inl ⟨t, ht⟩)
  have h2 {t} (ht : t ∈ Icc 0 α) : support (usedSupportSaturation U α) (companionNormal t) =
      support U (companionNormal t) :=
    FinitePolygon.support_circumscription hU (usedNormal α) (Sum.inr ⟨t, ht⟩)
  have hsweep : sweptNiche (usedSupportSaturation U α) α x = sweptNiche U α x :=
    sweptNiche_eq_of_clippedCorner_eq (hU.isDownwardCap_usedSupportSaturation hα).isCompact
      hU.isCompact hα0 hα fun t ht => by
        rw [cornerWall, cornerWall, firstWall, firstWall, secondWall, secondWall,
          h1 ⟨ht.1.le, ht.2.le⟩, h2 ⟨ht.1.le, ht.2.le⟩]
  rw [partialBarrier, partialBarrier, hsweep, firstWall, firstWall, h1 ⟨hα0.le, le_rfl⟩]

/-- Exact PD.15: an affine-middle maximizer is the used-support saturation
cut by its own affine middle ceiling. -/
theorem IsJointCapMaximizer.eq_usedSupportSaturation_capCut
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    U = capCut (AmbidextrousSofa.usedSupportSaturation U α) (fun x => m * x + c) := by
  have hC := hU.isCap
  have hV := hC.isDownwardCap_usedSupportSaturation hU.angle_mem.2
  have hsub : U ⊆ AmbidextrousSofa.usedSupportSaturation U α :=
    FinitePolygon.subset_circumscription hC _
  have hproj : horizontalProjection (AmbidextrousSofa.usedSupportSaturation U α) =
      horizontalProjection U := FinitePolygon.horizontalProjection_circumscription hC _
  have hI := horizontalProjection_eq_Icc hC.nonempty hC.isCompact hC.convex
  have hw : 0 < capWidth U := by linarith [hU.width_bounds.1, one_lt_M]
  have hw' : capWidth U = horizontalRight U - horizontalLeft U := rfl
  -- A strict increase even at a wing endpoint would give a positive interval integral by roof
  -- continuity. Maximality therefore pins all these actual roof values.
  have hcharged {x} (hx : x ∈ Icc (horizontalLeft U) (horizontalLeft U + capWidth U / 4) ∪
      Icc (horizontalRight U - capWidth U / 4) (horizontalRight U)) :
      capRoof (AmbidextrousSofa.usedSupportSaturation U α) x = capRoof U x :=
    le_antisymm (not_lt.1 fun h => (hU.score_le_same_angle hV).not_gt
      (hC.capScore_lt_of_charged_roof_gain hV hsub hproj hw (fun y _ =>
        hC.partialBarrier_usedSupportSaturation hU.angle_pos hU.angle_mem.2 y) hx h))
      (hC.capRoof_mono hV hsub x)
  have hline := hC.capRoof_le_affine_of_affine_segment (by rw [hI]; constructor <;> linarith)
    (by rw [hI]; constructor <;> linarith) (by linarith) haffine
  refine Subset.antisymm (fun p hp => ⟨hsub hp, (le_capRoof hC.isCompact hp).trans
    (hline p.1 ⟨p, hp, rfl⟩)⟩) fun p hp => ?_
  have hxU : p.1 ∈ horizontalProjection U := hproj ▸ ⟨p, hp.1, rfl⟩
  refine (hC.mem_iff_projection_and_roof p).2 ⟨hxU, (hV.inStrip hp.1).1, ?_⟩
  by_cases hxJ : p.1 ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U)
  · exact (haffine p.1 hxJ).symm ▸ hp.2
  rw [hI] at hxU
  rw [← hcharged ((le_or_gt p.1 (horizontalLeft U + capWidth U / 4)).imp (⟨hxU.1, ·⟩)
    fun h => ⟨le_of_not_ge fun h' => hxJ ⟨h.le, h'⟩, hxU.2⟩)]
  exact le_capRoof hV.isCompact hp.1

end AmbidextrousSofa
