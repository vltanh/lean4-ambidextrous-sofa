import AmbidextrousSofa.Analysis.EndpointPressure
import AmbidextrousSofa.Analysis.OrdinarySofaBound
import AmbidextrousSofa.Topology.VerticalRegion

/-!
# The actual one-turn body cut out by a full cap niche

Whenever the entire actual niche lies below the cap roof on its projection,
the retained region is compact and connected. Its explicitly constructed
continuous motion satisfies both outer support walls and avoids every
attached inner quadrant. The start and finish lie in the actual incoming
and outgoing corridor arms. Thus the ordinary one-turn area theorem applies
to this literal body. No equality between the cap and its survivor's convex
hull, unit-curvature assumption, or signed-area substitution is used.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def oneTurnSurvivor (U : Set Plane) : Set Plane :=
  {p | p ∈ U ∧ sweptNiche U (Real.pi / 2) p.1 ≤ p.2}

theorem oneTurnSurvivor_subset (U : Set Plane) : oneTurnSurvivor U ⊆ U := fun _ hp => hp.1

theorem IsDownwardCap.continuous_sweptNiche_pi_div_two {U : Set Plane}
    (hU : IsDownwardCap U) : Continuous (sweptNiche U (Real.pi / 2)) := by
  have heq : partialBarrier U (Real.pi / 2) = sweptNiche U (Real.pi / 2) :=
    funext hU.partialBarrier_pi_div_two
  rw [← heq]
  exact hU.continuous_partialBarrier_pi_div_two

theorem IsDownwardCap.isClosed_oneTurnSurvivor {U : Set Plane} (hU : IsDownwardCap U) :
    IsClosed (oneTurnSurvivor U) :=
  hU.isCompact.isClosed.inter (isClosed_le
    (hU.continuous_sweptNiche_pi_div_two.comp continuous_fst) continuous_snd)

theorem IsDownwardCap.isCompact_oneTurnSurvivor {U : Set Plane} (hU : IsDownwardCap U) :
    IsCompact (oneTurnSurvivor U) :=
  hU.isCompact.of_isClosed_subset hU.isClosed_oneTurnSurvivor (oneTurnSurvivor_subset U)

theorem IsDownwardCap.oneTurnSurvivor_eq_verticalIntervalRegion {U : Set Plane}
    (hU : IsDownwardCap U) :
    oneTurnSurvivor U = verticalIntervalRegion (horizontalProjection U)
      (sweptNiche U (Real.pi / 2)) (capRoof U) := by
  ext p
  change (p ∈ U ∧ sweptNiche U (Real.pi / 2) p.1 ≤ p.2) ↔ _
  rw [hU.mem_iff_projection_and_roof, mem_verticalIntervalRegion]
  constructor
  · rintro ⟨⟨hx, hp0, hroof⟩, hn⟩
    exact ⟨hx, hn, hroof⟩
  · rintro ⟨hx, hn, hroof⟩
    exact ⟨⟨hx, (sweptNiche_nonneg U _ p.1).trans hn, hroof⟩, hn⟩

theorem IsDownwardCap.isConnected_oneTurnSurvivor {U : Set Plane} (hU : IsDownwardCap U)
    (hfit : ∀ x ∈ horizontalProjection U, sweptNiche U (Real.pi / 2) x ≤ capRoof U x) :
    IsConnected (oneTurnSurvivor U) := by
  rw [hU.oneTurnSurvivor_eq_verticalIntervalRegion]
  apply isConnected_verticalIntervalRegion _
    hU.continuous_sweptNiche_pi_div_two.continuousOn hU.continuousOn_capRoof hfit
  rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
  exact isConnected_Icc (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact)

/-- The canonical supports of the original cap define an actual rigid path,
even if some support contacts are not retained in the niche-cut body. -/
def IsDownwardCap.canonicalLowerPath {U : Set Plane} (hU : IsDownwardCap U) : RigidMotionPath where
  angle := fun t => -(Real.pi / 2 * t)
  shift := fun t => (1 - support U (unitNormal (Real.pi / 2 * t)),
    1 - support U (companionNormal (Real.pi / 2 * t)))
  continuous_angle := by fun_prop
  continuous_shift := by
    have hu := (continuous_support hU.isCompact).comp continuous_unitNormal
    have hv := (continuous_support hU.isCompact).comp continuous_companionNormal
    exact (continuous_const.sub (hu.comp (by fun_prop))).prodMk
      (continuous_const.sub (hv.comp (by fun_prop)))

theorem IsDownwardCap.canonicalLowerPath_placement {U : Set Plane} (hU : IsDownwardCap U)
    (t : ℝ) (p : Plane) :
    hU.canonicalLowerPath.placement t p = canonicalPlacement U (Real.pi / 2 * t) p := by
  rw [canonicalPlacement_eq_rigidMap]
  rfl

theorem IsDownwardCap.oneTurnSurvivor_subset_canonicalHall {U : Set Plane}
    (hU : IsDownwardCap U) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    oneTurnSurvivor U ⊆ canonicalHall U (unitNormal θ) (companionNormal θ) := by
  intro p hp
  apply (mem_canonicalHall U _ _ p).mpr
  refine ⟨coordDot_le_support hU.isCompact hp.1 _,
    coordDot_le_support hU.isCompact hp.1 _, ?_⟩
  by_cases hθ0 : θ = 0
  · right
    have hy := (hU.inStrip hp.1).1
    have htop := hU.support_upward_le_one
    simpa only [hθ0, companionNormal, Real.sin_zero, Real.cos_zero, neg_zero,
      coordDot, mul_zero, mul_one, zero_add] using
      (by linarith : support U (0, 1) - 1 ≤ p.2)
  by_cases hθL : θ = Real.pi / 2
  · left
    have hy := (hU.inStrip hp.1).1
    have htop := hU.support_upward_le_one
    simpa only [hθL, unitNormal, Real.cos_pi_div_two, Real.sin_pi_div_two,
      coordDot, mul_zero, mul_one, zero_add] using
      (by linarith : support U (0, 1) - 1 ≤ p.2)
  · have hθopen : θ ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθ0), lt_of_le_of_ne hθ.2 hθL⟩
    apply (cornerWall_le_iff
      (Real.sin_pos_of_pos_of_lt_pi hθopen.1 (by linarith [hθopen.2, Real.pi_pos]))
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθopen.1, Real.pi_pos], hθopen.2⟩)).mp
    exact (cornerWall_le_sweptNiche
      (sweptWallValues_bddAbove hU.isCompact le_rfl p.1) hθopen).trans hp.2

theorem IsDownwardCap.canonicalPlacement_start_mem {U : Set Plane}
    (hU : IsDownwardCap U) {p : Plane} (hp : p ∈ U) :
    canonicalPlacement U 0 p ∈ incomingArm := by
  have hx : p.1 ≤ support U (1, 0) := by
    simpa only [coordDot, mul_one, mul_zero, add_zero] using
      coordDot_le_support hU.isCompact hp (1, 0)
  have hy : p.2 ≤ support U (0, 1) := by
    simpa only [coordDot, mul_zero, mul_one, zero_add] using
      coordDot_le_support hU.isCompact hp (0, 1)
  have hy0 := (hU.inStrip hp).1
  have htop := hU.support_upward_le_one
  simp only [canonicalPlacement, unitNormal, companionNormal, Real.cos_zero,
    Real.sin_zero, neg_zero, coordDot, mul_one, mul_zero, add_zero, zero_add,
    incomingArm, mem_setOf_eq]
  exact ⟨by linarith, by linarith, by linarith⟩

theorem IsDownwardCap.canonicalPlacement_finish_mem {U : Set Plane}
    (hU : IsDownwardCap U) {p : Plane} (hp : p ∈ U) :
    canonicalPlacement U (Real.pi / 2) p ∈ lowerOutgoingArm := by
  have hx : -p.1 ≤ support U (-1, 0) := by
    simpa only [coordDot, mul_neg_one, mul_zero, add_zero] using
      coordDot_le_support hU.isCompact hp (-1, 0)
  have hy : p.2 ≤ support U (0, 1) := by
    simpa only [coordDot, mul_zero, mul_one, zero_add] using
      coordDot_le_support hU.isCompact hp (0, 1)
  have hy0 := (hU.inStrip hp).1
  have htop := hU.support_upward_le_one
  simp only [canonicalPlacement, unitNormal, companionNormal, Real.cos_pi_div_two,
    Real.sin_pi_div_two, coordDot, mul_one, mul_zero, mul_neg_one, add_zero, zero_add,
    lowerOutgoingArm, mem_setOf_eq]
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Every point of the actual survivor follows this same complete passage.
The roof-fit hypothesis is needed for connectedness, not for containment
in the moving corridors. -/
theorem IsDownwardCap.oneTurnSurvivor_lowerPassage {U : Set Plane} (hU : IsDownwardCap U) :
    Passage (oneTurnSurvivor U) lowerHall incomingArm lowerOutgoingArm hU.canonicalLowerPath := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rintro _ ⟨p, hp, rfl⟩
    rw [hU.canonicalLowerPath_placement]
    apply (canonicalPlacement_mem_lowerHall_iff U _ p).mpr
    apply hU.oneTurnSurvivor_subset_canonicalHall _ hp
    have hL : 0 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
    exact ⟨mul_nonneg hL ht.1, by nlinarith [ht.2]⟩
  · rintro _ ⟨p, hp, rfl⟩
    rw [hU.canonicalLowerPath_placement, mul_zero]
    exact hU.canonicalPlacement_start_mem hp.1
  · rintro _ ⟨p, hp, rfl⟩
    rw [hU.canonicalLowerPath_placement, mul_one]
    exact hU.canonicalPlacement_finish_mem hp.1

/-- The ordinary rational area theorem now applies to the literal cap
survivor after its actual nonempty-fiber inequality has been established. -/
theorem IsDownwardCap.volumeReal_oneTurnSurvivor_le {U : Set Plane} (hU : IsDownwardCap U)
    (hfit : ∀ x ∈ horizontalProjection U, sweptNiche U (Real.pi / 2) x ≤ capRoof U x) :
    volume.real (oneTurnSurvivor U) ≤ (22199 : ℝ) / 10000 :=
  volumeReal_le_ordinaryBound_of_lowerPassage hU.isCompact_oneTurnSurvivor
    (hU.isConnected_oneTurnSurvivor hfit) hU.oneTurnSurvivor_lowerPassage

end AmbidextrousSofa
