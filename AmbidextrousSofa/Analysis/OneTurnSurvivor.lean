module

public import AmbidextrousSofa.Analysis.EndpointPressure
public import AmbidextrousSofa.Analysis.OrdinarySofaBound
public import AmbidextrousSofa.Topology.VerticalRegion

@[expose] public section

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

theorem IsDownwardCap.continuous_sweptNiche_pi_div_two {U : Set Plane}
    (hU : IsDownwardCap U) : Continuous (sweptNiche U (Real.pi / 2)) :=
  funext hU.partialBarrier_pi_div_two ▸ hU.continuous_partialBarrier_pi_div_two

theorem IsDownwardCap.oneTurnSurvivor_eq_verticalIntervalRegion {U : Set Plane}
    (hU : IsDownwardCap U) :
    oneTurnSurvivor U = verticalIntervalRegion (horizontalProjection U)
      (sweptNiche U (Real.pi / 2)) (capRoof U) := by
  ext p
  have := sweptNiche_nonneg U (Real.pi / 2) p.1
  simp only [oneTurnSurvivor, mem_ofPred_eq, hU.mem_iff_projection_and_roof,
    mem_verticalIntervalRegion]
  grind

/-- The canonical supports of the original cap define an actual rigid path,
even if some support contacts are not retained in the niche-cut body. -/
def IsDownwardCap.canonicalLowerPath {U : Set Plane} (hU : IsDownwardCap U) : RigidMotionPath where
  angle := fun t => -(Real.pi / 2 * t)
  shift := fun t => (1 - support U (unitNormal (Real.pi / 2 * t)),
    1 - support U (companionNormal (Real.pi / 2 * t)))
  continuous_angle := by fun_prop
  continuous_shift := by
    have := continuous_support hU.isCompact
    have := continuous_unitNormal
    have := continuous_companionNormal
    fun_prop

theorem IsDownwardCap.canonicalLowerPath_placement {U : Set Plane} (hU : IsDownwardCap U)
    (t : ℝ) (p : Plane) :
    hU.canonicalLowerPath.placement t p = canonicalPlacement U (Real.pi / 2 * t) p :=
  (canonicalPlacement_eq_rigidMap U _ p).symm

/-- Every point of the actual survivor follows this same complete passage.
The roof-fit hypothesis is needed for connectedness, not for containment
in the moving corridors. -/
theorem IsDownwardCap.oneTurnSurvivor_lowerPassage {U : Set Plane} (hU : IsDownwardCap U) :
    Passage (oneTurnSurvivor U) lowerHall incomingArm lowerOutgoingArm hU.canonicalLowerPath := by
  have hy {p : Plane} (hp : p ∈ U) : support U (0, 1) - 1 ≤ p.2 := by
    linarith [(hU.inStrip hp).1, hU.support_upward_le_one]
  refine ⟨fun t ht => ?_, ?_, ?_⟩ <;> rintro _ ⟨p, ⟨hp, hn⟩, rfl⟩ <;>
    rw [hU.canonicalLowerPath_placement]
  · rw [canonicalPlacement_mem_lowerHall_iff, mem_canonicalHall]
    refine ⟨coordDot_le_support hU.isCompact hp _, coordDot_le_support hU.isCompact hp _, ?_⟩
    rcases ht.1.eq_or_lt with rfl | h0
    · right; simpa [companionNormal, coordDot] using hy hp
    rcases ht.2.eq_or_lt with rfl | h1
    · left; simpa [unitNormal, coordDot] using hy hp
    have hθ : Real.pi / 2 * t ∈ Ioo 0 (Real.pi / 2) :=
      ⟨mul_pos (by positivity) h0, mul_lt_of_lt_one_right (by positivity) h1⟩
    exact (cornerWall_le_iff (sin_cos_pos_of_mem_quarter hθ).1
      (sin_cos_pos_of_mem_quarter hθ).2).mp
      ((cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact le_rfl p.1) hθ).trans hn)
  all_goals
    have := hy hp
    have := coordDot_le_support hU.isCompact hp (1, 0)
    have := coordDot_le_support hU.isCompact hp (-1, 0)
    have := coordDot_le_support hU.isCompact hp (0, 1)
    simp [canonicalPlacement, unitNormal, companionNormal, coordDot, incomingArm,
      lowerOutgoingArm] at *
    refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- The ordinary rational area theorem now applies to the literal cap
survivor after its actual nonempty-fiber inequality has been established. -/
theorem IsDownwardCap.volumeReal_oneTurnSurvivor_le {U : Set Plane} (hU : IsDownwardCap U)
    (hfit : ∀ x ∈ horizontalProjection U, sweptNiche U (Real.pi / 2) x ≤ capRoof U x) :
    volume.real (oneTurnSurvivor U) ≤ (22199 : ℝ) / 10000 :=
  volumeReal_le_ordinaryBound_of_lowerPassage
    (hU.isCompact.inter_right (isClosed_le
      (hU.continuous_sweptNiche_pi_div_two.comp continuous_fst) continuous_snd))
    (hU.oneTurnSurvivor_eq_verticalIntervalRegion ▸ isConnected_verticalIntervalRegion
      ((hU.convex.isConnected hU.nonempty).image _ continuous_fst.continuousOn)
      hU.continuous_sweptNiche_pi_div_two.continuousOn hU.continuousOn_capRoof hfit)
    hU.oneTurnSurvivor_lowerPassage

end AmbidextrousSofa
