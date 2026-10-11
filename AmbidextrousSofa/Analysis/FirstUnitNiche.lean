module

public import AmbidextrousSofa.Analysis.FirstUnitTangency
public import AmbidextrousSofa.Analysis.CompanionZero

@[expose] public section

/-!
# Actual first-unit niche contact

The full first-wall envelope is obtained from the monotone actual first
tangent. At every interior angle the first wall passes through the first
tangent point, and the original companion wall lies above it by at least
the negative first momentum; the literal left cut, whose wall is below
the original wall, supplies this slack. Thus a nonpositive first momentum
makes the first tangent point a niche contact.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

open scoped ActualPair

theorem fullTiltedSupportQuarterPair_cut_wall_eq_scalar (t x : ℝ) :
    secondWall V t x = ((F).g t - 1 + x * Real.sin t) / Real.cos t := by
  simp only [secondWall, companionNormal_eq_unitNormal]
  rfl

/-- At an interior angle the first wall passes through the first tangent point, and the
original companion wall over it is higher by at least `-p / cos`. -/
theorem fullTiltedSupportQuarterPair_first_wall_tangency {t : ℝ}
    (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    firstWall U t (B t).1 = (B t).2 ∧
      -p t ≤ (secondWall U t (B t).1 - (B t).2) * Real.cos t := by
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ht
  refine ⟨fullTiltedSupportQuarterPair_first_tangency hU hm haffine hρ hρ0 hρK heq
    ⟨ht.1.le, ht.2⟩ ▸ firstWall_firstTangency U hs.ne', ?_⟩
  have hgap : (secondWall V t (B t).1 - (B t).2) * Real.cos t = -p t := by
    rw [fullTiltedSupportQuarterPair_cut_wall_eq_scalar hU hm haffine hρ hρ0 hρK heq, sub_mul,
      div_mul_cancel₀ _ hc.ne']
    dsimp only [firstTangentPoint, Reference.supportPoint, supportP]
    linear_combination (-(F).fD t) * Real.sin_sq_add_cos_sq t
  linarith [mul_le_mul_of_nonneg_right (secondWall_mono (leftCompanionCap_subset _ _)
    hU.isCap_fullLeftCompanion.nonempty hU.isCap.isCompact hc (B t).1) hc.le]

theorem fullTiltedSupportQuarterPair_first_wall_envelope
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1)
    {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    ∀ s ∈ Ioo (0 : ℝ) (Real.pi / 2), firstWall U s (B t).1 ≤ (B t).2 := by
  have hmatch (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) (Real.pi / 2)) : B s = firstTangency U s :=
    fullTiltedSupportQuarterPair_first_tangency hU hm haffine hρ hρ0 hρK heq ⟨hs.1.le, hs.2⟩
  have horder := (fullTiltedSupportQuarterPair_first_tangent_order
    hU hm haffine hρ hρ0 hρK heq hunit).1
  have hmono : MonotoneOn (fun s => (firstTangency U s).1) (Ioo 0 (Real.pi / 2)) :=
    fun s hs r hr hsr => by
      simpa only [hmatch s hs, hmatch r hr] using
        horder (Ioo_subset_Icc_self hs) (Ioo_subset_Icc_self hr) hsr
  intro s hs
  simpa only [hmatch t ht] using firstWall_le_at_firstTangency U hmono
    (fun s hs x => hU.isCap.hasDerivAt_firstWall_of_open_first_density hρ hρ0 hρK heq
      (firstQuarter_subset_regularCurvatureDomain_of_nonneg hm) hs x) hs ht

theorem fullTiltedSupportQuarterPair_niche_first_tangency
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1)
    {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2))
    (hp : p t ≤ 0) (hy : 0 ≤ (B t).2) :
    sweptNiche U (Real.pi / 2) (B t).1 = (B t).2 := by
  obtain ⟨hfirst, hgap⟩ := fullTiltedSupportQuarterPair_first_wall_tangency
    hU hm haffine hρ hρ0 hρK heq ht
  -- The companion wall lies above the first tangency, so the first wall is the corner wall.
  have hcorner : cornerWall U t (B t).1 = (B t).2 := by
    rw [cornerWall, hfirst, min_eq_left (sub_nonneg.mp ((mul_nonneg_iff_of_pos_right
      (sin_cos_pos_of_mem_quarter ht).2).mp ((neg_nonneg.mpr hp).trans hgap)))]
  refine le_antisymm (sweptNiche_le_of_forall (by positivity) hy fun s hs =>
    (min_le_left _ _).trans (fullTiltedSupportQuarterPair_first_wall_envelope
      hU hm haffine hρ hρ0 hρK heq hunit ht s hs)) ?_
  rw [← hcorner]
  exact cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCap.isCompact le_rfl _) ht

end ActualPair

end AmbidextrousSofa
