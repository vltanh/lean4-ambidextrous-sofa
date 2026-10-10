import AmbidextrousSofa.Analysis.FirstUnitTangency
import AmbidextrousSofa.Analysis.CompanionZero

/-!
# Actual first-unit niche contact and first companion floor crossing

The full first-wall envelope is obtained from the monotone actual first
tangent. A nonpositive first momentum supplies companion slack using the
literal left cut, whose wall is below the original wall. The first zero
of the companion tangent height is constructed independently of any
contact-phase decomposition. Its abscissa is above the actual low-wing
circle minimum and at most one unit from the left middle endpoint.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
local notation "B" => firstTangentPoint F.f F.fD
local notation "D" => secondTangentPoint F.g F.gD
local notation "p" => supportP F.fD F.g
local notation "V" => leftCompanionCap U (horizontalLeft U + capWidth U / 4)

theorem fullTiltedSupportQuarterPair_companion_wall_first_tangency_gap {t : ℝ}
    (hc : Real.cos t ≠ 0) :
    (secondWall V t (B t).1 - (B t).2) * Real.cos t = -p t := by
  have hg : support V (companionNormal t) = F.g t := by
    change support V (companionNormal t) = angleSupport V (t + Real.pi / 2)
    rw [angleSupport, companionNormal_eq_unitNormal]
  rw [sub_mul, secondWall, div_mul_cancel₀ _ hc, hg]
  dsimp only [firstTangentPoint, Reference.supportPoint, supportP]
  have hcircle := congrArg (fun r : ℝ => F.fD t * r) (Real.sin_sq_add_cos_sq t)
  nlinarith only [hcircle]

theorem fullTiltedSupportQuarterPair_companion_wall_second_tangency {t : ℝ}
    (hc : Real.cos t ≠ 0) : secondWall V t (D t).1 = (D t).2 := by
  have hg : support V (companionNormal t) = F.g t := by
    change support V (companionNormal t) = angleSupport V (t + Real.pi / 2)
    rw [angleSupport, companionNormal_eq_unitNormal]
  rw [secondWall, div_eq_iff hc, hg, secondTangentPoint, companionSupportPoint_coordinates]
  have hcircle := congrArg (fun r : ℝ => (F.g t - 1) * r) (Real.sin_sq_add_cos_sq t)
  dsimp only [Prod.fst, Prod.snd]
  nlinarith only [hcircle]

theorem fullTiltedSupportQuarterPair_first_wall_envelope
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1)
    {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    ∀ s ∈ Ioo (0 : ℝ) (Real.pi / 2), firstWall U s (B t).1 ≤ (B t).2 := by
  have hmatch (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) (Real.pi / 2)) : B s = firstTangency U s :=
    fullTiltedSupportQuarterPair_first_tangency hU hm haffine hρ hρ0 hρK heq ⟨hs.1.le, hs.2⟩
  have horder := (fullTiltedSupportQuarterPair_first_tangent_order
    hU hm haffine hρ hρ0 hρK heq hunit).1
  have hmono : MonotoneOn (fun s => (firstTangency U s).1) (Ioo 0 (Real.pi / 2)) := by
    intro s hs r hr hsr
    simpa only [hmatch s hs, hmatch r hr] using
      horder (Ioo_subset_Icc_self hs) (Ioo_subset_Icc_self hr) hsr
  have hwall := fun s hs x => hU.isCap.hasDerivAt_firstWall_of_open_first_density
    hρ hρ0 hρK heq (firstQuarter_subset_regularCurvatureDomain_of_nonneg hm) hs x
  intro s hs
  simpa only [hmatch t ht] using firstWall_le_at_firstTangency U hmono hwall hs ht

theorem fullTiltedSupportQuarterPair_niche_first_tangency
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1)
    {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2))
    (hp : p t ≤ 0) (hy : 0 ≤ (B t).2) :
    sweptNiche U (Real.pi / 2) (B t).1 = (B t).2 := by
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])).ne'
  have hgap := fullTiltedSupportQuarterPair_companion_wall_first_tangency_gap
    hU hm haffine hρ hρ0 hρK heq hc.ne'
  have hcut : (B t).2 ≤ secondWall V t (B t).1 := by
    have hprod : 0 ≤ (secondWall V t (B t).1 - (B t).2) * Real.cos t := by
      rw [hgap]
      exact neg_nonneg.mpr hp
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hc).mp hprod)
  have hsecond : (B t).2 ≤ secondWall U t (B t).1 := hcut.trans
    (secondWall_mono (leftCompanionCap_subset _ _) hU.isCap_fullLeftCompanion.nonempty
      hU.isCap.isCompact hc _)
  have hmatch := fullTiltedSupportQuarterPair_first_tangency
    hU hm haffine hρ hρ0 hρK heq ⟨ht.1.le, ht.2⟩
  have hfirst : firstWall U t (B t).1 = (B t).2 := by
    rw [hmatch]
    exact firstWall_firstTangency U hs
  have hcorner : cornerWall U t (B t).1 = (B t).2 := by
    rw [cornerWall, hfirst, min_eq_left hsecond]
  apply le_antisymm
  · apply sweptNiche_le_of_forall (by linarith only [Real.pi_pos]) hy
    intro s hs
    exact (min_le_left _ _).trans (fullTiltedSupportQuarterPair_first_wall_envelope
      hU hm haffine hρ hρ0 hρK heq hunit ht s hs)
  · rw [← hcorner]
    exact cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCap.isCompact le_rfl _) ht

/-- The abscissa bound uses only membership of the actual low-wing
support point in the cut cap, and therefore remains true through folds. -/
theorem fullTiltedSupportQuarterPair_second_tangency_abscissa_le {C t : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (ht : t ∈ Icc 0 (Real.pi / 2)) : C + (D t).1 ≤ 1 := by
  have hpoint := (fullTiltedSupportQuarterPair_points_mem
    hU hm haffine hρ hρ0 hρK heq).2 t ht
  have hx : (Reference.companionSupportPoint F.g F.gD t).1 ≤
      horizontalLeft U + capWidth U / 4 := hpoint.2.2
  have hj : horizontalLeft U + capWidth U / 4 = -C := by
    unfold capWidth
    rw [hl, hr]
    ring
  rw [hj] at hx
  have hD : (D t).1 = (Reference.companionSupportPoint F.g F.gD t).1 + Real.sin t := by
    rw [secondTangentPoint, companionSupportPoint_coordinates,
      companionSupportPoint_coordinates]
    dsimp only [Prod.fst]
    ring
  rw [hD]
  linarith only [hx, Real.sin_le_one t]

theorem fullTiltedSupportQuarterPair_first_floor_crossing {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hmpos : 0 < m) (hheight : capHeight U = 1)
    (hh : 0 < h) (hlow : capRoof U (-C) = 1 - h) :
    ∃ γ ∈ Ioo 0 (Real.pi / 2),
      (D γ).2 = 0 ∧ (∀ t ∈ Ico 0 γ, (D t).2 < 0) ∧
      companionZero V ≤ (D γ).1 ∧ C + (D γ).1 ≤ 1 := by
  have hL : (0 : ℝ) < Real.pi / 2 := by positivity
  obtain ⟨_hB0, _hBL, hD0, hDL, _hpL, _hqL⟩ :=
    fullTiltedSupportQuarterPair_tangent_traces hU hm haffine hρ hρ0 hρK heq
      hl hr hmpos hheight hlow
  obtain ⟨_hBx, _hBy, _hDx, hDy, _hderiv⟩ :=
    fullTiltedSupportQuarterPair_tangent_calculus hU hm haffine hρ hρ0 hρK heq
  have heL := (hU.endpoint_heights_pos_of_affine hheight ⟨m, c, haffine⟩).2
  have hcont : ContinuousOn (fun t => -(D t).2) (Icc 0 (Real.pi / 2)) := by
    simpa only [uIcc_of_le hL.le] using hDy.continuousOn.neg
  obtain ⟨γ, hγ, heqγ, hbefore⟩ := exists_first_level_crossing hL hcont
    (show (0 : ℝ) < -(D 0).2 by simpa only [hD0, neg_neg] using hh)
    (show -(D (Real.pi / 2)).2 ≤ 0 by simpa only [hDL] using neg_nonpos.mpr heL.le)
  have hγy : (D γ).2 = 0 := by linarith only [heqγ]
  have hγL : γ < Real.pi / 2 := by
    apply lt_of_le_of_ne hγ.2
    intro heq
    rw [heq, hDL] at hγy
    exact heL.ne' hγy
  have hγq : γ ∈ Ioo 0 (Real.pi / 2) := ⟨hγ.1, hγL⟩
  have hγc : 0 < Real.cos γ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [hγ.1, Real.pi_pos], hγL⟩
  have hwall := fullTiltedSupportQuarterPair_companion_wall_second_tangency
    hU hm haffine hρ hρ0 hρK heq hγc.ne'
  have hzero : companionZero V ≤ (D γ).1 := by
    by_contra hnot
    have hnegative := hU.isCap_fullLeftCompanion.secondWall_neg_of_lt_companionZero
      (lt_of_not_ge hnot) hγq
    rw [hwall, hγy] at hnegative
    exact lt_irrefl 0 hnegative
  refine ⟨γ, hγq, hγy, ?_, hzero,
    fullTiltedSupportQuarterPair_second_tangency_abscissa_le
      hU hm haffine hρ hρ0 hρK heq hl hr ⟨hγ.1.le, hγ.2⟩⟩
  intro t ht
  have h := hbefore t ht
  linarith only [h]

end ActualPair

end AmbidextrousSofa
