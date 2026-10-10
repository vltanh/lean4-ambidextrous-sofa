module

public import AmbidextrousSofa.Analysis.FirstUnitProjection

@[expose] public section

/-!
# Literal tangent displacements and the four first-unit moments

All four moments follow from the absolutely continuous coordinates of
the actual support pair. The initial companion moment uses its first
floor abscissa, which is allowed to differ from the global circle
minimum. The exact selected top projection supplies the inequality
between these two abscissae.
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

local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
set_option quotPrecheck false in
local notation "B" => firstTangentPoint (F).f (F).fD
set_option quotPrecheck false in
local notation "D" => secondTangentPoint (F).g (F).gD
local notation "v" => (fun t : ℝ => leftCompanionWingDensity m ρ (t + Real.pi / 2))
local notation "V" => leftCompanionCap U (horizontalLeft U + capWidth U / 4)

theorem fullTiltedSupportQuarterPair_tangent_displacements {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2) :
    (∫ t in a..b, (1 - ρ t) * Real.sin t) = (B b).1 - (B a).1 ∧
      (∫ t in a..b, (1 - ρ t) * Real.cos t) = (B a).2 - (B b).2 ∧
      (∫ t in a..b, (1 - v t) * Real.cos t) = (D b).1 - (D a).1 ∧
      (∫ t in a..b, (1 - v t) * Real.sin t) = (D b).2 - (D a).2 := by
  obtain ⟨hBx, hBy, hDx, hDy, hderiv⟩ :=
    fullTiltedSupportQuarterPair_tangent_calculus hU hm haffine hρ hρ0 hρK heq
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hsub : uIcc a b ⊆ uIcc 0 (Real.pi / 2) := by
    simpa only [uIcc_of_le hab, uIcc_of_le hL] using Icc_subset_Icc ha hb
  have hd := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo ha hb) hderiv
  refine ⟨integral_eq_sub_of_ac_of_ae_hasDerivAt hab (hBx.mono hsub)
    (hd.mono fun _ ht => ht.1), ?_,
    integral_eq_sub_of_ac_of_ae_hasDerivAt hab (hDx.mono hsub)
      (hd.mono fun _ ht => ht.2.2.1),
    integral_eq_sub_of_ac_of_ae_hasDerivAt hab (hDy.mono hsub)
      (hd.mono fun _ ht => ht.2.2.2)⟩
  have hneg : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt (fun s => -(B s).2) ((1 - ρ t) * Real.cos t) t := by
    filter_upwards [hd] with t ht
    exact ht.2.1.neg.congr_deriv (by ring)
  have h := integral_eq_sub_of_ac_of_ae_hasDerivAt hab (hBy.neg.mono hsub) hneg
  convert h using 1 <;> ring

/-- The first-unit hypothesis identifies the right middle niche height
with the actual first tangent height. No moment identity is supplied as
an assumption. -/
theorem fullTiltedSupportQuarterPair_first_floor_right_moments {C h β γ : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hmpos : 0 < m) (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1)
    (hβ : β ∈ Ioo 0 (Real.pi / 2)) (hγ : γ ∈ Icc 0 (Real.pi / 2))
    (hβx : (B β).1 = C) (hβp : supportP (F).fD (F).g β ≤ 0)
    (hγy : (D γ).2 = 0) :
    (∫ t in 0..γ, (1 - v t) * Real.cos t) = C + (D γ).1 ∧
      (∫ t in 0..γ, (1 - v t) * Real.sin t) = h ∧
      (∫ t in β..(Real.pi / 2), (1 - ρ t) * Real.sin t) =
        (MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C ∧
      (∫ t in β..(Real.pi / 2), (1 - ρ t) * Real.cos t) =
        sweptNiche U (Real.pi / 2) C := by
  obtain ⟨_hB0, hBL, hD0, _hDL, _hpL, _hqL⟩ :=
    fullTiltedSupportQuarterPair_tangent_traces hU hm haffine hρ hρ0 hρK heq
      hl hr hmpos hheight hlow
  have horder := (fullTiltedSupportQuarterPair_first_tangent_order
    hU hm haffine hρ hρ0 hρK heq hunit).2
  have hy := horder (Ioo_subset_Icc_self hβ)
    ⟨by positivity, le_rfl⟩ hβ.2.le
  rw [hBL] at hy
  have hniche := fullTiltedSupportQuarterPair_niche_first_tangency
    hU hm haffine hρ hρ0 hρK heq hunit hβ hβp hy
  rw [hβx] at hniche
  have hleft := fullTiltedSupportQuarterPair_tangent_displacements
    hU hm haffine hρ hρ0 hρK heq le_rfl hγ.1 hγ.2
  have hright := fullTiltedSupportQuarterPair_tangent_displacements
    hU hm haffine hρ hρ0 hρK heq hβ.1.le hβ.2.le le_rfl
  rw [hD0, hγy] at hleft
  rw [hBL, hβx] at hright
  refine ⟨?_, ?_, hright.1, ?_⟩
  · simpa only [Prod.fst, sub_neg_eq_add, add_comm] using hleft.2.2.1
  · simpa only [Prod.snd, sub_neg_eq_add, zero_add] using hleft.2.2.2
  · simpa only [Prod.snd, sub_zero, hniche] using hright.2.1

/-- Every actual companion floor contact is to the right of the global
low-wing zero. The selected top identity and source-point box give the
three displacement inequalities needed by the final energy argument. -/
theorem fullTiltedSupportQuarterPair_floor_abscissa_bounds {C h γ : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh0 : 0 < h) (hh1 : h < 17 / 50)
    (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1)
    (htop : C < (MovingSofaOptimality.vminus U (Real.pi / 2)).1)
    (hγ : γ ∈ Ioo 0 (Real.pi / 2)) (hγy : (D γ).2 = 0) :
    (MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C ≤ C + (D γ).1 ∧
      C + (D γ).1 ≤ 1 ∧ (MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C ≤ C := by
  have hmid : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]
    congr 1 <;> ring
  have haff := haffine
  rw [hmid] at haff
  have hj : horizontalLeft U + capWidth U / 4 = -C := by
    unfold capWidth
    rw [hl, hr]
    ring
  have hprojection := hU.firstUnit_top_projection_eq hl hr hC0 hC1 hh0 hh1 hheight
    haff hlow hhigh hρ hρ0 hρK heq hunit
  have hzeroPos : 0 < C + companionZero (leftCompanionCap U (-C)) := by
    by_contra hnot
    rw [max_eq_right (le_of_not_gt hnot)] at hprojection
    linarith only [hprojection, htop]
  rw [max_eq_left hzeroPos.le] at hprojection
  have hc : 0 < Real.cos γ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [hγ.1, Real.pi_pos], hγ.2⟩
  have hwall := fullTiltedSupportQuarterPair_companion_wall_second_tangency
    hU hm haffine hρ hρ0 hρK heq hc.ne'
  have hz : companionZero V ≤ (D γ).1 := by
    by_contra hnot
    have hnegative := hU.isCap_fullLeftCompanion.secondWall_neg_of_lt_companionZero
      (lt_of_not_ge hnot) hγ
    rw [hwall, hγy] at hnegative
    exact lt_irrefl 0 hnegative
  rw [hj] at hz
  have hright := (hU.isCap.fst_mem_Icc
    (MovingSofaOptimality.vminus_mem_edge hU.isCap.imported_isConvexBody (Real.pi / 2)).1).2
  rw [hr] at hright
  refine ⟨?_, fullTiltedSupportQuarterPair_second_tangency_abscissa_le
    hU hm haffine hρ hρ0 hρK heq hl hr (Ioo_subset_Icc_self hγ), ?_⟩
  · linarith only [hprojection, hz]
  · linarith only [hright]

end ActualPair

end AmbidextrousSofa
