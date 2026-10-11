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
set_option quotPrecheck false
local notation "B" => firstTangentPoint (F).f (F).fD
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
  have hsub : uIcc a b ⊆ uIcc 0 (Real.pi / 2) :=
    uIcc_subset_uIcc (mem_uIcc_of_le ha (hab.trans hb)) (mem_uIcc_of_le (ha.trans hab) hb)
  have hd := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo ha hb) hderiv
  have hBy' : (∫ t in a..b, (1 - ρ t) * Real.cos t) = _ :=
    integral_eq_sub_of_ac_of_ae_hasDerivAt hab (hBy.neg.mono hsub)
      (hd.mono fun _ ht => ht.2.1.neg.congr_deriv (by ring))
  refine ⟨integral_eq_sub_of_ac_of_ae_hasDerivAt hab (hBx.mono hsub) (hd.mono fun _ ht => ht.1),
    hBy'.trans (by simp only [Pi.neg_apply]; ring),
    integral_eq_sub_of_ac_of_ae_hasDerivAt hab (hDx.mono hsub) (hd.mono fun _ ht => ht.2.2.1),
    integral_eq_sub_of_ac_of_ae_hasDerivAt hab (hDy.mono hsub) (hd.mono fun _ ht => ht.2.2.2)⟩

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
  obtain ⟨-, hBL, hD0, -⟩ := fullTiltedSupportQuarterPair_tangent_traces
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hheight hlow
  have hy : 0 ≤ (B β).2 := by
    simpa only [hBL] using (fullTiltedSupportQuarterPair_first_tangent_order
      hU hm haffine hρ hρ0 hρK heq hunit).2 (Ioo_subset_Icc_self hβ) ⟨by positivity, le_rfl⟩
      hβ.2.le
  have hniche := fullTiltedSupportQuarterPair_niche_first_tangency
    hU hm haffine hρ hρ0 hρK heq hunit hβ hβp hy
  obtain ⟨-, -, hS, hh⟩ := fullTiltedSupportQuarterPair_tangent_displacements
    hU hm haffine hρ hρ0 hρK heq le_rfl hγ.1 hγ.2
  obtain ⟨hT, hz, -⟩ := fullTiltedSupportQuarterPair_tangent_displacements
    hU hm haffine hρ hρ0 hρK heq hβ.1.le hβ.2.le le_rfl
  rw [hD0] at hS hh
  rw [hBL, hβx] at hT
  rw [hBL, ← hniche, hβx] at hz
  refine ⟨hS.trans ?_, hh.trans ?_, hT, hz.trans ?_⟩ <;> simp only [hγy] <;> ring

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
  have hprojection := hU.firstUnit_top_projection_eq hl hr hC0 hC1 hh0 hh1 hheight
    (fun x hx => haffine x ⟨by linarith only [hx.1, hl, hr], by linarith only [hx.2, hl, hr]⟩)
    hlow hhigh hρ hρ0 hρK heq hunit
  have hwall := fullTiltedSupportQuarterPair_companion_wall_second_tangency
    hU hm haffine hρ hρ0 hρK heq (Real.cos_pos_of_mem_Ioo
      ⟨by linarith only [hγ.1, Real.pi_pos], hγ.2⟩).ne'
  have hz : companionZero V ≤ (D γ).1 := not_lt.mp fun h => by
    linarith only [hU.isCap_fullLeftCompanion.secondWall_neg_of_lt_companionZero h hγ, hwall, hγy]
  rw [show horizontalLeft U + capWidth U / 4 = -C by rw [capWidth, hl, hr]; ring] at hz
  have hright := (hU.isCap.fst_mem_Icc
    (MovingSofaOptimality.vminus_mem_edge hU.isCap.imported_isConvexBody (Real.pi / 2)).1).2
  refine ⟨?_, fullTiltedSupportQuarterPair_second_tangency_abscissa_le
    hU hm haffine hρ hρ0 hρK heq hl hr (Ioo_subset_Icc_self hγ),
    by linarith only [hright, hr]⟩
  rcases max_choice (C + companionZero (leftCompanionCap U (-C))) 0 with h | h <;>
    rw [h] at hprojection <;> linarith only [hprojection, htop, hz]

end ActualPair

end AmbidextrousSofa
