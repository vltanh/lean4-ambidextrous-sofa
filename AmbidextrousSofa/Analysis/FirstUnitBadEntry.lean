module

public import AmbidextrousSofa.Analysis.FirstUnitPhases
public import AmbidextrousSofa.Analysis.FirstUnitPrefixEnergy
public import AmbidextrousSofa.Analysis.CoreSourceLowerBounds

@[expose] public section

/-!
# Actual ordered first-bad-entry estimates

The literal source pieces supply both lower laws used by the prefix
energy estimate. Thus the first possible companion excess occurs after
the actual middle crossing, with second momentum at most one quarter.
The ordered phases then carry that bound to every later excess point.
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
local notation "p" => supportP (F).fD (F).g
local notation "q" => supportQ (F).gD (F).f
local notation "v" => (fun t : ℝ => leftCompanionWingDensity m ρ (t + Real.pi / 2))
local notation "B" => firstTangentPoint (F).f (F).fD

theorem fullTiltedSupportQuarterPair_first_bad_after_middle {C h α β η τ : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50)
    (hmpos : 0 < m) (hsmall : C + m < 1) (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1)
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (hβ : β ∈ Icc (0 : ℝ) (Real.pi / 2)) (hβx : (B β).1 = C)
    (hτ : τ ∈ Ioo α η) (hpτ : p τ = -1)
    (hpfirst : ∀ t ∈ Ico α τ, -1 < p t)
    (hprefix : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) τ), v t ≤ 1) :
    α < β ∧ β < τ ∧ q τ ≤ 1 / 4 ∧
      (∀ t ∈ Icc α β, (p t - 1) ^ 2 + (q t + 1) ^ 2 ≤ 5) ∧
      (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), 1 < v t → q t ≤ 1 / 4) := by
  have hC : 0 < C := by linarith only [hC0]
  have D := fullTiltedSupportQuarterPair_cornerArcDynamics
    hU hm haffine hρ hρ0 hρK heq hl hr hC hsmall hheight hhigh hκ
  have hαβ := hphase.first_lt_of_first_neg hβ
    (fullTiltedSupportQuarterPair_first_momentum_neg_after_middle
      hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh hlow hβ (by rw [hβx])).2
  have hτcc : τ ∈ Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨(hphase.first_mem.1.trans hτ.1).le, hτ.2.le.trans hphase.second_mem.2.le⟩
  have hsign : ∀ t ∈ Ioo α τ, p t < 0 ∧ 0 < q t :=
    fun t ht => hphase.core_signs t ⟨ht.1, ht.2.trans hτ.2⟩
  have hcore := fullTiltedSupportQuarterPair_ae_first_density_ge_core_on_prefix
    hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh hmpos hheight hlow hhigh
    hunit hphase.first_mem.1.le hτcc hphase.first_zero hsign hprefix
  have hcharged : ∀ᵐ t ∂volume.restrict (Ioo α τ), t < β → 1 + q t ≤ 2 * ρ t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae
      ((ae_restrict_iff' measurableSet_Ioo).mp
        (fullTiltedSupportQuarterPair_ae_first_density_ge_charged_on_prefix
          hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh hmpos hheight hlow hhigh
          hunit hphase.first_mem.1.le hτcc hphase.first_zero hsign hprefix hβ hβx))]
      with t ht hc htβ using hc ⟨ht.1, lt_min htβ ht.2⟩
  obtain ⟨hβτ, hqτ, henergy⟩ := D.first_bad_after_window_and_height_bound
    hphase hαβ hτ hpτ hpfirst hunit hcharged
    (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hαβ.le le_rfl) hcore)
  refine ⟨hαβ, hβτ, hqτ, henergy, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Ioo).mp hprefix),
    hU.fullTiltedSupportQuarterPair_source_controls hl hr hC hm hsmall hheight haffine hhigh
      hρ hρ0 hρK hκ heq] with t ht hpref hs hv
  rcases lt_or_ge t τ with htτ | htτ
  · exact absurd (hpref ⟨ht.1, htτ⟩) hv.not_ge
  rcases le_or_gt t η with htη | htη
  · linarith only [(D.first_bad_future_bounds hphase hτ hpτ t ⟨htτ, htη⟩).2, hqτ, htτ]
  obtain ⟨hp, hq⟩ := hphase.final_signs t ⟨htη, ht.2.le⟩
  linarith only [(hs.2.2.2 hp hq).1, hv]

end ActualPair

end AmbidextrousSofa
