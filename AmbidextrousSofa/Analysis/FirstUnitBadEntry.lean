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

open scoped ActualPair

theorem FirstUnitSetting.first_bad_after_middle {C h α β η τ : ℝ}
    (P : FirstUnitSetting U m ρ C h) (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (hβ : β ∈ Icc (0 : ℝ) (Real.pi / 2)) (hβx : (B β).1 = C)
    (hτ : τ ∈ Ioo α η) (hpτ : p τ = -1) (hpfirst : ∀ t ∈ Ico α τ, -1 < p t)
    (hprefix : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) τ), v t ≤ 1) :
    β < τ ∧ q τ ≤ 1 / 4 ∧
      (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), 1 < v t → q t ≤ 1 / 4) := by
  obtain ⟨Dyn, hshadow⟩ := P.corner_dynamics hU hm haffine hρ hρ0 hρK heq
  have hαβ := hphase.first_lt_of_first_neg hβ
    (P.first_momentum_neg_after_middle hU hm haffine hρ hρ0 hρK heq hβ hβx.ge).2
  obtain ⟨hcore, hcharged⟩ := P.ae_first_density_ge_on_prefix hU hm haffine hρ hρ0 hρK heq
    hphase hτ.2.le hprefix hβ hβx
  obtain ⟨hβτ, hqτ⟩ := Dyn.first_bad_after_window_and_height_bound hphase hαβ hτ hpτ hpfirst
    P.hunit hcharged (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hαβ.le le_rfl) hcore)
  refine ⟨hβτ, hqτ, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Ioo).mp hprefix), hshadow]
    with t ht hpref hs hv
  rcases lt_or_ge t τ with htτ | htτ
  · exact absurd (hpref ⟨ht.1, htτ⟩) hv.not_ge
  rcases le_or_gt t η with htη | htη
  · linarith only [(Dyn.first_bad_future_bounds hphase hτ hpτ t ⟨htτ, htη⟩).2, hqτ, htτ]
  obtain ⟨hp, hq⟩ := hphase.final_signs t ⟨htη, ht.2.le⟩
  linarith only [(hs.2 hp hq).1, hv]

end ActualPair

end AmbidextrousSofa
