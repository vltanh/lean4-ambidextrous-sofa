module

public import AmbidextrousSofa.Analysis.FirstUnitBadEntry

@[expose] public section

/-!
# Choosing the actual first-unit events

After the sign changes, the first middle crossing and the first possible
companion excess are chosen from the actual closed support pair. Their
ordering and the one-quarter excess height are conclusions. No event
time or source occupation is supplied to this selector.
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

theorem FirstUnitSetting.exists_firstUnit_events {C h α η : ℝ}
    (P : FirstUnitSetting U m ρ C h) (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    ∃ β, α < β ∧ β ∈ Ioo (0 : ℝ) (Real.pi / 2) ∧ (B β).1 = C ∧
      (∀ t ∈ Ico (0 : ℝ) β, (B t).1 < C) ∧ (∀ t ∈ Icc β (Real.pi / 2), C ≤ (B t).1) ∧
      3 / 5 ≤ Real.sin β ∧
      ((∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), v t ≤ 1) ∨
        ∃ τ ∈ Ioo β η, p τ = -1 ∧ q τ ≤ 1 / 4 ∧
          (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) τ), v t ≤ 1) ∧
          (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), 1 < v t → q t ≤ 1 / 4)) := by
  obtain ⟨β, hβ, hβx, hbefore, hafter, hβsin, hβp⟩ :=
    P.exists_first_middle_crossing hU hm haffine hρ hρ0 hρK heq
      (by linarith only [(P.top_overhang hU hm haffine hρ hρ0 hρK heq).1])
  obtain ⟨Dyn, hshadow⟩ := P.corner_dynamics hU hm haffine hρ hρ0 hρK heq
  refine ⟨β, hphase.first_lt_of_first_neg (Ioo_subset_Icc_self hβ) hβp, hβ, hβx, hbefore,
    hafter, hβsin, (Dyn.first_bad_crossing_or_unit hphase (hshadow.mono fun _ hs => hs.2)).imp_right
      fun ⟨τ, hτ, hpτ, hpfirst, hprefix⟩ => ?_⟩
  obtain ⟨hβτ, hqτ, hbad⟩ := P.first_bad_after_middle hU hm haffine hρ hρ0 hρK heq hphase
    (Ioo_subset_Icc_self hβ) hβx hτ hpτ hpfirst hprefix
  exact ⟨τ, ⟨hβτ, hτ.2⟩, hpτ, hqτ, hprefix, hbad⟩

end ActualPair

end AmbidextrousSofa
