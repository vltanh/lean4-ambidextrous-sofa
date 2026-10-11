module

public import AmbidextrousSofa.Analysis.FirstUnitEventSelection
public import AmbidextrousSofa.Analysis.FirstFloorOrder

@[expose] public section

/-!
# Actual contact geometry for the common occupation law

The first tangent stays at a positive niche contact over the open middle
interval throughout its charged window, for either order of the second
momentum zero and the window crossing. This statement uses the literal
support pair and provides the geometric input of the charged window to
occupation.
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

theorem FirstUnitSetting.first_window_positive_contact {C h α β η t : ℝ}
    (P : FirstUnitSetting U m ρ C h) (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (hβ : β ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hβx : (B β).1 = C)
    (hbefore : ∀ s ∈ Ico (0 : ℝ) β, (B s).1 < C) (ht : t ∈ Ioo α β) :
    p t < 0 ∧ (B t).1 ∈ Ioo (-C) C ∧ 0 < (B t).2 ∧
      sweptNiche U (Real.pi / 2) (B t).1 = (B t).2 := by
  have htq : t ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hphase.first_mem.1.trans ht.1, ht.2.trans hβ.2⟩
  have hp : p t < 0 := hphase.first_neg ⟨ht.1, htq.2.le⟩
  have hxR : (B t).1 < C := hbefore t ⟨htq.1.le, ht.2⟩
  have hx0 := (fullTiltedSupportQuarterPair_first_tangent_order hU hm haffine hρ hρ0 hρK heq
    P.hunit).1 ⟨le_rfl, by positivity⟩ (Ioo_subset_Icc_self htq) htq.1.le
  simp only [(fullTiltedSupportQuarterPair_tangent_traces
    hU hm haffine hρ hρ0 hρK heq P.hl P.hr P.hmpos P.hheight P.hlow).1] at hx0
  have hy := fullTiltedSupportQuarterPair_first_tangent_height_pos_of_abscissa_lt
    hU hm haffine hρ hρ0 hρK heq P.hheight P.hunit (Ioo_subset_Icc_self htq) hβ
    ht.2.le (hxR.trans_eq hβx.symm)
  exact ⟨hp, ⟨by linarith only [hx0, P.hC0], hxR⟩, hy,
    fullTiltedSupportQuarterPair_niche_first_tangency
      hU hm haffine hρ hρ0 hρK heq P.hunit htq hp.le hy.le⟩

end ActualPair

end AmbidextrousSofa
