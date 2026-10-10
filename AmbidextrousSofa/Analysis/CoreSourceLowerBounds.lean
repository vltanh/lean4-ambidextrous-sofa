module

public import AmbidextrousSofa.Analysis.CoreContactGeometry
public import AmbidextrousSofa.Analysis.FirstSourceDensity

@[expose] public section

/-!
# First-source lower bounds on the actual tilted core prefix

Every contact piece is constructed from the literal support pair. Its
positive middle core lies strictly after the affine normal, which also
supplies the regular-domain condition needed by source differentiation.
The final lower bounds have no supplied contact, occupation, or flux
certificate. The charged bound stops at the actual middle crossing.
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
local notation "Z" => innerCornerPoint (F).f (F).g
set_option quotPrecheck false in
local notation "p" => supportP (F).fD (F).g
set_option quotPrecheck false in
local notation "q" => supportQ (F).gD (F).f
local notation "v" => (fun t : ℝ => leftCompanionWingDensity m ρ (t + Real.pi / 2))

theorem fullTiltedSupportQuarterPair_core_prefix_regular {C h α τ : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50)
    (hmpos : 0 < m) (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1)
    (hunit : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ r ≤ 1)
    (hα : 0 ≤ α) (hτ : τ ∈ Icc 0 (Real.pi / 2)) (hpα : p α = 0)
    (hphase : ∀ r ∈ Ioo α τ, p r < 0 ∧ 0 < q r)
    (hcompanion : ∀ᵐ r ∂volume.restrict (Ioo 0 τ), v r ≤ 1) :
    Ioo α τ ⊆ regularCornerDomain m := by
  have hmidR : horizontalRight U - capWidth U / 4 = C := by
    unfold capWidth
    rw [hl, hr]
    ring
  have hhigh' : capRoof U (horizontalRight U - capWidth U / 4) = 1 := by
    rwa [hmidR]
  intro t ht
  have htq : t ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hα.trans_lt ht.1, ht.2.trans_le hτ.2⟩
  have hgeometry := fullTiltedSupportQuarterPair_core_geometry hU hm haffine hρ hρ0 hρK heq
    hl hr hC0 hC1 hh hmpos hheight hlow hunit hα hτ hpα hphase hcompanion ht
  have hx : (Z t).1 ≤ horizontalRight U - capWidth U / 4 := by
    rw [hmidR]
    exact hgeometry.1.2.le
  exact mem_regularCornerDomain_of_after_nonneg_affine hm htq
    (fullTiltedSupportQuarterPair_positive_core_after_affine
      hU hm haffine hρ hρ0 hρK heq hhigh' htq hgeometry.2.1 hx)

theorem fullTiltedSupportQuarterPair_ae_first_density_ge_core_on_prefix {C h α τ : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50)
    (hmpos : 0 < m) (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1)
    (hunit : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ r ≤ 1)
    (hα : 0 ≤ α) (hτ : τ ∈ Icc 0 (Real.pi / 2)) (hpα : p α = 0)
    (hphase : ∀ r ∈ Ioo α τ, p r < 0 ∧ 0 < q r)
    (hcompanion : ∀ᵐ r ∂volume.restrict (Ioo 0 τ), v r ≤ 1) :
    ∀ᵐ t ∂volume.restrict (Ioo α τ), q t ≤ ρ t := by
  apply fullTiltedSupportQuarterPair_ae_first_density_ge_core
    hU hm haffine hρ hρ0 hρK heq hheight
    (fullTiltedSupportQuarterPair_core_prefix_regular hU hm haffine hρ hρ0 hρK heq
      hl hr hC0 hC1 hh hmpos hheight hlow hhigh hunit hα hτ hpα hphase hcompanion)
  intro s t hαs hst htτ
  exact fullTiltedSupportQuarterPair_first_source_core_piece hU hm haffine hρ hρ0 hρK heq
    hl hr hC0 hC1 hh hmpos hheight hlow hunit hα hτ hpα hphase hcompanion
    ⟨hαs, hst.trans htτ⟩ ⟨hαs.trans hst, htτ⟩ hst

theorem fullTiltedSupportQuarterPair_ae_first_density_ge_charged_on_prefix {C h α τ β : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50)
    (hmpos : 0 < m) (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1)
    (hunit : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ r ≤ 1)
    (hα : 0 ≤ α) (hτ : τ ∈ Icc 0 (Real.pi / 2)) (hpα : p α = 0)
    (hphase : ∀ r ∈ Ioo α τ, p r < 0 ∧ 0 < q r)
    (hcompanion : ∀ᵐ r ∂volume.restrict (Ioo 0 τ), v r ≤ 1)
    (hβ : β ∈ Icc 0 (Real.pi / 2)) (hβx : (B β).1 = C) :
    ∀ᵐ t ∂volume.restrict (Ioo α (min β τ)), 1 + q t ≤ 2 * ρ t := by
  have hregular := fullTiltedSupportQuarterPair_core_prefix_regular hU hm haffine hρ hρ0 hρK heq
    hl hr hC0 hC1 hh hmpos hheight hlow hhigh hunit hα hτ hpα hphase hcompanion
  apply fullTiltedSupportQuarterPair_ae_first_density_ge_charged
    hU hm haffine hρ hρ0 hρK heq hheight
    (fun t ht => hregular ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩)
  intro s t hαs hst htb
  have htτ : t < τ := htb.trans_le (min_le_right _ _)
  have htβ : t ≤ β := htb.le.trans (min_le_left _ _)
  exact fullTiltedSupportQuarterPair_first_source_charged_pieces hU hm haffine hρ hρ0 hρK heq
    hl hr hC0 hC1 hh hmpos hheight hlow hunit hα hτ hpα hphase hcompanion hβ hβx
    ⟨hαs, hst.trans htτ⟩ ⟨hαs.trans hst, htτ⟩ hst htβ

/-- The measured lower law extends the unit bound to both actual
endpoints of a nondegenerate core prefix by continuity. -/
theorem fullTiltedSupportQuarterPair_core_prefix_q_le_one {C h α τ : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh : h ≤ 17 / 50)
    (hmpos : 0 < m) (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1)
    (hunit : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ r ≤ 1)
    (hα : 0 ≤ α) (hτ : τ ∈ Icc 0 (Real.pi / 2)) (hατ : α < τ) (hpα : p α = 0)
    (hphase : ∀ r ∈ Ioo α τ, p r < 0 ∧ 0 < q r)
    (hcompanion : ∀ᵐ r ∂volume.restrict (Ioo 0 τ), v r ≤ 1) :
    ∀ t ∈ Icc α τ, q t ≤ 1 := by
  have hlower := fullTiltedSupportQuarterPair_ae_first_density_ge_core_on_prefix
    hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh hmpos hheight hlow hhigh
      hunit hα hτ hpα hphase hcompanion
  have hupper := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hα hτ.2) hunit
  have hcont : ContinuousOn q (Icc α τ) :=
    (((F).continuous_gD.add (F).continuous_f).sub continuousOn_const).mono (Icc_subset_Icc hα hτ.2)
  apply ContinuousOn.le_on_Icc_of_ae_le_on_Ioo hcont hατ
  filter_upwards [hlower, hupper] with t ht hu
  exact ht.trans hu

end ActualPair

end AmbidextrousSofa
