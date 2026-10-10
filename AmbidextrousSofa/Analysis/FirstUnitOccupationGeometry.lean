import AmbidextrousSofa.Analysis.FirstUnitEventSelection
import AmbidextrousSofa.Analysis.FirstFloorOrder

/-!
# Actual contact geometry for the common occupation law

The first tangent stays at a positive niche contact throughout its
charged window, for either order of the second momentum zero and the
window crossing. A companion-unit prefix makes the positive core a
unique contact of the actual swept wall. These statements use the
literal support pair and provide the geometric inputs to occupation.
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
local notation "p" => supportP F.fD F.g
local notation "q" => supportQ F.gD F.f
local notation "v" => (fun t : ℝ => leftCompanionWingDensity m ρ (t + Real.pi / 2))
local notation "B" => firstTangentPoint F.f F.fD
local notation "Z" => innerCornerPoint F.f F.g

theorem fullTiltedSupportQuarterPair_first_window_positive_contact {C h α β η t : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 1 / 2 < C) (hmpos : 0 < m) (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h)
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ s ≤ 1)
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (hβ : β ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hβx : (B β).1 = C)
    (hbefore : ∀ s ∈ Ico (0 : ℝ) β, (B s).1 < C) (ht : t ∈ Ioo α β) :
    p t < 0 ∧ (B t).1 ∈ Ioo (-C) C ∧ 0 < (B t).2 ∧
      sweptNiche U (Real.pi / 2) (B t).1 = (B t).2 := by
  have htq : t ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨hphase.first_mem.1.trans ht.1, ht.2.trans hβ.2⟩
  have hp : p t < 0 := by
    rcases lt_trichotomy t η with hlt | heq | hgt
    · exact (hphase.core_signs t ⟨ht.1, hlt⟩).1
    · simpa only [heq] using hphase.first_at_second
    · exact (hphase.final_signs t ⟨hgt, htq.2.le⟩).1
  have hxR : (B t).1 < C := hbefore t ⟨htq.1.le, ht.2⟩
  have hB0 := (fullTiltedSupportQuarterPair_tangent_traces
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hheight hlow).1
  have horder := (fullTiltedSupportQuarterPair_first_tangent_order
    hU hm haffine hρ hρ0 hρK heq hunit).1
  have hx0 := horder (show (0 : ℝ) ∈ Icc 0 (Real.pi / 2) from
    ⟨le_rfl, by positivity⟩) (Ioo_subset_Icc_self htq) htq.1.le
  rw [hB0] at hx0
  have hxL : -C < (B t).1 := by
    change 2 * C - 1 ≤ (B t).1 at hx0
    linarith only [hx0, hC]
  have hy := fullTiltedSupportQuarterPair_first_tangent_height_pos_of_abscissa_lt
    hU hm haffine hρ hρ0 hρK heq hheight hunit (Ioo_subset_Icc_self htq) hβ
    ht.2.le (by rw [hβx]; exact hxR)
  exact ⟨hp, ⟨hxL, hxR⟩, hy,
    fullTiltedSupportQuarterPair_niche_first_tangency
      hU hm haffine hρ hρ0 hρK heq hunit htq hp.le hy.le⟩

theorem fullTiltedSupportQuarterPair_unique_core_contact_on_prefix {C h α η τ t : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50) (hh0 : 0 < h) (hh1 : h < 17 / 50)
    (hheight : capHeight U = 1)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1)
    (hκ : ∀ s, ρ s ≤ sourceKappa (upperCornerVelocity U s))
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ s ≤ 1)
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (hτ : τ ∈ Icc (0 : ℝ) (Real.pi / 2)) (hτη : τ ≤ η)
    (hcompanion : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) τ), v s ≤ 1)
    (ht : t ∈ Ioo α τ) :
    t ∈ regularCornerDomain m ∧ (Z t).1 ∈ Ioo (-C) C ∧ 0 < (Z t).2 ∧
      sweptNiche U (Real.pi / 2) (Z t).1 = (Z t).2 ∧
      (∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
        fullWallClip hU.isCap.toCompactCap (Z t).1 s =
          sweptNiche U (Real.pi / 2) (Z t).1 → s = t) := by
  have htphase : t ∈ Ioo α η := ⟨ht.1, ht.2.trans_le hτη⟩
  have hgeo := fullTiltedSupportQuarterPair_core_phase_geometry
    hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh0 hh1 hheight hlow hhigh
    hκ hunit hphase (Ioo_subset_Ioc_self htphase)
  have hJR : horizontalRight U - capWidth U / 4 = C := by
    unfold capWidth
    rw [hl, hr]
    ring
  have hcontact := fullTiltedSupportQuarterPair_core_contact hU hm haffine hρ hρ0 hρK heq
    hτ hunit hcompanion ⟨hphase.first_mem.1.trans ht.1, ht.2⟩
    (hphase.core_signs t htphase).1 (hphase.core_signs t htphase).2 hgeo.2.1
    (by rw [hJR]; exact hgeo.1.2.le)
  exact ⟨hgeo.2.2.1, hgeo.1, hgeo.2.1, hcontact.1, hcontact.2⟩

end ActualPair

end AmbidextrousSofa
