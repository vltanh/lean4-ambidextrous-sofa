module

public import AmbidextrousSofa.Analysis.TiltedEnergyBarrier
public import AmbidextrousSofa.Analysis.TiltedEndpointBounds
public import AmbidextrousSofa.Analysis.TiltedLateExcessScalar

@[expose] public section

/-!
# Excess bounds at the actual first momentum zero

The first momentum zero is compared with the stopping point of the
actual initial circle. If the zero comes first, its exact radius gives
the short excess estimate. If the floor comes first, the actual energy
barrier transfers the floor energy to the zero. The endpoint pressure
bounds then select the two exact small-height estimates.
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
local notation "p" => supportP (F).fD (F).g
set_option quotPrecheck false in
local notation "q" => supportQ (F).gD (F).f

/-- All circle, floor, and endpoint estimates are supplied by the
actual tilted maximum. The energy barrier, first-zero and quadratic
inputs are the ordinary conclusions of the source ODE calculus. -/
theorem fullTiltedSupportQuarterPair_first_zero_excess_stops_early {C h A : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 2 / 3 < C) (hC1 : C < 37 / 50)
    (hmpos : 0 < m) (hsmall : C + m < 1)
    (hh0 : 0 < h) (hh1 : h < 17 / 50)
    (hheight : capHeight U = 1) (hhigh : capRoof U C = 1)
    (hlow : capRoof U (-C) = 1 - h)
    (hκ : ∀ s, ρ s ≤ sourceKappa (upperCornerVelocity U s))
    (hbarrier : ∀ a ∈ Icc 0 (Real.pi / 2), ∀ t ∈ Icc a (Real.pi / 2),
      clippedCornerEnergy p q t ≤ max (17 / 4) (clippedCornerEnergy p q a))
    (hA : A ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hpA : p A = 0)
    (hpbefore : ∀ t ∈ Ico (0 : ℝ) A, 0 < p t) (hqA : 1 < q A)
    (hquad : 0 ≤ capRoof U (horizontalRight U) + h - 3 * C * A + A ^ 2 / 2) :
    q A - 1 < 19 / 100 ∧
      Analysis.quadraticExcessLength (q A - 1) < 1 / 3 ∧
      A + Analysis.quadraticExcessLength (q A - 1) < 11 / 15 := by
  obtain ⟨hBlo, hBhi, hBupper, hBlower⟩ := hU.tilted_endpoint_momentum_bounds hl hr
    (by linarith only [hC0]) hC1.le hh0.le hh1 hm hheight
    ((centered_quarter_points hl hr).2.2 ▸ haffine) hlow hhigh
  obtain ⟨τ, hτ, hphase, -, hpc, hqc, hstop⟩ :=
    fullTiltedSupportQuarterPair_exists_initial_stopping_circle
      hU hm haffine hρ hρ0 hρK heq hl hr (by linarith only [hC0]) hmpos hsmall hh0 hheight hhigh
      hlow hκ
  set B := capRoof U (horizontalRight U) - 1 + h
  replace hpc := hpc ⟨hτ.1.le, le_rfl⟩
  replace hqc := hqc ⟨hτ.1.le, le_rfl⟩
  have hd0 : 2 ≤ 3 * C := by linarith only [hC0]
  have hd1 : 3 * C < 111 / 50 := by linarith only [hC1]
  have hAd : A ≤ 3 * C := by linarith only [hA.2, Real.pi_lt_four, hd0]
  have hε : 0 ≤ q A - 1 := by linarith only [hqA]
  have hτA : τ ≤ A := not_lt.1 fun hAτ => by linarith only [(hphase A ⟨hA.1.le, hAτ⟩).1, hpA]
  rcases hτA.eq_or_lt with rfl | hτA
  · have hb := Analysis.initial_circle_excess_bounds hd0 hd1 hBlo hBhi hA
      (hpc.symm.trans hpA) (hqc ▸ hqA)
    rw [← hqc] at hb
    exact ⟨by linarith only [hb.2.1], by linarith only [hb.2.2], by linarith only [hb.1, hb.2.2]⟩
  have hpτ : 0 < p τ := hpbefore τ ⟨hτ.1.le, hτA⟩
  have hfloor : τ = Analysis.initialFloorAngle h := hstop.resolve_left hpτ.ne'
  have hhsmall : h < 1 / 8 := Analysis.initial_floor_positive_forces_small_tilt (B := B) hd0
    hh0.le hh1.le (by linarith only [hBupper]) (by
      rwa [hpc, hfloor, Analysis.initialFloorCircleP, Analysis.cos_initialFloorAngle hh0.le
        (by linarith only [hh1]), Analysis.sin_initialFloorAngle] at hpτ)
  have hEA : clippedCornerEnergy p q A = 1 / 4 + (q A + 1) ^ 2 := by
    rw [clippedCornerEnergy, hpA]
    norm_num
  have hdecrease := (le_max_iff.1 (hbarrier τ ⟨hτ.1.le, hτ.2.le⟩ A ⟨hτA.le, hA.2.le⟩)).resolve_left
    (by rw [hEA]; nlinarith only [hqA])
  have hfloorE : clippedCornerEnergy p q τ ≤ Analysis.initialFloorTest (3 * C) B h + 1 / 4 := by
    refine (clippedCornerEnergy_le_initialFloorEnergy p q τ).trans_eq ?_
    rw [hpc, hqc, hfloor, Analysis.initialFloorTest,
      Analysis.initialFloorCircle_energy_at_floor hh0.le (by linarith only [hh1])]
    ring
  have henergy : (2 + (q A - 1)) ^ 2 ≤ Analysis.initialFloorTest (3 * C) B h := by
    linarith only [hdecrease, hfloorE, hEA]
  have hquad' : 0 ≤ 1 + B - 3 * C * A + A ^ 2 / 2 := by linarith only [hquad]
  rcases le_or_gt (1 / 25) h with hhcut | hhcut
  · exact Analysis.medium_tilt_excess_stops_early hd0 hd1.le hhcut hhsmall.le
      (by linarith only [hBlower hhsmall.le]) (by linarith only [hBupper]) hε hAd henergy hquad'
  · exact Analysis.small_tilt_excess_stops_early hd0 hd1.le hh0.le hhcut.le hBlo.le
      (by linarith only [hBupper, hhcut]) hε hAd henergy hquad'

end ActualPair

end AmbidextrousSofa
