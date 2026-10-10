import AmbidextrousSofa.Analysis.TiltedEnergyBarrier
import AmbidextrousSofa.Analysis.TiltedEndpointBounds
import AmbidextrousSofa.Analysis.TiltedLateExcessScalar

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
local notation "p" => supportP F.fD F.g
local notation "q" => supportQ F.gD F.f

/-- All circle, floor, and endpoint estimates are supplied by the
actual tilted maximum. The first-zero and quadratic inputs are the
ordinary crossing conclusions of the source ODE calculus. -/
theorem fullTiltedSupportQuarterPair_first_zero_excess_stops_early {C h A : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 2 / 3 < C) (hC1 : C < 37 / 50)
    (hmpos : 0 < m) (hsmall : C + m < 1)
    (hh0 : 0 < h) (hh1 : h < 17 / 50)
    (hheight : capHeight U = 1) (hhigh : capRoof U C = 1)
    (hlow : capRoof U (-C) = 1 - h)
    (hκ : ∀ s, ρ s ≤ sourceKappa (upperCornerVelocity U s))
    (hA : A ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hpA : p A = 0)
    (hpbefore : ∀ t ∈ Ico (0 : ℝ) A, 0 < p t) (hqA : 1 < q A)
    (hquad : 0 ≤ capRoof U (horizontalRight U) + h - 3 * C * A + A ^ 2 / 2) :
    q A - 1 < 19 / 100 ∧
      Analysis.quadraticExcessLength (q A - 1) < 1 / 3 ∧
      A + Analysis.quadraticExcessLength (q A - 1) < 11 / 15 := by
  let B : ℝ := capRoof U (horizontalRight U) - 1 + h
  have hmid : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]
    congr 1 <;> ring
  have haff := haffine
  rw [hmid] at haff
  obtain ⟨hBlo, hBhi, hBupper, hBlower⟩ := hU.tilted_endpoint_momentum_bounds
    hl hr (by linarith only [hC0]) hC1.le hh0.le hh1 hm hheight haff hlow hhigh
  change -7 / 12 < B at hBlo
  change B < 7 / 40 at hBhi
  change B ≤ -1 / 4 + 5 * h / 4 at hBupper
  change h ≤ 1 / 8 → -7 / 12 + 3 * h / 2 ≤ B at hBlower
  have hd0 : 2 ≤ 3 * C := by linarith only [hC0]
  have hd1 : 3 * C < 111 / 50 := by linarith only [hC1]
  have hAd : A ≤ 3 * C := by linarith only [hA.2, Real.pi_lt_four, hd0]
  have hh2 : h ≤ 2 := by linarith only [hh1]
  have hε : 0 ≤ q A - 1 := by linarith only [hqA]
  have hquadB : 0 ≤ 1 + B - 3 * C * A + A ^ 2 / 2 := by
    dsimp only [B]
    linarith only [hquad]
  obtain ⟨τ, hτ, hphase, _hzero, hpcircle, hqcircle, _hDcircle, _hqτ, hstop⟩ :=
    fullTiltedSupportQuarterPair_exists_initial_stopping_circle
      hU hm haffine hρ hρ0 hρK heq hl hr (by linarith only [hC0]) hmpos hsmall
      hh0 hheight hhigh hlow hκ
  have hτmem : τ ∈ Icc (0 : ℝ) τ := ⟨hτ.1.le, le_rfl⟩
  have hpc : p τ = Analysis.initialFloorCircleP (3 * C) B τ := hpcircle τ hτmem
  have hqc : q τ = Analysis.initialFloorCircleQ (3 * C) B τ := hqcircle τ hτmem
  have hτA : τ ≤ A := by
    by_contra hnot
    have hpos := (hphase A ⟨hA.1.le, lt_of_not_ge hnot⟩).1
    linarith only [hpos, hpA]
  by_cases hτeq : τ = A
  · rw [hτeq] at hpc hqc
    have hbounds := Analysis.initial_circle_excess_bounds hd0 hd1 hBlo hBhi hA
      (hpc.symm.trans hpA) (by rw [← hqc]; exact hqA)
    rw [← hqc] at hbounds
    exact ⟨by linarith only [hbounds.2.2.1], by linarith only [hbounds.2.2.2],
      by linarith only [hbounds.2.1, hbounds.2.2.2]⟩
  have hτltA : τ < A := lt_of_le_of_ne hτA hτeq
  have hpτ : 0 < p τ := hpbefore τ ⟨hτ.1.le, hτltA⟩
  have hfloor : τ = Analysis.initialFloorAngle h :=
    hstop.resolve_left (ne_of_gt hpτ)
  have hpfloor : 0 < 1 + B * (1 - h) - 3 * C * Analysis.initialFloorSine h := by
    have hpositive : 0 < Analysis.initialFloorCircleP (3 * C) B τ := by
      rw [← hpc]
      exact hpτ
    rwa [hfloor, Analysis.initialFloorCircleP,
      Analysis.cos_initialFloorAngle hh0.le hh2, Analysis.sin_initialFloorAngle] at hpositive
  have hhsmall : h < 1 / 8 := Analysis.initial_floor_positive_forces_small_tilt
    hd0 hh0.le hh1.le (by linarith only [hBupper]) hpfloor
  have hEA : clippedCornerEnergy p q A = 1 / 4 + (q A + 1) ^ 2 := by
    unfold clippedCornerEnergy
    rw [hpA]
    norm_num
  have hEAhigh : 17 / 4 < clippedCornerEnergy p q A := by
    rw [hEA]
    have hprod := mul_pos (show 0 < q A - 1 by linarith only [hqA])
      (show 0 < q A + 3 by linarith only [hqA])
    nlinarith only [hprod]
  have hdecrease : clippedCornerEnergy p q A ≤ clippedCornerEnergy p q τ := by
    have hbarrier := fullTiltedSupportQuarterPair_energy_le_max_from
      hU hm haffine hρ hρ0 hρK heq hl hr (by linarith only [hC0]) hsmall
      hheight hhigh hκ ⟨hτ.1.le, hτ.2.le⟩ ⟨hτA, hA.2.le⟩
    rcases le_max_iff.mp hbarrier with hbad | hgood
    · exact False.elim (not_le_of_gt hEAhigh hbad)
    · exact hgood
  have hfloorE : clippedCornerEnergy p q τ ≤
      Analysis.initialFloorTest (3 * C) B h + 1 / 4 := by
    apply (clippedCornerEnergy_le_initialFloorEnergy p q τ).trans_eq
    rw [hpc, hqc, hfloor, Analysis.initialFloorCircle_energy_at_floor hh0.le hh2]
    unfold Analysis.initialFloorTest
    ring
  have henergy : (2 + (q A - 1)) ^ 2 ≤ Analysis.initialFloorTest (3 * C) B h := by
    have h := hdecrease.trans hfloorE
    rw [hEA] at h
    nlinarith only [h]
  by_cases hhcut : 1 / 25 ≤ h
  · have htest := Analysis.initial_floor_test_medium_tilt_le hd0 hd1.le hhcut hhsmall.le
      (by linarith only [hBlower hhsmall.le]) (by linarith only [hBupper])
    have hquad' : 0 ≤ 29 / 32 - 3 * C * A + A ^ 2 / 2 := by
      linarith only [hquadB, hBupper, hhsmall]
    obtain ⟨hεbound, _hAbound, hell, hend⟩ := Analysis.medium_tilt_excess_stops_early
      hd0 hε hAd (henergy.trans htest) hquad'
    exact ⟨by linarith only [hεbound], by linarith only [hell], hend⟩
  · have hhcut' : h ≤ 1 / 25 := le_of_not_ge hhcut
    have hBsmall : B ≤ -1 / 5 := by linarith only [hBupper, hhcut']
    have htest := Analysis.initial_floor_test_small_tilt_le hd0 hh0.le hhcut' hBlo.le hBsmall
    have hquad' : 0 ≤ 4 / 5 - 3 * C * A + A ^ 2 / 2 := by
      linarith only [hquadB, hBsmall]
    exact Analysis.small_tilt_excess_stops_early hd0 hd1.le hε hAd
      (henergy.trans htest) hquad'

end ActualPair

end AmbidextrousSofa
