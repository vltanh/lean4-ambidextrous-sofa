import AmbidextrousSofa.Analysis.ExactEstimates

/-!
# Initial-floor energy for tilted supports

The two energy tests are derived from the actual zero-density momentum
circle, stopped at either the floor or the first zero of the first
momentum. Energy propagation uses absolutely continuous momenta and their
almost-everywhere source equations. No continuity of the curvature
densities, optimizing profile, or sharp value certificate is assumed.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa.Analysis

def initialFloorSine (h : ℝ) : ℝ := Real.sqrt (h * (2 - h))

def initialFloorAngle (h : ℝ) : ℝ := Real.arccos (1 - h)

def initialFloorCircleP (d B t : ℝ) : ℝ := 1 + B * Real.cos t - d * Real.sin t

def initialFloorCircleQ (d B t : ℝ) : ℝ := -1 + d * Real.cos t + B * Real.sin t

def initialFloorEnergy (p q : ℝ) : ℝ := (p - 1 / 2) ^ 2 + (q + 1) ^ 2

def InitialFloorEnergyConditions (d B h : ℝ) : Prop :=
  d ^ 2 + B ^ 2 ≤ 5 ∧
    d ^ 2 + B ^ 2 + B * (1 - h) - d * initialFloorSine h ≤ 4

theorem initialFloorSine_nonneg (h : ℝ) : 0 ≤ initialFloorSine h := Real.sqrt_nonneg _

theorem initialFloorSine_sq {h : ℝ} (h0 : 0 ≤ h) (h2 : h ≤ 2) :
    initialFloorSine h ^ 2 = h * (2 - h) :=
  Real.sq_sqrt (mul_nonneg h0 (sub_nonneg.mpr h2))

theorem initialFloorSine_le_one {h : ℝ} (h0 : 0 ≤ h) (h2 : h ≤ 2) :
    initialFloorSine h ≤ 1 := by
  have hs := initialFloorSine_sq h0 h2
  by_contra hnle
  have hgt : 1 < initialFloorSine h := lt_of_not_ge hnle
  have hp := mul_pos (sub_pos.mpr hgt)
    (show 0 < initialFloorSine h + 1 by linarith)
  nlinarith [sq_nonneg (h - 1)]

theorem cos_initialFloorAngle {h : ℝ} (h0 : 0 ≤ h) (h2 : h ≤ 2) :
    Real.cos (initialFloorAngle h) = 1 - h :=
  Real.cos_arccos (by linarith) (by linarith)

theorem sin_initialFloorAngle (h : ℝ) :
    Real.sin (initialFloorAngle h) = initialFloorSine h := by
  rw [initialFloorAngle, Real.sin_arccos, initialFloorSine]
  congr 1
  ring

theorem hasDerivAt_initialFloorCircleP (d B t : ℝ) :
    HasDerivAt (initialFloorCircleP d B) (-1 - initialFloorCircleQ d B t) t := by
  apply ((((Real.hasDerivAt_cos t).const_mul B).const_add 1).sub
    ((Real.hasDerivAt_sin t).const_mul d)).congr_deriv
  unfold initialFloorCircleQ
  ring

theorem hasDerivAt_initialFloorCircleQ (d B t : ℝ) :
    HasDerivAt (initialFloorCircleQ d B) (initialFloorCircleP d B t - 1) t := by
  apply ((((Real.hasDerivAt_cos t).const_mul d).const_add (-1)).add
    ((Real.hasDerivAt_sin t).const_mul B)).congr_deriv
  unfold initialFloorCircleP
  ring

theorem initialFloorCircle_radius (d B t : ℝ) :
    (initialFloorCircleP d B t - 1) ^ 2 + (initialFloorCircleQ d B t + 1) ^ 2 =
      d ^ 2 + B ^ 2 := by
  have hd := congrArg (fun x : ℝ => d ^ 2 * x) (Real.sin_sq_add_cos_sq t)
  have hB := congrArg (fun x : ℝ => B ^ 2 * x) (Real.sin_sq_add_cos_sq t)
  unfold initialFloorCircleP initialFloorCircleQ
  nlinarith

theorem initialFloorCircle_energy (d B t : ℝ) :
    initialFloorEnergy (initialFloorCircleP d B t) (initialFloorCircleQ d B t) =
      d ^ 2 + B ^ 2 + initialFloorCircleP d B t - 3 / 4 := by
  have h := initialFloorCircle_radius d B t
  unfold initialFloorEnergy
  nlinarith

theorem initialFloorCircle_energy_at_floor {d B h : ℝ} (h0 : 0 ≤ h) (h2 : h ≤ 2) :
    initialFloorEnergy (initialFloorCircleP d B (initialFloorAngle h))
      (initialFloorCircleQ d B (initialFloorAngle h)) =
        d ^ 2 + B ^ 2 + 1 / 4 + B * (1 - h) - d * initialFloorSine h := by
  rw [initialFloorCircle_energy]
  unfold initialFloorCircleP
  rw [cos_initialFloorAngle h0 h2, sin_initialFloorAngle]
  ring

theorem initialFloor_conditions_iff_stopping_energy (d B h : ℝ) :
    InitialFloorEnergyConditions d B h ↔
      d ^ 2 + B ^ 2 + 1 / 4 + max (B * (1 - h) - d * initialFloorSine h) (-1) ≤ 17 / 4 := by
  constructor
  · rintro ⟨hr, he⟩
    have hm : max (B * (1 - h) - d * initialFloorSine h) (-1) ≤ 4 - (d ^ 2 + B ^ 2) :=
      max_le (by linarith) (by linarith)
    linarith
  · intro he
    constructor
    · linarith [le_max_right (B * (1 - h) - d * initialFloorSine h) (-1)]
    · linarith [le_max_left (B * (1 - h) - d * initialFloorSine h) (-1)]

/-- The circle is used only at its actual stopping point. In the first
alternative no continuation to the later floor angle is invoked. -/
theorem initialFloor_stopped_circle_energy {d B h τ : ℝ}
    (h0 : 0 ≤ h) (h2 : h ≤ 2)
    (hstop : initialFloorCircleP d B τ = 0 ∨ τ = initialFloorAngle h) :
    initialFloorEnergy (initialFloorCircleP d B τ) (initialFloorCircleQ d B τ) ≤
      d ^ 2 + B ^ 2 + 1 / 4 + max (B * (1 - h) - d * initialFloorSine h) (-1) := by
  rcases hstop with hp | rfl
  · rw [initialFloorCircle_energy, hp]
    linarith [le_max_right (B * (1 - h) - d * initialFloorSine h) (-1)]
  · rw [initialFloorCircle_energy_at_floor h0 h2]
    linarith [le_max_left (B * (1 - h) - d * initialFloorSine h) (-1)]

theorem initialFloor_stopped_energy_le {d B h τ : ℝ}
    (h0 : 0 ≤ h) (h2 : h ≤ 2) (hcond : InitialFloorEnergyConditions d B h)
    (hstop : initialFloorCircleP d B τ = 0 ∨ τ = initialFloorAngle h) :
    initialFloorEnergy (initialFloorCircleP d B τ) (initialFloorCircleQ d B τ) ≤ 17 / 4 :=
  (initialFloor_stopped_circle_energy h0 h2 hstop).trans
    ((initialFloor_conditions_iff_stopping_energy d B h).1 hcond)

theorem absolutelyContinuousOnInterval_const_real (c a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
  (LipschitzWith.lipschitzOnWith (lipschitzWith_const c)).absolutelyContinuousOnInterval

theorem absolutelyContinuousOnInterval_initialFloorEnergy
    {p q : ℝ → ℝ} {a b : ℝ}
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hq : AbsolutelyContinuousOnInterval q a b) :
    AbsolutelyContinuousOnInterval (fun t => initialFloorEnergy (p t) (q t)) a b := by
  have hp' := hp.sub (absolutelyContinuousOnInterval_const_real (1 / 2) a b)
  have hq' := hq.add (absolutelyContinuousOnInterval_const_real 1 a b)
  simpa only [initialFloorEnergy, pow_two, Pi.add_apply, Pi.sub_apply, Pi.mul_apply] using
    (hp'.mul hp').add (hq'.mul hq')

/-- The same-sign energy is nonincreasing for AC momenta obeying the
actual source equations with `u=0` and `v≤1/2`, almost everywhere. -/
theorem initialFloorEnergy_le_of_sourceODE {p q v : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hq : AbsolutelyContinuousOnInterval q a b)
    (hode : ∀ᵐ t ∂volume.restrict (Icc a b),
      HasDerivAt p (-1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hqpos : ∀ᵐ t ∂volume.restrict (Icc a b), -1 ≤ q t)
    (hv : ∀ᵐ t ∂volume.restrict (Icc a b), v t ≤ 1 / 2) :
    initialFloorEnergy (p b) (q b) ≤ initialFloorEnergy (p a) (q a) := by
  have hE := absolutelyContinuousOnInterval_initialFloorEnergy hp hq
  have hD : (fun t => deriv (fun x => initialFloorEnergy (p x) (q x)) t) ≤ᵐ[
      volume.restrict (Icc a b)] (fun _ => 0) := by
    filter_upwards [hode, hqpos, hv] with t ht hqt hvt
    have hd := ((ht.1.sub_const (1 / 2)).pow 2).add ((ht.2.add_const 1).pow 2)
    change deriv (fun x => (p x - 1 / 2) ^ 2 + (q x + 1) ^ 2) t ≤ 0
    rw [hd.deriv]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ q t + 1 by linarith) (show v t - 1 / 2 ≤ 0 by linarith)]
  have hint := intervalIntegral.integral_mono_ae_restrict hab
    hE.intervalIntegrable_deriv intervalIntegrable_const hD
  rw [hE.integral_deriv_eq_sub] at hint
  simpa only [intervalIntegral.integral_zero, sub_nonpos] using hint

/-- Uniqueness of the zero-density circle follows from the actual AC
momentum equations and zero initial difference energy. -/
theorem eqOn_initialFloorCircle_of_zero_source {p q : ℝ → ℝ} {d B τ : ℝ}
    (hτ : 0 ≤ τ)
    (hp : AbsolutelyContinuousOnInterval p 0 τ)
    (hq : AbsolutelyContinuousOnInterval q 0 τ)
    (hode : ∀ᵐ t ∂volume.restrict (Icc 0 τ),
      HasDerivAt p (-1 - q t) t ∧ HasDerivAt q (p t - 1) t)
    (hp0 : p 0 = 1 + B) (hq0 : q 0 = d - 1) :
    EqOn p (initialFloorCircleP d B) (Icc 0 τ) ∧
      EqOn q (initialFloorCircleQ d B) (Icc 0 τ) := by
  have hcp : ContDiff ℝ 1 (initialFloorCircleP d B) := by unfold initialFloorCircleP; fun_prop
  have hcq : ContDiff ℝ 1 (initialFloorCircleQ d B) := by unfold initialFloorCircleQ; fun_prop
  let x : ℝ → ℝ := fun t => p t - initialFloorCircleP d B t
  let y : ℝ → ℝ := fun t => q t - initialFloorCircleQ d B t
  have hx : AbsolutelyContinuousOnInterval x 0 τ :=
    hp.sub hcp.contDiffOn.absolutelyContinuousOnInterval
  have hy : AbsolutelyContinuousOnInterval y 0 τ :=
    hq.sub hcq.contDiffOn.absolutelyContinuousOnInterval
  have hE : AbsolutelyContinuousOnInterval (fun t => x t ^ 2 + y t ^ 2) 0 τ := by
    simpa only [pow_two, Pi.add_apply, Pi.mul_apply] using (hx.mul hx).add (hy.mul hy)
  have hode' := (ae_restrict_iff' measurableSet_Icc).1 hode
  have hD : ∀ᵐ t ∂volume, t ∈ uIcc 0 τ →
      HasDerivAt (fun s => x s ^ 2 + y s ^ 2) 0 t := by
    filter_upwards [hode'] with t ht hmem
    rw [uIcc_of_le hτ] at hmem
    have hd := (((ht hmem).1.sub (hasDerivAt_initialFloorCircleP d B t)).pow 2).add
      (((ht hmem).2.sub (hasDerivAt_initialFloorCircleQ d B t)).pow 2)
    exact hd.congr_deriv (by ring)
  obtain ⟨K, hK⟩ := hE.const_of_ae_hasDerivAt_zero hD
  have hzero := hK 0 (by simp)
  have hx0 : x 0 = 0 := by simp [x, initialFloorCircleP, hp0]
  have hy0 : y 0 = 0 := by simp [y, initialFloorCircleQ, hq0]
  rw [hx0, hy0] at hzero
  have hpoint : ∀ t ∈ Icc (0 : ℝ) τ, x t = 0 ∧ y t = 0 := by
    intro t ht
    have h := hK t (by simpa only [uIcc_of_le hτ] using ht)
    constructor <;> apply sq_eq_zero_iff.mp <;> nlinarith [sq_nonneg (x t), sq_nonneg (y t)]
  exact ⟨fun t ht => sub_eq_zero.mp (hpoint t ht).1,
    fun t ht => sub_eq_zero.mp (hpoint t ht).2⟩

theorem firstMomentum_zero_companion_le_one {p q : ℝ}
    (hp : p = 0) (hE : initialFloorEnergy p q ≤ 17 / 4) : q ≤ 1 := by
  unfold initialFloorEnergy at hE
  rw [hp] at hE
  by_contra h
  have hgt : 1 < q := lt_of_not_ge h
  have hprod := mul_pos (sub_pos.mpr hgt) (show 0 < q + 3 by linarith)
  nlinarith

/-- IE's analytic first-crossing conclusion, with the stopped initial
circle and the subsequent same-sign evolution joined explicitly. -/
theorem initialFloor_first_crossing_le_one
    {p q v : ℝ → ℝ} {d B h τ α : ℝ}
    (h0 : 0 ≤ h) (h2 : h ≤ 2) (hτα : τ ≤ α)
    (hcond : InitialFloorEnergyConditions d B h)
    (hp : AbsolutelyContinuousOnInterval p τ α)
    (hq : AbsolutelyContinuousOnInterval q τ α)
    (hode : ∀ᵐ t ∂volume.restrict (Icc τ α),
      HasDerivAt p (-1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hqpos : ∀ᵐ t ∂volume.restrict (Icc τ α), -1 ≤ q t)
    (hv : ∀ᵐ t ∂volume.restrict (Icc τ α), v t ≤ 1 / 2)
    (hpτ : p τ = initialFloorCircleP d B τ)
    (hqτ : q τ = initialFloorCircleQ d B τ)
    (hstop : initialFloorCircleP d B τ = 0 ∨ τ = initialFloorAngle h)
    (hpα : p α = 0) : q α ≤ 1 := by
  have hstart := initialFloor_stopped_energy_le h0 h2 hcond hstop
  have hdecrease := initialFloorEnergy_le_of_sourceODE hτα hp hq hode hqpos hv
  rw [hpτ, hqτ] at hdecrease
  exact firstMomentum_zero_companion_le_one hpα (hdecrease.trans hstart)

end AmbidextrousSofa.Analysis
