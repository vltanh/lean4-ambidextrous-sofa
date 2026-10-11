module

public import AmbidextrousSofa.Analysis.ExactEstimates

@[expose] public section

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
  nlinarith [initialFloorSine_sq h0 h2, initialFloorSine_nonneg h, sq_nonneg (h - 1)]

theorem cos_initialFloorAngle {h : ℝ} (h0 : 0 ≤ h) (h2 : h ≤ 2) :
    Real.cos (initialFloorAngle h) = 1 - h :=
  Real.cos_arccos (by linarith) (by linarith)

theorem sin_initialFloorAngle (h : ℝ) :
    Real.sin (initialFloorAngle h) = initialFloorSine h := by
  rw [initialFloorAngle, Real.sin_arccos, initialFloorSine]
  ring_nf

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
  unfold initialFloorCircleP initialFloorCircleQ
  linear_combination (d ^ 2 + B ^ 2) * Real.sin_sq_add_cos_sq t

theorem initialFloorCircle_energy (d B t : ℝ) :
    initialFloorEnergy (initialFloorCircleP d B t) (initialFloorCircleQ d B t) =
      d ^ 2 + B ^ 2 + initialFloorCircleP d B t - 3 / 4 := by
  unfold initialFloorEnergy
  linear_combination initialFloorCircle_radius d B t

theorem initialFloorCircle_energy_at_floor {d B h : ℝ} (h0 : 0 ≤ h) (h2 : h ≤ 2) :
    initialFloorEnergy (initialFloorCircleP d B (initialFloorAngle h))
      (initialFloorCircleQ d B (initialFloorAngle h)) =
        d ^ 2 + B ^ 2 + 1 / 4 + B * (1 - h) - d * initialFloorSine h := by
  rw [initialFloorCircle_energy, initialFloorCircleP, cos_initialFloorAngle h0 h2,
    sin_initialFloorAngle]
  ring

/-- The circle is used only at its actual stopping point. In the first
alternative no continuation to the later floor angle is invoked. -/
theorem initialFloor_stopped_energy_le {d B h τ : ℝ}
    (h0 : 0 ≤ h) (h2 : h ≤ 2) (hcond : InitialFloorEnergyConditions d B h)
    (hstop : initialFloorCircleP d B τ = 0 ∨ τ = initialFloorAngle h) :
    initialFloorEnergy (initialFloorCircleP d B τ) (initialFloorCircleQ d B τ) ≤ 17 / 4 := by
  obtain ⟨hr, he⟩ := hcond
  rcases hstop with hp | rfl
  · rw [initialFloorCircle_energy, hp]; linarith
  · rw [initialFloorCircle_energy_at_floor h0 h2]; linarith

theorem absolutelyContinuousOnInterval_const_real (c a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
  (LipschitzWith.lipschitzOnWith (LipschitzWith.const c)).absolutelyContinuousOnInterval

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
  have hx := hp.fun_sub (ContDiffOn.absolutelyContinuousOnInterval (f := initialFloorCircleP d B)
    (by unfold initialFloorCircleP; fun_prop))
  have hy := hq.fun_sub (ContDiffOn.absolutelyContinuousOnInterval (f := initialFloorCircleQ d B)
    (by unfold initialFloorCircleQ; fun_prop))
  obtain ⟨K, hK⟩ := ((hx.fun_mul hx).fun_add (hy.fun_mul hy)).const_of_ae_hasDerivAt_zero <| by
    rw [uIcc_of_le hτ]
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hode] with t ht hmem
    have hx := (ht hmem).1.fun_sub (hasDerivAt_initialFloorCircleP d B t)
    have hy := (ht hmem).2.fun_sub (hasDerivAt_initialFloorCircleQ d B t)
    exact ((hx.fun_mul hx).fun_add (hy.fun_mul hy)).congr_deriv (by ring)
  have hK0 := hK 0 (by simp)
  simp only [initialFloorCircleP, initialFloorCircleQ, hp0, hq0, Real.cos_zero,
    Real.sin_zero] at hK0
  have key t (ht : t ∈ Icc 0 τ) := mul_self_add_mul_self_eq_zero.1
    ((hK t (by rwa [uIcc_of_le hτ])).trans (by rw [← hK0]; ring))
  exact ⟨fun t ht => sub_eq_zero.1 (key t ht).1, fun t ht => sub_eq_zero.1 (key t ht).2⟩

end AmbidextrousSofa.Analysis
