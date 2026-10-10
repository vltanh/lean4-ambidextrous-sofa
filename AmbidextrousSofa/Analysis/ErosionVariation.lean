import AmbidextrousSofa.Analysis.EndpointPressure
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Simultaneous wall and endpoint variations

The finite wall integral is differentiated while both integration endpoints
move. A uniform wall-velocity bound controls each moving sliver by a
quadratic error. This accounts for all endpoint terms without differentiating
an indicator or assuming that the end faces have positive height.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem hasDerivAt_zero_of_quadratic_bound {f : ℝ → ℝ} {C : ℝ}
    (hzero : f 0 = 0) (hbound : ∀ ε, |f ε| ≤ C * ε ^ 2) :
    HasDerivAt f 0 0 := by
  have hbig : f =O[𝓝 (0 : ℝ)] (fun ε : ℝ => ε ^ 2) :=
    Asymptotics.IsBigO.of_bound C (Eventually.of_forall (fun ε => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ε)] using hbound ε))
  have hsmall := hbig.trans_isLittleO
    (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (n := 2) (by norm_num))
  apply hasDerivAt_iff_isLittleO.mpr
  simpa only [hzero, sub_zero, smul_zero] using hsmall

/-- The discrepancy between moving the integrand on a fixed interval and
moving its two endpoints with the integrand frozen at parameter zero. -/
def endpointIntegralError (F : ℝ → ℝ → ℝ) (l r lD rD ε : ℝ) : ℝ :=
  (∫ x in r..(r + ε * rD), F ε x - F 0 x) -
    ∫ x in l..(l + ε * lD), F ε x - F 0 x

theorem endpointIntegralError_zero (F : ℝ → ℝ → ℝ) (l r lD rD : ℝ) :
    endpointIntegralError F l r lD rD 0 = 0 := by
  simp only [endpointIntegralError, zero_mul, add_zero, intervalIntegral.integral_same, sub_self]

theorem abs_endpointIntegralError_le {F : ℝ → ℝ → ℝ} {K : ℝ}
    (hbound : ∀ ε x, |F ε x - F 0 x| ≤ K * |ε|) (l r lD rD ε : ℝ) :
    |endpointIntegralError F l r lD rD ε| ≤
      K * (|rD| + |lD|) * ε ^ 2 := by
  have hsliver : ∀ q d : ℝ,
      |∫ x in q..(q + ε * d), F ε x - F 0 x| ≤ K * |d| * ε ^ 2 := by
    intro q d
    calc
      |∫ x in q..(q + ε * d), F ε x - F 0 x| ≤ K * |ε| * |q + ε * d - q| := by
        simpa only [Real.norm_eq_abs] using
          (intervalIntegral.norm_integral_le_of_norm_le_const
            (a := q) (b := q + ε * d) (C := K * |ε|)
            (fun x _ => by simpa only [Real.norm_eq_abs] using hbound ε x))
      _ = K * |d| * |ε| ^ 2 := by
        rw [show q + ε * d - q = ε * d by ring, abs_mul]
        ring
      _ = K * |d| * ε ^ 2 := by rw [sq_abs]
  calc
    |endpointIntegralError F l r lD rD ε| ≤
        |∫ x in r..(r + ε * rD), F ε x - F 0 x| +
          |∫ x in l..(l + ε * lD), F ε x - F 0 x| := by
      simpa only [endpointIntegralError, sub_eq_add_neg, abs_neg] using
        abs_add_le (∫ x in r..(r + ε * rD), F ε x - F 0 x)
          (-(∫ x in l..(l + ε * lD), F ε x - F 0 x))
    _ ≤ K * |rD| * ε ^ 2 + K * |lD| * ε ^ 2 :=
      add_le_add (hsliver r rD) (hsliver l lD)
    _ = K * (|rD| + |lD|) * ε ^ 2 := by ring

theorem integral_moving_eq_fixed_add_error {F : ℝ → ℝ → ℝ}
    (hcont : ∀ ε, Continuous (F ε)) (l r lD rD ε : ℝ) :
    (∫ x in (l + ε * lD)..(r + ε * rD), F ε x) =
      (∫ x in l..r, F ε x) +
        (∫ x in (l + ε * lD)..(r + ε * rD), F 0 x) -
          (∫ x in l..r, F 0 x) + endpointIntegralError F l r lD rD ε := by
  have hsplit : ∀ η : ℝ,
      (∫ x in (l + ε * lD)..(r + ε * rD), F η x) =
        (∫ x in l..r, F η x) + (∫ x in r..(r + ε * rD), F η x) -
          ∫ x in l..(l + ε * lD), F η x := by
    intro η
    have hfirst := intervalIntegral.integral_add_adjacent_intervals
      ((hcont η).intervalIntegrable l r) ((hcont η).intervalIntegrable r (r + ε * rD))
    have hsecond := intervalIntegral.integral_interval_sub_left
      ((hcont η).intervalIntegrable l (r + ε * rD))
      ((hcont η).intervalIntegrable l (l + ε * lD))
    linarith
  unfold endpointIntegralError
  rw [intervalIntegral.integral_sub ((hcont ε).intervalIntegrable _ _)
      ((hcont 0).intervalIntegrable _ _),
    intervalIntegral.integral_sub ((hcont ε).intervalIntegrable _ _)
      ((hcont 0).intervalIntegrable _ _)]
  linarith [hsplit ε, hsplit 0]

namespace WallExpr

variable {ι : Type*}

/-- Both contributions are actual derivatives: selected wall velocities
in the interior and the ordinary endpoint traces on the two moving slivers. -/
theorem hasDerivAt_integral_affineEnvelope_moving [Fintype ι]
    (e : WallExpr ι) (a b w : ι → ℝ) (ha : Function.Injective a)
    (l r lD rD : ℝ) :
    HasDerivAt (fun ε => ∫ x in (l + ε * lD)..(r + ε * rD),
      e.affineEnvelope a b w ε x)
      ((∫ x in l..r, e.sourceDensity a b w x) +
        e.affineEnvelope a b w 0 r * rD - e.affineEnvelope a b w 0 l * lD) 0 := by
  let K : ℝ := ∑ i, |w i|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i _ => abs_nonneg (w i))
  have hw : ∀ i, |w i| ≤ K := fun i =>
    Finset.single_le_sum (fun j _ => abs_nonneg (w j)) (Finset.mem_univ i)
  have hbound : ∀ ε x,
      |e.affineEnvelope a b w ε x - e.affineEnvelope a b w 0 x| ≤ K * |ε| := by
    intro ε x
    have h := (e.lipschitz_affineEnvelope_parameter a b w hK hw x).dist_le_mul ε 0
    simpa only [Real.dist_eq, Real.coe_nnabs, abs_of_nonneg hK, sub_zero] using h
  have herror := hasDerivAt_zero_of_quadratic_bound
    (endpointIntegralError_zero (e.affineEnvelope a b w) l r lD rD)
    (abs_endpointIntegralError_le hbound l r lD rD)
  have hfixed := e.hasDerivAt_integral_affineEnvelope a b w ha l r
  have hends := hasDerivAt_integral_affine_endpoints
    (e.continuous_affineEnvelope a b w 0) l r lD rD
  have h := ((hfixed.add hends).sub_const
    (∫ x in l..r, e.affineEnvelope a b w 0 x)).add herror
  convert h using 1
  · funext ε
    exact integral_moving_eq_fixed_add_error (e.continuous_affineEnvelope a b w) l r lD rD ε
  · ring

end WallExpr

/-- Finite simultaneous support and endpoint variations. All three moving
integration windows come from the same two projection endpoints. -/
theorem hasDerivAt_finite_intervalSpatialScore_moving
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (outer : WallExpr ι) (inner : WallExpr κ) (a b w : ι → ℝ) (c d v : κ → ℝ)
    (ha : Function.Injective a) (hc : Function.Injective c) (l r lD rD : ℝ) :
    HasDerivAt (fun ε => intervalSpatialScore
      (outer.affineEnvelope a b w ε) (inner.affineEnvelope c d v ε)
      (l + ε * lD) (r + ε * rD))
      (((∫ x in l..(l + (r - l) / 4), outer.sourceDensity a b w x) +
        (∫ x in (r - (r - l) / 4)..r, outer.sourceDensity a b w x) -
        ∫ x in (l + (r - l) / 4)..(r - (r - l) / 4), inner.sourceDensity c d v x) +
        outer.affineEnvelope a b w 0 r * rD - outer.affineEnvelope a b w 0 l * lD -
        (outer.affineEnvelope a b w 0 (r - (r - l) / 4) +
          inner.affineEnvelope c d v 0 (r - (r - l) / 4)) * (lD + 3 * rD) / 4 +
        (outer.affineEnvelope a b w 0 (l + (r - l) / 4) +
          inner.affineEnvelope c d v 0 (l + (r - l) / 4)) * (3 * lD + rD) / 4) 0 := by
  have hleft := outer.hasDerivAt_integral_affineEnvelope_moving a b w ha
    l (l + (r - l) / 4) lD ((3 * lD + rD) / 4)
  have hright := outer.hasDerivAt_integral_affineEnvelope_moving a b w ha
    (r - (r - l) / 4) r ((lD + 3 * rD) / 4) rD
  have hmiddle := inner.hasDerivAt_integral_affineEnvelope_moving c d v hc
    (l + (r - l) / 4) (r - (r - l) / 4) ((3 * lD + rD) / 4) ((lD + 3 * rD) / 4)
  convert (hleft.add hright).sub hmiddle using 1
  · funext ε
    unfold intervalSpatialScore
    have hlow : l + ε * lD + (r + ε * rD - (l + ε * lD)) / 4 =
        l + (r - l) / 4 + ε * ((3 * lD + rD) / 4) := by ring
    have hhigh : r + ε * rD - (r + ε * rD - (l + ε * lD)) / 4 =
        r - (r - l) / 4 + ε * ((lD + 3 * rD) / 4) := by ring
    rw [hlow, hhigh]
  · ring

end AmbidextrousSofa
