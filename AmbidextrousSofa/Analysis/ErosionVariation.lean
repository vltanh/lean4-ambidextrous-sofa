module

public import AmbidextrousSofa.Analysis.EndpointPressure
public import Mathlib.Analysis.Asymptotics.Lemmas

@[expose] public section

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
    (hbound : ∀ ε, |f ε| ≤ C * ε ^ 2) : HasDerivAt f 0 0 := by
  simpa using ((Asymptotics.IsBigO.of_bound C (.of_forall fun ε => by simpa using hbound ε) :
    f =O[𝓝 0] fun x : ℝ => ‖x - 0‖ ^ 2).hasFDerivAt one_lt_two).hasDerivAt

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
  have hK : 0 ≤ ∑ i, |w i| := Finset.sum_nonneg fun i _ => abs_nonneg (w i)
  have hcont := e.continuous_affineEnvelope a b w
  -- The wall moves at speed at most `∑ i, |w i|`, so each moving sliver is quadratically small.
  have hsliver (q d : ℝ) : HasDerivAt (fun ε => ∫ x in q..(q + ε * d),
      e.affineEnvelope a b w ε x - e.affineEnvelope a b w 0 x) 0 0 := by
    refine hasDerivAt_zero_of_quadratic_bound (C := (∑ i, |w i|) * |d|) fun ε => ?_
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (E := ℝ)
      (C := (∑ i, |w i|) * |ε|) fun x _ => ?_).trans_eq ?_
    · simpa [Real.dist_eq, abs_of_nonneg hK] using (e.lipschitz_affineEnvelope_parameter a b w hK
        (fun i => Finset.single_le_sum (fun j _ => abs_nonneg (w j)) (Finset.mem_univ i))
        x).dist_le_mul ε 0
    · rw [add_sub_cancel_left, abs_mul, ← sq_abs]; ring
  convert (((e.hasDerivAt_integral_affineEnvelope a b w ha l r).add
    (hasDerivAt_integral_affine_endpoints (hcont 0) l r lD rD)).sub_const
    (∫ x in l..r, e.affineEnvelope a b w 0 x)).add ((hsliver r rD).sub (hsliver l lD)) using 1
  · funext ε
    have hsplit (G : ℝ → ℝ) (hG : Continuous G) : ∫ x in (l + ε * lD)..(r + ε * rD), G x =
        (∫ x in l..r, G x) + (∫ x in r..(r + ε * rD), G x) - ∫ x in l..(l + ε * lD), G x := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hG.intervalIntegrable _ l)
        (hG.intervalIntegrable l _), ← intervalIntegral.integral_add_adjacent_intervals
        (hG.intervalIntegrable l r) (hG.intervalIntegrable r _),
        intervalIntegral.integral_symm (l + ε * lD) l]
      ring
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hsplit _ (hcont ε), hsplit _ (hcont 0),
      intervalIntegral.integral_sub ((hcont ε).intervalIntegrable _ _)
        ((hcont 0).intervalIntegrable _ _),
      intervalIntegral.integral_sub ((hcont ε).intervalIntegrable _ _)
        ((hcont 0).intervalIntegrable _ _)]
    ring
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
  convert ((outer.hasDerivAt_integral_affineEnvelope_moving a b w ha
    l (l + (r - l) / 4) lD ((3 * lD + rD) / 4)).add
    (outer.hasDerivAt_integral_affineEnvelope_moving a b w ha
      (r - (r - l) / 4) r ((lD + 3 * rD) / 4) rD)).sub
    (inner.hasDerivAt_integral_affineEnvelope_moving c d v hc
      (l + (r - l) / 4) (r - (r - l) / 4) ((3 * lD + rD) / 4) ((lD + 3 * rD) / 4)) using 1
  · funext ε
    simp only [intervalSpatialScore, Pi.add_apply, Pi.sub_apply]
    ring_nf
  · ring

end AmbidextrousSofa
