module

public import AmbidextrousSofa.Measure.CapScore

@[expose] public section

/-!
# Actual graph area and oriented parameter integrals

The graph identities below allow right derivatives and integrable derivative
functions, so piecewise smooth curves with curvature jumps are covered. The
graph value is an explicit pointwise hypothesis; the integral conclusion is
proved by change of variables and integration by parts. Reversing a graph
arc changes its oriented contribution automatically.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def coordDet (p q : Plane) : ℝ := p.1 * q.2 - p.2 * q.1

/-- The line-integral form of oriented graph area. All endpoint products are
retained; they are the terms needed for vertical faces and joining arcs. -/
theorem twice_integral_graph_parametrization
    {a b : ℝ} {F X Y XD YD : ℝ → ℝ}
    (hab : a ≤ b) (hX : ContinuousOn X (Icc a b)) (hY : ContinuousOn Y (Icc a b))
    (hXD : ∀ t ∈ Ioo a b, HasDerivWithinAt X (XD t) (Ioi t) t)
    (hYD : ∀ t ∈ Ioo a b, HasDerivWithinAt Y (YD t) (Ioi t) t)
    (hXDi : IntervalIntegrable XD volume a b) (hYDi : IntervalIntegrable YD volume a b)
    (hF : ContinuousOn F (X '' Icc a b))
    (hgraph : ∀ t ∈ Ioo a b, F (X t) = Y t) :
    2 * (∫ x in X a..X b, F x) = X b * Y b - X a * Y a -
      ∫ t in a..b, coordDet (X t, Y t) (XD t, YD t) := by
  have hXu : ContinuousOn X (uIcc a b) := by rwa [uIcc_of_le hab]
  have hYu : ContinuousOn Y (uIcc a b) := by rwa [uIcc_of_le hab]
  have hFu : ContinuousOn F (X '' uIcc a b) := by rwa [uIcc_of_le hab]
  have hXD' : ∀ t ∈ Ioo (min a b) (max a b), HasDerivWithinAt X (XD t) (Ioi t) t := by
    rwa [min_eq_left hab, max_eq_right hab]
  -- Parameter substitution for the graph, including orientation; no injectivity is needed.
  have hsubst : (∫ x in X a..X b, F x) = ∫ t in a..b, Y t * XD t := by
    rw [← intervalIntegral.integral_comp_mul_deriv''' hXu hXD'
      (by simpa only [min_eq_left hab, max_eq_right hab] using
        hF.mono (image_mono Ioo_subset_Icc_self))
      (hFu.integrableOn_compact (isCompact_uIcc.image_of_continuousOn hXu))
      ((intervalIntegrable_iff').mp (hXDi.continuousOn_mul (hFu.comp hXu (mapsTo_image X _))))]
    exact intervalIntegral.integral_congr_Ioo_of_le hab fun t ht =>
      congrArg (· * XD t) (hgraph t ht)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right hXu hYu hXD'
    (by simpa only [min_eq_left hab, max_eq_right hab] using hYD) hXDi hYDi
  have hcomm : (∫ t in a..b, XD t * Y t) = ∫ t in a..b, Y t * XD t :=
    intervalIntegral.integral_congr fun t _ => mul_comm (XD t) (Y t)
  simp only [coordDet]
  rw [hsubst,
    intervalIntegral.integral_sub (hYDi.continuousOn_mul hXu) (hXDi.continuousOn_mul hYu)]
  linarith

/-- A cap is the actual region under its attained roof, including endpoint fibers. -/
theorem IsDownwardCap.eq_verticalIntervalRegion {U : Set Plane} (hU : IsDownwardCap U) :
    U = verticalIntervalRegion (Icc (horizontalLeft U) (horizontalRight U))
      (fun _ => 0) (capRoof U) := by
  ext p
  rw [hU.mem_iff_projection_and_roof,
    horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
  rfl

/-- Cavalieri for the area of an intrinsic downward cap. -/
theorem IsDownwardCap.volumeReal_eq_integral_capRoof {U : Set Plane}
    (hU : IsDownwardCap U) :
    volume.real U = ∫ x in Icc (horizontalLeft U) (horizontalRight U), capRoof U x := by
  have hroof : ∀ x, 0 ≤ capRoof U x := capRoof_nonneg hU.isCompact fun p hp => (hU.inStrip hp).1
  have hvol := volume_verticalIntervalRegion_eq_lintegral (lower := fun _ => 0)
    (I := Icc (horizontalLeft U) (horizontalRight U)) measurableSet_Icc measurable_const
    hU.measurable_capRoof
  rw [← hU.eq_verticalIntervalRegion] at hvol
  simp only [sub_zero, ← ofReal_integral_eq_lintegral_ofReal (hU.integrableOn_capRoof_Icc _ _)
    (.of_forall hroof)] at hvol
  rw [measureReal_def, hvol, ENNReal.toReal_ofReal (integral_nonneg hroof)]

theorem IsDownwardCap.intervalIntegrable_capRoof {U : Set Plane}
    (hU : IsDownwardCap U) (a b : ℝ) : IntervalIntegrable (capRoof U) volume a b :=
  (intervalIntegrable_iff').mpr (hU.integrableOn_capRoof_Icc _ _)

/-- Two curved wings and an actual horizontal top face partition cap area.
The wing integrals are oriented from the right toward the left. -/
theorem IsDownwardCap.volumeReal_eq_wing_integrals {U : Set Plane}
    (hU : IsDownwardCap U) {l r a b : ℝ}
    (hl : horizontalLeft U = l) (hr : horizontalRight U = r) (hab : a ≤ b)
    (hface : ∀ x ∈ Icc a b, capRoof U x = 1) :
    volume.real U = -(∫ x in a..l, capRoof U x) + (b - a) -
      ∫ x in r..b, capRoof U x := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hU.intervalIntegrable_capRoof l a) (hU.intervalIntegrable_capRoof a r)
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hU.intervalIntegrable_capRoof a b) (hU.intervalIntegrable_capRoof b r)
  have h3 : (∫ x in a..b, capRoof U x) = b - a :=
    (intervalIntegral.integral_congr fun x hx => hface x (uIcc_of_le hab ▸ hx)).trans (by simp)
  rw [hU.volumeReal_eq_integral_capRoof, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact),
    hl, hr, intervalIntegral.integral_symm l a, intervalIntegral.integral_symm b r]
  linarith

end AmbidextrousSofa
