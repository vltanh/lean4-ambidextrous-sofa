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

/-- Parameter substitution for an actual graph, including orientation.
No injectivity or artificial nonnegative-area convention is imposed. -/
theorem integral_graph_parametrization {a b : ℝ} {F X Y XD : ℝ → ℝ}
    (hab : a ≤ b) (hX : ContinuousOn X (Icc a b)) (hY : ContinuousOn Y (Icc a b))
    (hXD : ∀ t ∈ Ioo a b, HasDerivWithinAt X (XD t) (Ioi t) t)
    (hXDi : IntervalIntegrable XD volume a b)
    (hF : ContinuousOn F (X '' Icc a b))
    (hgraph : ∀ t ∈ Ioo a b, F (X t) = Y t) :
    (∫ x in X a..X b, F x) = ∫ t in a..b, Y t * XD t := by
  have hXu : ContinuousOn X (uIcc a b) := by simpa only [uIcc_of_le hab] using hX
  have hFu : ContinuousOn F (X '' uIcc a b) := by
    simpa only [uIcc_of_le hab] using hF
  have hcomp : ContinuousOn (F ∘ X) (uIcc a b) :=
    hFu.comp hXu (fun t ht => mem_image_of_mem X ht)
  have hcompI : IntervalIntegrable (fun t => (F ∘ X) t * XD t) volume a b :=
    hXDi.continuousOn_mul hcomp
  have hsubstitution := intervalIntegral.integral_comp_mul_deriv''' hXu
    (by simpa only [min_eq_left hab, max_eq_right hab] using hXD)
    (by simpa only [min_eq_left hab, max_eq_right hab] using
      hF.mono (image_mono Ioo_subset_Icc_self))
    (hFu.integrableOn_compact (isCompact_uIcc.image_of_continuousOn hXu))
    (intervalIntegrable_iff'.mp hcompI)
  rw [← hsubstitution]
  apply intervalIntegral.integral_congr_Ioo_of_le hab
  intro t ht
  rw [Function.comp_apply, hgraph t ht]

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
  have hXu : ContinuousOn X (uIcc a b) := by simpa only [uIcc_of_le hab] using hX
  have hYu : ContinuousOn Y (uIcc a b) := by simpa only [uIcc_of_le hab] using hY
  have hXY := hYDi.continuousOn_mul hXu
  have hYX := hXDi.continuousOn_mul hYu
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    hXu hYu
    (by simpa only [min_eq_left hab, max_eq_right hab] using hXD)
    (by simpa only [min_eq_left hab, max_eq_right hab] using hYD)
    hXDi hYDi
  have hcomm : (∫ t in a..b, XD t * Y t) = ∫ t in a..b, Y t * XD t := by
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hcomm] at hparts
  rw [integral_graph_parametrization hab hX hY hXD hXDi hF hgraph]
  simp only [coordDet]
  rw [intervalIntegral.integral_sub hXY hYX]
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
  have hroof : ∀ x, 0 ≤ capRoof U x :=
    capRoof_nonneg hU.isCompact (fun p hp => (hU.inStrip hp).1)
  have hInt := hU.integrableOn_capRoof_Icc (horizontalLeft U) (horizontalRight U)
  have hvol : volume (verticalIntervalRegion
      (Icc (horizontalLeft U) (horizontalRight U)) (fun _ => 0) (capRoof U)) =
      ∫⁻ x in Icc (horizontalLeft U) (horizontalRight U),
        ENNReal.ofReal (capRoof U x - 0) :=
    volume_verticalIntervalRegion_eq_lintegral measurableSet_Icc
      measurable_const hU.measurable_capRoof
  rw [← hU.eq_verticalIntervalRegion] at hvol
  simp only [sub_zero] at hvol
  have hof := ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall hroof)
  rw [← hof] at hvol
  change (volume U).toReal = _
  rw [hvol, ENNReal.toReal_ofReal (integral_nonneg hroof)]

theorem IsDownwardCap.intervalIntegrable_capRoof {U : Set Plane}
    (hU : IsDownwardCap U) (a b : ℝ) : IntervalIntegrable (capRoof U) volume a b := by
  apply intervalIntegrable_iff'.mpr
  simpa only [uIcc] using hU.integrableOn_capRoof_Icc (min a b) (max a b)

theorem IsDownwardCap.volumeReal_eq_intervalIntegral_capRoof {U : Set Plane}
    (hU : IsDownwardCap U) :
    volume.real U = ∫ x in horizontalLeft U..horizontalRight U, capRoof U x := by
  rw [hU.volumeReal_eq_integral_capRoof, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact)]

/-- Two curved wings and an actual horizontal top face partition cap area.
The wing integrals are oriented from the right toward the left. -/
theorem IsDownwardCap.volumeReal_eq_wing_integrals {U : Set Plane}
    (hU : IsDownwardCap U) {l r a b : ℝ}
    (hl : horizontalLeft U = l) (hr : horizontalRight U = r) (hab : a ≤ b)
    (hface : ∀ x ∈ Icc a b, capRoof U x = 1) :
    volume.real U = -(∫ x in a..l, capRoof U x) + (b - a) -
      ∫ x in r..b, capRoof U x := by
  rw [hU.volumeReal_eq_intervalIntegral_capRoof, hl, hr]
  have hla := hU.intervalIntegrable_capRoof l a
  have habi := hU.intervalIntegrable_capRoof a b
  have hbr := hU.intervalIntegrable_capRoof b r
  have hfaceInt : (∫ x in a..b, capRoof U x) = b - a := by
    calc
      _ = ∫ _x in a..b, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hab] at hx
        exact hface x hx
      _ = b - a := by simp
  have hsum := intervalIntegral.integral_add_adjacent_intervals hla habi
  have hsum' := intervalIntegral.integral_add_adjacent_intervals (hla.trans habi) hbr
  rw [← hsum, hfaceInt] at hsum'
  rw [intervalIntegral.integral_symm l a, intervalIntegral.integral_symm b r]
  linarith

end AmbidextrousSofa
