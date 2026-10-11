module

public import AmbidextrousSofa.Analysis.PolygonExposure

@[expose] public section

/-!
# Actual endpoint movement from a positive vertical end face

Moving a displayed box wall need not move the actual projection. Here a
positive end face gives a point strictly below every nonaxis upper wall.
Its small horizontal displacement lies in the enlarged polygon and
realizes the new endpoint. All sampled upper supports stay fixed. This is
the geometric condition needed before applying the moving-window pressure
formulas.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace FinitePolygon

variable {ι : Type*}

theorem baseline_halfspace_of_endpoints {l r x height : ℝ} {n : Plane}
    (hl : coordDot (l, 0) n ≤ height) (hr : coordDot (r, 0) n ≤ height)
    (hx : x ∈ Icc l r) : coordDot (x, 0) n ≤ height := by
  simp only [coordDot, zero_mul, add_zero] at hl hr ⊢
  rcases le_total 0 n.1 with hn | hn
  exacts [(mul_le_mul_of_nonneg_right hx.2 hn).trans hr,
    (mul_le_mul_of_nonpos_right hx.1 hn).trans hl]

/-- Near a positive end face, the baseline stays below every wall. -/
private theorem eventually_baseline [Fintype ι] {x₀ e : ℝ} {normal : ι → Plane}
    {height : ι → ℝ} (hnormal : ∀ i, 0 < (normal i).2) (he : 0 < e)
    (hface : ∀ i, coordDot (x₀, e) (normal i) ≤ height i) :
    ∀ᶠ x in 𝓝 x₀, ∀ i, coordDot (x, 0) (normal i) ≤ height i := by
  refine eventually_all.2 fun i => ?_
  have h : coordDot (x₀, 0) (normal i) < height i := by
    have := hface i
    unfold coordDot at *
    linarith [mul_pos he (hnormal i)]
  have hc : Continuous fun x : ℝ => coordDot (x, 0) (normal i) := by unfold coordDot; fun_prop
  exact (hc.tendsto x₀).eventually_le_const h

/-- Enlarging the base interval of an exact polygon keeps every supporting parameter, as
long as the new baseline stays below every wall. -/
private theorem enlarged {l r l' r' : ℝ} {normal : ι → Plane} {height : ι → ℝ}
    (hl : l' ≤ l) (hr : r ≤ r') (hlr : l ≤ r) (hnormal : ∀ i, 0 < (normal i).2)
    (hbaseline : ∀ x ∈ Icc l' r', ∀ i, coordDot (x, 0) (normal i) ≤ height i)
    (hne : (upperPolygon l r normal height).Nonempty)
    (hexact : ∀ i, support (upperPolygon l r normal height) (normal i) = height i) :
    IsDownwardCap (upperPolygon l' r' normal height) ∧
      (∀ x ∈ Icc l' r', ∀ i, coordDot (x, 0) (normal i) ≤ height i) ∧
      horizontalProjection (upperPolygon l' r' normal height) = Icc l' r' ∧
      ∀ i, support (upperPolygon l' r' normal height) (normal i) = height i := by
  have hsub : upperPolygon l r normal height ⊆ upperPolygon l' r' normal height := fun p hp => by
    obtain ⟨hx, hy, hhalf⟩ := (mem_upperPolygon_iff _ _ _ _ _).mp hp
    exact (mem_upperPolygon_iff _ _ _ _ _).mpr ⟨Icc_subset_Icc hl hr hx, hy, hhalf⟩
  refine ⟨isDownwardCap_upperPolygon _ _ _ _ (hl.trans (hlr.trans hr)) (fun i => (hnormal i).le)
    hbaseline, hbaseline, horizontalProjection_upperPolygon _ _ _ _ hbaseline,
    fun i => le_antisymm ?_ ?_⟩
  · exact support_le_of_forall (hne.mono hsub) fun p hp =>
      ((mem_upperPolygon_iff _ _ _ _ _).mp hp).2.2 i
  · exact hexact i ▸ support_mono hsub hne (isCompact_upperPolygon _ _ _ _) _

/-- A positive right end face gives actual outward movement of the right
projection endpoint. The top and all nonaxis supporting parameters stay
fixed throughout this family. -/
theorem exists_right_axis_variation [Fintype ι] {l r e : ℝ}
    (normal : ι → Plane) (height : ι → ℝ) (hlr : l ≤ r)
    (hnormal : ∀ i, 0 < (normal i).2)
    (hbaseline : ∀ x ∈ Icc l r, ∀ i, coordDot (x, 0) (normal i) ≤ height i)
    (hexact : ∀ i, support (upperPolygon l r normal height) (normal i) = height i)
    (hface : (r, e) ∈ upperPolygon l r normal height) (he : 0 < e) :
    ∃ δ > 0, ∀ ε ∈ Ico (0 : ℝ) δ,
      IsDownwardCap (upperPolygon l (r + ε) normal height) ∧
      (∀ x ∈ Icc l (r + ε), ∀ i, coordDot (x, 0) (normal i) ≤ height i) ∧
      horizontalProjection (upperPolygon l (r + ε) normal height) = Icc l (r + ε) ∧
      ∀ i, support (upperPolygon l (r + ε) normal height) (normal i) = height i := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    (eventually_baseline hnormal he ((mem_upperPolygon_iff _ _ _ _ _).mp hface).2.2)
  refine ⟨δ, hδ, fun ε hε => enlarged le_rfl (by linarith [hε.1]) hlr hnormal
    (fun x hx i => baseline_halfspace_of_endpoints (hbaseline l ⟨le_rfl, hlr⟩ i)
      (hball (by simpa [Real.dist_eq, abs_of_nonneg hε.1] using hε.2) i) hx) ⟨_, hface⟩ hexact⟩

/-- The left endpoint has the same positive-face justification, with its
actual coordinate moving at speed minus one. -/
theorem exists_left_axis_variation [Fintype ι] {l r e : ℝ}
    (normal : ι → Plane) (height : ι → ℝ) (hlr : l ≤ r)
    (hnormal : ∀ i, 0 < (normal i).2)
    (hbaseline : ∀ x ∈ Icc l r, ∀ i, coordDot (x, 0) (normal i) ≤ height i)
    (hexact : ∀ i, support (upperPolygon l r normal height) (normal i) = height i)
    (hface : (l, e) ∈ upperPolygon l r normal height) (he : 0 < e) :
    ∃ δ > 0, ∀ ε ∈ Ico (0 : ℝ) δ,
      IsDownwardCap (upperPolygon (l - ε) r normal height) ∧
      (∀ x ∈ Icc (l - ε) r, ∀ i, coordDot (x, 0) (normal i) ≤ height i) ∧
      horizontalProjection (upperPolygon (l - ε) r normal height) = Icc (l - ε) r ∧
      ∀ i, support (upperPolygon (l - ε) r normal height) (normal i) = height i := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    (eventually_baseline hnormal he ((mem_upperPolygon_iff _ _ _ _ _).mp hface).2.2)
  refine ⟨δ, hδ, fun ε hε => enlarged (by linarith [hε.1]) le_rfl hlr hnormal
    (fun x hx i => baseline_halfspace_of_endpoints
      (hball (by simpa [Real.dist_eq, abs_of_nonneg hε.1] using hε.2) i)
      (hbaseline r ⟨hlr, le_rfl⟩ i) hx) ⟨_, hface⟩ hexact⟩

/-- The actual upper-system expression for the unchanged finite barrier. -/
def barrierEnvelope (normal : ι → Plane) (height : ι → ℝ)
    (corners : List (ι × ι)) (terminal : Option ι) (x : ℝ) : ℝ :=
  (barrierExpr corners terminal).eval
    (fun i => wallSlope normal i * x + barrierIntercept normal height i)

theorem continuous_barrierEnvelope (normal : ι → Plane) (height : ι → ℝ)
    (corners : List (ι × ι)) (terminal : Option ι) :
    Continuous (barrierEnvelope normal height corners terminal) :=
  (barrierExpr corners terminal).continuous_eval (fun _ => by fun_prop)

end FinitePolygon

end AmbidextrousSofa
