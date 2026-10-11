module

public import AmbidextrousSofa.Geometry.Barriers

@[expose] public section

/-!
# Finite, measurable, and integrable whole-angle barriers

The two individual wall heights can have small denominators near an endpoint
of the angular interval. Their minimum nevertheless has a uniform upper
bound: on the first quadrant at least one of sine and cosine is at least
one half. That wall alone controls the minimum. Compactness of the actual
set supplies a common support bound on the closed quarter-turn.

Consequently the real supremum in `sweptNiche` is a genuine bounded supremum,
at every horizontal coordinate, including outside the body's projection.
It is lower semicontinuous as a supremum of continuous wall minima. The
terminal wall is retained in `partialBarrier`; both barriers are measurable
and integrable on every compact horizontal interval.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-! ## Continuous affine walls -/

/-- Each wall is continuous in the horizontal coordinate, even at angular
endpoints where Lean's total division convention gives a zero denominator. -/
theorem continuous_firstWall (K : Set Plane) (θ : ℝ) : Continuous (firstWall K θ) := by
  unfold firstWall; fun_prop

/-- Compactness and angular support continuity give one finite upper bound
for both support directions over the entire closed quarter-turn. -/
theorem exists_support_upper_bound_quarterTurn {K : Set Plane} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Icc (0 : ℝ) (Real.pi / 2),
      support K (unitNormal θ) ≤ C ∧ support K (companionNormal θ) ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := Real.pi / 2)).bddAbove_image
    (((continuous_support hK).comp continuous_unitNormal).max
      ((continuous_support hK).comp continuous_companionNormal)).continuousOn
  exact ⟨max C 0, le_max_right _ _, fun θ hθ =>
    max_le_iff.1 ((hC (mem_image_of_mem _ hθ)).trans (le_max_left _ _))⟩

/-! ## A denominator bounded away from zero controls the minimum -/

/-- At least one denominator is at least one half in the open first quadrant. -/
theorem half_le_sin_or_half_le_cos {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    (1 / 2 : ℝ) ≤ Real.sin θ ∨ (1 / 2 : ℝ) ≤ Real.cos θ := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  by_contra! h
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The minimum has a finite linear upper bound despite the two potentially
small angular denominators. No strip-height hypothesis is needed. -/
theorem cornerWall_le_of_support_bounds {K : Set Plane} {θ C : ℝ}
    (hC : 0 ≤ C) (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hu : support K (unitNormal θ) ≤ C)
    (hv : support K (companionNormal θ) ≤ C) (x : ℝ) :
    cornerWall K θ x ≤ 2 * (C + 1 + |x|) := by
  have hN : 0 ≤ C + 1 + |x| := by positivity
  have hx : ∀ t, |t| ≤ 1 → -|x| ≤ x * t ∧ x * t ≤ |x| := fun t ht =>
    abs_le.1 ((abs_mul x t).trans_le (mul_le_of_le_one_right (abs_nonneg x) ht))
  rcases half_le_sin_or_half_le_cos hθ with hs | hc
  · refine (min_le_left _ _).trans ?_
    rw [firstWall, div_le_iff₀ (by linarith)]
    linarith [(hx _ (Real.abs_cos_le_one θ)).1, mul_nonneg hN (sub_nonneg.mpr hs)]
  · refine (min_le_right _ _).trans ?_
    rw [secondWall, div_le_iff₀ (by linarith)]
    linarith [(hx _ (Real.abs_sin_le_one θ)).2, mul_nonneg hN (sub_nonneg.mpr hc)]

/-- Every swept value is bounded above, including at abscissae outside the
compact body's horizontal projection. Positivity of `α` is unnecessary here:
an empty angular interval is bounded as well. -/
theorem sweptWallValues_bddAbove {K : Set Plane} (hK : IsCompact K)
    {α : ℝ} (hα : α ≤ Real.pi / 2) (x : ℝ) :
    BddAbove (sweptWallValues K α x) := by
  obtain ⟨C, hC, hS⟩ := exists_support_upper_bound_quarterTurn hK
  refine ⟨2 * (C + 1 + |x|), forall_mem_image.2 fun θ hθ => ?_⟩
  have hθ' : θ ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ.1, hθ.2.trans_le hα⟩
  obtain ⟨hu, hv⟩ := hS θ (Ioo_subset_Icc_self hθ')
  exact cornerWall_le_of_support_bounds hC hθ' hu hv x

/-! ## Lower semicontinuity and measurability -/

theorem measurable_sweptNiche {K : Set Plane} (hK : IsCompact K)
    {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) :
    Measurable (sweptNiche K α) := by
  -- the positive swept supremum is lower semicontinuous: a wall above `c` stays above nearby
  refine LowerSemicontinuous.measurable fun x c hc => ?_
  rcases lt_max_iff.1 hc with hc | hc
  · obtain ⟨_, ⟨θ, hθ, rfl⟩, hcθ⟩ := exists_lt_of_lt_csSup (sweptWallValues_nonempty K hα0 x) hc
    exact (((continuous_firstWall K θ).min (by unfold secondWall; fun_prop)).continuousAt.eventually
      (lt_mem_nhds hcθ)).mono fun x' h =>
        h.trans_le (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hK hα x') hθ)
  · exact .of_forall fun x' => hc.trans_le (sweptNiche_nonneg K α x')

theorem measurable_partialBarrier {K : Set Plane} (hK : IsCompact K)
    {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) :
    Measurable (partialBarrier K α) :=
  (measurable_sweptNiche hK hα0 hα).max (continuous_firstWall K α).measurable

/-! ## Genuine bounds and integrability on compact horizontal intervals -/

theorem abs_le_endpoint_sum_of_mem_Icc {l r x : ℝ} (hx : x ∈ Icc l r) :
    |x| ≤ |l| + |r| := by
  apply abs_le.mpr
  constructor <;> linarith [hx.1, hx.2, neg_abs_le l, le_abs_self r, abs_nonneg l, abs_nonneg r]

theorem exists_sweptNiche_bound_Icc {K : Set Plane} (hK : IsCompact K)
    {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) (l r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc l r, sweptNiche K α x ≤ C := by
  obtain ⟨C, hC, hS⟩ := exists_support_upper_bound_quarterTurn hK
  refine ⟨2 * (C + 1 + |l| + |r|), by positivity, fun x hx =>
    sweptNiche_le_of_forall hα0 (by positivity) fun θ hθ => ?_⟩
  have hθ' : θ ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ.1, hθ.2.trans_le hα⟩
  obtain ⟨hu, hv⟩ := hS θ (Ioo_subset_Icc_self hθ')
  linarith [cornerWall_le_of_support_bounds hC hθ' hu hv x, abs_le_endpoint_sum_of_mem_Icc hx]

theorem integrableOn_sweptNiche_Icc {K : Set Plane} (hK : IsCompact K)
    {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) (l r : ℝ) :
    IntegrableOn (sweptNiche K α) (Icc l r) := by
  obtain ⟨C, -, hC⟩ := exists_sweptNiche_bound_Icc hK hα0 hα l r
  refine .of_bound measure_Icc_lt_top (measurable_sweptNiche hK hα0 hα).aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sweptNiche_nonneg K α x)]
  exact hC x hx

theorem integrableOn_partialBarrier_Icc {K : Set Plane} (hK : IsCompact K)
    {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) (l r : ℝ) :
    IntegrableOn (partialBarrier K α) (Icc l r) :=
  (integrableOn_sweptNiche_Icc hK hα0 hα l r).sup (continuous_firstWall K α).integrableOn_Icc

/-! ## The companion roof integrals -/

/-- The zero-extended cap roof is measurable and lies in `[0,1]` for every
compact set in the unit strip, so it is integrable on any finite interval. -/
theorem integrableOn_capRoof_Icc {K : Set Plane} (hK : IsCompact K)
    (hStrip : K ⊆ unitStrip) (l r : ℝ) :
    IntegrableOn (capRoof K) (Icc l r) := by
  have hK0 : ∀ p ∈ K, 0 ≤ p.2 := fun p hp => (hStrip hp).1
  refine .of_bound measure_Icc_lt_top (measurable_capRoof hK hK0).aestronglyMeasurable 1
    (.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (capRoof_nonneg hK hK0 x)]
  exact capRoof_le_one hK hStrip x

theorem integrableOn_roofDeficit_Icc {K : Set Plane} (hK : IsCompact K)
    (hStrip : K ⊆ unitStrip) (l r : ℝ) :
    IntegrableOn (fun x => 1 - capRoof K x) (Icc l r) :=
  (integrableOn_const measure_Icc_lt_top.ne).sub (integrableOn_capRoof_Icc hK hStrip l r)

theorem IsDownwardCap.integrableOn_capRoof_Icc {U : Set Plane}
    (hU : IsDownwardCap U) (l r : ℝ) : IntegrableOn (capRoof U) (Icc l r) :=
  AmbidextrousSofa.integrableOn_capRoof_Icc hU.isCompact hU.inStrip l r

theorem IsDownwardCap.integrableOn_roofDeficit_Icc {U : Set Plane}
    (hU : IsDownwardCap U) (l r : ℝ) :
    IntegrableOn (fun x => 1 - capRoof U x) (Icc l r) :=
  AmbidextrousSofa.integrableOn_roofDeficit_Icc hU.isCompact hU.inStrip l r

end AmbidextrousSofa
