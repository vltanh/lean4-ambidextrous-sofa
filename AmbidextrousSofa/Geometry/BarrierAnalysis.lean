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
  unfold firstWall
  fun_prop

theorem continuous_secondWall (K : Set Plane) (θ : ℝ) : Continuous (secondWall K θ) := by
  unfold secondWall
  fun_prop

theorem continuous_cornerWall (K : Set Plane) (θ : ℝ) : Continuous (cornerWall K θ) :=
  (continuous_firstWall K θ).min (continuous_secondWall K θ)

/-- Compactness and angular support continuity give one finite upper bound
for both support directions over the entire closed quarter-turn. -/
theorem exists_support_upper_bound_quarterTurn {K : Set Plane} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Icc (0 : ℝ) (Real.pi / 2),
      support K (unitNormal θ) ≤ C ∧ support K (companionNormal θ) ≤ C := by
  have hu : Continuous (fun θ => support K (unitNormal θ)) :=
    (continuous_support hK).comp continuous_unitNormal
  have hv : Continuous (fun θ => support K (companionNormal θ)) :=
    (continuous_support hK).comp continuous_companionNormal
  obtain ⟨Cu, hCu⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) (Real.pi / 2))).bddAbove_image hu.continuousOn
  obtain ⟨Cv, hCv⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) (Real.pi / 2))).bddAbove_image hv.continuousOn
  refine ⟨max (max Cu Cv) 0, le_max_right _ _, ?_⟩
  intro θ hθ
  constructor
  · exact (hCu (mem_image_of_mem _ hθ)).trans
      ((le_max_left Cu Cv).trans (le_max_left _ _))
  · exact (hCv (mem_image_of_mem _ hθ)).trans
      ((le_max_right Cu Cv).trans (le_max_left _ _))

/-! ## A denominator bounded away from zero controls the minimum -/

/-- At least one denominator is at least one half in the open first quadrant. -/
theorem half_le_sin_or_half_le_cos {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    (1 / 2 : ℝ) ≤ Real.sin θ ∨ (1 / 2 : ℝ) ≤ Real.cos θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1
    (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  by_cases hsHalf : (1 / 2 : ℝ) ≤ Real.sin θ
  · exact Or.inl hsHalf
  · right
    by_contra hcHalf
    have hsLt : Real.sin θ < 1 / 2 := lt_of_not_ge hsHalf
    have hcLt : Real.cos θ < 1 / 2 := lt_of_not_ge hcHalf
    have hsProd := mul_pos (sub_pos.mpr hsLt) (add_pos hs (by norm_num : (0 : ℝ) < 1 / 2))
    have hcProd := mul_pos (sub_pos.mpr hcLt) (add_pos hc (by norm_num : (0 : ℝ) < 1 / 2))
    nlinarith [Real.sin_sq_add_cos_sq θ]

theorem firstWall_numerator_le {K : Set Plane} {θ C : ℝ}
    (hSupport : support K (unitNormal θ) ≤ C) (x : ℝ) :
    support K (unitNormal θ) - 1 - x * Real.cos θ ≤ C + 1 + |x| := by
  have hMul : |x * Real.cos θ| ≤ |x| := by
    rw [abs_mul]
    calc
      |x| * |Real.cos θ| ≤ |x| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) (abs_nonneg x)
      _ = |x| := mul_one _
  linarith [neg_abs_le (x * Real.cos θ)]

theorem secondWall_numerator_le {K : Set Plane} {θ C : ℝ}
    (hSupport : support K (companionNormal θ) ≤ C) (x : ℝ) :
    support K (companionNormal θ) - 1 + x * Real.sin θ ≤ C + 1 + |x| := by
  have hMul : |x * Real.sin θ| ≤ |x| := by
    rw [abs_mul]
    calc
      |x| * |Real.sin θ| ≤ |x| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) (abs_nonneg x)
      _ = |x| := mul_one _
  linarith [le_abs_self (x * Real.sin θ)]

/-- The minimum has a finite linear upper bound despite the two potentially
small angular denominators. No strip-height hypothesis is needed. -/
theorem cornerWall_le_of_support_bounds {K : Set Plane} {θ C : ℝ}
    (hC : 0 ≤ C) (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hu : support K (unitNormal θ) ≤ C)
    (hv : support K (companionNormal θ) ≤ C) (x : ℝ) :
    cornerWall K θ x ≤ 2 * (C + 1 + |x|) := by
  have hNumerator : 0 ≤ C + 1 + |x| := by positivity
  rcases half_le_sin_or_half_le_cos hθ with hs | hc
  · calc
      cornerWall K θ x ≤ firstWall K θ x := min_le_left _ _
      _ ≤ 2 * (C + 1 + |x|) := by
        rw [firstWall, div_le_iff₀ (by linarith : 0 < Real.sin θ)]
        have hProduct := mul_nonneg hNumerator (sub_nonneg.mpr hs)
        have hNum := firstWall_numerator_le hu x
        nlinarith
  · calc
      cornerWall K θ x ≤ secondWall K θ x := min_le_right _ _
      _ ≤ 2 * (C + 1 + |x|) := by
        rw [secondWall, div_le_iff₀ (by linarith : 0 < Real.cos θ)]
        have hProduct := mul_nonneg hNumerator (sub_nonneg.mpr hc)
        have hNum := secondWall_numerator_le hv x
        nlinarith

/-- Every swept value is bounded above, including at abscissae outside the
compact body's horizontal projection. Positivity of `α` is unnecessary here:
an empty angular interval is bounded as well. -/
theorem sweptWallValues_bddAbove {K : Set Plane} (hK : IsCompact K)
    {α : ℝ} (hα : α ≤ Real.pi / 2) (x : ℝ) :
    BddAbove (sweptWallValues K α x) := by
  obtain ⟨C, hC, hSupport⟩ := exists_support_upper_bound_quarterTurn hK
  refine ⟨2 * (C + 1 + |x|), ?_⟩
  rintro y ⟨θ, hθ, rfl⟩
  have hθQuarter : θ ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ.1, hθ.2.trans_le hα⟩
  have hBounds := hSupport θ ⟨hθQuarter.1.le, hθQuarter.2.le⟩
  exact cornerWall_le_of_support_bounds hC hθQuarter hBounds.1 hBounds.2 x

/-- A single compact-set constant controls the whole niche for all horizontal
coordinates. This proves boundedness rather than requiring it as a field. -/
theorem exists_sweptNiche_linear_bound {K : Set Plane} (hK : IsCompact K)
    {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, sweptNiche K α x ≤ 2 * (C + 1 + |x|) := by
  obtain ⟨C, hC, hSupport⟩ := exists_support_upper_bound_quarterTurn hK
  refine ⟨C, hC, ?_⟩
  intro x
  apply sweptNiche_le_of_forall hα0 (by positivity)
  intro θ hθ
  have hθQuarter : θ ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ.1, hθ.2.trans_le hα⟩
  have hBounds := hSupport θ ⟨hθQuarter.1.le, hθQuarter.2.le⟩
  exact cornerWall_le_of_support_bounds hC hθQuarter hBounds.1 hBounds.2 x

/-! ## Lower semicontinuity and measurability -/

/-- The positive swept supremum is lower semicontinuous. The boundedness
proved above is used in the direction from a single wall to the supremum. -/
theorem lowerSemicontinuous_sweptNiche {K : Set Plane} (hK : IsCompact K)
    {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) :
    LowerSemicontinuous (sweptNiche K α) := by
  apply lowerSemicontinuous_iff_isOpen_preimage.mpr
  intro c
  by_cases hc : c < 0
  · have hFull : sweptNiche K α ⁻¹' Ioi c = (Set.univ : Set ℝ) := by
      ext x
      simp only [mem_preimage, mem_Ioi, mem_univ, iff_true]
      exact hc.trans_le (sweptNiche_nonneg K α x)
    rw [hFull]
    exact isOpen_univ
  · have hRepresentation : sweptNiche K α ⁻¹' Ioi c =
        ⋃ θ ∈ Ioo (0 : ℝ) α, {x : ℝ | c < cornerWall K θ x} := by
      ext x
      simp only [mem_preimage, mem_Ioi, mem_iUnion, mem_setOf_eq]
      constructor
      · intro hx
        have hSup : c < sSup (sweptWallValues K α x) := by
          rcases lt_max_iff.mp hx with hs | hZero
          · exact hs
          · exact (hc hZero).elim
        by_contra hNo
        have hWalls : ∀ θ ∈ Ioo (0 : ℝ) α, cornerWall K θ x ≤ c := by
          intro θ hθ
          by_contra hNotLe
          exact hNo ⟨θ, hθ, lt_of_not_ge hNotLe⟩
        have hSupLe : sSup (sweptWallValues K α x) ≤ c :=
          csSup_le (sweptWallValues_nonempty K hα0 x) (forall_mem_image.mpr hWalls)
        exact (not_lt_of_ge hSupLe) hSup
      · rintro ⟨θ, hθ, hcx⟩
        exact hcx.trans_le (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hK hα x) hθ)
    rw [hRepresentation]
    exact isOpen_iUnion (fun θ => isOpen_iUnion (fun _hθ =>
      isOpen_lt continuous_const (continuous_cornerWall K θ)))

theorem measurable_sweptNiche {K : Set Plane} (hK : IsCompact K)
    {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) :
    Measurable (sweptNiche K α) :=
  (lowerSemicontinuous_sweptNiche hK hα0 hα).measurable

theorem lowerSemicontinuous_partialBarrier {K : Set Plane} (hK : IsCompact K)
    {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) :
    LowerSemicontinuous (partialBarrier K α) :=
  (lowerSemicontinuous_sweptNiche hK hα0 hα).sup
    (continuous_firstWall K α).lowerSemicontinuous

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
  obtain ⟨C, hC, hBound⟩ := exists_sweptNiche_linear_bound hK hα0 hα
  refine ⟨2 * (C + 1 + |l| + |r|), by positivity, ?_⟩
  intro x hx
  have hAbs := abs_le_endpoint_sum_of_mem_Icc hx
  have hNiche := hBound x
  linarith

theorem exists_partialBarrier_bound_Icc {K : Set Plane} (hK : IsCompact K)
    {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) (l r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc l r, partialBarrier K α x ≤ C := by
  obtain ⟨C, hC, hBound⟩ := exists_sweptNiche_bound_Icc hK hα0 hα l r
  obtain ⟨D, hD⟩ :=
    (isCompact_Icc : IsCompact (Icc l r)).bddAbove_image (continuous_firstWall K α).continuousOn
  refine ⟨max C D, hC.trans (le_max_left _ _), ?_⟩
  intro x hx
  exact max_le ((hBound x hx).trans (le_max_left _ _))
    ((hD (mem_image_of_mem _ hx)).trans (le_max_right _ _))

theorem integrableOn_sweptNiche_Icc {K : Set Plane} (hK : IsCompact K)
    {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) (l r : ℝ) :
    IntegrableOn (sweptNiche K α) (Icc l r) := by
  obtain ⟨C, _hC, hBound⟩ := exists_sweptNiche_bound_Icc hK hα0 hα l r
  have hConst : IntegrableOn (fun _ : ℝ => C) (Icc l r) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  apply Integrable.mono' hConst (measurable_sweptNiche hK hα0 hα).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sweptNiche_nonneg K α x)]
  exact hBound x hx

theorem integrableOn_partialBarrier_Icc {K : Set Plane} (hK : IsCompact K)
    {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) (l r : ℝ) :
    IntegrableOn (partialBarrier K α) (Icc l r) := by
  obtain ⟨C, _hC, hBound⟩ := exists_partialBarrier_bound_Icc hK hα0 hα l r
  have hConst : IntegrableOn (fun _ : ℝ => C) (Icc l r) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  apply Integrable.mono' hConst (measurable_partialBarrier hK hα0 hα).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (partialBarrier_nonneg K α x)]
  exact hBound x hx

/-! ## The companion roof integrals -/

/-- The zero-extended cap roof is measurable and lies in `[0,1]` for every
compact set in the unit strip, so it is integrable on any finite interval. -/
theorem integrableOn_capRoof_Icc {K : Set Plane} (hK : IsCompact K)
    (hStrip : K ⊆ unitStrip) (l r : ℝ) :
    IntegrableOn (capRoof K) (Icc l r) := by
  have hK0 : ∀ p ∈ K, 0 ≤ p.2 := fun p hp => (hStrip hp).1
  have hConst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc l r) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  apply Integrable.mono' hConst (measurable_capRoof hK hK0).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (capRoof_nonneg hK hK0 x)]
    exact capRoof_le_one hK hStrip x)

theorem integrableOn_roofDeficit_Icc {K : Set Plane} (hK : IsCompact K)
    (hStrip : K ⊆ unitStrip) (l r : ℝ) :
    IntegrableOn (fun x => 1 - capRoof K x) (Icc l r) := by
  have hConst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc l r) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  exact Integrable.sub hConst (integrableOn_capRoof_Icc hK hStrip l r)

theorem IsDownwardCap.integrableOn_capRoof_Icc {U : Set Plane}
    (hU : IsDownwardCap U) (l r : ℝ) : IntegrableOn (capRoof U) (Icc l r) :=
  AmbidextrousSofa.integrableOn_capRoof_Icc hU.isCompact hU.inStrip l r

theorem IsDownwardCap.integrableOn_roofDeficit_Icc {U : Set Plane}
    (hU : IsDownwardCap U) (l r : ℝ) :
    IntegrableOn (fun x => 1 - capRoof U x) (Icc l r) :=
  AmbidextrousSofa.integrableOn_roofDeficit_Icc hU.isCompact hU.inStrip l r

end AmbidextrousSofa
