module

public import AmbidextrousSofa.Analysis.PartialSharpCurvatureDensity

@[expose] public section

/-!
# The actual proper regular upper domain

The terminal normal is removed in addition to the top and affine-middle
normals. Restricting the previously proved three-wing measure argument
to each side of the terminal normal glues the actual proper interval
bounds. The resulting density is the curvature of the original cap on
this entire regular domain.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def regularProperCurvatureDomain (α m : ℝ) : Set ℝ :=
  regularCurvatureDomain m \ {α}

theorem isOpen_regularProperCurvatureDomain (α m : ℝ) :
    IsOpen (regularProperCurvatureDomain α m) := by
  have hopen : IsOpen (regularCurvatureDomain m) := by
    rw [regularCurvatureDomain_eq_three]
    exact (isOpen_Ioo.union isOpen_Ioo).union isOpen_Ioo
  exact hopen.diff isClosed_singleton

theorem measurableSet_regularProperCurvatureDomain (α m : ℝ) :
    MeasurableSet (regularProperCurvatureDomain α m) :=
  (isOpen_regularProperCurvatureDomain α m).measurableSet

theorem regularProperCurvatureDomain_subset (α m : ℝ) :
    regularProperCurvatureDomain α m ⊆ Ioo (0 : ℝ) Real.pi :=
  sdiff_subset.trans (regularCurvatureDomain_subset m)

theorem regularProperCurvatureDomain_eq_sides (α m : ℝ) :
    regularProperCurvatureDomain α m =
      (regularCurvatureDomain m ∩ Iio α) ∪ (regularCurvatureDomain m ∩ Ioi α) := by
  ext t
  simp only [regularProperCurvatureDomain, mem_sdiff, mem_singleton_iff,
    mem_union, mem_inter_iff, mem_Iio, mem_Ioi]
  constructor
  · rintro ⟨ht, hne⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨ht, hlt⟩
    · exact Or.inr ⟨ht, hgt⟩
  · rintro (⟨ht, hlt⟩ | ⟨ht, hgt⟩)
    · exact ⟨ht, hlt.ne⟩
    · exact ⟨ht, hgt.ne'⟩

theorem measure_restrict_regularProperCurvatureDomain_le
    {μ ν : Measure ℝ} {α m : ℝ}
    (h : ∀ A B : ℝ, 0 ≤ A → B ≤ Real.pi → Real.pi / 2 ∉ Ioo A B →
      α ∉ Ioo A B → (∀ t ∈ Ioo A B, Real.cos t + m * Real.sin t ≠ 0) →
        μ.restrict (Ioo A B) ≤ ν.restrict (Ioo A B)) :
    μ.restrict (regularProperCurvatureDomain α m) ≤
      ν.restrict (regularProperCurvatureDomain α m) := by
  have hbelow : (μ.restrict (Iio α)).restrict (regularCurvatureDomain m) ≤
      (ν.restrict (Iio α)).restrict (regularCurvatureDomain m) := by
    apply measure_restrict_regularCurvatureDomain_le
    intro A B hA hB htop hperp
    have hsub : Ioo A (min B α) ⊆ Ioo A B := fun t ht =>
      ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
    have hbound := h A (min B α) hA ((min_le_left _ _).trans hB)
      (fun ht => htop (hsub ht))
      (fun ht => (not_lt_of_ge (min_le_right B α)) ht.2)
      (fun t ht => hperp t (hsub ht))
    have hinter : Ioo A B ∩ Iio α = Ioo A (min B α) := by
      ext t
      simp only [mem_inter_iff, mem_Ioo, mem_Iio, lt_min_iff]
      tauto
    simpa only [Measure.restrict_restrict measurableSet_Ioo, hinter] using hbound
  have habove : (μ.restrict (Ioi α)).restrict (regularCurvatureDomain m) ≤
      (ν.restrict (Ioi α)).restrict (regularCurvatureDomain m) := by
    apply measure_restrict_regularCurvatureDomain_le
    intro A B hA hB htop hperp
    have hsub : Ioo (max A α) B ⊆ Ioo A B := fun t ht =>
      ⟨(le_max_left _ _).trans_lt ht.1, ht.2⟩
    have hbound := h (max A α) B (hA.trans (le_max_left _ _)) hB
      (fun ht => htop (hsub ht))
      (fun ht => (not_lt_of_ge (le_max_right A α)) ht.1)
      (fun t ht => hperp t (hsub ht))
    have hinter : Ioo A B ∩ Ioi α = Ioo (max A α) B := by
      ext t
      simp only [mem_inter_iff, mem_Ioo, mem_Ioi, max_lt_iff]
      tauto
    simpa only [Measure.restrict_restrict measurableSet_Ioo, hinter] using hbound
  rw [Measure.restrict_restrict (measurableSet_regularCurvatureDomain m)] at hbelow habove
  have hd : Disjoint (regularCurvatureDomain m ∩ Iio α)
      (regularCurvatureDomain m ∩ Ioi α) := by
    apply disjoint_left.mpr
    intro t ht hs
    exact (not_lt_of_ge hs.2.le) ht.2
  rw [regularProperCurvatureDomain_eq_sides,
    Measure.restrict_union hd ((measurableSet_regularCurvatureDomain m).inter measurableSet_Ioi),
    Measure.restrict_union hd ((measurableSet_regularCurvatureDomain m).inter measurableSet_Ioi)]
  exact add_le_add hbelow habove

theorem IsJointCapMaximizer.curvature_density_on_regular_proper_domain
    {K : Set Plane} {α m c : ℝ} (hK : IsJointCapMaximizer K α)
    (hproper : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity K t)) ∧
      (∀ t, ρ t ≤ 8 * (|horizontalLeft K| + |horizontalRight K| + 1) + 24) ∧
      (upperCurvature K).restrict (regularProperCurvatureDomain α m) =
        (volume.restrict (regularProperCurvatureDomain α m)).withDensity
          (fun t => ENNReal.ofReal (ρ t)) := by
  let C := 8 * (|horizontalLeft K| + |horizontalRight K| + 1) + 24
  let f := fun t => ENNReal.ofReal (sourceKappa (upperCornerVelocity K t))
  have hcoarse : (upperCurvature K).restrict (regularProperCurvatureDomain α m) ≤
      ENNReal.ofReal C • volume.restrict (regularProperCurvatureDomain α m) := by
    have h := measure_restrict_regularProperCurvatureDomain_le
      (μ := upperCurvature K) (ν := ENNReal.ofReal C • (volume : Measure ℝ))
      (α := α) (m := m) (by
        intro A B hA hB htop hterminal hperp
        simpa only [Measure.restrict_smul] using
          hK.curvature_restrict_le_on_proper_open_wing hproper haffine hA hB htop hterminal hperp)
    simpa only [Measure.restrict_smul] using h
  have hsharp : (upperCurvature K).restrict (regularProperCurvatureDomain α m) ≤
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity f := by
    have h := measure_restrict_regularProperCurvatureDomain_le
      (μ := upperCurvature K) (ν := (volume : Measure ℝ).withDensity f)
      (α := α) (m := m) (by
        intro A B hA hB htop hterminal hperp
        simpa only [Measure.restrict_withDensity measurableSet_Ioo] using
          hK.curvature_restrict_le_source_density_on_proper_open_wing hproper haffine
            hA hB htop hterminal hperp)
    simpa only [Measure.restrict_withDensity (measurableSet_regularProperCurvatureDomain α m)] using h
  letI : IsFiniteMeasure ((upperCurvature K).restrict (regularProperCurvatureDomain α m)) :=
    isFiniteMeasure_restrict.mpr
      (lt_of_le_of_lt (measure_mono (regularProperCurvatureDomain_subset α m)) measure_Ioo_lt_top).ne
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (regularProperCurvatureDomain α m)) :=
    isFiniteMeasure_restrict.mpr
      (lt_of_le_of_lt (measure_mono (regularProperCurvatureDomain_subset α m)) measure_Ioo_lt_top).ne
  exact exists_real_density_of_two_bounds (by dsimp [C]; positivity)
    (continuous_sourceKappa.measurable.comp hK.isCap.measurable_upperCornerVelocity)
    (fun t => sourceKappa_nonneg _) hcoarse hsharp

theorem IsJointCapMaximizer.sigmaAt_eq_zero_on_regular_proper_domain
    {K : Set Plane} {α m c t : ℝ} (hK : IsJointCapMaximizer K α)
    (hproper : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (ht : t ∈ regularProperCurvatureDomain α m) : MovingSofaOptimality.sigmaAt K t = 0 := by
  obtain ⟨ρ, hρ, hρbounds, _, heq⟩ := hK.curvature_density_on_regular_proper_domain hproper haffine
  have h := measureReal_eq_integral_of_restrict_withDensity hρ (fun x => (hρbounds x).1)
    heq (measurableSet_singleton t) (singleton_subset_iff.mpr ht)
  simpa [MovingSofaOptimality.sigmaAt, upperCurvature, measureReal_def, integral_singleton] using h

end AmbidextrousSofa
