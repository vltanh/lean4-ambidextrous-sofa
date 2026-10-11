module

public import AmbidextrousSofa.Analysis.FirstUnitCrossings

@[expose] public section

/-!
# The companion fold budget after the first bad entry

On the remaining positive core, the fractional source equations make
`q - p` nonincreasing. Its initial value is at most five quarters. This
bounds the companion density by `5/4 - q`, and charges its entire excess
to one quarter of the unused first density. The argument allows an
arbitrary fractional companion-tangent source; it does not need that
source to vanish at excess points.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

/-- Full core visibility is only needed before the first bad entry.
After it, the strict sign bound alone makes the fractional energy
residual nonpositive. -/
theorem Analysis.firstUnit_core_residual_condition
    {p q χ : ℝ → ℝ} {β τ η : ℝ}
    (hχ : ∀ᵐ t ∂volume.restrict (Ioo β η), χ t ≤ 1)
    (hvisible : ∀ᵐ t ∂volume.restrict (Ioo β τ), χ t = 1)
    (hsum : ∀ t ∈ Icc τ η, p t + q t ≤ 0) :
    ∀ᵐ t ∂volume.restrict (Icc β η), χ t ≤ 1 ∧ (χ t = 1 ∨ p t + q t ≤ 0) := by
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hχ,
    ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Ioo).mp hvisible)] with t ht hχt hv
  exact ⟨hχt, (lt_or_ge t τ).imp (fun h => hv ⟨ht.1, h⟩) fun h => hsum t ⟨h, ht.2.le⟩⟩

namespace CornerArcDynamics

variable {p q u v : ℝ → ℝ}

theorem first_bad_fold_budget {L α η τ : ℝ} {δ χ : ℝ → ℝ}
    (D : CornerArcDynamics p q u v 0 L)
    (hphase : StrictCornerSignPhases p q L α η)
    (hτ : τ ∈ Ioo α η) (hpτ : p τ = -1) (hqτ : q τ ≤ 1 / 4)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) L), u t ≤ 1)
    (hprefix : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) τ), v t ≤ 1)
    (hshadow : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) L),
      p t < 0 → q t < 0 → v t = 0)
    (hsource : ∀ᵐ t ∂volume.restrict (Ioo τ η),
      u t = q t * χ t ∧ v t = (1 - v t) * δ t - p t * χ t)
    (hrange : ∀ᵐ t ∂volume.restrict (Ioo τ η),
      0 ≤ δ t ∧ δ t ≤ 1 ∧ χ t ≤ 1) :
    (∀ t ∈ Icc τ η, p t + q t ≤ -3 / 4) ∧
      ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) L), max (v t - 1) 0 ≤ (1 - u t) / 4 := by
  have Dtail := D.restrict (hphase.first_mem.1.trans hτ.1).le hτ.2.le hphase.second_mem.2.le
  have hsigns (t : ℝ) (ht : t ∈ Icc τ η) : p t ≤ -1 ∧ 0 ≤ q t ∧ q t ≤ 1 / 4 := by
    have hf := D.first_bad_future_bounds hphase hτ hpτ t ht
    refine ⟨by linarith [ht.1], ?_, by linarith [ht.1]⟩
    rcases ht.2.lt_or_eq with htη | rfl
    exacts [(hphase.core_signs t ⟨hτ.1.trans_le ht.1, htη⟩).2.le, hphase.second_zero.ge]
  -- On the remaining core the fractional source law makes `q - p` nonincreasing.
  have hw (t : ℝ) (ht : t ∈ Icc τ η) : q t - p t ≤ 5 / 4 := by
    have h := absolutelyContinuousOnInterval_quadratic_upper_bound (c := 0) (k := 0)
      (Dtail.second_ac.sub Dtail.first_ac) hτ.2.le (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo, Dtail.ode, hsource, hrange]
          with s hs hd hsrc hr
        obtain ⟨hp, hq0, hq1⟩ := hsigns s (Ioo_subset_Icc_self hs)
        refine ⟨hd.2.sub hd.1, ?_⟩
        rw [hsrc.1]
        nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hr.2.2)
          (show p s + q s + δ s * q s ≤ 0 by linarith [mul_le_of_le_one_left hq0 hr.2.1]),
          mul_nonpos_of_nonneg_of_nonpos hr.1 (show p s + 1 ≤ 0 by linarith), hsrc.2, hr.1]) ht
    simp only [Pi.sub_apply, hpτ] at h
    linarith
  refine ⟨fun t ht => by linarith [hsigns t ht], ?_⟩
  -- It bounds the companion density by `5/4 - q` on the remaining core.
  have htail : ∀ᵐ t ∂volume.restrict (Icc τ η), max (v t - 1) 0 ≤ (1 - u t) / 4 := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hsource, hrange] with t ht hs hr
    obtain ⟨hp, hq0, hq1⟩ := hsigns t (Ioo_subset_Icc_self ht)
    have hvp : v t ≤ -p t := by
      nlinarith only [mul_nonpos_of_nonneg_of_nonpos hr.1 (show p t + 1 ≤ 0 by linarith),
        mul_nonpos_of_nonpos_of_nonneg (show p t ≤ 0 by linarith) (sub_nonneg.mpr hr.2.2), hs.2,
        hr.1]
    have huq : u t ≤ q t := hs.1 ▸ mul_le_of_le_one_right hq0 hr.2.2
    have := hw t (Ioo_subset_Icc_self ht)
    exact max_le (by linarith) (by linarith)
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hunit, hshadow,
    ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Icc).mp htail),
    ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Ioo).mp hprefix)]
    with t ht hut hs htail hpref
  by_cases hin : t ∈ Icc τ η
  · exact htail hin
  -- Outside the remaining core the companion density is unit bounded.
  have hv : v t ≤ 1 := by
    rcases lt_or_ge t τ with htτ | htτ
    · exact hpref ⟨ht.1, htτ⟩
    · have hsign := hphase.final_signs t ⟨lt_of_not_ge fun h => hin ⟨htτ, h⟩, ht.2.le⟩
      exact (hs hsign.1 hsign.2).trans_le zero_le_one
  exact max_le (by linarith) (by linarith)

end CornerArcDynamics

end AmbidextrousSofa
