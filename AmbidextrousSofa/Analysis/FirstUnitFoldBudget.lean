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

namespace Analysis

theorem firstUnit_fractional_core_difference_derivative_nonpos
    {p q u v δ χ : ℝ} (hp : p ≤ -1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 4)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hχ1 : χ ≤ 1)
    (hu : u = q * χ) (hv : v = (1 - v) * δ - p * χ) :
    (v - 1 + p) - (u - 1 - q) ≤ 0 := by
  have hden : 0 < 1 + δ := by linarith only [hδ0]
  have hv' : (1 + δ) * v = δ - p * χ := by nlinarith only [hv]
  have hid : (1 + δ) * ((v - 1 + p) - (u - 1 - q)) =
      (1 - χ) * (p + q + δ * q) + δ * (p + 1) := by
    calc
      _ = (1 + δ) * v - (1 + δ) * u + (1 + δ) * (p + q) := by ring
      _ = (δ - p * χ) - (1 + δ) * (q * χ) + (1 + δ) * (p + q) := by
        rw [hv', hu]
      _ = _ := by ring
  have hδq : δ * q ≤ q := by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hδ1 hq0
  have hbracket : p + q + δ * q ≤ 0 := by linarith only [hp, hq1, hδq]
  have hnonpos : (1 + δ) * ((v - 1 + p) - (u - 1 - q)) ≤ 0 := by
    rw [hid]
    exact add_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hχ1) hbracket)
      (mul_nonpos_of_nonneg_of_nonpos hδ0 (by linarith only [hp]))
  by_contra hnot
  exact (not_le_of_gt (mul_pos hden (lt_of_not_ge hnot))) hnonpos

theorem firstUnit_fractional_companion_le_neg_first
    {p v δ χ : ℝ} (hp : p ≤ -1) (hδ0 : 0 ≤ δ) (hχ1 : χ ≤ 1)
    (hv : v = (1 - v) * δ - p * χ) : v ≤ -p := by
  have hden : 0 < 1 + δ := by linarith only [hδ0]
  have hid : (1 + δ) * (v + p) = δ * (p + 1) + p * (1 - χ) := by
    nlinarith only [hv]
  have hnonpos : (1 + δ) * (v + p) ≤ 0 := by
    rw [hid]
    exact add_nonpos
      (mul_nonpos_of_nonneg_of_nonpos hδ0 (by linarith only [hp]))
      (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hp]) (sub_nonneg.mpr hχ1))
  by_contra hnot
  have hpos : 0 < v + p := by linarith only [lt_of_not_ge hnot]
  exact (not_le_of_gt (mul_pos hden hpos)) hnonpos

theorem firstUnit_fractional_core_fold_le
    {p q u v δ χ : ℝ} (hp : p ≤ -1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 4)
    (hδ0 : 0 ≤ δ) (hχ1 : χ ≤ 1) (hw : q - p ≤ 5 / 4)
    (hu : u = q * χ) (hv : v = (1 - v) * δ - p * χ) :
    v ≤ 5 / 4 ∧ max (v - 1) 0 ≤ (1 - u) / 4 := by
  have hvp := firstUnit_fractional_companion_le_neg_first hp hδ0 hχ1 hv
  have huq : u ≤ q := by
    rw [hu]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hχ1 hq0
  refine ⟨by linarith only [hvp, hw, hq0], max_le ?_ ?_⟩
  · linarith only [hvp, hw, huq, hq0]
  · linarith only [huq, hq1]

theorem firstUnit_fold_le_of_companion_le_one {u v : ℝ}
    (hu : u ≤ 1) (hv : v ≤ 1) : max (v - 1) 0 ≤ (1 - u) / 4 := by
  rw [max_eq_right (sub_nonpos.mpr hv)]
  exact div_nonneg (sub_nonneg.mpr hu) (by norm_num)

/-- The only analytic input beyond the momentum ODE is the literal
fractional source law on the remaining core. No fold bound is assumed. -/
theorem firstUnit_fractional_core_fold_bound
    {p q u v δ χ : ℝ → ℝ} {τ η : ℝ} (hτη : τ ≤ η)
    (hp : AbsolutelyContinuousOnInterval p τ η)
    (hq : AbsolutelyContinuousOnInterval q τ η)
    (hpτ : p τ = -1) (hqτ : q τ ≤ 1 / 4)
    (hphase : ∀ t ∈ Icc τ η, p t ≤ -1 ∧ 0 ≤ q t ∧ q t ≤ 1 / 4)
    (hode : ∀ᵐ t ∂volume.restrict (Ioo τ η),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hsource : ∀ᵐ t ∂volume.restrict (Ioo τ η),
      u t = q t * χ t ∧ v t = (1 - v t) * δ t - p t * χ t)
    (hrange : ∀ᵐ t ∂volume.restrict (Ioo τ η),
      0 ≤ δ t ∧ δ t ≤ 1 ∧ χ t ≤ 1) :
    (∀ t ∈ Icc τ η, q t - p t ≤ 5 / 4) ∧
      (∀ᵐ t ∂volume.restrict (Ioo τ η),
        v t ≤ 5 / 4 ∧ max (v t - 1) 0 ≤ (1 - u t) / 4) := by
  have hd : ∀ᵐ t ∂volume.restrict (Ioo τ η),
      HasDerivAt (fun s => q s - p s) ((v t - 1 + p t) - (u t - 1 - q t)) t ∧
        (v t - 1 + p t) - (u t - 1 - q t) ≤ 0 + 0 * (t - τ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hode, hsource, hrange]
      with t ht hdt hs hr
    obtain ⟨hpt, hqt0, hqt1⟩ := hphase t (Ioo_subset_Icc_self ht)
    refine ⟨hdt.2.sub hdt.1, ?_⟩
    simpa only [zero_mul, add_zero] using
      firstUnit_fractional_core_difference_derivative_nonpos
        hpt hqt0 hqt1 hr.1 hr.2.1 hr.2.2 hs.1 hs.2
  have hw : ∀ t ∈ Icc τ η, q t - p t ≤ 5 / 4 := by
    intro t ht
    have h := absolutelyContinuousOnInterval_quadratic_upper_bound (hq.sub hp) hτη hd ht
    simp only [Pi.sub_apply, zero_mul, zero_div, add_zero, hpτ] at h
    linarith only [h, hqτ]
  refine ⟨hw, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hsource, hrange] with t ht hs hr
  obtain ⟨hpt, hqt0, hqt1⟩ := hphase t (Ioo_subset_Icc_self ht)
  exact firstUnit_fractional_core_fold_le hpt hqt0 hqt1 hr.1 hr.2.2
    (hw t (Ioo_subset_Icc_self ht)) hs.1 hs.2

/-- Full core visibility is only needed before the first bad entry.
After it, the strict sign bound alone makes the fractional energy
residual nonpositive. -/
theorem firstUnit_core_residual_condition
    {p q χ : ℝ → ℝ} {β τ η : ℝ}
    (hχ : ∀ᵐ t ∂volume.restrict (Ioo β η), χ t ≤ 1)
    (hvisible : ∀ᵐ t ∂volume.restrict (Ioo β τ), χ t = 1)
    (hsum : ∀ t ∈ Icc τ η, p t + q t ≤ 0) :
    ∀ᵐ t ∂volume.restrict (Icc β η), χ t ≤ 1 ∧ (χ t = 1 ∨ p t + q t ≤ 0) := by
  rw [← restrict_Ioo_eq_restrict_Icc]
  have hvisible' := (ae_restrict_iff' measurableSet_Ioo).mp hvisible
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hχ, ae_restrict_of_ae hvisible']
    with t ht hχt hv
  refine ⟨hχt, ?_⟩
  by_cases htτ : t < τ
  · exact Or.inl (hv ⟨ht.1, htτ⟩)
  · exact Or.inr (hsum t ⟨le_of_not_gt htτ, ht.2.le⟩)

end Analysis

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
    (∀ t ∈ Icc τ η, q t - p t ≤ 5 / 4 ∧ p t + q t ≤ -3 / 4) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) L),
        v t ≤ 5 / 4 ∧ max (v t - 1) 0 ≤ (1 - u t) / 4) := by
  have h0τ : 0 ≤ τ := (hphase.first_mem.1.trans hτ.1).le
  have Dtail := D.restrict h0τ hτ.2.le hphase.second_mem.2.le
  have hfuture := D.first_bad_future_bounds hphase hτ hpτ
  have htailSigns : ∀ t ∈ Icc τ η, p t ≤ -1 ∧ 0 ≤ q t ∧ q t ≤ 1 / 4 := by
    intro t ht
    have hf := hfuture t ht
    have hqt : 0 ≤ q t := by
      rcases ht.2.lt_or_eq with htη | htη
      · exact (hphase.core_signs t ⟨hτ.1.trans_le ht.1, htη⟩).2.le
      · simpa only [htη, hphase.second_zero] using (le_rfl : (0 : ℝ) ≤ 0)
    exact ⟨by linarith only [hf.1, ht.1], hqt,
      by linarith only [hf.2, ht.1, hqτ]⟩
  obtain ⟨hw, hfold⟩ := Analysis.firstUnit_fractional_core_fold_bound hτ.2.le
    Dtail.first_ac Dtail.second_ac hpτ hqτ htailSigns Dtail.ode hsource hrange
  refine ⟨?_, ?_⟩
  · intro t ht
    exact ⟨hw t ht, by linarith only [(htailSigns t ht).1, (htailSigns t ht).2.2]⟩
  · have hfoldClosed : ∀ᵐ t ∂volume.restrict (Icc τ η),
        v t ≤ 5 / 4 ∧ max (v t - 1) 0 ≤ (1 - u t) / 4 := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact hfold
    have htailGlobal := (ae_restrict_iff' measurableSet_Icc).mp hfoldClosed
    have hprefixGlobal := (ae_restrict_iff' measurableSet_Ioo).mp hprefix
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hunit, hshadow,
      ae_restrict_of_ae htailGlobal, ae_restrict_of_ae hprefixGlobal]
      with t ht hut hs htail hpref
    by_cases htτ : t < τ
    · have hv := hpref ⟨ht.1, htτ⟩
      exact ⟨by linarith only [hv], Analysis.firstUnit_fold_le_of_companion_le_one hut hv⟩
    · by_cases htη : t ≤ η
      · exact htail ⟨le_of_not_gt htτ, htη⟩
      · have hsign := hphase.final_signs t ⟨lt_of_not_ge htη, ht.2.le⟩
        have hv : v t ≤ 1 := by rw [hs hsign.1 hsign.2]; norm_num
        exact ⟨by linarith only [hv], Analysis.firstUnit_fold_le_of_companion_le_one hut hv⟩

end CornerArcDynamics

end AmbidextrousSofa
