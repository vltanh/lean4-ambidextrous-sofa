module

public import AmbidextrousSofa.Analysis.FirstUnitCrossings

@[expose] public section

/-!
# Exact source sectors from one common occupation law

The two source equations use the same corner coefficient. The initial
positive sector forces that coefficient to vanish; the final negative
sector forces both the corner and companion-tangent coefficients to
vanish. The actual first-tangent window then supplies the charged and
uncharged formulas for either order of the window crossing and the
second momentum zero.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa.Analysis

theorem firstUnit_initial_source_of_common_balance
    {p q u v b δ χ : ℝ} (hq : 0 < q) (hb : 0 ≤ b) (hχ : 0 ≤ χ)
    (hu0 : u = 0) (hu : u = (1 - u) * b + q * χ)
    (hv : v = (1 - v) * δ - p * χ) : u = 0 ∧ v = (1 - v) * δ := by
  have heq : 0 = b + q * χ := by
    simpa only [hu0, sub_zero, one_mul] using hu
  have hprod : 0 ≤ q * χ := mul_nonneg hq.le hχ
  have hprod0 : q * χ = 0 := by linarith only [heq, hb, hprod]
  have hχ0 : χ = 0 := (mul_eq_zero.mp hprod0).resolve_left hq.ne'
  exact ⟨hu0, by simpa only [hχ0, mul_zero, sub_zero] using hv⟩

theorem firstUnit_negative_source_coefficients_zero
    {p v δ χ : ℝ} (hp : p < 0) (hδ : 0 ≤ δ) (hχ : 0 ≤ χ)
    (hv0 : v = 0) (hv : v = (1 - v) * δ - p * χ) : δ = 0 ∧ χ = 0 := by
  have heq : 0 = δ - p * χ := by
    simpa only [hv0, sub_zero, one_mul] using hv
  have hprod : 0 ≤ (-p) * χ := mul_nonneg (neg_nonneg.mpr hp.le) hχ
  have hprod0 : (-p) * χ = 0 := by nlinarith only [heq, hδ, hprod]
  have hχ0 : χ = 0 := (mul_eq_zero.mp hprod0).resolve_left (neg_pos.mpr hp).ne'
  have hδ0 : δ = 0 := by simpa only [hχ0, mul_zero, sub_zero] using heq.symm
  exact ⟨hδ0, hχ0⟩

theorem firstUnit_late_charged_source_of_common_balance
    {p q u v b δ χ : ℝ} (hp : p < 0) (hδ : 0 ≤ δ) (hχ : 0 ≤ χ)
    (hb : b = 1) (hv0 : v = 0)
    (hu : u = (1 - u) * b + q * χ) (hv : v = (1 - v) * δ - p * χ) :
    u = 1 / 2 ∧ v = 0 := by
  have hzero := firstUnit_negative_source_coefficients_zero hp hδ hχ hv0 hv
  rw [hb, hzero.2, mul_one, mul_zero, add_zero] at hu
  exact ⟨by linarith only [hu], hv0⟩

theorem firstUnit_final_source_of_common_balance
    {p q u v b δ χ : ℝ} (hp : p < 0) (hδ : 0 ≤ δ) (hχ : 0 ≤ χ)
    (hb : b = 0) (hv0 : v = 0)
    (hu : u = (1 - u) * b + q * χ) (hv : v = (1 - v) * δ - p * χ) :
    u = 0 ∧ v = 0 := by
  have hzero := firstUnit_negative_source_coefficients_zero hp hδ hχ hv0 hv
  exact ⟨by simpa only [hb, hzero.2, mul_zero, add_zero] using hu, hv0⟩

/-- The exact five sectors follow from the common balance and the
actual charged first-tangent indicator. Corner visibility is used only
on the charged part of the positive core. -/
theorem firstUnit_source_sectors_of_common_balance
    {p q u v b δ χ : ℝ → ℝ} {L α β η : ℝ}
    (hphase : StrictCornerSignPhases p q L α η) (hαβ : α ≤ β) (hβL : β ≤ L)
    (hbalance : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) L),
      u t = (1 - u t) * b t + q t * χ t ∧
        v t = (1 - v t) * δ t - p t * χ t)
    (hnonneg : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) L),
      0 ≤ b t ∧ 0 ≤ δ t ∧ 0 ≤ χ t)
    (hfirstShadow : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) L),
      0 < p t → 0 < q t → u t = 0)
    (hsecondShadow : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) L),
      p t < 0 → q t < 0 → v t = 0)
    (hcharged : ∀ᵐ t ∂volume.restrict (Ioo α β), b t = 1)
    (hafter : ∀ᵐ t ∂volume.restrict (Ioo β L), b t = 0)
    (hvisible : ∀ᵐ t ∂volume.restrict (Ioo α (min β η)), χ t = 1) :
    (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) α),
      u t = 0 ∧ v t = (1 - v t) * δ t) ∧
    (∀ᵐ t ∂volume.restrict (Icc α (min β η)),
      u t = (1 - u t) + q t ∧ v t = (1 - v t) * δ t - p t) ∧
    (∀ᵐ t ∂volume.restrict (Icc (min β η) η),
      u t = q t * χ t ∧ v t = (1 - v t) * δ t - p t * χ t) ∧
    (∀ᵐ t ∂volume.restrict (Icc η (max β η)), u t = 1 / 2 ∧ v t = 0) ∧
    (∀ᵐ t ∂volume.restrict (Icc (max β η) L), u t = 0 ∧ v t = 0) := by
  have h0α : 0 ≤ α := hphase.first_mem.1.le
  have h0η : 0 ≤ η := (hphase.first_mem.1.trans hphase.second_mem.1).le
  have hmaxL : max β η ≤ L := max_le hβL hphase.second_mem.2.le
  have hchargedGlobal := (ae_restrict_iff' measurableSet_Ioo).mp hcharged
  have hafterGlobal := (ae_restrict_iff' measurableSet_Ioo).mp hafter
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← restrict_Ioo_eq_restrict_Icc]
    have hsub : Ioo (0 : ℝ) α ⊆ Ioo (0 : ℝ) L :=
      Ioo_subset_Ioo le_rfl hphase.first_mem.2.le
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset hsub hbalance,
      ae_restrict_of_ae_restrict_of_subset hsub hnonneg,
      ae_restrict_of_ae_restrict_of_subset hsub hfirstShadow] with t ht hs hn hz
    have hsign := hphase.initial_signs t ⟨ht.1.le, ht.2⟩
    exact firstUnit_initial_source_of_common_balance hsign.2 hn.1 hn.2.2
      (hz hsign.1 hsign.2) hs.1 hs.2
  · rw [← restrict_Ioo_eq_restrict_Icc]
    have hsub : Ioo α (min β η) ⊆ Ioo (0 : ℝ) L :=
      Ioo_subset_Ioo h0α ((min_le_right _ _).trans hphase.second_mem.2.le)
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset hsub hbalance,
      ae_restrict_of_ae hchargedGlobal, hvisible] with t ht hs hb hχ
    have hb1 := hb ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
    simpa only [hb1, hχ, mul_one] using hs
  · rw [← restrict_Ioo_eq_restrict_Icc]
    have hsub : Ioo (min β η) η ⊆ Ioo (0 : ℝ) L :=
      Ioo_subset_Ioo (le_min (h0α.trans hαβ) h0η) hphase.second_mem.2.le
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset hsub hbalance,
      ae_restrict_of_ae hafterGlobal] with t ht hs hb
    have hβt : β < t := by
      by_contra hnot
      exact (not_le_of_gt ht.1) (le_min (le_of_not_gt hnot) ht.2.le)
    have hb0 := hb ⟨hβt, ht.2.trans hphase.second_mem.2⟩
    simpa only [hb0, mul_zero, zero_add] using hs
  · rw [← restrict_Ioo_eq_restrict_Icc]
    have hsub : Ioo η (max β η) ⊆ Ioo (0 : ℝ) L := Ioo_subset_Ioo h0η hmaxL
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset hsub hbalance,
      ae_restrict_of_ae_restrict_of_subset hsub hnonneg,
      ae_restrict_of_ae_restrict_of_subset hsub hsecondShadow,
      ae_restrict_of_ae hchargedGlobal] with t ht hs hn hz hb
    have htβ : t < β := by
      by_contra hnot
      exact (not_le_of_gt ht.2) (max_le (le_of_not_gt hnot) ht.1.le)
    have hsign := hphase.final_signs t ⟨ht.1, ht.2.le.trans hmaxL⟩
    exact firstUnit_late_charged_source_of_common_balance hsign.1 hn.2.1 hn.2.2
      (hb ⟨hphase.second_mem.1.trans ht.1, htβ⟩) (hz hsign.1 hsign.2) hs.1 hs.2
  · rw [← restrict_Ioo_eq_restrict_Icc]
    have hsub : Ioo (max β η) L ⊆ Ioo (0 : ℝ) L :=
      Ioo_subset_Ioo (h0η.trans (le_max_right _ _)) le_rfl
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset hsub hbalance,
      ae_restrict_of_ae_restrict_of_subset hsub hnonneg,
      ae_restrict_of_ae_restrict_of_subset hsub hsecondShadow,
      ae_restrict_of_ae hafterGlobal] with t ht hs hn hz hb
    have hsign := hphase.final_signs t ⟨(le_max_right _ _).trans_lt ht.1, ht.2.le⟩
    exact firstUnit_final_source_of_common_balance hsign.1 hn.2.1 hn.2.2
      (hb ⟨(le_max_left _ _).trans_lt ht.1, ht.2⟩) (hz hsign.1 hsign.2) hs.1 hs.2

end AmbidextrousSofa.Analysis
