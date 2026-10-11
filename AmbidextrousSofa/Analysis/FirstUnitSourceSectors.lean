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
  obtain ⟨h0α, hαL⟩ := hphase.first_mem
  obtain ⟨hαη, hηL⟩ := hphase.second_mem
  have hmaxL : max β η ≤ L := max_le hβL hηL.le
  have hall := (ae_restrict_iff' measurableSet_Ioo).mp
    (hbalance.and (hnonneg.and (hfirstShadow.and hsecondShadow)))
  have hC := (ae_restrict_iff' measurableSet_Ioo).mp hcharged
  have hA := (ae_restrict_iff' measurableSet_Ioo).mp hafter
  have hV := (ae_restrict_iff' measurableSet_Ioo).mp hvisible
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [← restrict_Ioo_eq_restrict_Icc] <;>
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hall,
      ae_restrict_of_ae hC, ae_restrict_of_ae hA, ae_restrict_of_ae hV]
      with t ht hk hb1 hb0 hχ1
  · obtain ⟨⟨hu, hv⟩, ⟨hb, -, hχ⟩, hz, -⟩ := hk ⟨ht.1, ht.2.trans hαL⟩
    obtain ⟨hp, hq⟩ := hphase.initial_signs t ⟨ht.1.le, ht.2⟩
    rw [hz hp hq] at hu ⊢
    have hχ0 : χ t = 0 := by nlinarith only [hu, hb, hχ, hq]
    exact ⟨rfl, by simpa only [hχ0, mul_zero, sub_zero] using hv⟩
  · simpa only [hb1 ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩, hχ1 ht, mul_one] using
      (hk ⟨h0α.trans ht.1, ht.2.trans_le ((min_le_right _ _).trans hηL.le)⟩).1
  · have hβt : β < t := (min_lt_iff.mp ht.1).resolve_right (not_lt.mpr ht.2.le)
    simpa only [hb0 ⟨hβt, ht.2.trans hηL⟩, mul_zero, zero_add] using
      (hk ⟨(h0α.trans_le hαβ).trans hβt, ht.2.trans hηL⟩).1
  · obtain ⟨⟨hu, hv⟩, ⟨-, hδ, hχ⟩, -, hz⟩ :=
      hk ⟨(h0α.trans hαη).trans ht.1, ht.2.trans_le hmaxL⟩
    obtain ⟨hp, hq⟩ := hphase.final_signs t ⟨ht.1, ht.2.le.trans hmaxL⟩
    rw [hz hp hq] at hv ⊢
    have hχ0 : χ t = 0 := by nlinarith only [hv, hδ, hχ, hp]
    rw [hb1 ⟨hαη.trans ht.1, (lt_max_iff.mp ht.2).resolve_right (not_lt.mpr ht.1.le)⟩,
      hχ0] at hu
    exact ⟨by linarith only [hu], rfl⟩
  · have hηt := (le_max_right β η).trans_lt ht.1
    obtain ⟨⟨hu, hv⟩, ⟨-, hδ, hχ⟩, -, hz⟩ := hk ⟨(h0α.trans hαη).trans hηt, ht.2⟩
    obtain ⟨hp, hq⟩ := hphase.final_signs t ⟨hηt, ht.2.le⟩
    rw [hz hp hq] at hv ⊢
    have hχ0 : χ t = 0 := by nlinarith only [hv, hδ, hχ, hp]
    rw [hb0 ⟨(le_max_left β η).trans_lt ht.1, ht.2⟩, hχ0] at hu
    exact ⟨by linarith only [hu], rfl⟩

end AmbidextrousSofa.Analysis
