module

public import AmbidextrousSofa.Analysis.HorizontalLeakageDynamics

@[expose] public section

/-!
# Actual short-interval occupation of horizontal curvature excess

The first `q = 1` crossing closes all possible future excess by the
energy theorem. Before it, the first `p = 0` crossing is the only possible
start of excess. The exact source bounds force its quadratic decay and
locate its starting time. The actual maximizing cap supplies every ODE
and source hypothesis in the final application.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem HorizontalCornerDynamics.exists_quadratic_excess_envelope
    {p q u v : ℝ → ℝ} {L C e h T : ℝ}
    (D : HorizontalCornerDynamics p q u v L)
    (he : 0 < e) (hC : 2 / 3 < C) (hh : 0 ≤ h) (hh1 : h < 1)
    (hT : 0 ≤ T) (hcross : e ≤ 3 * C * T - T ^ 2 / 2)
    (henergy : 9 * C ^ 2 - e * (1 - e) ≤
      (2 + (h ^ 2 + 2 * h) / 4) ^ 2)
    (hplim : Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 e))
    (hqlim : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 (3 * C - 1)))
    (hlater : ∃ d ∈ Ioo (0 : ℝ) L, q d ≤ 1) :
    ∃ A ∈ Icc (0 : ℝ) T,
      ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) L),
        u s - 1 ≤ horizontalLeakageEnvelope A h s := by
  obtain ⟨d, hd, hqd⟩ := hlater
  obtain ⟨b, hb, hqb, hqbefore⟩ := exists_first_level_crossing_of_right_limit
    (fun t ht => (D.continuous t ht).2) hqlim (by linarith : 1 < 3 * C - 1) hd hqd
  have hbL : b < L := hb.2.trans_lt hd.2
  have hfuture := (ae_restrict_iff' measurableSet_Ioo).mp
    (D.ae_unit_after_first_eq_one ⟨hb.1, hbL⟩ hqb)
  by_cases hpb : 0 < p b
  · refine ⟨0, ⟨le_rfl, hT⟩, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo, D.shadow,
      ae_restrict_of_ae hfuture, ae_restrict_of_ae (volume.ae_ne b)] with s hs hshadow hf hne
    refine (sub_nonpos.mpr ?_).trans (horizontalLeakageEnvelope_nonneg 0 h s)
    rcases lt_or_ge s b with hsb | hsb
    · have := D.first_linear_decrease hs.1 hsb.le hbL
        (fun t ht => hqbefore t ⟨hs.1.trans ht.1, ht.2⟩) ⟨hsb.le, le_rfl⟩
      linarith [(hshadow (by linarith) (by linarith [hqbefore s ⟨hs.1, hsb⟩])).1]
    · exact hf ⟨hsb.lt_of_ne' hne, hs.2⟩
  obtain ⟨A, hA, hpA, hpbefore⟩ := exists_first_level_crossing_of_right_limit
    (fun t ht => (D.continuous t ht).1) hplim he ⟨hb.1, hbL⟩ (le_of_not_gt hpb)
  have hAL : A < L := hA.2.trans_lt hbL
  have hqstart :=
    D.crossing_first_bound he.le (by positivity) hplim hqlim henergy ⟨hA.1, hAL⟩ hpA
  have hqdec {s : ℝ} (hs : s ∈ Icc A b) (hs1 : s ≤ A + 1) :
      q s ≤ q A - (s - A) / 2 - (s - A) ^ 2 / 4 :=
    D.second_quadratic_after_crossing hA.1 hA.2 hbL hpA
      (fun s hs => hqbefore s ⟨hA.1.trans hs.1, hs.2⟩) hs hs1
  have hbh : b ≤ A + h := by
    by_contra! hbh
    obtain ⟨s, hs0, hs1⟩ := exists_between (lt_min hbh (by linarith : A + h < A + 1))
    have hsb := hs1.trans_le (min_le_left _ _)
    have hAs : A < s := by linarith
    nlinarith [hqbefore s ⟨hA.1.trans hAs, hsb⟩, hqdec ⟨hAs.le, hsb.le⟩
      (hs1.trans_le (min_le_right _ _)).le,
      mul_pos (by linarith : 0 < (s - A) - h) (by linarith : 0 < (s - A) + h + 2)]
  have hAT : A ≤ T := by
    by_contra! hTA
    have hTpos : 0 < T := hT.lt_of_ne (by rintro rfl; linarith)
    nlinarith [hpbefore T ⟨hTpos, hTA⟩, D.first_quadratic_before_crossing hplim hqlim hAL
      hpbefore (fun s hs => hqbefore s ⟨hs.1, hs.2.trans_le hA.2⟩) ⟨hTpos, hTA.le⟩]
  refine ⟨A, ⟨hA.1.le, hAT⟩, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo, D.shadow, D.source,
    ae_restrict_of_ae hfuture, ae_restrict_of_ae (volume.ae_ne b)]
    with s hs hshadow hsource hf hne
  rcases lt_or_ge s A with hsA | hsA
  · linarith [(hshadow (hpbefore s ⟨hs.1, hsA⟩)
      (by linarith [hqbefore s ⟨hs.1, hsA.trans_le hA.2⟩])).1,
      horizontalLeakageEnvelope_nonneg A h s]
  rcases lt_or_ge s b with hsb | hsb
  · have hmem : s ∈ Icc A (A + h) := ⟨hsA, hsb.le.trans hbh⟩
    have hu := hsource.1
    rw [sourceKappa_eq_self_of_one_le (hqbefore s ⟨hs.1, hsb⟩).le] at hu
    rw [horizontalLeakageEnvelope, indicator_of_mem hmem, horizontalLeakageQuadratic]
    linarith [hqdec ⟨hsA, hsb.le⟩ (by linarith)]
  · linarith [hf ⟨hsb.lt_of_ne' hne, hs.2⟩, horizontalLeakageEnvelope_nonneg A h s]

theorem IsFullCapMaximizer.exists_horizontal_quadratic_excess_envelope
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {K C h T : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1)
    (hwidth : capWidth U = 4 * C) (hC : 2 / 3 < C)
    (he : 0 < capRoof U (horizontalRight U))
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (hκ : ∀ s, ρ s ≤ sourceKappa (upperCornerVelocity U s))
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity
        (fun s => ENNReal.ofReal (ρ s)))
    (hh : 0 ≤ h) (hh1 : h < 1) (hT : 0 ≤ T)
    (hcross : capRoof U (horizontalRight U) ≤ 3 * C * T - T ^ 2 / 2)
    (henergy : 9 * C ^ 2 - capRoof U (horizontalRight U) *
      (1 - capRoof U (horizontalRight U)) ≤ (2 + (h ^ 2 + 2 * h) / 4) ^ 2) :
    ∃ A ∈ Icc (0 : ℝ) T,
      ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
        ρ s - 1 ≤ horizontalLeakageEnvelope A h s := by
  -- every differential and source hypothesis is supplied by the actual cap
  have hD : HorizontalCornerDynamics (fun s => -secondCornerVelocity U s)
      (firstCornerVelocity U) ρ (fun s => ρ (s + Real.pi / 2)) (Real.pi / 2) := by
    have hreg {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi / 2) :
        Icc a b ⊆ regularCornerDomain 0 := by
      rw [regularCornerDomain_zero]; exact Icc_subset_Ioo ha hb
    refine ⟨fun s hs => ?_, fun ha hab hb => ?_, ?_, ?_, fun s => hρ0 _, fun s =>
      ⟨hU.isCap.neg_secondCornerVelocity_le_one s, hU.isCap.firstCornerVelocity_ge_neg_one s⟩,
      ?_⟩
    · have hc := hU.isCap.continuousAt_cornerVelocities_on_regularCornerDomain hρ hρ0 hρK heq
        (hreg hs.1 hs.2 ⟨le_rfl, le_rfl⟩)
      exact ⟨hc.2.neg, hc.1⟩
    · have hdir := regularCornerDomain_interval_directions (hreg ha hb)
      have hac := hU.isCap.absolutelyContinuousOnInterval_cornerVelocities_of_density
        hρ hρ0 hρK heq hab hdir.1 hdir.2
      exact ⟨hac.2.neg, hac.1⟩
    · refine ae_restrict_of_local_intervals isOpen_Ioo fun s hs => ?_
      obtain ⟨a, ha0, has⟩ := exists_between hs.1
      obtain ⟨b, hsb, hbL⟩ := exists_between hs.2
      have hdir := regularCornerDomain_interval_directions (hreg ha0 hbL)
      exact ⟨a, b, ⟨has, hsb⟩, (hU.isCap.ae_hasDerivAt_cornerVelocities_of_density hρ hρ0
        hρK heq (has.le.trans hsb.le) hdir.1 hdir.2).mono fun t hd =>
          ⟨hd.2.neg.congr_deriv (by ring), hd.1.congr_deriv (by ring)⟩⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      have h := upperCorner_density_bounds_on_quarter hκ hs
      exact ⟨h.1, by simpa only [sourceKappa_neg] using h.2⟩
    · have hs := hU.ae_curvature_same_sign_quadrants (m := 0) (c := 1)
        (by simpa using hmiddle) hρ hρ0 hρK heq
      rw [regularCornerDomain_zero] at hs
      filter_upwards [hs] with s hs hp hq
      exact hs.1 ⟨hq, by linarith⟩
  have hlim := hU.cornerVelocities_tendsto_zero_right hheight hmiddle
  have hq : horizontalRight U - 1 - (horizontalLeft U + capWidth U / 4) = 3 * C - 1 := by
    rw [capWidth] at hwidth ⊢; linarith
  obtain ⟨d, hd, hqd⟩ := hU.exists_later_negative_firstCornerVelocity hheight hmiddle
    (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2)
  exact hD.exists_quadratic_excess_envelope he hC hh hh1 hT hcross henergy
    (by simpa using hlim.snd_nhds.neg) (by simpa only [hq] using hlim.fst_nhds)
    ⟨d, hd, by linarith⟩

end AmbidextrousSofa
