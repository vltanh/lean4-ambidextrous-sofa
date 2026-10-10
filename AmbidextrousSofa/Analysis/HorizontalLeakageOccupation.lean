import AmbidextrousSofa.Analysis.HorizontalLeakageDynamics

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
  classical
  obtain ⟨d, hd, hqd⟩ := hlater
  obtain ⟨b, hb, hqb, hqbefore⟩ := exists_first_level_crossing_of_right_limit
    (fun t ht => (D.continuous t ht).2) hqlim (by linarith : 1 < 3 * C - 1) hd hqd
  have hbL : b < L := hb.2.trans_lt hd.2
  have hfuture := (ae_restrict_iff' measurableSet_Ioo).mp
    (D.ae_unit_after_first_eq_one ⟨hb.1, hbL⟩ hqb)
  by_cases hpb : 0 < p b
  · have hppos : ∀ s ∈ Ioo (0 : ℝ) b, 0 < p s := by
      intro s hs
      have h := D.first_linear_decrease hs.1 hs.2.le hbL
        (fun t ht => hqbefore t ⟨hs.1.trans ht.1, ht.2⟩)
        (show b ∈ Icc s b from ⟨hs.2.le, le_rfl⟩)
      linarith [hs.2]
    refine ⟨0, ⟨le_rfl, hT⟩, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo, D.shadow,
      ae_restrict_of_ae hfuture, ae_restrict_of_ae (volume.ae_ne b)] with s hs hshadow hf hne
    have hu : u s ≤ 1 := by
      by_cases hsb : s < b
      · rw [(hshadow (hppos s ⟨hs.1, hsb⟩)
          (by linarith [hqbefore s ⟨hs.1, hsb⟩])).1]
        norm_num
      · exact hf ⟨lt_of_le_of_ne (le_of_not_gt hsb) (Ne.symm hne), hs.2⟩
    exact (sub_nonpos.mpr hu).trans (horizontalLeakageEnvelope_nonneg 0 h s)
  · obtain ⟨A, hA, hpA, hpbefore⟩ := exists_first_level_crossing_of_right_limit
      (fun t ht => (D.continuous t ht).1) hplim he
      (show b ∈ Ioo (0 : ℝ) L from ⟨hb.1, hbL⟩) (le_of_not_gt hpb)
    have hAL : A < L := hA.2.trans_lt hbL
    have hqA : ∀ s ∈ Ioo A b, 1 < q s :=
      fun s hs => hqbefore s ⟨hA.1.trans hs.1, hs.2⟩
    have hqstart := D.crossing_first_bound he.le
      (show 0 ≤ (h ^ 2 + 2 * h) / 4 by positivity)
      hplim hqlim henergy ⟨hA.1, hAL⟩ hpA
    have hqdec (s : ℝ) (hs : s ∈ Icc A b) (hs1 : s ≤ A + 1) :
        q s ≤ q A - (s - A) / 2 - (s - A) ^ 2 / 4 :=
      D.second_quadratic_after_crossing hA.1 hA.2 hbL hpA hqA hs hs1
    have hbh : b ≤ A + h := by
      by_contra hnot
      have hlt : A + h < min b (A + 1) :=
        lt_min (lt_of_not_ge hnot) (by linarith)
      obtain ⟨s, hs0, hs1⟩ := exists_between hlt
      have hsb := hs1.trans_le (min_le_left _ _)
      have hsone := hs1.trans_le (min_le_right _ _)
      have hAs : A < s := by linarith
      have hqpos := hqbefore s ⟨hA.1.trans hAs, hsb⟩
      have hbound := hqdec s ⟨hAs.le, hsb.le⟩ hsone.le
      have hprod := mul_pos (by linarith : 0 < (s - A) - h)
        (by linarith : 0 < (s - A) + h + 2)
      nlinarith
    have hAT : A ≤ T := by
      by_contra hnot
      have hTA : T < A := lt_of_not_ge hnot
      have hTpos : 0 < T := by
        by_contra hbad
        have hzero : T = 0 := le_antisymm (le_of_not_gt hbad) hT
        rw [hzero] at hcross
        nlinarith
      have hpT := hpbefore T ⟨hTpos, hTA⟩
      have hbound := D.first_quadratic_before_crossing hplim hqlim hAL hpbefore
        (fun s hs => hqbefore s ⟨hs.1, hs.2.trans_le hA.2⟩) ⟨hTpos, hTA.le⟩
      nlinarith
    refine ⟨A, ⟨hA.1.le, hAT⟩, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo, D.shadow, D.source,
      ae_restrict_of_ae hfuture, ae_restrict_of_ae (volume.ae_ne A),
      ae_restrict_of_ae (volume.ae_ne b)] with s hs hshadow hsource hf hneA hneb
    by_cases hsA : s < A
    · have hqb' := hqbefore s ⟨hs.1, hsA.trans_le hA.2⟩
      rw [(hshadow (hpbefore s ⟨hs.1, hsA⟩) (by linarith)).1]
      exact (by norm_num : (0 : ℝ) - 1 ≤ 0).trans
        (horizontalLeakageEnvelope_nonneg A h s)
    have hAs : A < s := lt_of_le_of_ne (le_of_not_gt hsA) (Ne.symm hneA)
    by_cases hsb : s < b
    · have hmem : s ∈ Icc A (A + h) := ⟨hAs.le, hsb.le.trans hbh⟩
      have hbound := hqdec s ⟨hAs.le, hsb.le⟩
        (show s ≤ A + 1 from hmem.2.trans (by linarith))
      have hu := hsource.1
      rw [sourceKappa_eq_self_of_one_le (hqbefore s ⟨hs.1, hsb⟩).le] at hu
      rw [horizontalLeakageEnvelope, indicator_of_mem hmem]
      unfold horizontalLeakageQuadratic
      linarith
    · have hu := hf ⟨lt_of_le_of_ne (le_of_not_gt hsb) (Ne.symm hneb), hs.2⟩
      exact (sub_nonpos.mpr hu).trans (horizontalLeakageEnvelope_nonneg A h s)

/-- Every differential and source hypothesis of the short-excess
argument is supplied by the actual horizontal maximizing cap. -/
theorem IsFullCapMaximizer.horizontalCornerDynamics
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {K : ℝ}
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (hκ : ∀ s, ρ s ≤ sourceKappa (upperCornerVelocity U s))
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity
        (fun s => ENNReal.ofReal (ρ s))) :
    HorizontalCornerDynamics (fun s => -secondCornerVelocity U s)
      (firstCornerVelocity U) ρ (fun s => ρ (s + Real.pi / 2)) (Real.pi / 2) := by
  have hregular : ∀ s ∈ Ioo (0 : ℝ) (Real.pi / 2), s ∈ regularCornerDomain 0 := by
    simpa only [regularCornerDomain_zero] using
      (fun s (hs : s ∈ Ioo (0 : ℝ) (Real.pi / 2)) => hs)
  have hinterval : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < Real.pi / 2 →
      Icc a b ⊆ regularCornerDomain 0 := by
    intro a b ha hab hb t ht
    exact hregular t ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  refine ⟨?_, ?_, ?_, ?_, (fun s => hρ0 (s + Real.pi / 2)), ?_, ?_⟩
  · intro s hs
    have hc := hU.isCap.continuousAt_cornerVelocities_on_regularCornerDomain
      hρ hρ0 hρK heq (hregular s hs)
    exact ⟨hc.2.neg, hc.1⟩
  · intro a b ha hab hb
    have hdir := regularCornerDomain_interval_directions (hinterval ha hab hb)
    have hac := hU.isCap.absolutelyContinuousOnInterval_cornerVelocities_of_density
      hρ hρ0 hρK heq hab hdir.1 hdir.2
    exact ⟨hac.2.neg, hac.1⟩
  · apply ae_restrict_of_local_intervals isOpen_Ioo
    intro s hs
    obtain ⟨a, ha0, has⟩ := exists_between hs.1
    obtain ⟨b, hsb, hbL⟩ := exists_between hs.2
    have hab : a ≤ b := has.le.trans hsb.le
    have hdir := regularCornerDomain_interval_directions (hinterval ha0 hab hbL)
    refine ⟨a, b, ⟨has, hsb⟩, ?_⟩
    filter_upwards [hU.isCap.ae_hasDerivAt_cornerVelocities_of_density
      hρ hρ0 hρK heq hab hdir.1 hdir.2] with t hd
    exact ⟨hd.2.neg.congr_deriv (by ring), hd.1.congr_deriv (by ring)⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have h := upperCorner_density_bounds_on_quarter hκ hs
    exact ⟨h.1, by simpa only [sourceKappa_neg] using h.2⟩
  · intro s
    exact ⟨hU.isCap.neg_secondCornerVelocity_le_one s,
      hU.isCap.firstCornerVelocity_ge_neg_one s⟩
  · have hs := hU.ae_curvature_same_sign_quadrants (m := 0) (c := 1)
      (by simpa only [zero_mul, zero_add] using hmiddle) hρ hρ0 hρK heq
    rw [regularCornerDomain_zero] at hs
    filter_upwards [hs] with s hs
    intro hp hq
    exact hs.1 ⟨hq, by linarith⟩

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
  have hD := hU.horizontalCornerDynamics hmiddle hρ hρ0 hρK hκ heq
  have hlim := hU.cornerVelocities_tendsto_zero_right hheight hmiddle
  have hp : Tendsto (fun s => -secondCornerVelocity U s) (𝓝[>] (0 : ℝ))
      (𝓝 (capRoof U (horizontalRight U))) := by
    simpa only [neg_neg] using hlim.snd.neg
  have hq : Tendsto (firstCornerVelocity U) (𝓝[>] (0 : ℝ)) (𝓝 (3 * C - 1)) := by
    have hvalue : horizontalRight U - 1 - (horizontalLeft U + capWidth U / 4) =
        3 * C - 1 := by
      unfold capWidth at hwidth ⊢
      linarith
    simpa only [hvalue] using hlim.fst
  have hlater : ∃ d ∈ Ioo (0 : ℝ) (Real.pi / 2), firstCornerVelocity U d ≤ 1 := by
    obtain ⟨d, hd, hqd⟩ := hU.exists_later_negative_firstCornerVelocity
      hheight hmiddle (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2)
    exact ⟨d, hd, by linarith⟩
  exact hD.exists_quadratic_excess_envelope he hC hh hh1 hT hcross henergy hp hq hlater

end AmbidextrousSofa
