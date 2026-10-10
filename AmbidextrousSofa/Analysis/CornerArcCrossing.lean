import AmbidextrousSofa.Analysis.CornerArcDynamics
import AmbidextrousSofa.Analysis.TiltedLateExcessScalar

/-!
# The single possible excess interval of a regular corner arc

The first downward crossing of `q = 1` closes all later excess by the
proved energy barrier. Before it, the first zero of `p` is the only
possible start. Both crossings are constructed from the actual
continuous functions. The quadratic envelope retains this literal
first zero and its literal second-momentum height.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

namespace CornerArcDynamics

variable {p q u v : ℝ → ℝ} {a b : ℝ}

theorem exists_first_excess_crossings
    (D : CornerArcDynamics p q u v a b)
    (hpa : 0 < p a) (hqa : 1 < q a) (hqb : q b ≤ 1) :
    (∀ᵐ t ∂volume.restrict (Ioo a b), u t ≤ 1) ∨
      ∃ A B : ℝ, A ∈ Ioo a B ∧ B ∈ Ioc a b ∧
        p A = 0 ∧ q B = 1 ∧ 1 < q A ∧
        (∀ t ∈ Ico a A, 0 < p t) ∧
        (∀ t ∈ Ico a B, 1 < q t) ∧
        0 ≤ p a - (q a + 1) * (A - a) + (A - a) ^ 2 / 2 ∧
        (∀ᵐ t ∂volume.restrict (Ioo a b), t ∉ Ioo A B → u t ≤ 1) := by
  classical
  have hab : a < b := by
    apply lt_of_le_of_ne D.ordered
    intro heq
    rw [← heq] at hqb
    exact (not_lt_of_ge hqb) hqa
  obtain ⟨B, hB, hqB, hqbefore⟩ := exists_first_level_crossing hab D.continuousOn.2 hqa hqb
  have Dpre := D.restrict le_rfl hB.1.le hB.2
  have hpB := Dpre.first_le_one_at_second_downcrossing hqa hqB
    (fun t ht => hqbefore t ⟨ht.1.le, ht.2⟩)
  have hfuture := (ae_restrict_iff' measurableSet_Ioo).mp
    ((D.restrict hB.1.le hB.2 le_rfl).ae_unit_of_second_le_one hpB hqB.le)
  have close_of_positive_before
      (hpositive : ∀ t ∈ Ioo a B, 0 < p t) :
      ∀ᵐ t ∂volume.restrict (Ioo a b), u t ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, D.shadow,
      ae_restrict_of_ae hfuture, ae_restrict_of_ae (volume.ae_ne B)] with t ht hs hf hne
    by_cases htB : t < B
    · rw [(hs (hpositive t ⟨ht.1, htB⟩)
        (by linarith only [hqbefore t ⟨ht.1.le, htB⟩])).1]
      norm_num
    · exact hf ⟨lt_of_le_of_ne (le_of_not_gt htB) (Ne.symm hne), ht.2⟩
  by_cases hposB : 0 < p B
  · left
    apply close_of_positive_before
    intro t ht
    have hDt := D.restrict ht.1.le ht.2.le hB.2
    have h := hDt.first_linear_decrease
      (fun s hs => hqbefore s ⟨(ht.1.trans hs.1).le, hs.2⟩)
      (show B ∈ Icc t B from ⟨ht.2.le, le_rfl⟩)
    linarith only [h, hposB, ht.2]
  · obtain ⟨A, hA, hpA, hpbefore⟩ := exists_first_level_crossing hB.1
      Dpre.continuousOn.1 hpa (le_of_not_gt hposB)
    rcases hA.2.eq_or_lt with hAB | hAB
    · left
      apply close_of_positive_before
      intro t ht
      exact hpbefore t ⟨ht.1.le, ht.2.trans_eq hAB.symm⟩
    · right
      have DA := D.restrict le_rfl hA.1.le (hA.2.trans hB.2)
      have hquad := DA.first_quadratic_from_initial
        (fun t ht => hpbefore t ⟨ht.1.le, ht.2⟩)
        (fun t ht => by linarith only [hqbefore t ⟨ht.1.le, ht.2.trans_le hA.2⟩])
        (show A ∈ Icc a A from ⟨hA.1.le, le_rfl⟩)
      rw [hpA] at hquad
      refine ⟨A, B, ⟨hA.1, hAB⟩, hB, hpA, hqB,
        hqbefore A ⟨hA.1.le, hAB⟩, hpbefore, hqbefore, hquad, ?_⟩
      filter_upwards [ae_restrict_mem measurableSet_Ioo, D.shadow,
        ae_restrict_of_ae hfuture, ae_restrict_of_ae (volume.ae_ne A),
        ae_restrict_of_ae (volume.ae_ne B)] with t ht hs hf hneA hneB hout
      by_cases htA : t < A
      · rw [(hs (hpbefore t ⟨ht.1.le, htA⟩)
          (by linarith only [hqbefore t ⟨ht.1.le, htA.trans hAB⟩])).1]
        norm_num
      · have hAt : A < t := lt_of_le_of_ne (le_of_not_gt htA) (Ne.symm hneA)
        have hBt : B ≤ t := by
          by_contra hnot
          exact hout ⟨hAt, lt_of_not_ge hnot⟩
        exact hf ⟨lt_of_le_of_ne hBt (Ne.symm hneB), ht.2⟩

/-- The first zero and second crossing remain literal endpoints. The
duration bound follows by comparing at a point strictly between a
putative overlong interval and the predicted quadratic endpoint. -/
theorem quadratic_excess_envelope_of_crossings
    (D : CornerArcDynamics p q u v a b) {A B ell : ℝ}
    (haA : a ≤ A) (hAB : A < B) (hBb : B ≤ b)
    (hpA : p A ≤ 0) (hq : ∀ t ∈ Ioo A B, 1 < q t)
    (hout : ∀ᵐ t ∂volume.restrict (Ioo a b), t ∉ Ioo A B → u t ≤ 1)
    (hell0 : 0 ≤ ell) (hell1 : ell < 1)
    (hqA : q A - 1 ≤ ell / 2 + ell ^ 2 / 4) :
    B ≤ A + ell ∧
      ∀ᵐ t ∂volume.restrict (Ioo a b), u t - 1 ≤ horizontalLeakageEnvelope A ell t := by
  have Dcore := D.restrict haA hAB.le hBb
  have hdec (t : ℝ) (ht : t ∈ Icc A B) (ht1 : t ≤ A + 1) :
      q t ≤ q A - (t - A) / 2 - (t - A) ^ 2 / 4 :=
    Dcore.second_quadratic_after_nonpositive_first hpA hq ht ht1
  have hlength : B ≤ A + ell := by
    by_contra hnot
    have hgap : A + ell < min B (A + 1) :=
      lt_min (lt_of_not_ge hnot) (by linarith only [hell1])
    obtain ⟨t, htl, htr⟩ := exists_between hgap
    have htB := htr.trans_le (min_le_left _ _)
    have htone := htr.trans_le (min_le_right _ _)
    have hAt : A < t := by linarith only [htl, hell0]
    have hhigh := hq t ⟨hAt, htB⟩
    have hbound := hdec t ⟨hAt.le, htB.le⟩ htone.le
    have hprod := mul_pos (show 0 < (t - A) - ell by linarith only [htl])
      (show 0 < (t - A) + ell + 2 by linarith only [hAt, hell0])
    nlinarith only [hhigh, hbound, hprod, hqA]
  refine ⟨hlength, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo, D.source, hout] with t ht hk hout
  by_cases hcore : t ∈ Ioo A B
  · have htwin : t ∈ Icc A (A + ell) := ⟨hcore.1.le, hcore.2.le.trans hlength⟩
    have hbound := hdec t (Ioo_subset_Icc_self hcore)
      (htwin.2.trans (by linarith only [hell1]))
    have hu := hk.1
    rw [sourceKappa_eq_self_of_one_le (hq t hcore).le] at hu
    rw [horizontalLeakageEnvelope, indicator_of_mem htwin]
    unfold horizontalLeakageQuadratic
    nlinarith only [hu, hbound, hqA]
  · exact (sub_nonpos.mpr (hout hcore)).trans (horizontalLeakageEnvelope_nonneg A ell t)

theorem quadratic_excess_envelope_at_first_crossing
    (D : CornerArcDynamics p q u v a b) {A B : ℝ}
    (haA : a ≤ A) (hAB : A < B) (hBb : B ≤ b)
    (hpA : p A ≤ 0) (hqA : 1 ≤ q A) (hq : ∀ t ∈ Ioo A B, 1 < q t)
    (hout : ∀ᵐ t ∂volume.restrict (Ioo a b), t ∉ Ioo A B → u t ≤ 1)
    (hell : Analysis.quadraticExcessLength (q A - 1) < 1) :
    B ≤ A + Analysis.quadraticExcessLength (q A - 1) ∧
      ∀ᵐ t ∂volume.restrict (Ioo a b), u t - 1 ≤
        horizontalLeakageEnvelope A (Analysis.quadraticExcessLength (q A - 1)) t := by
  have hε : 0 ≤ q A - 1 := sub_nonneg.mpr hqA
  exact D.quadratic_excess_envelope_of_crossings haA hAB hBb hpA hq hout
    (Analysis.quadraticExcessLength_nonneg hε) hell
    (Analysis.quadraticExcessLength_identity hε).le

end CornerArcDynamics

end AmbidextrousSofa
