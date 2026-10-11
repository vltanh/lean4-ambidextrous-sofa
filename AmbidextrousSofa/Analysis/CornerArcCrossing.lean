module

public import AmbidextrousSofa.Analysis.HorizontalLeakageDynamics
public import AmbidextrousSofa.Analysis.TiltedInitialCircle
public import AmbidextrousSofa.Analysis.TiltedLateExcessScalar

@[expose] public section

/-!
# The single possible excess interval of a regular corner arc

The first downward crossing of `q = 1` closes all later excess by the
proved energy barrier. Before it, the first zero of `p` is the only
possible start. Both crossings are constructed from the actual
continuous functions. The quadratic envelope retains this literal
first zero and its literal second-momentum height.
-/

open Set MeasureTheory

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
  obtain ⟨B, hB, hqB, hqbefore⟩ := exists_first_level_crossing
    (D.ordered.lt_of_ne (by rintro rfl; linarith)) D.continuousOn.2 hqa hqb
  have Dpre := D.restrict le_rfl hB.1.le hB.2
  have hfuture := (ae_restrict_iff' measurableSet_Ioo).mp
    ((D.restrict hB.1.le hB.2 le_rfl).ae_unit_of_second_le_one
      (Dpre.first_le_one_at_second_downcrossing hqa hqB fun t ht => hqbefore t ⟨ht.1.le, ht.2⟩)
      hqB.le)
  -- Away from `Ioo A B`, the source vanishes before `A` and the energy barrier acts after `B`.
  have hout (A : ℝ) (hAB : A ≤ B) (hpos : ∀ t ∈ Ioo a A, 0 < p t) :
      ∀ᵐ t ∂volume.restrict (Ioo a b), t ∉ Ioo A B → u t ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, D.shadow, ae_restrict_of_ae hfuture,
      ae_restrict_of_ae (volume.ae_ne A), ae_restrict_of_ae (volume.ae_ne B)]
      with t ht hs hf hA hB' hAB'
    rcases hA.lt_or_gt with htA | htA
    · rw [(hs (hpos t ⟨ht.1, htA⟩) (by linarith [hqbefore t ⟨ht.1.le, htA.trans_le hAB⟩])).1]
      norm_num
    · exact hf ⟨(le_of_not_gt fun h => hAB' ⟨htA, h⟩).lt_of_ne hB'.symm, ht.2⟩
  have hall (hpos : ∀ t ∈ Ioo a B, 0 < p t) : ∀ᵐ t ∂volume.restrict (Ioo a b), u t ≤ 1 := by
    filter_upwards [hout B le_rfl hpos] with t h using h fun h' => lt_asymm h'.1 h'.2
  by_cases hposB : 0 < p B
  · refine .inl (hall fun t ht => ?_)
    have := (D.restrict ht.1.le ht.2.le hB.2).first_linear_decrease
      (fun s hs => hqbefore s ⟨(ht.1.trans hs.1).le, hs.2⟩) ⟨ht.2.le, le_rfl⟩
    linarith [ht.2]
  obtain ⟨A, hA, hpA, hpbefore⟩ := exists_first_level_crossing hB.1
    Dpre.continuousOn.1 hpa (le_of_not_gt hposB)
  rcases hA.2.eq_or_lt with rfl | hAB
  · exact .inl (hall fun t ht => hpbefore t ⟨ht.1.le, ht.2⟩)
  refine .inr ⟨A, B, ⟨hA.1, hAB⟩, hB, hpA, hqB, hqbefore A ⟨hA.1.le, hAB⟩, hpbefore, hqbefore,
    hpA ▸ (D.restrict le_rfl hA.1.le (hA.2.trans hB.2)).first_quadratic_from_initial
      (fun t ht => hpbefore t ⟨ht.1.le, ht.2⟩)
      (fun t ht => by linarith [hqbefore t ⟨ht.1.le, ht.2.trans_le hA.2⟩]) ⟨hA.1.le, le_rfl⟩,
    hout A hAB.le fun t ht => hpbefore t ⟨ht.1.le, ht.2⟩⟩

/-- The first zero and second crossing remain literal endpoints. The
duration bound follows by comparing at a point strictly between a
putative overlong interval and the predicted quadratic endpoint. -/
theorem quadratic_excess_envelope_at_first_crossing
    (D : CornerArcDynamics p q u v a b) {A B : ℝ}
    (haA : a ≤ A) (hAB : A < B) (hBb : B ≤ b)
    (hpA : p A ≤ 0) (hqA : 1 ≤ q A) (hq : ∀ t ∈ Ioo A B, 1 < q t)
    (hout : ∀ᵐ t ∂volume.restrict (Ioo a b), t ∉ Ioo A B → u t ≤ 1)
    (hell : Analysis.quadraticExcessLength (q A - 1) < 1) :
    B ≤ A + Analysis.quadraticExcessLength (q A - 1) ∧
      ∀ᵐ t ∂volume.restrict (Ioo a b), u t - 1 ≤
        horizontalLeakageEnvelope A (Analysis.quadraticExcessLength (q A - 1)) t := by
  have hell0 := Analysis.quadraticExcessLength_nonneg (sub_nonneg.mpr hqA)
  have hqA' := Analysis.quadraticExcessLength_identity (sub_nonneg.mpr hqA)
  set ell := Analysis.quadraticExcessLength (q A - 1)
  have hdec (t : ℝ) (ht : t ∈ Icc A B) (ht1 : t ≤ A + 1) :=
    (D.restrict haA hAB.le hBb).second_quadratic_after_nonpositive_first hpA hq ht ht1
  have hlength : B ≤ A + ell := by
    by_contra! h
    obtain ⟨t, htl, htr⟩ := exists_between (lt_min h (by linarith : A + ell < A + 1))
    rw [lt_min_iff] at htr
    linarith [hq t ⟨by linarith, htr.1⟩, hdec t ⟨by linarith, htr.1.le⟩ htr.2.le,
      mul_pos (sub_pos.mpr htl) (by linarith : 0 < t - A + ell + 2)]
  refine ⟨hlength, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo, D.source, hout] with t ht hk hout
  by_cases hcore : t ∈ Ioo A B
  · have htwin : t ∈ Icc A (A + ell) := ⟨hcore.1.le, hcore.2.le.trans hlength⟩
    rw [sourceKappa_eq_self_of_one_le (hq t hcore).le] at hk
    rw [horizontalLeakageEnvelope, indicator_of_mem htwin, horizontalLeakageQuadratic]
    linarith [hk.1, hdec t (Ioo_subset_Icc_self hcore) (by linarith [htwin.2])]
  · exact (sub_nonpos.mpr (hout hcore)).trans (horizontalLeakageEnvelope_nonneg A ell t)

end CornerArcDynamics

end AmbidextrousSofa
