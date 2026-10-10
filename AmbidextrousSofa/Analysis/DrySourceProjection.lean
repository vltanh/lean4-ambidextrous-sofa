module

public import AmbidextrousSofa.Analysis.TiltedZeroGeometry
public import AmbidextrousSofa.Analysis.SourceLocalization
public import AmbidextrousSofa.Analysis.HorizontalCutoff

@[expose] public section

/-!
# Vanishing finite positive length on a strictly dry interval

Strict negativity of the actual companion numerator away from the initial
axis survives a Hausdorff limit uniformly on a compact spatial interval.
Every literal finite inner source there therefore has a small quarter
angle. The two corresponding source families have total mass bounded by
the neighboring-wall estimate. Letting the angular cutoff shrink proves
vanishing positive length, including finite ties at height zero.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem CapHausdorffTendsto.secondWallNumerator_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {point angle : ℕ → ℝ} {x t : ℝ}
    (hx : Tendsto point atTop (𝓝 x)) (ht : Tendsto angle atTop (𝓝 t)) :
    Tendsto (fun n => secondWallNumerator (U n) (angle n) (point n)) atTop
      (𝓝 (secondWallNumerator K t x)) :=
  ((h.support_tendsto_moving hU hK
    ((continuous_companionNormal.tendsto t).comp ht)).sub_const 1).add
      (hx.mul ((Real.continuous_sin.tendsto t).comp ht))

theorem CapHausdorffTendsto.eventually_secondWallNumerator_neg_on_compact
    {U : ℕ → Set Plane} {K : Set Plane} {F : Set ℝ} {η : ℝ}
    (h : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n))
    (hK : IsDownwardCap K) (hF : IsCompact F) (hη : 0 < η)
    (hnegative : ∀ x ∈ F, ∀ t ∈ Ioc (0 : ℝ) (Real.pi / 2),
      secondWallNumerator K t x < 0) :
    ∀ᶠ n in atTop, ∀ x ∈ F, ∀ t ∈ Icc η (Real.pi / 2),
      secondWallNumerator (U n) t x < 0 := by
  classical
  by_contra hnot
  have hbad : ∀ k : ℕ, ∃ n, k ≤ n ∧ ∃ x ∈ F, ∃ t ∈ Icc η (Real.pi / 2),
      ¬ secondWallNumerator (U n) t x < 0 := by
    intro k
    by_contra hk
    apply hnot
    refine eventually_atTop.mpr ⟨k, ?_⟩
    intro n hn x hx t ht
    by_contra hnt
    exact hk ⟨n, hn, x, hx, t, ht, hnt⟩
  choose ns hns point hpoint angle hangle hnonneg using hbad
  obtain ⟨z, hz, ms, hms, hpair⟩ := (hF.prod isCompact_Icc).tendsto_subseq
    (fun n => show (point n, angle n) ∈ F ×ˢ Icc η (Real.pi / 2) from
      ⟨hpoint n, hangle n⟩)
  let seq : ℕ → ℕ := fun n => ns (ms n)
  have hseq : Tendsto seq atTop atTop :=
    (tendsto_atTop_mono hns tendsto_id).comp hms.tendsto_atTop
  have hsub : CapHausdorffTendsto (fun n => U (seq n)) K := h.comp hseq
  have hlim := hsub.secondWallNumerator_tendsto
    (fun n => hU (seq n)) hK hpair.fst_nhds hpair.snd_nhds
  have hnonnegative : 0 ≤ secondWallNumerator K z.2 z.1 := ge_of_tendsto hlim
    (Eventually.of_forall (fun n => le_of_not_gt (hnonneg (ms n))))
  exact not_lt_of_ge hnonnegative
    (hnegative z.1 hz.1 z.2 ⟨hη.trans_le hz.2.1, hz.2.2⟩)

namespace AngularGrid

open FinitePolygon

theorem eventually_innerSources_quarter_lt_on_dry
    {U : ℕ → Set Plane} {K : Set Plane} {F : Set ℝ}
    {grid : ℕ → Finset QuarterAngle} {η : ℝ}
    (h : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n))
    (hK : IsDownwardCap K) (hF : IsCompact F) (hη : 0 < η)
    (hnegative : ∀ x ∈ F, ∀ t ∈ Ioc (0 : ℝ) (Real.pi / 2),
      secondWallNumerator K t x < 0) :
    ∀ᶠ n in atTop, ∀ x ∈ F, ∀ j : SourceIndex (grid n),
      x ∈ innerSourceSet (U n) (grid n) j →
        sourceQuarterAngle (fullAngle (grid n) j) < η := by
  filter_upwards [h.eventually_secondWallNumerator_neg_on_compact hU hK hF hη hnegative]
    with n hn x hx j hsource
  by_contra hnot
  let t : ℝ := sourceQuarterAngle (fullAngle (grid n) j)
  have ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2) := sourceQuarterAngle_mem _ _
  have hnum := hn x hx t ⟨le_of_not_gt hnot, ht.2.le⟩
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  have hsecond : secondWall (U n) t x < 0 := div_neg_of_neg_of_pos hnum hc
  have hcorner : 0 ≤ cornerWall (U n) t x := by
    rw [innerSource_cornerWall (U n) (grid n) j hsource]
    exact finiteBarrier_nonneg _ _ _ _ _
  exact not_lt_of_ge (hcorner.trans (min_le_right _ _)) hsecond

theorem fullAngle_mem_initial_pair_of_quarter_lt
    (grid : Finset QuarterAngle) (j : SourceIndex grid) {η : ℝ}
    (h : sourceQuarterAngle (fullAngle grid j) < η) :
    fullAngle grid j ∈ Icc (0 : ℝ) η ∨
      fullAngle grid j ∈ Icc (Real.pi / 2) (Real.pi / 2 + η) := by
  rw [sourceQuarterAngle_fullAngle] at h
  cases j with
  | inl t => exact Or.inl ⟨(interiorPoint_mem grid t).1.le, h.le⟩
  | inr t =>
    simp only [Sum.elim_inr] at h
    right
    change Real.pi / 2 ≤ (t.val : ℝ) + Real.pi / 2 ∧
      (t.val : ℝ) + Real.pi / 2 ≤ Real.pi / 2 + η
    constructor <;> linarith only [h, (interiorPoint_mem grid t).1]

theorem sum_sin_innerSourceMassOn_eq_positiveLength
    (U : Set Plane) (grid : Finset QuarterAngle) {a b : ℝ} (hab : a ≤ b) :
    (∑ j : SourceIndex grid, (normal grid j).2 * innerSourceMassOn U grid a b j) =
      finitePositiveLength U (normal grid) (pairList grid) none a b := by
  classical
  rw [finitePositiveLength_eq_sum _ _ _ _ (wallSlopes_injective grid) hab]
  apply Finset.sum_congr rfl
  intro j _
  rw [innerSourceMassOn_eq_div U grid hab]
  field_simp [(normal_snd_pos grid j).ne']

theorem finitePositiveLength_le_small_pair_mass
    {U : Set Plane} (hU : IsDownwardCap U) {R a b η : ℝ}
    (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (level : ℕ) (hab : a ≤ b) (hη : 0 ≤ η)
    (ha : horizontalLeft U + capWidth U / 4 ≤ a)
    (hb : b ≤ horizontalRight U - capWidth U / 4)
    (hsource : ∀ x ∈ Ioc a b, ∀ j : SourceIndex (dyadic level),
      x ∈ innerSourceSet U (dyadic level) j →
        sourceQuarterAngle (fullAngle (dyadic level) j) < η) :
    finitePositiveLength U (normal (dyadic level)) (pairList (dyadic level)) none a b ≤
      2 * (4 * R + 12) * (η + mesh level) := by
  classical
  let grid := dyadic level
  let E : Set ℝ := Icc (0 : ℝ) η
  let F : Set ℝ := Icc (Real.pi / 2) (Real.pi / 2 + η)
  have hterm (j : SourceIndex grid) :
      (normal grid j).2 * innerSourceMassOn U grid a b j ≤
        (if fullAngle grid j ∈ E then innerSourceMass U grid j else 0) +
        (if fullAngle grid j ∈ F then innerSourceMass U grid j else 0) := by
    have hlocal : innerSourceMassOn U grid a b j ≤ innerSourceMass U grid j :=
      innerSourceMassOn_le U grid ha hab hb j
    have hscaled : (normal grid j).2 * innerSourceMassOn U grid a b j ≤
        innerSourceMassOn U grid a b j := by
      have hs : (normal grid j).2 ≤ 1 := by
        rw [normal_eq_unitNormal]
        exact Real.sin_le_one _
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hs
        (innerSourceMassOn_nonneg U grid hab j)
    by_cases hjE : fullAngle grid j ∈ E
    · rw [if_pos hjE]
      exact (hscaled.trans hlocal).trans (le_add_of_nonneg_right
        (by split_ifs
            · exact innerSourceMass_nonneg hU grid j
            · exact le_rfl))
    · by_cases hjF : fullAngle grid j ∈ F
      · rw [if_neg hjE, if_pos hjF, zero_add]
        exact hscaled.trans hlocal
      · have hzero : innerSourceMassOn U grid a b j = 0 := by
          apply innerSourceMassOn_eq_zero_of_disjoint U grid hab j
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro x hx
          rcases fullAngle_mem_initial_pair_of_quarter_lt grid j
            (hsource x hx.1 j hx.2) with hE | hF
          · exact hjE hE
          · exact hjF hF
        simp only [hzero, mul_zero, if_neg hjE, if_neg hjF, zero_add, le_refl]
  have hsum : finitePositiveLength U (normal grid) (pairList grid) none a b ≤
      (∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ E),
        innerSourceMass U grid j) +
      ∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ F),
        innerSourceMass U grid j := by
    rw [← sum_sin_innerSourceMassOn_eq_positiveLength U grid hab,
      Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => hterm j)
  have hE := innerSourceMass_sum_interval_le hU hR hbox level hη
  have hF := innerSourceMass_sum_interval_le hU hR hbox level
    (show Real.pi / 2 ≤ Real.pi / 2 + η by linarith only [hη])
  change _ ≤ (4 * R + 12) * (η - 0 + mesh level) at hE
  change _ ≤ (4 * R + 12) * (Real.pi / 2 + η - Real.pi / 2 + mesh level) at hF
  dsimp only [grid, E, F] at hsum
  nlinarith only [hsum, hE, hF]

/-- A compact strict dry interval acquires no positive horizontal length
in the actual dyadic approximation. The source cutoff is removed only
after taking the selected cap limit. -/
theorem finitePositiveLength_tendsto_zero_on_dry_interval
    {U : ℕ → Set Plane} {K : Set Plane} {level : ℕ → ℕ} {R a b : ℝ}
    (h : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n))
    (hK : IsDownwardCap K) (hlevel : Tendsto level atTop atTop)
    (hR : 0 ≤ R) (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hab : a ≤ b) (ha : horizontalLeft K + capWidth K / 4 < a)
    (hb : b < horizontalRight K - capWidth K / 4)
    (hnegative : ∀ x ∈ Icc a b, ∀ t ∈ Ioc (0 : ℝ) (Real.pi / 2),
      secondWallNumerator K t x < 0) :
    Tendsto (fun n => finitePositiveLength (U n) (normal (dyadic (level n)))
      (pairList (dyadic (level n))) none a b) atTop (𝓝 0) := by
  have hl := h.horizontalLeft_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
  have hr := h.horizontalRight_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
  have hjL := hl.add ((hr.sub hl).div_const 4)
  have hjR := hr.sub ((hr.sub hl).div_const 4)
  have hinside : ∀ᶠ n in atTop,
      horizontalLeft (U n) + capWidth (U n) / 4 ≤ a ∧
      b ≤ horizontalRight (U n) - capWidth (U n) / 4 := by
    filter_upwards [hjL.eventually (Iio_mem_nhds ha), hjR.eventually (Ioi_mem_nhds hb)]
      with n hnL hnR
    exact ⟨hnL.le, hnR.le⟩
  let D : ℝ := 4 * R + 12
  have hD : 0 < D := by dsimp only [D]; linarith only [hR]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨η, hη, hηε⟩ := exists_between (div_pos hε (show 0 < 4 * D by positivity))
  have hsmall : 4 * D * η < ε := by
    nlinarith only [(lt_div_iff₀ (show 0 < 4 * D by positivity)).mp hηε]
  have hsource := eventually_innerSources_quarter_lt_on_dry h hU hK isCompact_Icc hη hnegative
    (grid := fun n => dyadic (level n))
  have hmesh : ∀ᶠ n in atTop, mesh (level n) < η :=
    (mesh_tendsto.comp hlevel).eventually (Iio_mem_nhds hη)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hinside.and (hsource.and hmesh))
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hinterior, hsources, hmesh⟩ := hN n hn
  have hbound := finitePositiveLength_le_small_pair_mass (hU n) hR (hbox n) (level n)
    hab hη.le hinterior.1 hinterior.2
    (fun x hx j hj => hsources x ⟨hx.1.le, hx.2⟩ j hj)
  have hnonnegative : 0 ≤ finitePositiveLength (U n) (normal (dyadic (level n)))
      (pairList (dyadic (level n))) none a b := ENNReal.toReal_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonnegative]
  have hmargin := mul_pos hD (sub_pos.mpr hmesh)
  dsimp only [D] at hmargin
  dsimp only [D] at hsmall
  nlinarith only [hbound, hsmall, hmargin]

end AngularGrid

end AmbidextrousSofa
