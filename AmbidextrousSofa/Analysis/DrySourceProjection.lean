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

theorem CapHausdorffTendsto.eventually_secondWallNumerator_neg_on_compact
    {U : ℕ → Set Plane} {K : Set Plane} {F : Set ℝ} {η : ℝ}
    (h : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n))
    (hK : IsDownwardCap K) (hF : IsCompact F) (hη : 0 < η)
    (hnegative : ∀ x ∈ F, ∀ t ∈ Ioc (0 : ℝ) (Real.pi / 2),
      secondWallNumerator K t x < 0) :
    ∀ᶠ n in atTop, ∀ x ∈ F, ∀ t ∈ Icc η (Real.pi / 2),
      secondWallNumerator (U n) t x < 0 := by
  by_contra hnot
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop (not_eventually.mp hnot)
  push Not at hbad
  choose point hpoint angle hangle hbad using hbad
  obtain ⟨z, hz, ms, hms, hpair⟩ := (hF.prod isCompact_Icc).tendsto_subseq
    fun n => mk_mem_prod (hpoint n) (hangle n)
  have hsub : CapHausdorffTendsto (fun n => U (φ (ms n))) K :=
    h.comp (hφ.comp hms).tendsto_atTop
  have ht := hpair.snd_nhds
  have hlim := ((hsub.support_tendsto_moving (fun _ => hU _) hK
    ((continuous_companionNormal.tendsto _).comp ht)).sub_const 1).add
      (hpair.fst_nhds.mul ((Real.continuous_sin.tendsto _).comp ht))
  -- the numerator is nonnegative along the bad subsequence, hence at its limit
  exact (ge_of_tendsto hlim (.of_forall fun n => hbad (ms n))).not_gt
    (hnegative z.1 hz.1 z.2 ⟨hη.trans_le hz.2.1, hz.2.2⟩)

namespace AngularGrid

open FinitePolygon

theorem finitePositiveLength_le_small_pair_mass
    {U : Set Plane} (hU : IsDownwardCap U) {R a b η : ℝ}
    (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (level : ℕ) (hab : a ≤ b) (hη : 0 ≤ η)
    (ha : horizontalLeft U + capWidth U / 4 ≤ a)
    (hb : b ≤ horizontalRight U - capWidth U / 4)
    (hneg : ∀ x ∈ Ioc a b, ∀ t ∈ Icc η (Real.pi / 2), secondWallNumerator U t x < 0) :
    finitePositiveLength U (normal (dyadic level)) (pairList (dyadic level)) none a b ≤
      2 * (4 * R + 12) * (η + mesh level) := by
  have hE := innerSourceMass_sum_interval_le hU hR hbox level hη
  have hF := innerSourceMass_sum_interval_le hU hR hbox level
    (le_add_of_nonneg_right hη (a := Real.pi / 2))
  rw [Finset.sum_filter] at hE hF
  refine le_trans ?_ ((add_le_add hE hF).trans_eq (by ring))
  rw [← Finset.sum_add_distrib, finitePositiveLength_eq_sum _ _ _ _ (wallSlopes_injective _) hab]
  -- each source contributes at most its inner mass, and only if its angle is near `0` or `π / 2`
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← (eq_div_iff (normal_snd_pos _ j).ne').mp (innerSourceMassOn_eq_div U _ hab j)]
  have hs : (normal (dyadic level) j).2 ≤ 1 := by
    rw [normal_eq_unitNormal]; exact Real.sin_le_one _
  have hle : _ ≤ innerSourceMass U _ j :=
    (mul_le_of_le_one_right (innerSourceMassOn_nonneg U _ hab j) hs).trans
      (innerSourceMassOn_le U _ ha hab hb j)
  have := innerSourceMass_nonneg hU (dyadic level) j
  split_ifs with hjE hjF hjF <;> try linarith
  rw [innerSourceMassOn_eq_zero_of_disjoint U _ hab j
    (eq_empty_iff_forall_notMem.mpr fun x hx => ?_), zero_mul, add_zero]
  -- a source at a point where the second wall is negative has a small quarter angle
  have hq : sourceQuarterAngle (fullAngle _ j) < η := by
    by_contra hnot
    have ht := sourceQuarterAngle_mem (dyadic level) j
    have hcorner := finiteBarrier_nonneg U (normal _) (pairList (dyadic level)) none x
    rw [← innerSource_cornerWall U _ j hx.2] at hcorner
    exact (hcorner.trans (min_le_right _ _)).not_gt (div_neg_of_neg_of_pos
      (hneg x hx.1 _ ⟨not_lt.mp hnot, ht.2.le⟩)
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩))
  rw [sourceQuarterAngle_fullAngle] at hq
  rcases j with t | t <;> have ht := (interiorPoint_mem (dyadic level) t).1
  · exact hjE ⟨ht.le, hq.le⟩
  · exact hjF ⟨le_add_of_nonneg_left ht.le, by
      simp only [fullAngle]; linarith [show (t.val : ℝ) < η from hq]⟩

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
  refine tendsto_order.2 ⟨fun ε hε => .of_forall fun n => hε.trans_le measureReal_nonneg,
    fun ε hε => ?_⟩
  obtain ⟨η, hη, hηε⟩ := exists_between (div_pos hε (by positivity : (0 : ℝ) < 4 * (4 * R + 12)))
  rw [lt_div_iff₀ (by positivity)] at hηε
  filter_upwards [(hl.add ((hr.sub hl).div_const 4)).eventually (gt_mem_nhds ha),
    (hr.sub ((hr.sub hl).div_const 4)).eventually (lt_mem_nhds hb),
    h.eventually_secondWallNumerator_neg_on_compact hU hK isCompact_Icc hη hnegative,
    hlevel.eventually (mesh_tendsto.eventually (gt_mem_nhds hη))] with n hnL hnR hsrc hmesh
  have := finitePositiveLength_le_small_pair_mass (hU n) hR (hbox n) (level n) hab hη.le
    hnL.le hnR.le fun x hx => hsrc x (Ioc_subset_Icc_self hx)
  linarith [mul_nonneg hR (sub_nonneg.2 hmesh.le)]

end AngularGrid

end AmbidextrousSofa
