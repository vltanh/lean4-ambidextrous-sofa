import AmbidextrousSofa.Analysis.ShadowSecants
import AmbidextrousSofa.Analysis.AtomIntervalLimit

/-!
# The actual same-sign source law

A positive same-sign margin persists uniformly near a moving sampled
normal. The exact finite shadowing inequalities therefore bound the
actual selected curvature atoms by zero or half the mesh, with the
already controlled errors. Summation, Hausdorff convergence, and Lebesgue
differentiation give the corresponding bounds for the actual cap density.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem eventually_uniform_pos_of_moving_tendsto
    {J : ℕ → Type*} (angle value : ∀ n, J n → ℝ) {t L : ℝ} (hL : 0 < L)
    (hlim : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∀ j : ∀ n, J (ns n),
        Tendsto (fun n => angle (ns n) (j n)) atTop (𝓝 t) →
        Tendsto (fun n => value (ns n) (j n)) atTop (𝓝 L)) :
    ∃ δ > 0, ∀ᶠ n in atTop, ∀ j : J n,
      |angle n j - t| < δ → 0 < value n j := by
  obtain ⟨δ, hδ, hbound⟩ := eventually_uniform_upper_of_moving_tendsto
    angle (fun n j => -value n j) (L := -L)
    (fun ns hns j hj => (hlim ns hns j hj).neg) (half_pos hL)
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hbound] with n hn
  intro j hj
  have h := hn j hj
  linarith

def sameSignVelocityMargin (positive : Bool) (U : Set Plane) (t : ℝ) : ℝ :=
  if positive then min (-secondCornerVelocity U t) (firstCornerVelocity U t)
    else min (secondCornerVelocity U t) (-firstCornerVelocity U t)

def sameSignCoefficient (positive : Bool) (t : ℝ) : ℝ :=
  if t < Real.pi / 2 then (if positive then 0 else 1 / 2)
    else (if positive then 1 / 2 else 0)

theorem sameSignCoefficient_nonneg (positive : Bool) (t : ℝ) :
    0 ≤ sameSignCoefficient positive t := by
  unfold sameSignCoefficient
  split <;> cases positive <;> norm_num

theorem sameSignCoefficient_le_half (positive : Bool) (t : ℝ) :
    sameSignCoefficient positive t ≤ 1 / 2 := by
  unfold sameSignCoefficient
  split <;> cases positive <;> norm_num

namespace AngularGrid

def sameSignShadowMargin (positive : Bool) (U : Set Plane) (t δ : ℝ) : ℝ :=
  if positive then positiveShadowMargin U t δ else negativeShadowMargin U t δ

theorem IsSelectedPolygon.curvature_atom_le_shadow {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hc : 0 ≤ coefficient)
    (positive : Bool) (j : SourceIndex (dyadic level))
    (hmargin : 0 < sameSignShadowMargin positive U
      (sourceQuarterAngle (fullAngle (dyadic level) j)) (mesh level)) :
    (upperCurvature U {fullAngle (dyadic level) j}).toReal ≤
      2 * sameSignCoefficient positive (fullAngle (dyadic level) j) *
        Real.tan (mesh level / 2) + middleOuterMass U (dyadic level) j +
          selectionDefect target U level coefficient j := by
  cases positive with
  | false =>
    cases j with
    | inl t =>
      have hm : 0 < negativeShadowMargin U t.val (mesh level) := by
        simpa [sameSignShadowMargin, sourceQuarterAngle_fullAngle] using hmargin
      have h := (hU.negative_shadow_atoms hc t hm).2
      simpa [sameSignCoefficient, fullAngle, (interiorPoint_mem (dyadic level) t).2] using h
    | inr t =>
      have hm : 0 < negativeShadowMargin U t.val (mesh level) := by
        simpa [sameSignShadowMargin, sourceQuarterAngle_fullAngle] using hmargin
      have ht : ¬ (t.val : ℝ) + Real.pi / 2 < Real.pi / 2 := by
        linarith [(interiorPoint_mem (dyadic level) t).1]
      have h := (hU.negative_shadow_atoms hc t hm).1
      simpa [sameSignCoefficient, fullAngle, ht] using h
  | true =>
    cases j with
    | inl t =>
      have hm : 0 < positiveShadowMargin U t.val (mesh level) := by
        simpa [sameSignShadowMargin, sourceQuarterAngle_fullAngle] using hmargin
      have h := (hU.positive_shadow_atoms hc t hm).1
      simpa [sameSignCoefficient, fullAngle, (interiorPoint_mem (dyadic level) t).2] using h
    | inr t =>
      have hm : 0 < positiveShadowMargin U t.val (mesh level) := by
        simpa [sameSignShadowMargin, sourceQuarterAngle_fullAngle] using hmargin
      have ht : ¬ (t.val : ℝ) + Real.pi / 2 < Real.pi / 2 := by
        linarith [(interiorPoint_mem (dyadic level) t).1]
      have h := (hU.positive_shadow_atoms hc t hm).2
      simpa [sameSignCoefficient, fullAngle, ht] using h

end AngularGrid

theorem CapHausdorffTendsto.sameSignShadowMargin_tendsto
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B) (positive : Bool)
    {angle δ : ℕ → ℝ} {t : ℝ} (hangle : Tendsto angle atTop (𝓝 t))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hsin : ∀ n, 0 < Real.sin (δ n)) (hcos : ∀ n, 0 ≤ Real.cos (δ n))
    (ht : Imported.sigmaAt K t = 0) (htcomp : Imported.sigmaAt K (t + Real.pi / 2) = 0) :
    Tendsto (fun n => AngularGrid.sameSignShadowMargin positive (U n) (angle n) (δ n)) atTop
      (𝓝 (sameSignVelocityMargin positive K t)) := by
  cases positive with
  | false => exact h.negativeShadowMargin_tendsto hU hK hB hbox hangle hδ hsin hcos ht htcomp
  | true => exact h.positiveShadowMargin_tendsto hU hK hB hbox hangle hδ hsin hcos ht htcomp

namespace AngularGrid

theorem eventually_sameSignShadowMargin_pos
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B) (positive : Bool)
    {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop) {t : ℝ}
    (htop : t ≠ Real.pi / 2)
    (ht : Imported.sigmaAt K (sourceQuarterAngle t) = 0)
    (htcomp : Imported.sigmaAt K (sourceQuarterAngle t + Real.pi / 2) = 0)
    (hmargin : 0 < sameSignVelocityMargin positive K (sourceQuarterAngle t)) :
    ∃ δ > 0, ∀ᶠ n in atTop, ∀ j : SourceIndex (dyadic (level n)),
      |fullAngle (dyadic (level n)) j - t| < δ →
        0 < sameSignShadowMargin positive (U n)
          (sourceQuarterAngle (fullAngle (dyadic (level n)) j)) (mesh (level n)) := by
  apply eventually_uniform_pos_of_moving_tendsto
    (fun n => fullAngle (dyadic (level n)))
    (fun n j => sameSignShadowMargin positive (U n)
      (sourceQuarterAngle (fullAngle (dyadic (level n)) j)) (mesh (level n))) hmargin
  intro ns hns j hangle
  exact (h.comp hns).sameSignShadowMargin_tendsto (fun n => hU (ns n)) hK hB
    (fun n => hbox (ns n)) positive (sourceQuarterAngle_tendsto hangle htop)
    (mesh_tendsto.comp (hlevel.comp hns)) (fun n => mesh_sin_pos (level (ns n)))
    (fun n => (mesh_cos_pos (level (ns n))).le) ht htcomp

theorem tan_half_div_mesh_tendsto {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop) :
    Tendsto (fun n => Real.tan (mesh (level n) / 2) / mesh (level n)) atTop (𝓝 (1 / 2)) := by
  have hhalf : Tendsto (fun n => mesh (level n) / 2) atTop (𝓝 0) := by
    simpa only [zero_div] using (mesh_tendsto.comp hlevel).div_const 2
  have hratio := tan_div_self_tendsto hhalf (fun n => div_pos (mesh_pos (level n)) (by norm_num))
  simpa only [div_div, div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hratio.div_const 2

theorem eventually_shadow_atoms_le
    {target : Set Plane} {U : ℕ → Set Plane} {B : Set Plane}
    {boxLeft boxRight : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    (positive : Bool) {t ε : ℝ} (htop : t ≠ Real.pi / 2)
    (ht : Imported.sigmaAt target (sourceQuarterAngle t) = 0)
    (htcomp : Imported.sigmaAt target (sourceQuarterAngle t + Real.pi / 2) = 0)
    (hmargin : 0 < sameSignVelocityMargin positive target (sourceQuarterAngle t))
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ᶠ n in atTop, ∀ j : SourceIndex (dyadic (level n)),
      |fullAngle (dyadic (level n)) j - t| < δ →
        (upperCurvature (U n) {fullAngle (dyadic (level n)) j}).toReal ≤
          (sameSignCoefficient positive t + ε) * mesh (level n) +
            middleOuterMass (U n) (dyadic (level n)) j +
              selectionDefect target (U n) (level n) (coefficient n) j := by
  obtain ⟨δ₀, hδ₀, hfinite⟩ := eventually_sameSignShadowMargin_pos hHausdorff
    (fun n => (hU n).isCap) hTarget hB hbox positive hlevel htop ht htcomp hmargin
  let gap := if t < Real.pi / 2 then Real.pi / 2 - t else t - Real.pi / 2
  have hgap : 0 < gap := by
    dsimp only [gap]
    split_ifs with hlt
    · exact sub_pos.mpr hlt
    · exact sub_pos.mpr (lt_of_le_of_ne (le_of_not_gt hlt) htop.symm)
  let δ := min δ₀ gap
  have hδ : 0 < δ := lt_min hδ₀ hgap
  have hδ₀' : δ ≤ δ₀ := min_le_left _ _
  have hδgap : δ ≤ gap := min_le_right _ _
  have hsame : ∀ s : ℝ, |s - t| < δ → sameSignCoefficient positive s =
      sameSignCoefficient positive t := by
    intro s hs
    have hnear := abs_lt.mp hs
    by_cases ht' : t < Real.pi / 2
    · have hgap' : gap = Real.pi / 2 - t := if_pos ht'
      have hs' : s < Real.pi / 2 := by linarith [hnear.2]
      simp only [sameSignCoefficient, if_pos ht', if_pos hs']
    · have hgap' : gap = t - Real.pi / 2 := if_neg ht'
      have hs' : ¬ s < Real.pi / 2 := by linarith [hnear.1]
      simp only [sameSignCoefficient, if_neg ht', if_neg hs']
  have hratio := (tan_half_div_mesh_tendsto hlevel).eventually_lt_const
    (show (1 / 2 : ℝ) < 1 / 2 + ε by linarith)
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hfinite, hratio] with n hn hratio
  intro j hj
  have hm := hn j (hj.trans_le hδ₀')
  have hatom := (hU n).curvature_atom_le_shadow (hc n) positive j hm
  rw [hsame _ hj] at hatom
  have htan : Real.tan (mesh (level n) / 2) ≤ (1 / 2 + ε) * mesh (level n) :=
    (div_le_iff₀ (mesh_pos (level n))).mp hratio.le
  have hC0 := sameSignCoefficient_nonneg positive t
  have hC1 := sameSignCoefficient_le_half positive t
  have hweight := mul_le_mul_of_nonneg_right hC1 hε.le
  have hfactor : 2 * sameSignCoefficient positive t * (1 / 2 + ε) ≤
      sameSignCoefficient positive t + ε := by nlinarith [hweight]
  have hscaled := mul_le_mul_of_nonneg_left htan
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC0)
  have hfinal := mul_le_mul_of_nonneg_right hfactor (mesh_pos (level n)).le
  nlinarith

theorem curvature_local_shadow_bound
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c t ε : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    {ρ : ℝ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s)
    (heq : (upperCurvature target).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (positive : Bool) (ht : t ∈ regularCurvatureDomain m)
    (hpaired : sourceQuarterAngle t ∈ regularCornerDomain m)
    (hmargin : 0 < sameSignVelocityMargin positive target (sourceQuarterAngle t))
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ d : ℝ, 0 < d → d < δ →
      (upperCurvature target).real (Ioc t (t + d)) ≤ (sameSignCoefficient positive t + ε) * d := by
  have htop := (mem_regularCurvatureDomain_iff.mp ht).2.2.1
  have hfirst := sigmaAt_eq_zero_of_density hρ hρ0 heq hpaired.2.1
  have hsecond := sigmaAt_eq_zero_of_density hρ hρ0 heq hpaired.2.2
  obtain ⟨δ₀, hδ₀, hfinite⟩ := eventually_shadow_atoms_le hTarget hU hHausdorff hlevel hc
    (isCompact_Icc.prod isCompact_Icc) hbox positive htop hfirst hsecond hmargin hε
  have hopen : IsOpen (regularCurvatureDomain m) := by
    rw [regularCurvatureDomain_eq_three]
    exact (isOpen_Ioo.union isOpen_Ioo).union isOpen_Ioo
  obtain ⟨a, b, htIoo, hIoo⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds ht)
  let δ := min δ₀ (b - t)
  have hδ : 0 < δ := lt_min hδ₀ (sub_pos.mpr htIoo.2)
  have hδ₀' : δ ≤ δ₀ := min_le_left _ _
  have hδb : δ ≤ b - t := min_le_right _ _
  refine ⟨δ, hδ, ?_⟩
  intro d hd hdδ
  have hreg : Icc t (t + d) ⊆ regularCurvatureDomain m := by
    intro s hs
    apply hIoo
    exact ⟨htIoo.1.trans_le hs.1, by linarith [hs.2]⟩
  have hbound := curvature_Ioc_le_of_eventual_atom_bound hTarget hU hHausdorff hlevel hc
    hrate hbox hwidth haffine
    (show 0 ≤ sameSignCoefficient positive t + ε from
      add_nonneg (sameSignCoefficient_nonneg positive t) hε.le)
    (show t ≤ t + d by linarith) hreg
    (sigmaAt_eq_zero_of_density hρ hρ0 heq ht)
    (sigmaAt_eq_zero_of_density hρ hρ0 heq (hreg ⟨by linarith, le_rfl⟩)) (by
      filter_upwards [hfinite] with n hn
      intro j hj
      apply hn j
      apply abs_lt.mpr
      constructor <;> linarith [hj.1, hj.2])
  simpa only [add_sub_cancel_left] using hbound

end AngularGrid

/-- The actual maximizer supplies its own selected sequence. The density
argument only assumes the literal measure representation already proved
on the regular domain, and does not introduce an exposure certificate. -/
theorem IsFullCapMaximizer.ae_density_same_sign_bound
    {K : Set Plane} (hK : IsFullCapMaximizer K) {m c C : ℝ} {ρ : ℝ → ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature K).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (positive : Bool) :
    ∀ᵐ t : ℝ ∂volume, t ∈ regularCurvatureDomain m →
      sourceQuarterAngle t ∈ regularCornerDomain m →
        0 < sameSignVelocityMargin positive K (sourceQuarterAngle t) →
          ρ t ≤ sameSignCoefficient positive t := by
  let R := |horizontalLeft K| + |horizontalRight K| + 1
  have hR : 0 ≤ R := by positivity
  have hbox : K ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1 := by
    apply subset_symmetricBox_of_horizontalBox
    intro p hp
    refine ⟨?_, hK.isCap.inStrip hp⟩
    rw [← horizontalProjection_eq_Icc hK.isCap.nonempty hK.isCap.isCompact hK.isCap.convex]
    exact ⟨p, hp, rfl⟩
  obtain ⟨level, coefficient, U, hlevel, hc, hrate, hU, _, hHausdorff⟩ :=
    AngularGrid.exists_selected_sequence hK (by linarith : -R ≤ R) hbox
  have hlevelTop : Tendsto level atTop atTop := tendsto_atTop_mono hlevel tendsto_id
  have hwidth : 0 < capWidth K := by linarith [hK.width_bounds.1, one_lt_M]
  have hopen : IsOpen (regularCurvatureDomain m) := by
    rw [regularCurvatureDomain_eq_three]
    exact (isOpen_Ioo.union isOpen_Ioo).union isOpen_Ioo
  have h := ae_density_le_of_conditional_local_bound hopen hρ hρ0 hρC heq
    (P := fun t => sourceQuarterAngle t ∈ regularCornerDomain m ∧
      0 < sameSignVelocityMargin positive K (sourceQuarterAngle t))
    (f := sameSignCoefficient positive) (by
      intro t ht hP ε hε
      exact AngularGrid.curvature_local_shadow_bound hK.isCap hU hHausdorff hlevelTop
        (fun n => (hc n).le) hrate (fun n => (hU n).inBox) hwidth haffine hρ hρ0 heq
        positive ht hP.1 hP.2 hε)
  filter_upwards [h] with t ht hregular hpaired hmargin
  exact ht hregular ⟨hpaired, hmargin⟩

/-- In the manuscript convention `p = -secondCornerVelocity` and
`q = firstCornerVelocity`, this is precisely the two same-sign quadrant
laws. Both densities represent the actual supporting-face curvature. -/
theorem IsFullCapMaximizer.ae_curvature_same_sign_quadrants
    {K : Set Plane} (hK : IsFullCapMaximizer K) {m c C : ℝ} {ρ : ℝ → ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature K).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t))) :
    ∀ᵐ t ∂volume.restrict (regularCornerDomain m),
      (0 < firstCornerVelocity K t ∧ secondCornerVelocity K t < 0 →
        ρ t = 0 ∧ ρ (t + Real.pi / 2) ≤ 1 / 2) ∧
      (firstCornerVelocity K t < 0 ∧ 0 < secondCornerVelocity K t →
        ρ (t + Real.pi / 2) = 0 ∧ ρ t ≤ 1 / 2) := by
  have hp := hK.ae_density_same_sign_bound haffine hρ hρ0 hρC heq true
  have hn := hK.ae_density_same_sign_bound haffine hρ hρ0 hρC heq false
  have hpShift := (measurePreserving_add_right volume (Real.pi / 2)).quasiMeasurePreserving.ae hp
  have hnShift := (measurePreserving_add_right volume (Real.pi / 2)).quasiMeasurePreserving.ae hn
  filter_upwards [ae_restrict_mem (isOpen_regularCornerDomain m).measurableSet,
    ae_restrict_of_ae hp, ae_restrict_of_ae hn,
    ae_restrict_of_ae hpShift, ae_restrict_of_ae hnShift] with t ht hp hn hpShift hnShift
  have hbase : sourceQuarterAngle t = t := by
    simp only [sourceQuarterAngle, if_pos ht.1.2]
  have hnot : ¬ t + Real.pi / 2 < Real.pi / 2 := by linarith [ht.1.1]
  have hshift : sourceQuarterAngle (t + Real.pi / 2) = t := by
    simp only [sourceQuarterAngle, if_neg hnot, add_sub_cancel_right]
  have hpBase := hp ht.2.1 (hbase.symm ▸ ht)
  have hnBase := hn ht.2.1 (hbase.symm ▸ ht)
  have hpComp := hpShift ht.2.2 (hshift.symm ▸ ht)
  have hnComp := hnShift ht.2.2 (hshift.symm ▸ ht)
  constructor
  · rintro ⟨hq, hr⟩
    have hm : 0 < sameSignVelocityMargin true K t := by
      simpa [sameSignVelocityMargin] using lt_min (neg_pos.mpr hr) hq
    have hfirst : ρ t ≤ 0 := by
      simpa [sameSignCoefficient, ht.1.2] using hpBase (hbase.symm ▸ hm)
    have hsecond : ρ (t + Real.pi / 2) ≤ 1 / 2 := by
      simpa [sameSignCoefficient, hnot] using hpComp (hshift.symm ▸ hm)
    exact ⟨le_antisymm hfirst (hρ0 t), hsecond⟩
  · rintro ⟨hq, hr⟩
    have hm : 0 < sameSignVelocityMargin false K t := by
      simpa [sameSignVelocityMargin] using lt_min hr (neg_pos.mpr hq)
    have hfirst : ρ t ≤ 1 / 2 := by
      simpa [sameSignCoefficient, ht.1.2] using hnBase (hbase.symm ▸ hm)
    have hsecond : ρ (t + Real.pi / 2) ≤ 0 := by
      simpa [sameSignCoefficient, hnot] using hnComp (hshift.symm ▸ hm)
    exact ⟨le_antisymm hsecond (hρ0 _), hfirst⟩

theorem IsFullCapMaximizer.curvature_density_corner_controls
    {K : Set Plane} (hK : IsFullCapMaximizer K) (hheight : capHeight K = 1)
    {m c : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity K t)) ∧
      (∀ t, ρ t ≤ 4 * (|horizontalLeft K| + |horizontalRight K| + 1) + 10) ∧
      (upperCurvature K).restrict (regularCurvatureDomain m) =
        (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)) ∧
      (∀ᵐ t ∂volume.restrict (regularCornerDomain m),
        ((attachedCorner K t).2 ≤ 0 → ρ t < 1 ∧ ρ (t + Real.pi / 2) < 1) ∧
        (0 < firstCornerVelocity K t ∧ secondCornerVelocity K t < 0 →
          ρ t = 0 ∧ ρ (t + Real.pi / 2) ≤ 1 / 2) ∧
        (firstCornerVelocity K t < 0 ∧ 0 < secondCornerVelocity K t →
          ρ (t + Real.pi / 2) = 0 ∧ ρ t ≤ 1 / 2)) := by
  obtain ⟨ρ, hρ, hbounds, hC, heq, hnonpositive⟩ :=
    hK.curvature_density_nonpositive_corner_control hheight haffine
  have hsign := hK.ae_curvature_same_sign_quadrants haffine hρ
    (fun t => (hbounds t).1) hC heq
  refine ⟨ρ, hρ, hbounds, hC, heq, ?_⟩
  filter_upwards [hnonpositive, hsign] with t hn hs
  exact ⟨hn.2.2, hs⟩

theorem IsFullCapMaximizer.horizontal_curvature_density_corner_controls
    {K : Set Plane} (hK : IsFullCapMaximizer K) (hheight : capHeight K = 1) {c : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K), capRoof K x = c) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity K t)) ∧
      (∀ t, ρ t ≤ 4 * (|horizontalLeft K| + |horizontalRight K| + 1) + 10) ∧
      (upperCurvature K).restrict (regularCurvatureDomain 0) =
        (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (ρ t)) ∧
      (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
        ((attachedCorner K t).2 ≤ 0 → ρ t < 1 ∧ ρ (t + Real.pi / 2) < 1) ∧
        (0 < firstCornerVelocity K t ∧ secondCornerVelocity K t < 0 →
          ρ t = 0 ∧ ρ (t + Real.pi / 2) ≤ 1 / 2) ∧
        (firstCornerVelocity K t < 0 ∧ 0 < secondCornerVelocity K t →
          ρ (t + Real.pi / 2) = 0 ∧ ρ t ≤ 1 / 2)) := by
  have h := hK.curvature_density_corner_controls hheight (m := 0) (c := c)
    (by simpa only [zero_mul, zero_add] using haffine)
  simpa only [regularCornerDomain_zero] using h

end AmbidextrousSofa
