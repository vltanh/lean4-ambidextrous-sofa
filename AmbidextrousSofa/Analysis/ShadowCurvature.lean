module

public import AmbidextrousSofa.Analysis.ShadowSecants
public import AmbidextrousSofa.Analysis.AtomIntervalLimit

@[expose] public section

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
  obtain ⟨δ, hδ, hbound⟩ := eventually_uniform_upper_of_moving_tendsto angle
    (fun n j => -value n j) (L := -L) (fun ns hns j hj => (hlim ns hns j hj).neg) (half_pos hL)
  exact ⟨δ, hδ, hbound.mono fun n hn j hj => by linarith [hn j hj]⟩

def sameSignVelocityMargin (positive : Bool) (U : Set Plane) (t : ℝ) : ℝ :=
  if positive then min (-secondCornerVelocity U t) (firstCornerVelocity U t)
    else min (secondCornerVelocity U t) (-firstCornerVelocity U t)

def sameSignCoefficient (positive : Bool) (t : ℝ) : ℝ :=
  if t < Real.pi / 2 then (if positive then 0 else 1 / 2)
    else (if positive then 1 / 2 else 0)

theorem sameSignCoefficient_nonneg (positive : Bool) (t : ℝ) :
    0 ≤ sameSignCoefficient positive t := by
  unfold sameSignCoefficient; split <;> cases positive <;> norm_num

theorem sameSignCoefficient_le_half (positive : Bool) (t : ℝ) :
    sameSignCoefficient positive t ≤ 1 / 2 := by
  unfold sameSignCoefficient; split <;> cases positive <;> norm_num

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
  rcases j with t | t <;> have ht := interiorPoint_mem (dyadic level) t <;> cases positive <;>
    simp only [sameSignShadowMargin, sourceQuarterAngle_fullAngle, Sum.elim_inl, Sum.elim_inr,
      Bool.false_eq_true, ↓reduceIte] at hmargin
  · simpa [sameSignCoefficient, fullAngle, ht.2] using (hU.negative_shadow_atoms hc t hmargin).2
  · simpa [sameSignCoefficient, fullAngle, ht.2] using (hU.positive_shadow_atoms hc t hmargin).1
  · simpa [sameSignCoefficient, fullAngle, ht.1.not_gt] using
      (hU.negative_shadow_atoms hc t hmargin).1
  · simpa [sameSignCoefficient, fullAngle, ht.1.not_gt] using
      (hU.positive_shadow_atoms hc t hmargin).2

end AngularGrid

theorem CapHausdorffTendsto.sameSignShadowMargin_tendsto
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B) (positive : Bool)
    {angle δ : ℕ → ℝ} {t : ℝ} (hangle : Tendsto angle atTop (𝓝 t))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hsin : ∀ n, 0 < Real.sin (δ n)) (hcos : ∀ n, 0 ≤ Real.cos (δ n))
    (ht : MovingSofaOptimality.sigmaAt K t = 0) (htcomp : MovingSofaOptimality.sigmaAt K (t + Real.pi / 2) = 0) :
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
    (ht : MovingSofaOptimality.sigmaAt K (sourceQuarterAngle t) = 0)
    (htcomp : MovingSofaOptimality.sigmaAt K (sourceQuarterAngle t + Real.pi / 2) = 0)
    (hmargin : 0 < sameSignVelocityMargin positive K (sourceQuarterAngle t)) :
    ∃ δ > 0, ∀ᶠ n in atTop, ∀ j : SourceIndex (dyadic (level n)),
      |fullAngle (dyadic (level n)) j - t| < δ →
        0 < sameSignShadowMargin positive (U n)
          (sourceQuarterAngle (fullAngle (dyadic (level n)) j)) (mesh (level n)) :=
  eventually_uniform_pos_of_moving_tendsto _ _ hmargin fun ns hns _ hangle =>
    CapHausdorffTendsto.sameSignShadowMargin_tendsto (h.comp hns) (fun n => hU (ns n)) hK hB
      (fun n => hbox (ns n)) positive (sourceQuarterAngle_tendsto hangle htop)
      (mesh_tendsto.comp (hlevel.comp hns)) (fun _ => mesh_sin_pos _)
      (fun _ => (mesh_cos_pos _).le) ht htcomp

theorem tan_half_div_mesh_tendsto {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop) :
    Tendsto (fun n => Real.tan (mesh (level n) / 2) / mesh (level n)) atTop (𝓝 (1 / 2)) := by
  have hhalf : Tendsto (fun n => mesh (level n) / 2) atTop (𝓝 0) := by
    simpa using (mesh_tendsto.comp hlevel).div_const 2
  simpa only [div_div, div_mul_cancel₀ _ (two_ne_zero' ℝ)] using
    (tan_div_self_tendsto hhalf fun n => half_pos (mesh_pos (level n))).div_const 2

theorem eventually_shadow_atoms_le
    {target : Set Plane} {U : ℕ → Set Plane} {B : Set Plane}
    {boxLeft boxRight : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    (positive : Bool) {t ε : ℝ} (htop : t ≠ Real.pi / 2)
    (ht : MovingSofaOptimality.sigmaAt target (sourceQuarterAngle t) = 0)
    (htcomp : MovingSofaOptimality.sigmaAt target (sourceQuarterAngle t + Real.pi / 2) = 0)
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
  -- Within `|t - π / 2|` of `t`, the coefficient does not change.
  have hsame (s : ℝ) (hs : |s - t| < |t - Real.pi / 2|) :
      sameSignCoefficient positive s = sameSignCoefficient positive t := by
    obtain ⟨hs1, hs2⟩ := abs_lt.mp hs
    have hiff : s < Real.pi / 2 ↔ t < Real.pi / 2 := by
      rcases abs_cases (t - Real.pi / 2) with ⟨h, -⟩ | ⟨h, -⟩ <;> constructor <;> intro <;> linarith
    simp only [sameSignCoefficient, hiff]
  refine ⟨min δ₀ |t - Real.pi / 2|, lt_min hδ₀ (abs_pos.2 (sub_ne_zero.2 htop)), ?_⟩
  filter_upwards [hfinite, (tan_half_div_mesh_tendsto hlevel).eventually_lt_const
    (by linarith : (1 / 2 : ℝ) < 1 / 2 + ε)] with n hn hratio j hj
  have hatom := (hU n).curvature_atom_le_shadow (hc n) positive j
    (hn j (hj.trans_le (min_le_left _ _)))
  rw [hsame _ (hj.trans_le (min_le_right _ _))] at hatom
  have hmesh := mesh_pos (level n)
  linarith [mul_le_mul_of_nonneg_left ((div_le_iff₀ hmesh).mp hratio.le)
      (sameSignCoefficient_nonneg positive t),
    mul_le_mul_of_nonneg_right (sameSignCoefficient_le_half positive t) (mul_pos hε hmesh).le]

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
  obtain ⟨δ₀, hδ₀, hfinite⟩ := eventually_shadow_atoms_le hTarget hU hHausdorff hlevel hc
    (isCompact_Icc.prod isCompact_Icc) hbox positive (mem_regularCurvatureDomain_iff.mp ht).2.2.1
    (sigmaAt_eq_zero_of_density hρ hρ0 heq hpaired.2.1)
    (sigmaAt_eq_zero_of_density hρ hρ0 heq hpaired.2.2) hmargin hε
  obtain ⟨a, b, htIoo, hIoo⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((isOpen_Ioo.sdiff (toFinite _).isClosed).mem_nhds ht)
  refine ⟨min δ₀ (b - t), lt_min hδ₀ (sub_pos.mpr htIoo.2), fun d hd hdδ => ?_⟩
  have hdδ₀ := hdδ.trans_le (min_le_left _ _)
  have hdb := hdδ.trans_le (min_le_right _ _)
  have hreg : Icc t (t + d) ⊆ regularCurvatureDomain m := fun s hs =>
    hIoo ⟨htIoo.1.trans_le hs.1, by linarith [hs.2]⟩
  simpa only [add_sub_cancel_left] using curvature_Ioc_le_of_eventual_atom_bound hTarget hU
    hHausdorff hlevel hc hrate hbox hwidth haffine
    (add_nonneg (sameSignCoefficient_nonneg positive t) hε.le) (by linarith) hreg
    (sigmaAt_eq_zero_of_density hρ hρ0 heq ht)
    (sigmaAt_eq_zero_of_density hρ hρ0 heq (hreg ⟨by linarith, le_rfl⟩))
    (hfinite.mono fun n hn j hj =>
      hn j (abs_lt.mpr ⟨by linarith [hj.1], by linarith [hj.2]⟩))

end AngularGrid

/-- The actual maximizer supplies its own selected sequence. The density
argument only assumes the literal measure representation already proved
on the regular domain, and does not introduce an exposure certificate.
The bound is applied at `t` and at `t + π / 2`, which both fold to the quarter angle `t`. -/
theorem IsFullCapMaximizer.ae_density_same_sign_bound
    {K : Set Plane} (hK : IsFullCapMaximizer K) {m c C : ℝ} {ρ : ℝ → ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature K).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (positive : Bool) :
    ∀ᵐ t ∂volume.restrict (regularCornerDomain m), 0 < sameSignVelocityMargin positive K t →
      ρ t ≤ (if positive then 0 else 1 / 2) ∧
        ρ (t + Real.pi / 2) ≤ (if positive then 1 / 2 else 0) := by
  have hR : 0 ≤ |horizontalLeft K| + |horizontalRight K| + 1 := by positivity
  obtain ⟨level, coefficient, U, hlevel, hc, hrate, hU, -, hHausdorff⟩ :=
    AngularGrid.exists_selected_sequence hK (neg_le_self hR) (subset_symmetricBox_of_horizontalBox
      fun p hp => ⟨hK.isCap.fst_mem_Icc hp, hK.isCap.inStrip hp⟩)
  have h := ae_density_le_of_conditional_local_bound (isOpen_Ioo.sdiff (toFinite _).isClosed)
    hρ hρ0 hρC heq (f := sameSignCoefficient positive) (P := fun t =>
      sourceQuarterAngle t ∈ regularCornerDomain m ∧
        0 < sameSignVelocityMargin positive K (sourceQuarterAngle t))
    fun t ht hP ε hε => AngularGrid.curvature_local_shadow_bound hK.isCap hU hHausdorff
      (tendsto_atTop_mono hlevel tendsto_id) (fun n => (hc n).le) hrate (fun n => (hU n).inBox)
      (by linarith only [hK.width_bounds.1, one_lt_M]) haffine hρ hρ0 heq positive ht hP.1 hP.2 hε
  filter_upwards [ae_restrict_mem (isOpen_regularCornerDomain m).measurableSet,
    ae_restrict_of_ae h, ae_restrict_of_ae
      ((measurePreserving_add_right volume (Real.pi / 2)).quasiMeasurePreserving.ae h)]
    with t ht h1 h2 hm
  have hnot : ¬ t + Real.pi / 2 < Real.pi / 2 := by linarith only [ht.1.1]
  have hbase : sourceQuarterAngle t = t := ite_eq_left ht.1.2
  have hshift : sourceQuarterAngle (t + Real.pi / 2) = t := by simp [sourceQuarterAngle, hnot]
  constructor
  · simpa [sameSignCoefficient, ht.1.2] using h1 ht.2.1 ⟨hbase.symm ▸ ht, hbase.symm ▸ hm⟩
  · simpa [sameSignCoefficient, hnot] using h2 ht.2.2 ⟨hshift.symm ▸ ht, hshift.symm ▸ hm⟩

/-- With `p = -secondCornerVelocity` and `q = firstCornerVelocity`, these are
the two same-sign quadrant laws. Both densities represent the actual supporting-face curvature. -/
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
  filter_upwards [hK.ae_density_same_sign_bound haffine hρ hρ0 hρC heq true,
    hK.ae_density_same_sign_bound haffine hρ hρ0 hρC heq false] with t hp hn
  refine ⟨fun ⟨hq, hr⟩ => ?_, fun ⟨hq, hr⟩ => ?_⟩
  · obtain ⟨h1, h2⟩ := hp (lt_min (neg_pos.mpr hr) hq)
    exact ⟨le_antisymm h1 (hρ0 t), h2⟩
  · obtain ⟨h1, h2⟩ := hn (lt_min hr (neg_pos.mpr hq))
    exact ⟨le_antisymm h2 (hρ0 _), h1⟩

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
  refine ⟨ρ, hρ, hbounds, hC, heq, ?_⟩
  filter_upwards [hnonpositive, hK.ae_curvature_same_sign_quadrants haffine hρ
    (fun t => (hbounds t).1) hC heq] with t hn hs using ⟨hn.2.2, hs⟩

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
  simpa only [regularCornerDomain_zero] using hK.curvature_density_corner_controls hheight
    (m := 0) (c := c) (by simpa only [zero_mul, zero_add] using haffine)

end AmbidextrousSofa
