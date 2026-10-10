import AmbidextrousSofa.Analysis.CompanionBaseline
import AmbidextrousSofa.Analysis.CoreContactGeometry

/-!
# Actual corner visibility through an initial nonpositive floor interval

The baseline comparison gives all earlier cut-wall gaps without any
companion curvature bound. Global first-unit curvature supplies every
later first-wall gap. At a positive opposite-sign corner these strict
gaps persist locally: compact remote angles retain a uniform gap, while
nearby second-wall derivatives remain strictly positive. This includes
the boundary case in which the companion tangent first touches zero at
the bad-entry angle.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
local notation "D" => secondTangentPoint F.g F.gD
local notation "Z" => innerCornerPoint F.f F.g
local notation "p" => supportP F.fD F.g
local notation "q" => supportQ F.gD F.f
local notation "V" => leftCompanionCap U (horizontalLeft U + capWidth U / 4)

theorem fullTiltedSupportQuarterPair_cut_wall_eq_scalar (t x : ℝ) :
    secondWall V t x = (F.g t - 1 + x * Real.sin t) / Real.cos t := by
  change secondWall V t x =
    (angleSupport V (t + Real.pi / 2) - 1 + x * Real.sin t) / Real.cos t
  simp only [secondWall, angleSupport, companionNormal_eq_unitNormal]

theorem fullTiltedSupportQuarterPair_cut_wall_lt_core_of_initial_floor_nonpos {t : ℝ}
    (ht : t ∈ Ioo 0 (Real.pi / 2)) (hy : 0 < (Z t).2)
    (hfloor : ∀ s ∈ Ioc (0 : ℝ) t, (D s).2 ≤ 0) :
    ∀ r ∈ Ioo (0 : ℝ) t, secondWall V r (Z t).1 < (Z t).2 := by
  have hwall := (fullTiltedSupportQuarterPair_walls_core
    hU hm haffine hρ hρ0 hρK heq ht).2
  have hscalar := fullTiltedSupportQuarterPair_cut_wall_eq_scalar hU hm haffine hρ hρ0 hρK heq
  intro r hr
  have h := companion_wall_lt_later_of_initial_tangent_nonpos ht hr
    (fun s hs => (fullTiltedSupportQuarterPair_support_derivatives
      hU hm haffine hρ hρ0 hρK heq hs).2) hfloor
    (show 0 < (F.g t - 1 + (Z t).1 * Real.sin t) / Real.cos t by
      rw [← hscalar t (Z t).1, hwall]
      exact hy)
  simpa only [← hscalar r (Z t).1, ← hscalar t (Z t).1, hwall] using h

theorem fullTiltedSupportQuarterPair_core_contact_of_initial_floor_nonpos {t : ℝ}
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ s ≤ 1)
    (ht : t ∈ Ioo 0 (Real.pi / 2)) (hp : p t < 0)
    (hy : 0 < (Z t).2) (hx : (Z t).1 ≤ horizontalRight U - capWidth U / 4)
    (hfloor : ∀ s ∈ Ioc (0 : ℝ) t, (D s).2 ≤ 0) :
    sweptNiche U (Real.pi / 2) (Z t).1 = (Z t).2 ∧
      (∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
        fullWallClip hU.isCap.toCompactCap (Z t).1 s =
          sweptNiche U (Real.pi / 2) (Z t).1 → s = t) := by
  exact fullTiltedSupportQuarterPair_core_contact_of_earlier_cut_walls
    hU hm haffine hρ hρ0 hρK heq hunit ht hp hy hx
    (fullTiltedSupportQuarterPair_cut_wall_lt_core_of_initial_floor_nonpos
      hU hm haffine hρ hρ0 hρK heq ht hy hfloor)

/-- Strict earlier wall gaps persist for all nearby moving corners.
The companion tangent need not remain below the floor in that
neighborhood; its positive corner gap is the local derivative margin. -/
theorem fullTiltedSupportQuarterPair_earlier_cut_walls_eventually {t : ℝ}
    (ht : t ∈ Ioo 0 (Real.pi / 2)) (hq : 0 < q t) (hy : 0 < (Z t).2)
    (hEarlier : ∀ r ∈ Ioo (0 : ℝ) t, secondWall V r (Z t).1 < (Z t).2) :
    ∀ᶠ s in 𝓝 t, ∀ r ∈ Ioo (0 : ℝ) s, secondWall V r (Z s).1 < (Z s).2 := by
  have hcore := fullTiltedSupportQuarterPair_core_continuous hU hm haffine hρ hρ0 hρK heq
  have hX : ContinuousAt (fun s => (Z s).1) t :=
    hcore.1.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hY : ContinuousAt (fun s => (Z s).2) t :=
    hcore.2.continuousAt (Icc_mem_nhds ht.1 ht.2)
  obtain ⟨_hBx, _hBy, hDx, _hDy, _hderiv⟩ :=
    fullTiltedSupportQuarterPair_tangent_calculus hU hm haffine hρ hρ0 hρK heq
  have hDcont : ContinuousAt (fun s => (D s).1) t := by
    have hcont : ContinuousOn (fun s => (D s).1) (Icc 0 (Real.pi / 2)) := by
      simpa only [uIcc_of_le (show (0 : ℝ) ≤ Real.pi / 2 by positivity)] using hDx.continuousOn
    exact hcont.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  have hgap : (D t).1 < (Z t).1 := by
    rw [innerCorner_fst_eq_secondTangent F.f F.g F.gD]
    exact lt_add_of_pos_right _ (mul_pos hq hc)
  let A := ((Z t).1 + (D t).1) / 2
  have hA0 : (D t).1 < A := by dsimp only [A]; linarith only [hgap]
  have hA1 : A < (Z t).1 := by dsimp only [A]; linarith only [hgap]
  have hevent : ∀ᶠ s in 𝓝 t,
      s ∈ Ioo (0 : ℝ) (Real.pi / 2) ∧ (D s).1 < A ∧ A < (Z s).1 := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2,
      Filter.Tendsto.eventually_lt_const hA0 hDcont.tendsto,
      Filter.Tendsto.eventually_const_lt hA1 hX.tendsto] with s hs hD hZ
    exact ⟨hs, hD, hZ⟩
  obtain ⟨l, u, htu, hlocal⟩ := mem_nhds_iff_exists_Ioo_subset.mp hevent
  let a := (l + t) / 2
  have hla : l < a := by dsimp only [a]; linarith only [htu.1]
  have hat : a < t := by dsimp only [a]; linarith only [htu.1]
  have ha : a ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    (hlocal ⟨hla, hat.trans htu.2⟩).1
  have hscalar := fullTiltedSupportQuarterPair_cut_wall_eq_scalar hU hm haffine hρ hρ0 hρK heq
  have hg : Continuous F.g :=
    hU.isCap_fullLeftCompanion.imported_isConvexBody.continuous_supp.comp
      (continuous_id.add_const (Real.pi / 2))
  have hzero : secondWall V 0 (Z t).1 ≤ 0 := by
    rw [hscalar]
    have hg0 := (fullTiltedSupportQuarterPair_base_traces
      hU hm haffine hρ hρ0 hρK heq).2.1
    simpa only [hg0, Real.sin_zero, Real.cos_zero, mul_zero, add_zero, div_one] using
      sub_nonpos.mpr hU.isCap_fullLeftCompanion.capHeight_le_one
  have hremote : ∀ᶠ s in 𝓝 t, ∀ r ∈ Icc (0 : ℝ) a,
      secondWall V r (Z s).1 < (Z s).2 := by
    apply (isCompact_Icc : IsCompact (Icc (0 : ℝ) a)).eventually_forall_of_forall_eventually
    intro r hr
    have hcr : Real.cos r ≠ 0 := (Real.cos_pos_of_mem_Ioo
      ⟨by linarith only [hr.1, Real.pi_pos], hr.2.trans_lt ha.2⟩).ne'
    have hfun : (fun z : ℝ × ℝ => secondWall V z.2 (Z z.1).1) =
        fun z => (F.g z.2 - 1 + (Z z.1).1 * Real.sin z.2) / Real.cos z.2 := by
      funext z
      exact hscalar z.2 (Z z.1).1
    have hcont : ContinuousAt (fun z : ℝ × ℝ => secondWall V z.2 (Z z.1).1) (t, r) := by
      rw [hfun]
      exact (((hg.continuousAt.comp continuous_snd.continuousAt).sub_const 1).add
        ((hX.comp continuous_fst.continuousAt).mul
          (Real.continuous_sin.continuousAt.comp continuous_snd.continuousAt))).div
            (Real.continuous_cos.continuousAt.comp continuous_snd.continuousAt) hcr
    have hcurrent : secondWall V r (Z t).1 < (Z t).2 := by
      rcases hr.1.eq_or_lt with hr0 | hr0
      · rw [← hr0]
        exact hzero.trans_lt hy
      · exact hEarlier r ⟨hr0, hr.2.trans_lt hat⟩
    exact hcont.tendsto.eventually_lt
      (hY.comp continuous_fst.continuousAt).tendsto hcurrent
  filter_upwards [hremote, Ioo_mem_nhds hat htu.2] with s hs hsu
  have hslocal := hlocal ⟨hla.trans hsu.1, hsu.2⟩
  intro r hr
  by_cases hra : r ≤ a
  · exact hs r ⟨hr.1.le, hra⟩
  · have har : a < r := lt_of_not_ge hra
    have hineq : secondWall V r (Z s).1 < secondWall V s (Z s).1 := by
      apply endpoint_lt_of_hasDerivAt_pos hr.2
        (fun w hw => fullTiltedSupportQuarterPair_cut_wall_derivative
          hU hm haffine hρ hρ0 hρK heq
          (hlocal ⟨hla.trans (har.trans_le hw.1), hw.2.trans_lt hsu.2⟩).1 (Z s).1)
      intro w hw
      have hwlocal := hlocal ⟨hla.trans (har.trans hw.1), hw.2.trans hsu.2⟩
      exact div_pos (sub_pos.mpr (hwlocal.2.1.trans hslocal.2.2))
        (sq_pos_of_ne_zero (Real.cos_pos_of_mem_Ioo
          ⟨by linarith only [hwlocal.1.1, Real.pi_pos], hwlocal.1.2⟩).ne')
    simpa only [(fullTiltedSupportQuarterPair_walls_core
      hU hm haffine hρ hρ0 hρK heq hslocal.1).2] using hineq

/-- This is the concrete neighborhood needed when the first floor zero
coincides with the bad-entry angle. It follows from the actual strict
wall gaps and does not assume future floor behavior. -/
theorem fullTiltedSupportQuarterPair_core_contact_eventually_of_initial_floor_nonpos {t : ℝ}
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ s ≤ 1)
    (ht : t ∈ Ioo 0 (Real.pi / 2)) (hp : p t < 0) (hq : 0 < q t)
    (hy : 0 < (Z t).2) (hx : (Z t).1 < horizontalRight U - capWidth U / 4)
    (hfloor : ∀ s ∈ Ioc (0 : ℝ) t, (D s).2 ≤ 0) :
    ∀ᶠ s in 𝓝 t, s ∈ Ioo (0 : ℝ) (Real.pi / 2) ∧
      sweptNiche U (Real.pi / 2) (Z s).1 = (Z s).2 ∧
      (∀ r ∈ Icc (0 : ℝ) (Real.pi / 2),
        fullWallClip hU.isCap.toCompactCap (Z s).1 r =
          sweptNiche U (Real.pi / 2) (Z s).1 → r = s) := by
  have hcore := fullTiltedSupportQuarterPair_core_continuous hU hm haffine hρ hρ0 hρK heq
  have hX := hcore.1.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hY := hcore.2.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hP : ContinuousAt p t :=
    (((F.continuous_fD.sub F.continuous_g).add continuousOn_const).continuousAt
      (Icc_mem_nhds ht.1 ht.2))
  have hearlier := fullTiltedSupportQuarterPair_earlier_cut_walls_eventually
    hU hm haffine hρ hρ0 hρK heq ht hq hy
    (fullTiltedSupportQuarterPair_cut_wall_lt_core_of_initial_floor_nonpos
      hU hm haffine hρ hρ0 hρK heq ht hy hfloor)
  filter_upwards [hearlier, Ioo_mem_nhds ht.1 ht.2,
    Filter.Tendsto.eventually_lt_const hp hP.tendsto,
    Filter.Tendsto.eventually_const_lt hy hY.tendsto,
    Filter.Tendsto.eventually_lt_const hx hX.tendsto] with s hs hsq hps hys hxs
  exact ⟨hsq, fullTiltedSupportQuarterPair_core_contact_of_earlier_cut_walls
    hU hm haffine hρ hρ0 hρK heq hunit hsq hps hys hxs.le hs⟩

end ActualPair

end AmbidextrousSofa
