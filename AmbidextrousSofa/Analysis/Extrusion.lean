module

public import AmbidextrousSofa.Analysis.CapOrder

@[expose] public section

/-!
# Vertical extrusion and height saturation of actual caps

An extrusion raises the whole roof and fills down to the baseline. Its
upward supports gain exactly the vertical translation pairing. Every
interior wall and the actual terminal wall therefore gain the same amount;
the nonnegative barrier gains at most that amount. The exterior and middle
windows have equal length, so the actual scalar score cannot decrease.

The final construction saturates any cap to height one. It applies to the
broad cap domain, including caps initially contained in the baseline.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-- Raise the roof by `ε`, retaining every vertical segment down to zero. -/
def verticalExtrusion (U : Set Plane) (ε : ℝ) : Set Plane :=
  upperCap ((fun p : Plane => p + (0, ε)) '' U)

theorem mem_verticalExtrusion_iff (U : Set Plane) (ε : ℝ) (p : Plane) :
    p ∈ verticalExtrusion U ε ↔
      0 ≤ p.2 ∧ ∃ q ∈ U, q.1 = p.1 ∧ p.2 ≤ q.2 + ε := by
  constructor
  · rintro ⟨hp0, y, hpy, q, hq, heq⟩
    have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    simp only [Prod.fst_add, Prod.snd_add, add_zero] at hx hy
    exact ⟨hp0, q, hq, hx, by linarith⟩
  · rintro ⟨hp0, q, hq, hqx, hpy⟩
    refine ⟨hp0, q.2 + ε, hpy, q, hq, ?_⟩
    apply Prod.ext
    · simpa only [Prod.fst_add, add_zero] using hqx
    · rfl

theorem IsDownwardCap.subset_verticalExtrusion {U : Set Plane}
    (hU : IsDownwardCap U) {ε : ℝ} (hε : 0 ≤ ε) : U ⊆ verticalExtrusion U ε := by
  intro p hp
  exact (mem_verticalExtrusion_iff U ε p).mpr
    ⟨(hU.inStrip hp).1, p, hp, rfl, by linarith⟩

theorem IsDownwardCap.verticalLift_nonneg {U : Set Plane}
    (hU : IsDownwardCap U) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ p ∈ ((fun q : Plane => q + (0, ε)) '' U), 0 ≤ p.2 := by
  rintro p ⟨q, hq, rfl⟩
  exact add_nonneg (hU.inStrip hq).1 hε

theorem IsDownwardCap.isCompact_verticalExtrusion {U : Set Plane}
    (hU : IsDownwardCap U) {ε : ℝ} (hε : 0 ≤ ε) :
    IsCompact (verticalExtrusion U ε) :=
  isCompact_upperCap (hU.isCompact.image (by fun_prop)) (hU.verticalLift_nonneg hε)

theorem IsDownwardCap.horizontalProjection_verticalExtrusion {U : Set Plane}
    (hU : IsDownwardCap U) {ε : ℝ} (hε : 0 ≤ ε) :
    horizontalProjection (verticalExtrusion U ε) = horizontalProjection U := by
  apply Set.Subset.antisymm
  · rintro x ⟨p, hp, hpx⟩
    obtain ⟨_, q, hq, hqx, _⟩ := (mem_verticalExtrusion_iff U ε p).mp hp
    exact ⟨q, hq, hqx.trans hpx⟩
  · exact Set.image_mono (hU.subset_verticalExtrusion hε)

theorem IsDownwardCap.isDownwardCap_verticalExtrusion {U : Set Plane}
    (hU : IsDownwardCap U) {ε : ℝ} (hε : 0 ≤ ε)
    (hheight : ∀ p ∈ U, p.2 + ε ≤ 1) : IsDownwardCap (verticalExtrusion U ε) := by
  apply isDownwardCap_upperCap (hU.nonempty.image _)
    (hU.isCompact.image (by fun_prop))
  · simpa only [add_comm] using hU.convex.translate ((0, ε) : Plane)
  · rintro p ⟨q, hq, rfl⟩
    exact ⟨add_nonneg (hU.inStrip hq).1 hε, hheight q hq⟩

/-- Roof translation holds on the actual common projection. Outside it the
roof convention remains zero, so no global additive formula is asserted. -/
theorem IsDownwardCap.capRoof_verticalExtrusion {U : Set Plane}
    (hU : IsDownwardCap U) {ε : ℝ} (hε : 0 ≤ ε) {x : ℝ}
    (hx : x ∈ horizontalProjection U) :
    capRoof (verticalExtrusion U ε) x = capRoof U x + ε := by
  have hcompact := hU.isCompact_verticalExtrusion hε
  have hxV : x ∈ horizontalProjection (verticalExtrusion U ε) := by
    rw [hU.horizontalProjection_verticalExtrusion hε]
    exact hx
  apply le_antisymm
  · obtain ⟨_, q, hq, hqx, hle⟩ :=
      (mem_verticalExtrusion_iff U ε (x, capRoof (verticalExtrusion U ε) x)).mp
        (capRoof_mem hcompact hxV)
    have hqroof : q.2 ≤ capRoof U x := by
      have hq' : (q.1, q.2) ∈ U := by simpa only [Prod.mk.eta] using hq
      simpa only [hqx] using le_capRoof hU.isCompact hq'
    exact hle.trans (add_le_add_left hqroof ε)
  · apply le_capRoof hcompact
    apply (mem_verticalExtrusion_iff U ε (x, capRoof U x + ε)).mpr
    exact ⟨add_nonneg (capRoof_nonneg hU.isCompact
      (fun p hp => (hU.inStrip hp).1) x) hε,
      (x, capRoof U x), capRoof_mem hU.isCompact hx, rfl, le_rfl⟩

/-- Every upward support receives the exact vertical translation correction. -/
theorem IsDownwardCap.support_verticalExtrusion {U : Set Plane}
    (hU : IsDownwardCap U) {ε : ℝ} (hε : 0 ≤ ε) {v : Plane} (hv : 0 ≤ v.2) :
    support (verticalExtrusion U ε) v = support U v + ε * v.2 := by
  rw [verticalExtrusion, support_upperCap (hU.isCompact.image (by fun_prop))
    (hU.nonempty.image _) (hU.verticalLift_nonneg hε) hv,
    support_translate hU.isCompact hU.nonempty]
  simp only [coordDot, zero_mul, zero_add]

theorem IsDownwardCap.firstWall_verticalExtrusion {U : Set Plane}
    (hU : IsDownwardCap U) {ε θ : ℝ} (hε : 0 ≤ ε) (hs : 0 < Real.sin θ)
    (x : ℝ) : firstWall (verticalExtrusion U ε) θ x = firstWall U θ x + ε := by
  unfold firstWall
  rw [hU.support_verticalExtrusion hε (v := unitNormal θ) hs.le]
  simp only [unitNormal]
  field_simp [hs.ne'] <;> ring

theorem IsDownwardCap.secondWall_verticalExtrusion {U : Set Plane}
    (hU : IsDownwardCap U) {ε θ : ℝ} (hε : 0 ≤ ε) (hc : 0 < Real.cos θ)
    (x : ℝ) : secondWall (verticalExtrusion U ε) θ x = secondWall U θ x + ε := by
  unfold secondWall
  rw [hU.support_verticalExtrusion hε (v := companionNormal θ) hc.le]
  simp only [companionNormal]
  field_simp [hc.ne'] <;> ring

theorem IsDownwardCap.cornerWall_verticalExtrusion {U : Set Plane}
    (hU : IsDownwardCap U) {ε θ : ℝ} (hε : 0 ≤ ε)
    (hs : 0 < Real.sin θ) (hc : 0 < Real.cos θ) (x : ℝ) :
    cornerWall (verticalExtrusion U ε) θ x = cornerWall U θ x + ε := by
  rw [cornerWall, hU.firstWall_verticalExtrusion hε hs,
    hU.secondWall_verticalExtrusion hε hc, min_add_add_right, cornerWall]

theorem IsDownwardCap.sweptNiche_verticalExtrusion_le {U : Set Plane}
    (hU : IsDownwardCap U) {ε α : ℝ} (hε : 0 ≤ ε)
    (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) (x : ℝ) :
    sweptNiche (verticalExtrusion U ε) α x ≤ sweptNiche U α x + ε := by
  apply sweptNiche_le_of_forall hα0 (add_nonneg (sweptNiche_nonneg U α x) hε)
  intro θ hθ
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1
    (by linarith [hθ.2, hα, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.trans_le hα⟩
  rw [hU.cornerWall_verticalExtrusion hε hs hc]
  exact add_le_add_left
    (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact hα x) hθ) ε

/-- The full terminal wall gains exactly `ε`; clipping the swept supremum at
zero gains at most `ε`. Both parts therefore satisfy the same upper bound. -/
theorem IsDownwardCap.partialBarrier_verticalExtrusion_le {U : Set Plane}
    (hU : IsDownwardCap U) {ε α : ℝ} (hε : 0 ≤ ε)
    (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) (x : ℝ) :
    partialBarrier (verticalExtrusion U ε) α x ≤ partialBarrier U α x + ε := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0
    (by linarith [hα, Real.pi_pos])
  apply max_le
  · exact (hU.sweptNiche_verticalExtrusion_le hε hα0 hα x).trans
      (add_le_add_left (le_max_left _ _) ε)
  · rw [hU.firstWall_verticalExtrusion hε hs]
    exact add_le_add_left (le_max_right _ _) ε

/-- Equal window lengths pay for the entire barrier increase, even when a
previously zero portion of the niche becomes positive. -/
theorem IsDownwardCap.capScore_le_verticalExtrusion {U : Set Plane}
    (hU : IsDownwardCap U) {ε α : ℝ} (hε : 0 ≤ ε)
    (hheight : ∀ p ∈ U, p.2 + ε ≤ 1)
    (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) :
    capScore U α ≤ capScore (verticalExtrusion U ε) α := by
  let l := horizontalLeft U
  let r := horizontalRight U
  let I := Icc l r
  let J := middleHalfInterval l r
  have hlr : l ≤ r := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hV := hU.isDownwardCap_verticalExtrusion hε hheight
  have hprojection := hU.horizontalProjection_verticalExtrusion hε
  have hleft : horizontalLeft (verticalExtrusion U ε) = l := congrArg sInf hprojection
  have hright : horizontalRight (verticalExtrusion U ε) = r := congrArg sSup hprojection
  have hconstI : IntegrableOn (fun _ : ℝ => ε) I :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hroof : IntegrableOn (capRoof U) (I \ J) :=
    (hU.integrableOn_capRoof_Icc l r).mono_set sdiff_subset
  have houter : (∫ x in I \ J, capRoof (verticalExtrusion U ε) x) =
      (∫ x in I \ J, capRoof U x) + (r - l) / 2 * ε := by
    calc
      (∫ x in I \ J, capRoof (verticalExtrusion U ε) x) =
          ∫ x in I \ J, capRoof U x + ε := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (measurableSet_Icc.diff
          (measurableSet_middleHalfInterval l r))] with x hx
        apply hU.capRoof_verticalExtrusion hε
        rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
        exact hx.1
      _ = (∫ x in I \ J, capRoof U x) + (r - l) / 2 * ε := by
        rw [integral_add hroof (hconstI.mono_set sdiff_subset), setIntegral_const]
        simp only [smul_eq_mul, I, J, volumeReal_exterior_middleHalfInterval hlr]
  have hbarrierU : IntegrableOn (partialBarrier U α) J :=
    (integrableOn_partialBarrier_Icc hU.isCompact hα0 hα l r).mono_set
      (middleHalfInterval_subset hlr)
  have hbarrierV : IntegrableOn (partialBarrier (verticalExtrusion U ε) α) J :=
    (integrableOn_partialBarrier_Icc hV.isCompact hα0 hα l r).mono_set
      (middleHalfInterval_subset hlr)
  have hmiddle : (∫ x in J, partialBarrier (verticalExtrusion U ε) α x) ≤
      (∫ x in J, partialBarrier U α x) + (r - l) / 2 * ε := by
    have h := integral_mono hbarrierV
      (hbarrierU.add (hconstI.mono_set (middleHalfInterval_subset hlr)))
      (fun x => hU.partialBarrier_verticalExtrusion_le hε hα0 hα x)
    simp only [Pi.add_apply] at h
    rw [integral_add hbarrierU
      (hconstI.mono_set (middleHalfInterval_subset hlr)), setIntegral_const] at h
    simpa only [smul_eq_mul, J, volumeReal_middleHalfInterval hlr] using h
  rw [capScore_eq_integrals, capScore_eq_integrals, hleft, hright]
  change (∫ x in I \ J, capRoof U x) - (∫ x in J, partialBarrier U α x) ≤
    (∫ x in I \ J, capRoof (verticalExtrusion U ε) x) -
      (∫ x in J, partialBarrier (verticalExtrusion U ε) α x)
  rw [houter]
  linarith

/-- Height is the actual attained upward support. -/
def capHeight (U : Set Plane) : ℝ := support U (0, 1)

theorem IsDownwardCap.capHeight_nonneg {U : Set Plane} (hU : IsDownwardCap U) :
    0 ≤ capHeight U := hU.support_upward_nonneg

theorem IsDownwardCap.capHeight_le_one {U : Set Plane} (hU : IsDownwardCap U) :
    capHeight U ≤ 1 := hU.support_upward_le_one

theorem IsDownwardCap.snd_le_capHeight {U : Set Plane} (hU : IsDownwardCap U)
    {p : Plane} (hp : p ∈ U) : p.2 ≤ capHeight U := by
  simpa only [capHeight, coordDot, mul_zero, mul_one, zero_add] using
    coordDot_le_support hU.isCompact hp ((0, 1) : Plane)

/-- The canonical height-one enlargement, defined without selecting a top point. -/
def heightSaturation (U : Set Plane) : Set Plane := verticalExtrusion U (1 - capHeight U)

theorem IsDownwardCap.isDownwardCap_heightSaturation {U : Set Plane}
    (hU : IsDownwardCap U) : IsDownwardCap (heightSaturation U) := by
  apply hU.isDownwardCap_verticalExtrusion (sub_nonneg.mpr hU.capHeight_le_one)
  intro p hp
  linarith [hU.snd_le_capHeight hp]

theorem IsDownwardCap.horizontalProjection_heightSaturation {U : Set Plane}
    (hU : IsDownwardCap U) :
    horizontalProjection (heightSaturation U) = horizontalProjection U :=
  hU.horizontalProjection_verticalExtrusion (sub_nonneg.mpr hU.capHeight_le_one)

theorem IsDownwardCap.capHeight_heightSaturation {U : Set Plane}
    (hU : IsDownwardCap U) : capHeight (heightSaturation U) = 1 := by
  rw [capHeight, heightSaturation,
    hU.support_verticalExtrusion (sub_nonneg.mpr hU.capHeight_le_one) (by norm_num)]
  unfold capHeight
  ring

theorem IsDownwardCap.exists_top_heightSaturation {U : Set Plane}
    (hU : IsDownwardCap U) : ∃ p ∈ heightSaturation U, p.2 = 1 := by
  have hV := hU.isDownwardCap_heightSaturation
  obtain ⟨p, hp, htop⟩ := exists_coordDot_eq_support hV.isCompact hV.nonempty (0, 1)
  refine ⟨p, hp, ?_⟩
  have heq := hU.capHeight_heightSaturation
  simpa only [coordDot, mul_zero, mul_one, zero_add] using htop.trans heq

theorem IsDownwardCap.capScore_le_heightSaturation {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) :
    capScore U α ≤ capScore (heightSaturation U) α := by
  apply hU.capScore_le_verticalExtrusion (sub_nonneg.mpr hU.capHeight_le_one)
    (fun p hp => by linarith [hU.snd_le_capHeight hp]) hα0 hα

end AmbidextrousSofa
