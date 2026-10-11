module

public import AmbidextrousSofa.Geometry.CapGeometry

@[expose] public section

/-!
# Support functions of actual planar sets

The support is defined directly from the coordinate dot product and a real
supremum. Compactness supplies boundedness and attainment; none of those facts
is stored as an extra certificate. Convex-hull invariance is proved from the
minimality of the actual convex hull. Upward support is preserved by downward
filling, which is the support identity needed by the scalar cap reduction.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

/-- Euclidean coordinate pairing, independent of the product norm. -/
def coordDot (p v : Plane) : ℝ := p.1 * v.1 + p.2 * v.2

theorem coordDot_add_left (p q v : Plane) : coordDot (p + q) v = coordDot p v + coordDot q v := by
  simp only [coordDot, Prod.fst_add, Prod.snd_add]; ring

theorem coordDot_smul_left (a : ℝ) (p v : Plane) : coordDot (a • p) v = a * coordDot p v := by
  simp only [coordDot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem coordDot_smul_right (a : ℝ) (p v : Plane) : coordDot p (a • v) = a * coordDot p v := by
  simp only [coordDot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem continuous_coordDot_right (v : Plane) : Continuous (fun p => coordDot p v) := by
  unfold coordDot; fun_prop

theorem continuous_coordDot_left (p : Plane) : Continuous (coordDot p) := by
  unfold coordDot; fun_prop

/-- Support in an arbitrary vector direction; meaningful on every compact nonempty set. -/
def support (K : Set Plane) (v : Plane) : ℝ := sSup ((fun p => coordDot p v) '' K)

def unitNormal (θ : ℝ) : Plane := (Real.cos θ, Real.sin θ)

/-- The angular support convention used throughout the manuscript. -/
def angleSupport (K : Set Plane) (θ : ℝ) : ℝ := support K (unitNormal θ)

theorem support_bddAbove {K : Set Plane} (hK : IsCompact K) (v : Plane) :
    BddAbove ((fun p => coordDot p v) '' K) :=
  hK.bddAbove_image (continuous_coordDot_right v).continuousOn

theorem coordDot_le_support {K : Set Plane} (hK : IsCompact K) {p : Plane}
    (hp : p ∈ K) (v : Plane) : coordDot p v ≤ support K v :=
  le_csSup (support_bddAbove hK v) (mem_image_of_mem _ hp)

/-- Every support maximum of a nonempty compact set is attained by an actual point. -/
theorem exists_coordDot_eq_support {K : Set Plane} (hK : IsCompact K)
    (hne : K.Nonempty) (v : Plane) : ∃ p ∈ K, coordDot p v = support K v :=
  (hK.image (continuous_coordDot_right v)).sSup_mem (hne.image _)

theorem support_le_of_forall {K : Set Plane} (hne : K.Nonempty) {v : Plane} {c : ℝ}
    (h : ∀ p ∈ K, coordDot p v ≤ c) : support K v ≤ c :=
  csSup_le (hne.image _) (forall_mem_image.2 h)

theorem support_mono {K L : Set Plane} (hKL : K ⊆ L) (hne : K.Nonempty)
    (hL : IsCompact L) (v : Plane) : support K v ≤ support L v :=
  csSup_le_csSup (support_bddAbove hL v) (hne.image _) (image_mono hKL)

theorem support_eq_of_mem {K : Set Plane} (hK : IsCompact K) {v : Plane} {c : ℝ}
    (hle : ∀ p ∈ K, coordDot p v ≤ c) {q : Plane} (hq : q ∈ K)
    (hqc : coordDot q v = c) : support K v = c :=
  (support_le_of_forall ⟨q, hq⟩ hle).antisymm (hqc ▸ coordDot_le_support hK hq v)

theorem continuous_support {K : Set Plane} (hK : IsCompact K) : Continuous (support K) :=
  hK.continuous_sSup (f := fun v p => coordDot p v) (by unfold coordDot; fun_prop)

theorem continuous_unitNormal : Continuous unitNormal := by unfold unitNormal; fun_prop

theorem continuous_angleSupport {K : Set Plane} (hK : IsCompact K) : Continuous (angleSupport K) :=
  (continuous_support hK).comp continuous_unitNormal

theorem convex_coordDot_halfspace (v : Plane) (c : ℝ) :
    Convex ℝ {p : Plane | coordDot p v ≤ c} :=
  convex_halfSpace_le ⟨fun p q => coordDot_add_left p q v, fun a p => coordDot_smul_left a p v⟩ c

/-- Actual convexification preserves every support value. -/
theorem support_actualHull {S : Set Plane} (hS : IsCompact S) (hne : S.Nonempty)
    (v : Plane) : support (actualHull S) v = support S v := by
  have hbound : ∀ p ∈ actualHull S, coordDot p v ≤ support S v :=
    convexHull_min (fun p hp => coordDot_le_support hS hp v) (convex_coordDot_halfspace v _)
  obtain ⟨p, hp, hpeq⟩ := exists_coordDot_eq_support hS hne v
  exact (support_le_of_forall (actualHull_nonempty hne) hbound).antisymm (hpeq ▸
    le_csSup ⟨_, forall_mem_image.2 hbound⟩ (mem_image_of_mem _ (subset_actualHull S hp)))

/-- Every actual compact convex body is the intersection of its supporting halfspaces. -/
theorem mem_iff_forall_coordDot_le_support {K : Set Plane} (hK : IsCompact K)
    (hne : K.Nonempty) (hconvex : Convex ℝ K) (p : Plane) :
    p ∈ K ↔ ∀ v : Plane, coordDot p v ≤ support K v := by
  refine ⟨fun hp v => coordDot_le_support hK hp v, fun hp => ?_⟩
  by_contra hpnot
  obtain ⟨f, u, hfK, hfp⟩ := geometric_hahn_banach_closed_point hconvex hK.isClosed hpnot
  let n : Plane := (f (1, 0), f (0, 1))
  have hf (x : Plane) : f x = coordDot x n := by
    have hx : x = x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    conv_lhs => rw [hx]
    rw [map_add, map_smul, map_smul]
    simp only [coordDot, n, smul_eq_mul]
  obtain ⟨q, hq, hqmax⟩ := exists_coordDot_eq_support hK hne n
  linarith [hfK q hq, hp n, hf p, hf q]

/-- Equality of support data determines the compact convex sets, including their boundaries. -/
theorem eq_of_support_eq {K L : Set Plane} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKconvex : Convex ℝ K) (hL : IsCompact L) (hLne : L.Nonempty)
    (hLconvex : Convex ℝ L) (hsupport : ∀ v : Plane, support K v = support L v) :
    K = L := by
  ext p
  simp only [mem_iff_forall_coordDot_le_support hK hKne hKconvex,
    mem_iff_forall_coordDot_le_support hL hLne hLconvex, hsupport]

/-- Raising a point to an available roof point cannot lower an upward support. -/
theorem support_upperCap {K : Set Plane} (hK : IsCompact K) (hne : K.Nonempty)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) {v : Plane} (hv : 0 ≤ v.2) :
    support (upperCap K) v = support K v := by
  refine le_antisymm (support_le_of_forall (hne.mono (subset_upperCap hK0)) ?_)
    (support_mono (subset_upperCap hK0) hne (isCompact_upperCap hK hK0) v)
  rintro p ⟨-, y, hpy, hy⟩
  exact (show coordDot p v ≤ coordDot (p.1, y) v from
    add_le_add_right (mul_le_mul_of_nonneg_right hpy hv) _).trans (coordDot_le_support hK hy v)

theorem angleSupport_upperCap {K : Set Plane} (hK : IsCompact K) (hne : K.Nonempty)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) {θ : ℝ} (hθ : 0 ≤ Real.sin θ) :
    angleSupport (upperCap K) θ = angleSupport K θ :=
  support_upperCap hK hne hK0 hθ

/-- Translation is recorded in the support as the exact linear correction. -/
theorem support_translate {K : Set Plane} (hK : IsCompact K) (hne : K.Nonempty)
    (a v : Plane) : support ((fun p => p + a) '' K) v = support K v + coordDot a v := by
  obtain ⟨p, hp, hpv⟩ := exists_coordDot_eq_support hK hne v
  refine support_eq_of_mem (hK.image (by fun_prop)) ?_ (mem_image_of_mem _ hp)
    (by rw [coordDot_add_left, hpv])
  rintro _ ⟨q, hq, rfl⟩
  rw [coordDot_add_left]
  exact add_le_add_left (coordDot_le_support hK hq v) _

theorem support_smul_direction {K : Set Plane} (hK : IsCompact K) (hne : K.Nonempty)
    (v : Plane) {a : ℝ} (ha : 0 ≤ a) : support K (a • v) = a * support K v := by
  obtain ⟨p, hp, hpv⟩ := exists_coordDot_eq_support hK hne v
  refine support_eq_of_mem hK (fun q hq => ?_) hp (by rw [coordDot_smul_right, hpv])
  rw [coordDot_smul_right]
  exact mul_le_mul_of_nonneg_left (coordDot_le_support hK hq v) ha

theorem coordDot_rotate (θ : ℝ) (p v : Plane) :
    coordDot (rotate θ p) v = coordDot p (rotate (-θ) v) := by
  simp only [coordDot, rotate, Real.cos_neg, Real.sin_neg]; ring

theorem rotate_unitNormal (θ φ : ℝ) : rotate θ (unitNormal φ) = unitNormal (θ + φ) := by
  simp only [rotate, unitNormal, Real.cos_add, Real.sin_add]

/-- A support face consists of actual points attaining the support maximum. -/
def supportFace (K : Set Plane) (v : Plane) : Set Plane := K ∩ {p | coordDot p v = support K v}

theorem support_horizontal_right (K : Set Plane) : support K (1, 0) = horizontalRight K := by
  simp only [support, coordDot, mul_one, mul_zero, add_zero, horizontalRight, horizontalProjection]

theorem support_horizontal_left {K : Set Plane} (hK : IsCompact K) (hne : K.Nonempty) :
    support K (-1, 0) = -horizontalLeft K := by
  obtain ⟨p, hp, hpLeft⟩ := horizontalLeft_mem hne hK
  refine support_eq_of_mem hK (fun q hq => ?_) hp
    (by simp only [coordDot, mul_neg, mul_one, mul_zero, add_zero, hpLeft])
  simp only [coordDot, mul_neg, mul_one, mul_zero, add_zero, neg_le_neg_iff]
  exact csInf_le (isCompact_horizontalProjection hK).bddBelow (mem_image_of_mem Prod.fst hq)

theorem IsDownwardCap.support_upward_le_one {U : Set Plane} (hU : IsDownwardCap U) :
    support U (0, 1) ≤ 1 :=
  support_le_of_forall hU.nonempty fun p hp => by
    simpa only [coordDot, mul_zero, zero_add, mul_one] using (hU.inStrip hp).2

end AmbidextrousSofa
