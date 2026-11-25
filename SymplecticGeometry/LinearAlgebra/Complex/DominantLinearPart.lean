/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.OperatorNorm
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.LinearAlgebra.Complex.Orientation
public import TauCeti.Geometry.Symplectic.CompatibleMetric
public import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.Orientation
public import TauCeti.Geometry.Symplectic.Plane
public import TauCeti.Geometry.Symplectic.Restrict
public import TauCeti.LinearAlgebra.Complex.LinearPart
public import TauCeti.LinearAlgebra.Orientation.Exact.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import SymplecticGeometry.Analysis.Normed.Operator.SpanSingleton
import SymplecticGeometry.LinearAlgebra.Complex.LinearPart

/-!
# Real-linear forms with dominant complex-linear part

Let `V` be a finite-dimensional real inner product space with a symplectic form `ω` and an almost
complex structure `J` whose metric `ω(·, J ·)` is the inner product. Let `A, B : V →L[ℝ] ℂ` be
real-linear forms, `A` complex linear and `B` complex antilinear for `J` and multiplication by
`i` on `ℂ`, with `‖B‖ < ‖A‖`. Then `F = A + B` is surjective, its kernel is a symplectic subspace,
and the orientation of the kernel induced by the symplectic orientation of `V` and the complex
orientation of `ℂ`, kernel first, is the symplectic orientation of the kernel.

This is the linear algebra behind the transversality and the orientation of the zero set of a
section whose antiholomorphic derivative is dominated by its holomorphic derivative.

## Main results

* `TauCeti.AlmostComplexStructure.norm_le_of_re_apply_eq_inner`: a real-linear form whose real
  and imaginary parts are `⟪a, ·⟫` and `⟪J a, ·⟫` has norm at most `‖a‖`.
* `TauCeti.SymplecticForm.exists_apply_eq_of_norm_lt`: there are vectors `x`, `y` with
  `ω x y > 0` and `F v = ω x v + i ω y v`.
* `TauCeti.SymplecticForm.ker_eq_orthogonal_span_pair`: the kernel of such a form is the
  symplectic complement of the span of `x` and `y`.
* `TauCeti.SymplecticForm.surjective_of_apply_eq`,
  `TauCeti.SymplecticForm.isSymplectic_ker_of_apply_eq` and
  `TauCeti.SymplecticForm.orientation_ker_eq_of_apply_eq`: the three results below for any form
  `F v = ω x v + i ω y v` with `ω x y ≠ 0` (with `0 < ω x y` for the orientation),
  on any real vector space `V` with a symplectic form (finite-dimensional for the last two),
  with no norm, inner product or `J`.
* `TauCeti.SymplecticForm.map_orientation_restrict_eq_complex_orientation`: on a symplectic plane
  containing `x` and `y`, such a form carries the symplectic orientation to that of `ℂ`.
* `TauCeti.SymplecticForm.surjective_of_norm_lt`: `F` is surjective.
* `TauCeti.SymplecticForm.isSymplectic_ker_of_norm_lt`: the kernel of `F` is symplectic.
* `TauCeti.SymplecticForm.orientation_ker_eq_of_norm_lt`: the kernel orientation
  (`Orientation.kerOfExact`) of the symplectic orientation of `V` and the orientation of `ℂ` is
  the symplectic orientation of the kernel.
* `TauCeti.SymplecticForm.surjective_of_norm_complexAntilinearPart_lt` and
  `TauCeti.SymplecticForm.isSymplectic_ker_of_norm_complexAntilinearPart_lt`: a real-linear map `F`
  to a complex normed space `W` of dimension one whose complex-antilinear part
  (`TauCeti.complexAntilinearPart`) has smaller norm than its complex-linear part
  (`TauCeti.complexLinearPart`) is surjective, with symplectic kernel. This is the form needed
  at a zero of a section of a Hermitian line bundle, where the derivative takes values in the fibre.

The proof is direct rather than by deforming `A + t B`: the Riesz vectors `a`, `b` of the real
parts of `A` and `B` give `x = -J (a + b)` and `y = a - b`, with `ω x y = ‖a‖ ^ 2 - ‖b‖ ^ 2`, and
`‖b‖ ≤ ‖B‖`, `‖A‖ ≤ ‖a‖` (the latter from Tau Ceti's
`TauCeti.AlmostComplexStructure.inner_sq_add_inner_sq_le`). The kernel is then the symplectic
complement of the plane spanned by `x` and `y`, on which `F` is orientation preserving.

For a map to a complex line `W`, a unit vector of `W` gives a complex-linear isometry `W ≃ ℂ`
(`LinearIsometryEquiv.toSpanSingleton`). Composing with it keeps the norms of both parts
(`TauCeti.IsComplexLinear.complexLinearPart_comp`,
`TauCeti.IsComplexLinear.complexAntilinearPart_comp`), the kernel and surjectivity, so the case of
`ℂ` applies.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.4.
* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
-/

public section

noncomputable section

open Module Complex

open scoped InnerProductSpace

namespace TauCeti

namespace SymplecticForm

section ApplyEq

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ω : SymplecticForm V}

/-- If a real-linear form `F : V → ℂ` reads `F v = ω x v + i ω y v`, its kernel is the symplectic
complement of the span of `x` and `y`. -/
theorem ker_eq_orthogonal_span_pair {F : V →ₗ[ℝ] ℂ} {x y : V}
    (hF : ∀ v, F v = ⟨ω x v, ω y v⟩) :
    LinearMap.ker F = ω.orthogonal (Submodule.span ℝ {x, y}) := by
  ext v
  rw [mem_orthogonal_span_iff]
  simp [hF, Complex.ext_iff]

/-- A real-linear form `F : V → ℂ` that reads `F v = ω x v + i ω y v`, with `ω x y ≠ 0`, is
surjective. -/
theorem surjective_of_apply_eq {F : V →ₗ[ℝ] ℂ} {x y : V} (hF : ∀ v, F v = ⟨ω x v, ω y v⟩)
    (hxy : ω x y ≠ 0) : Function.Surjective F := by
  intro z
  refine ⟨(z.re / ω x y) • y - (z.im / ω x y) • x, ?_⟩
  rw [map_sub, map_smul, map_smul, hF, hF, Complex.ext_iff]
  have hyx : ω y x = -ω x y := (ω.neg_eq x y).symm
  simp only [self_eq_zero, hyx, Complex.sub_re, Complex.smul_re, Complex.sub_im, Complex.smul_im,
    smul_eq_mul]
  constructor <;> field_simp <;> ring

variable [FiniteDimensional ℝ V]

/-- The kernel of a real-linear form `F : V → ℂ` that reads `F v = ω x v + i ω y v`, with
`ω x y ≠ 0`, is a symplectic subspace. -/
theorem isSymplectic_ker_of_apply_eq {F : V →ₗ[ℝ] ℂ} {x y : V} (hF : ∀ v, F v = ⟨ω x v, ω y v⟩)
    (hxy : ω x y ≠ 0) : ω.IsSymplectic (LinearMap.ker F) := by
  rw [ker_eq_orthogonal_span_pair hF, isSymplectic_orthogonal_iff]
  exact isSymplectic_iff_disjoint.2 (ω.disjoint_span_pair_orthogonal hxy)

/-- Let `N` be a symplectic plane containing `x` and `y`, with `0 < ω x y`, and let
`e : N ≃ ℂ` be the real-linear isomorphism `e v = ω x v + i ω y v`. Then `e` carries the
symplectic orientation of `N` to the orientation of `ℂ`. -/
theorem map_orientation_restrict_eq_complex_orientation {x y : V} (hxy : 0 < ω x y)
    {N : Submodule ℝ V} (hNs : ω.IsSymplectic N) (hN2 : finrank ℝ N = 2) (hx : x ∈ N)
    (hy : y ∈ N) (e : N ≃ₗ[ℝ] ℂ) (he : ∀ v : N, e v = ⟨ω x v, ω y v⟩) :
    Orientation.map (Fin 2) e ((ω.restrict N hNs.nondegenerate_restrict).orientation hN2) =
      Complex.orientation := by
  have hc0 : ω x y ≠ 0 := hxy.ne'
  have hyx : ω y x = -ω x y := (ω.neg_eq x y).symm
  have h1 : e.symm 1 = ⟨(ω x y)⁻¹ • y, N.smul_mem _ hy⟩ := by
    rw [LinearEquiv.symm_apply_eq, he, Complex.ext_iff]
    simp [hc0]
  have hI : e.symm I = ⟨-(ω x y)⁻¹ • x, N.smul_mem _ hx⟩ := by
    rw [LinearEquiv.symm_apply_eq, he, Complex.ext_iff]
    simp [hc0, hyx]
  have hb : (Complex.basisOneI.map e.symm).orientation =
      (ω.restrict N hNs.nondegenerate_restrict).orientation hN2 := by
    rw [basis_orientation_eq_orientation_iff]
    simp only [Basis.map_apply, Complex.coe_basisOneI, Matrix.cons_val_zero,
      Matrix.cons_val_one, h1, hI, restrict_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    have hyx' : ω.toBilinForm y x = -ω.toBilinForm x y := hyx
    have hxy' : 0 < ω.toBilinForm x y := hxy
    rw [hyx']
    have : 0 < (ω.toBilinForm x y)⁻¹ := inv_pos.2 hxy'
    nlinarith [mul_pos this (mul_pos this hxy')]
  rw [← hb, ← Basis.orientation_map]
  congr 1
  ext i
  simp

/-- Let `F : V → ℂ` be a real-linear form that reads `F v = ω x v + i ω y v`, with `0 < ω x y`.
The kernel `K` of `F` is symplectic (`isSymplectic_ker_of_apply_eq`), and the orientation of `K`
induced by the symplectic orientation of `V` and the orientation of `ℂ` through
`0 → K → V → ℂ → 0` (`Orientation.kerOfExact`, kernel first) is the symplectic orientation
of `K`. -/
theorem orientation_ker_eq_of_apply_eq {F : V →ₗ[ℝ] ℂ} {x y : V}
    (hF : ∀ v, F v = ⟨ω x v, ω y v⟩) (hxy : 0 < ω x y) {m : ℕ} (hV : finrank ℝ V = m + 2)
    (hm : finrank ℝ (LinearMap.ker F) = m) :
    Orientation.kerOfExact (LinearMap.ker F).injective_subtype
        (LinearMap.exact_subtype_ker_map _) (surjective_of_apply_eq hF hxy.ne')
        (ω.orientation hV) Complex.orientation hm Complex.finrank_real_complex =
      (ω.restrict _ (isSymplectic_ker_of_apply_eq hF hxy.ne').nondegenerate_restrict).orientation
        hm := by
  have hsurj := surjective_of_apply_eq hF hxy.ne'
  set K := LinearMap.ker F with hK
  have hKs : ω.IsSymplectic K := isSymplectic_ker_of_apply_eq hF hxy.ne'
  have hN : ω.orthogonal K = Submodule.span ℝ {x, y} := by
    rw [hK, ker_eq_orthogonal_span_pair hF, orthogonal_orthogonal]
  set N := ω.orthogonal K
  have hc : IsCompl K N := hKs.isCompl
  have hNs : ω.IsSymplectic N := isSymplectic_orthogonal_iff.2 hKs
  have hN2 : finrank ℝ N = 2 := by
    have := Submodule.finrank_add_eq_of_isCompl hc
    omega
  -- `F` restricts to an isomorphism from `N` onto `ℂ`.
  set eC : N ≃ₗ[ℝ] ℂ := LinearEquiv.ofBijective (F.domRestrict N)
    ⟨LinearMap.injective_domRestrict_iff.2 hc.disjoint.symm,
      (LinearMap.surjective_domRestrict_iff hsurj).2 hc.symm.codisjoint⟩
  have heC (v : N) : eC v = F v := by
    exact (LinearEquiv.ofBijective_apply _ v).trans (F.domRestrict_apply N v)
  have hmapC := map_orientation_restrict_eq_complex_orientation hxy hNs hN2
    (hN ▸ Submodule.subset_span (by simp)) (hN ▸ Submodule.subset_span (by simp)) eC
    (fun v ↦ (heC v).trans (hF v))
  set G := Submodule.prodEquivOfIsCompl K N hc
  have key := Orientation.map_ofExact LinearMap.inl_injective Function.Exact.inl_snd
    LinearMap.snd_surjective K.injective_subtype (LinearMap.exact_subtype_ker_map F)
    hsurj (LinearEquiv.refl ℝ K) G eC
    (fun v ↦ by simp [G]) (fun z ↦ by
      obtain ⟨⟨k, hk⟩, n⟩ := z
      simp [G, heC, LinearMap.mem_ker.1 hk])
    ((ω.restrict K hKs.nondegenerate_restrict).orientation hm)
    ((ω.restrict N hNs.nondegenerate_restrict).orientation hN2) hm hN2
  rw [Orientation.ofExact_inl_snd, Orientation.map_refl, Equiv.refl_apply, hmapC] at key
  rw [Orientation.kerOfExact_eq_iff, ← key, ← orientation_prod _ _ hm hN2 (by simp [hm, hN2])]
  -- The two sides differ only in the proofs that `ω` restricts nondegenerately to `K` and `N`.
  exact ((ω.isSymplectomorphism_prodEquivOfIsCompl hc).map_orientation _).trans rfl

end ApplyEq

end SymplecticForm

section NormLt

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {A B : V →L[ℝ] ℂ}

/-- A real-linear form `A : V → ℂ` whose real and imaginary parts are `⟪a, ·⟫` and `⟪J a, ·⟫`,
for an orthogonal almost complex structure `J`, has norm at most `‖a‖`. -/
theorem AlmostComplexStructure.norm_le_of_re_apply_eq_inner
    (hJ : ∀ v w, ⟪J v, J w⟫_ℝ = ⟪v, w⟫_ℝ) {a : V}
    (ha : ∀ v, (A v).re = ⟪a, v⟫_ℝ) (him : ∀ v, (A v).im = ⟪J a, v⟫_ℝ) : ‖A‖ ≤ ‖a‖ := by
  refine A.opNorm_le_bound (norm_nonneg _) fun v ↦ ?_
  have h := inner_sq_add_inner_sq_le hJ v a
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [Complex.sq_norm, Complex.normSq_apply, ha, him, real_inner_comm v a, real_inner_comm v (J a),
    mul_pow, ← sq, ← sq]
  linarith

namespace SymplecticForm

/-- **Real-linear forms with dominant complex-linear part, in symplectic terms.** Let the inner
product of `V` be the metric `ω(·, J ·)`, and let `A, B : V →L[ℝ] ℂ` be complex linear and complex
antilinear respectively, with `‖B‖ < ‖A‖`. Then there are `x y : V` with `0 < ω x y` such that
`(A + B) v = ω x v + i ω y v` for every `v`. -/
theorem exists_apply_eq_of_norm_lt [CompleteSpace V] (hg : ∀ v w, ω v (J w) = ⟪v, w⟫_ℝ)
    (hA : IsComplexLinear J.toLinearMap (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
      (A : V →ₗ[ℝ] ℂ))
    (hB : IsComplexAntilinear J.toLinearMap
      (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap (B : V →ₗ[ℝ] ℂ))
    (h : ‖B‖ < ‖A‖) :
    ∃ x y : V, 0 < ω x y ∧ ∀ v, (A + B) v = ⟨ω x v, ω y v⟩ := by
  set a := (InnerProductSpace.toDual ℝ V).symm (reCLM.comp A)
  set b := (InnerProductSpace.toDual ℝ V).symm (reCLM.comp B)
  have hare (v : V) : (A v).re = ⟪a, v⟫_ℝ := by simp [a]
  have hbre (v : V) : (B v).re = ⟪b, v⟫_ℝ := by simp [b]
  have hJ (u v : V) : ⟪J u, v⟫_ℝ = -⟪u, J v⟫_ℝ :=
    inner_apply_left_eq_neg_of_apply_apply_eq_inner hg u v
  have hω (u v : V) : ω u v = ⟪J u, v⟫_ℝ :=
    (inner_apply_left_eq_of_apply_apply_eq_inner hg u v).symm
  have haim (v : V) : (A v).im = ⟪J a, v⟫_ℝ := by
    have h1 := hA.apply v
    simp only [ContinuousLinearMap.coe_coe, AlmostComplexStructure.ofComplexModule_apply] at h1
    rw [hJ, ← hare, h1]
    simp
  have hbim (v : V) : (B v).im = -⟪J b, v⟫_ℝ := by
    have h1 := hB.apply v
    simp only [ContinuousLinearMap.coe_coe, AlmostComplexStructure.ofComplexModule_apply] at h1
    rw [hJ, neg_neg, ← hbre, h1]
    simp
  have hb : ‖b‖ ≤ ‖B‖ := by
    rw [LinearIsometryEquiv.norm_map]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by rw [Complex.reCLM_norm, one_mul])
  have hJJ (u v : V) : ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ := by
    have h := (ω.invariant_of_apply_apply_eq_inner hg).associatedBilinForm_invariant u v
    simpa only [associatedBilinForm_apply, hg] using h
  have ha : ‖A‖ ≤ ‖a‖ := AlmostComplexStructure.norm_le_of_re_apply_eq_inner hJJ hare haim
  refine ⟨-J (a + b), a - b, ?_, fun v ↦ ?_⟩
  · rw [hω, map_neg, J.apply_apply, neg_neg]
    simp only [inner_add_left, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm a b]
    nlinarith [norm_nonneg b]
  · apply Complex.ext
    · simp [hω, J.apply_apply, hare, hbre, add_comm]
    · simp [hω, haim, hbim, sub_eq_add_neg]

variable [FiniteDimensional ℝ V]

/-- **A real-linear form with dominant complex-linear part is surjective.** Let the inner product
of `V` be the metric `ω(·, J ·)`, and let `A, B : V →L[ℝ] ℂ` be complex linear and complex
antilinear respectively, with `‖B‖ < ‖A‖`. Then `A + B` is surjective. -/
theorem surjective_of_norm_lt (hg : ∀ v w, ω v (J w) = ⟪v, w⟫_ℝ)
    (hA : IsComplexLinear J.toLinearMap (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
      (A : V →ₗ[ℝ] ℂ))
    (hB : IsComplexAntilinear J.toLinearMap
      (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap (B : V →ₗ[ℝ] ℂ))
    (h : ‖B‖ < ‖A‖) : Function.Surjective (A + B) := by
  obtain ⟨x, y, hxy, hF⟩ := exists_apply_eq_of_norm_lt hg hA hB h
  exact surjective_of_apply_eq (F := ((A + B : V →L[ℝ] ℂ) : V →ₗ[ℝ] ℂ)) hF hxy.ne'

/-- **The kernel of a real-linear form with dominant complex-linear part is symplectic.** Let the
inner product of `V` be the metric `ω(·, J ·)`, and let `A, B : V →L[ℝ] ℂ` be complex linear and
complex antilinear respectively, with `‖B‖ < ‖A‖`. Then the kernel of `A + B` is a symplectic
subspace. -/
theorem isSymplectic_ker_of_norm_lt (hg : ∀ v w, ω v (J w) = ⟪v, w⟫_ℝ)
    (hA : IsComplexLinear J.toLinearMap (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
      (A : V →ₗ[ℝ] ℂ))
    (hB : IsComplexAntilinear J.toLinearMap
      (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap (B : V →ₗ[ℝ] ℂ))
    (h : ‖B‖ < ‖A‖) : ω.IsSymplectic (LinearMap.ker ((A + B : V →L[ℝ] ℂ) : V →ₗ[ℝ] ℂ)) := by
  obtain ⟨x, y, hxy, hF⟩ := exists_apply_eq_of_norm_lt hg hA hB h
  exact isSymplectic_ker_of_apply_eq hF hxy.ne'

/-- **The orientation of the kernel of a real-linear form with dominant complex-linear part.** Let
the inner product of `V` be the metric `ω(·, J ·)`, and let `A, B : V →L[ℝ] ℂ` be complex linear and
complex antilinear respectively, with `‖B‖ < ‖A‖`. The kernel `K` of `A + B` is symplectic
(`isSymplectic_ker_of_norm_lt`), and the orientation of `K` induced by the symplectic orientation
of `V` and the orientation of `ℂ` through `0 → K → V → ℂ → 0` (`Orientation.kerOfExact`, kernel
first) is the symplectic orientation of `K`. -/
theorem orientation_ker_eq_of_norm_lt (hg : ∀ v w, ω v (J w) = ⟪v, w⟫_ℝ)
    (hA : IsComplexLinear J.toLinearMap (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
      (A : V →ₗ[ℝ] ℂ))
    (hB : IsComplexAntilinear J.toLinearMap
      (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap (B : V →ₗ[ℝ] ℂ))
    (h : ‖B‖ < ‖A‖) {m : ℕ} (hV : finrank ℝ V = m + 2)
    (hm : finrank ℝ (LinearMap.ker ((A + B : V →L[ℝ] ℂ) : V →ₗ[ℝ] ℂ)) = m) :
    Orientation.kerOfExact (LinearMap.ker ((A + B : V →L[ℝ] ℂ) : V →ₗ[ℝ] ℂ)).injective_subtype
        (LinearMap.exact_subtype_ker_map _) (surjective_of_norm_lt hg hA hB h)
        (ω.orientation hV) Complex.orientation hm Complex.finrank_real_complex =
      (ω.restrict _ (isSymplectic_ker_of_norm_lt hg hA hB h).nondegenerate_restrict).orientation
        hm := by
  obtain ⟨x, y, hxy, hF⟩ := exists_apply_eq_of_norm_lt hg hA hB h
  exact orientation_ker_eq_of_apply_eq hF hxy hV hm

end SymplecticForm

end NormLt

section Line

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace ℂ W] [IsScalarTower ℝ ℂ W]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- If `F : V → W` has complex-antilinear part of smaller norm than its complex-linear part, there
is a real-linear isometry `ψ : W → ℂ` such that `ψ ∘ F` has the same property. -/
private theorem exists_norm_complexAntilinearPart_comp_lt (hW : finrank ℂ W = 1)
    {F : V →L[ℝ] W}
    (h : ‖LinearMap.toContinuousLinearMap (complexAntilinearPart J.toLinearMap
        (AlmostComplexStructure.ofComplexModule W).toLinearMap (F : V →ₗ[ℝ] W))‖ <
      ‖LinearMap.toContinuousLinearMap (complexLinearPart J.toLinearMap
        (AlmostComplexStructure.ofComplexModule W).toLinearMap (F : V →ₗ[ℝ] W))‖) :
    ∃ ψ : W →ₗᵢ[ℝ] ℂ,
      ‖LinearMap.toContinuousLinearMap (complexAntilinearPart J.toLinearMap
        (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
        (ψ.toLinearMap ∘ₗ (F : V →ₗ[ℝ] W)))‖ <
      ‖LinearMap.toContinuousLinearMap (complexLinearPart J.toLinearMap
        (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
        (ψ.toLinearMap ∘ₗ (F : V →ₗ[ℝ] W)))‖ := by
  have : Nontrivial W := Module.nontrivial_of_finrank_eq_succ hW
  obtain ⟨u, hu⟩ := exists_norm_eq W zero_le_one
  set φ := (LinearIsometryEquiv.toSpanSingleton ℂ W hW hu).symm
  set ψ : W →ₗᵢ[ℝ] ℂ := ⟨(φ : W →ₗ[ℂ] ℂ).restrictScalars ℝ, φ.norm_map⟩
  have hψ : IsComplexLinear (AlmostComplexStructure.ofComplexModule W).toLinearMap
      (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap ψ.toLinearMap :=
    isComplexLinear_of_apply fun w ↦ by
      simp [ψ, AlmostComplexStructure.ofComplexModule_apply]
  refine ⟨ψ, ?_⟩
  have key (P : V →ₗ[ℝ] W) : LinearMap.toContinuousLinearMap (ψ.toLinearMap ∘ₗ P) =
      ψ.toContinuousLinearMap.comp (LinearMap.toContinuousLinearMap P) := by
    ext v
    simp
  rw [hψ.complexLinearPart_comp, hψ.complexAntilinearPart_comp, key, key,
    ψ.norm_toContinuousLinearMap_comp, ψ.norm_toContinuousLinearMap_comp]
  exact h

/-- **A real-linear map to a complex line with dominant complex-linear part is surjective.**
Let the inner product of `V` be the metric `ω(·, J ·)`, let `W` be a complex normed space of
dimension one, and let `F : V →L[ℝ] W` be a real-linear map whose complex-antilinear part, for `J`
and multiplication by `i` on `W`, has smaller operator norm than its complex-linear part. Then `F`
is surjective. -/
theorem SymplecticForm.surjective_of_norm_complexAntilinearPart_lt
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫_ℝ) (hW : finrank ℂ W = 1) {F : V →L[ℝ] W}
    (h : ‖LinearMap.toContinuousLinearMap (complexAntilinearPart J.toLinearMap
        (AlmostComplexStructure.ofComplexModule W).toLinearMap (F : V →ₗ[ℝ] W))‖ <
      ‖LinearMap.toContinuousLinearMap (complexLinearPart J.toLinearMap
        (AlmostComplexStructure.ofComplexModule W).toLinearMap (F : V →ₗ[ℝ] W))‖) :
    Function.Surjective F := by
  obtain ⟨ψ, hψ⟩ := exists_norm_complexAntilinearPart_comp_lt hW h
  have hs := surjective_of_norm_lt hg
    (isComplexLinear_complexLinearPart J.square_neg
      (AlmostComplexStructure.ofComplexModule ℂ).square_neg _)
    (isComplexAntilinear_complexAntilinearPart J.square_neg
      (AlmostComplexStructure.ofComplexModule ℂ).square_neg _) hψ
  rw [← map_add, complexLinearPart_add_complexAntilinearPart,
    LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp] at hs
  exact hs.of_comp_left ψ.injective

/-- **The kernel of a real-linear map to a complex line with dominant complex-linear part is
symplectic.** Let the inner product of `V` be the metric `ω(·, J ·)`, let `W` be a complex normed
space of dimension one, and let `F : V →L[ℝ] W` be a real-linear map whose complex-antilinear part,
for `J` and multiplication by `i` on `W`, has smaller operator norm than its complex-linear part.
Then the kernel of `F` is a symplectic subspace. -/
theorem SymplecticForm.isSymplectic_ker_of_norm_complexAntilinearPart_lt
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫_ℝ) (hW : finrank ℂ W = 1) {F : V →L[ℝ] W}
    (h : ‖LinearMap.toContinuousLinearMap (complexAntilinearPart J.toLinearMap
        (AlmostComplexStructure.ofComplexModule W).toLinearMap (F : V →ₗ[ℝ] W))‖ <
      ‖LinearMap.toContinuousLinearMap (complexLinearPart J.toLinearMap
        (AlmostComplexStructure.ofComplexModule W).toLinearMap (F : V →ₗ[ℝ] W))‖) :
    ω.IsSymplectic (LinearMap.ker (F : V →ₗ[ℝ] W)) := by
  obtain ⟨ψ, hψ⟩ := exists_norm_complexAntilinearPart_comp_lt hW h
  have hk := isSymplectic_ker_of_norm_lt hg
    (isComplexLinear_complexLinearPart J.square_neg
      (AlmostComplexStructure.ofComplexModule ℂ).square_neg _)
    (isComplexAntilinear_complexAntilinearPart J.square_neg
      (AlmostComplexStructure.ofComplexModule ℂ).square_neg _) hψ
  rwa [ContinuousLinearMap.toLinearMap_add, LinearMap.coe_toContinuousLinearMap,
    LinearMap.coe_toContinuousLinearMap, complexLinearPart_add_complexAntilinearPart,
    LinearMap.ker_comp_of_ker_eq_bot _
      (LinearMap.ker_eq_bot.2 ψ.injective)] at hk

end Line

end TauCeti
