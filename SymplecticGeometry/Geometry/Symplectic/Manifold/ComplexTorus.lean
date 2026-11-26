/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.Quotient
public import TauCeti.Geometry.Symplectic.Manifold.Torus.Basic
import SymplecticGeometry.Algebra.Module.ZLattice.Complex
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Complex tori as standard symplectic tori

Let `Λ` be a lattice in `ℂ` (a discrete `ℤ`-submodule that spans `ℂ` over `ℝ`) and let
`p : Unit ⊕ Unit → ℝ` be positive periods. Give `ℂ ⧸ Λ` the manifold structure of Tau Ceti's
`TauCeti.Geometry.Manifold.Algebra.Quotient`, the structure in which
`WeierstrassCurve.exists_continuousAddEquiv_periodLattice_contMDiff` identifies a complex
elliptic curve with `ℂ ⧸ Λ`. This file identifies `ℂ ⧸ Λ` with Tau Ceti's standard torus
`T = ∀ i, AddCircle (p i)` and computes the pull-back of its symplectic form.

Fix a `ℤ`-basis `b₀, b₁` of `Λ`. The real-linear automorphism `A = latticeTorusEquiv p b` of `ℂ`
maps `b₀ ↦ p inl` and `b₁ ↦ I * p inr`, hence `Λ` onto `p inl ℤ + I p inr ℤ`, which is the set of
periods of Tau Ceti's covering map `TauCeti.complexPiTorusCover p`. So the composite
`latticeTorusCover p b` of `A` and that covering map is an onto additive map with kernel `Λ`, and
a local diffeomorphism. It therefore induces a diffeomorphism
`latticeTorusDiffeomorph p b` from `ℂ ⧸ Λ` onto `T`.

The covering map pulls `TauCeti.torusSymplecticForm p` back to
`ω₀ = TauCeti.stdComplexSymplecticForm`
(`TauCeti.mpullback_complexPiTorusCover_torusSymplecticForm`), and `A` scales the alternating
form `ω₀` by `det A` (Tau Ceti's `LinearMap.IsAlt.compl₁₂_self_eq_det_smul`). Hence
`latticeTorusCover p b` pulls the torus form back to `det A • ω₀`, where
`det A = p inl * p inr / Im (conj b₀ * b₁)`. The factor is positive for a positively oriented
basis, and such a basis always exists
(`ZLattice.exists_basis_zero_lt_im_conj_mul`).

## Main definitions

* `SymplecticGeometry.latticeTorusEquiv p b`: the real-linear automorphism of `ℂ` with
  `b₀ ↦ p inl` and `b₁ ↦ I * p inr`.
* `SymplecticGeometry.latticeTorusCover p b`: its composite with the covering map of `T`.
* `SymplecticGeometry.latticeTorusAddEquiv p b`, `SymplecticGeometry.latticeTorusDiffeomorph p b`:
  the induced additive isomorphism and diffeomorphism from `ℂ ⧸ Λ` onto `T`.

## Main results

* `SymplecticGeometry.latticeTorusDiffeomorph_comp_mk`: composed with the projection
  `ℂ → ℂ ⧸ Λ`, the diffeomorphism is `complexPiTorusCover p ∘ (funUnique Unit ℝ ℂ).symm ∘ A`.
* `SymplecticGeometry.det_latticeTorusEquiv`, `SymplecticGeometry.det_latticeTorusEquiv_pos`:
  `det A = p inl * p inr / Im (conj b₀ * b₁)`, which is positive for an oriented basis.
* `SymplecticGeometry.mpullback_latticeTorusCover_torusSymplecticForm`: the pull-back of the
  torus form along `latticeTorusCover p b` is `det A • ω₀`.

The computation of that pull-back through the derivative of the covering map follows the proof of
Tau Ceti's `TauCeti.mpullback_complexPiTorusCover_torusSymplecticForm`, and the computation of the
kernel of `latticeTorusCover p b` follows that of Tau Ceti's
`Module.Basis.ker_latticeCircleCoordinates`, with periods `p` in place of `1`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.2 (the
  fibre of the rational elliptic surface as a torus).
-/

public section

noncomputable section

open Complex ComplexConjugate Module TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {Λ : Submodule ℤ ℂ} [DiscreteTopology Λ] [IsZLattice ℝ Λ]

variable (p : Unit ⊕ Unit → ℝ) [∀ i, Fact (0 < p i)]

/-- The real basis `p inl, p inr • I` of `ℂ`, spanning the lattice of the standard torus. -/
private def periodBasis : Basis (Fin 2) ℝ ℂ :=
  basisOneI.unitsSMul ![Units.mk0 (p (.inl ())) (Fact.out : 0 < p _).ne',
    Units.mk0 (p (.inr ())) (Fact.out : 0 < p _).ne']

/-- The real-linear automorphism of `ℂ` that sends a `ℤ`-basis `b₀, b₁` of a lattice `Λ` to
`p inl` and `I * p inr`. It carries `Λ` onto the lattice `p inl ℤ + I p inr ℤ`. -/
def latticeTorusEquiv (b : Basis (Fin 2) ℤ Λ) : ℂ ≃L[ℝ] ℂ :=
  ((b.ofZLatticeBasis ℝ Λ).equiv (periodBasis p) (Equiv.refl _)).toContinuousLinearEquiv

variable (b : Basis (Fin 2) ℤ Λ)

/-- `latticeTorusEquiv p b z` in the coordinates `r₀, r₁` of `z` in the basis `b`: it is
`p inl r₀ + p inr r₁ I`. -/
theorem latticeTorusEquiv_apply (z : ℂ) :
    latticeTorusEquiv p b z = ⟨p (.inl ()) * (b.ofZLatticeBasis ℝ Λ).repr z 0,
      p (.inr ()) * (b.ofZLatticeBasis ℝ Λ).repr z 1⟩ := by
  rw [latticeTorusEquiv, LinearEquiv.coe_toContinuousLinearEquiv']
  conv_lhs => rw [← (b.ofZLatticeBasis ℝ Λ).sum_repr z]
  rw [map_sum, Fin.sum_univ_two, map_smul, map_smul, Basis.equiv_apply, Basis.equiv_apply]
  apply Complex.ext <;>
    simp [periodBasis, Basis.unitsSMul_apply, coe_basisOneI, mul_comm]

/-- The real part of `latticeTorusEquiv p b z` is `p inl` times the first coordinate of `z` in the
basis `b`. -/
@[simp]
theorem re_latticeTorusEquiv (z : ℂ) :
    (latticeTorusEquiv p b z).re = p (.inl ()) * (b.ofZLatticeBasis ℝ Λ).repr z 0 := by
  rw [latticeTorusEquiv_apply]

/-- The imaginary part of `latticeTorusEquiv p b z` is `p inr` times the second coordinate of `z`
in the basis `b`. -/
@[simp]
theorem im_latticeTorusEquiv (z : ℂ) :
    (latticeTorusEquiv p b z).im = p (.inr ()) * (b.ofZLatticeBasis ℝ Λ).repr z 1 := by
  rw [latticeTorusEquiv_apply]

/-- `latticeTorusEquiv p b` sends `b₀` to `p inl`. -/
@[simp]
theorem latticeTorusEquiv_apply_zero : latticeTorusEquiv p b (b 0) = p (.inl ()) := by
  rw [← Basis.ofZLatticeBasis_apply ℝ Λ b 0]
  apply Complex.ext <;> simp

/-- `latticeTorusEquiv p b` sends `b₁` to `I * p inr`. -/
@[simp]
theorem latticeTorusEquiv_apply_one : latticeTorusEquiv p b (b 1) = I * p (.inr ()) := by
  rw [← Basis.ofZLatticeBasis_apply ℝ Λ b 1]
  apply Complex.ext <;> simp

/-- The determinant of `latticeTorusEquiv p b` is `p inl * p inr / Im (conj b₀ * b₁)`. -/
theorem det_latticeTorusEquiv :
    LinearMap.det (latticeTorusEquiv p b : ℂ →ₗ[ℝ] ℂ) =
      p (.inl ()) * p (.inr ()) / (conj (b 0 : ℂ) * b 1).im := by
  have h : stdComplexSymplecticForm (latticeTorusEquiv p b (b 0)) (latticeTorusEquiv p b (b 1)) =
      LinearMap.det (latticeTorusEquiv p b : ℂ →ₗ[ℝ] ℂ) * stdComplexSymplecticForm (b 0) (b 1) :=
    congr($(stdComplexSymplecticForm.isAlt.compl₁₂_self_eq_det_smul basisOneI
      (latticeTorusEquiv p b : ℂ →ₗ[ℝ] ℂ)) (b 0) (b 1))
  rw [latticeTorusEquiv_apply_zero, latticeTorusEquiv_apply_one] at h
  simp only [stdComplexSymplecticForm_apply, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im]
    at h
  rw [eq_div_iff (ZLattice.im_conj_mul_basis_ne_zero Λ b)]
  simp only [mul_im, conj_re, conj_im]
  linear_combination -h

/-- For a positively oriented basis, `latticeTorusEquiv p b` has positive determinant. -/
theorem det_latticeTorusEquiv_pos (hb : 0 < (conj (b 0 : ℂ) * b 1).im) :
    0 < LinearMap.det (latticeTorusEquiv p b : ℂ →ₗ[ℝ] ℂ) := by
  rw [det_latticeTorusEquiv]
  have := (Fact.out : 0 < p (.inl ()))
  have := (Fact.out : 0 < p (.inr ()))
  positivity

/-- The composite `z ↦ complexPiTorusCover p (fun _ ↦ latticeTorusEquiv p b z)` of
`latticeTorusEquiv p b` with Tau Ceti's covering map of the standard torus, as an additive map. -/
def latticeTorusCover : ℂ →+ ∀ i, AddCircle (p i) where
  toFun z := complexPiTorusCover p
    ((ContinuousLinearEquiv.funUnique Unit ℝ ℂ).symm (latticeTorusEquiv p b z))
  map_zero' := by
    funext i
    cases i <;> simp
  map_add' z w := by
    funext i
    cases i <;> simp

/-- `latticeTorusCover p b` is the covering map of the torus after `latticeTorusEquiv p b`. -/
theorem coe_latticeTorusCover :
    ⇑(latticeTorusCover p b) =
      complexPiTorusCover p ∘ (ContinuousLinearEquiv.funUnique Unit ℝ ℂ).symm ∘
        latticeTorusEquiv p b :=
  (rfl)

/-- The kernel of `latticeTorusCover p b` is the lattice `Λ`. -/
theorem latticeTorusCover_eq_zero_iff {z : ℂ} : latticeTorusCover p b z = 0 ↔ z ∈ Λ := by
  have h0 := (Fact.out : 0 < p (.inl ())).ne'
  have h1 := (Fact.out : 0 < p (.inr ())).ne'
  have hΛ : z ∈ Λ ↔ z ∈ Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ Λ)) := by
    rw [Basis.ofZLatticeBasis_span]
  rw [hΛ, Basis.mem_span_iff_repr_mem, coe_latticeTorusCover]
  simp only [funext_iff, Sum.forall, Function.comp_apply, Pi.zero_apply,
    complexPiTorusCover_apply_inl, complexPiTorusCover_apply_inr,
    ContinuousLinearEquiv.coe_funUnique_symm, Function.const_apply, Unique.forall_iff,
    re_latticeTorusEquiv, im_latticeTorusEquiv,
    AddCircle.coe_eq_zero_iff, Fin.forall_fin_two, Set.mem_range, zsmul_eq_mul,
    mul_comm _ (p _), mul_right_inj' h0, mul_right_inj' h1, algebraMap_int_eq,
    eq_intCast]

/-- The kernel of `latticeTorusCover p b` is the lattice `Λ`. -/
theorem ker_latticeTorusCover : (latticeTorusCover p b).ker = Λ.toAddSubgroup := by
  ext z
  exact latticeTorusCover_eq_zero_iff p b

/-- `latticeTorusCover p b` is onto. -/
theorem latticeTorusCover_surjective : Function.Surjective (latticeTorusCover p b) := by
  rw [coe_latticeTorusCover]
  exact (complexPiTorusCover_surjective p).comp
    ((ContinuousLinearEquiv.funUnique Unit ℝ ℂ).symm.surjective.comp
      (latticeTorusEquiv p b).surjective)

/-- `latticeTorusCover p b` is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_latticeTorusCover :
    IsLocalDiffeomorph 𝓘(ℝ, ℂ) (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) ∞
      (latticeTorusCover p b) := by
  have h : IsLocalDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, Unit → ℂ) ∞
      ((ContinuousLinearEquiv.funUnique Unit ℝ ℂ).symm ∘ latticeTorusEquiv p b) := by
    simpa using ((latticeTorusEquiv p b).toDiffeomorph.trans
      (ContinuousLinearEquiv.funUnique Unit ℝ ℂ).symm.toDiffeomorph).isLocalDiffeomorph
  rw [coe_latticeTorusCover]
  exact fun z ↦ (h z).comp (hg := isLocalDiffeomorph_complexPiTorusCover p _)

/-- `latticeTorusCover p b` pulls the standard symplectic form of the torus back to
`det A • ω₀`, for `A = latticeTorusEquiv p b` and the standard area form `ω₀` of `ℂ`. -/
theorem mpullback_latticeTorusCover_torusSymplecticForm :
    SmoothForm.mpullback (latticeTorusCover p b)
        (isLocalDiffeomorph_latticeTorusCover p b).contMDiff (torusSymplecticForm p) =
      LinearMap.det (latticeTorusEquiv p b : ℂ →ₗ[ℝ] ℂ) • stdComplexSymplecticForm.constSmooth := by
  refine SmoothBundleForm.ext_eval₂ fun z v w ↦ ?_
  let L : ℂ →L[ℝ] Unit → ℂ :=
    ((ContinuousLinearEquiv.funUnique Unit ℝ ℂ).symm : ℂ →L[ℝ] Unit → ℂ).comp
      (latticeTorusEquiv p b : ℂ →L[ℝ] ℂ)
  let D : ℂ →L[ℝ] Unit ⊕ Unit → ℝ :=
    (complexToRealPi Unit : (Unit → ℂ) →L[ℝ] Unit ⊕ Unit → ℝ).comp L
  have hf : ⇑(latticeTorusCover p b) = complexPiTorusCover p ∘ L := by
    rw [coe_latticeTorusCover, ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_coe]
  have hd : HasMFDerivAt 𝓘(ℝ, ℂ) (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ))
      (latticeTorusCover p b) z D :=
    hf ▸ (hasMFDerivAt_complexPiTorusCover p (L z)).comp z L.hasMFDerivAt
  have key (v w : ℂ) :
      ∑ j : Unit, (D v (.inl j) * D w (.inr j) - D v (.inr j) * D w (.inl j)) =
        LinearMap.det (latticeTorusEquiv p b : ℂ →ₗ[ℝ] ℂ) * stdComplexSymplecticForm v w := by
    have h : stdComplexSymplecticForm (latticeTorusEquiv p b v) (latticeTorusEquiv p b w) =
        LinearMap.det (latticeTorusEquiv p b : ℂ →ₗ[ℝ] ℂ) * stdComplexSymplecticForm v w :=
      congr($(stdComplexSymplecticForm.isAlt.compl₁₂_self_eq_det_smul basisOneI
        (latticeTorusEquiv p b : ℂ →ₗ[ℝ] ℂ)) v w)
    simp only [stdComplexSymplecticForm_apply] at h
    simpa [D, L, complexToRealPi_apply, stdComplexSymplecticForm_apply] using h
  rw [SmoothForm.eval₂_mpullback, hd.mfderiv, eval₂_torusSymplecticForm]
  -- The tangent spaces of `ℂ` are `ℂ` itself, so `key` applies to the tangent vectors `v`, `w`.
  refine (key v w).trans ?_
  rw [← SymplecticForm.constSmooth_apply stdComplexSymplecticForm z v w]
  simp [SmoothBundleForm.eval₂_apply]

/-- The additive isomorphism from `ℂ ⧸ Λ` onto the standard torus induced by
`latticeTorusCover p b`. -/
def latticeTorusAddEquiv : ℂ ⧸ Λ.toAddSubgroup ≃+ ∀ i, AddCircle (p i) :=
  QuotientAddGroup.liftEquiv _ (latticeTorusCover_surjective p b) (ker_latticeTorusCover p b).symm

/-- `latticeTorusAddEquiv p b` sends the class of `z` to `latticeTorusCover p b z`. -/
@[simp]
theorem latticeTorusAddEquiv_mk (z : ℂ) :
    latticeTorusAddEquiv p b (z : ℂ ⧸ Λ.toAddSubgroup) = latticeTorusCover p b z :=
  QuotientAddGroup.liftEquiv_mk _ _ _ z

/-- **A complex torus is diffeomorphic to the standard torus.** For a `ℤ`-basis `b` of a lattice
`Λ` in `ℂ`, the smooth diffeomorphism from `ℂ ⧸ Λ` onto `∀ i, AddCircle (p i)` induced by
`latticeTorusCover p b`. -/
def latticeTorusDiffeomorph :
    Diffeomorph 𝓘(ℝ, ℂ) (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ))
      (ℂ ⧸ Λ.toAddSubgroup) (∀ i, AddCircle (p i)) ∞ where
  toEquiv := (latticeTorusAddEquiv p b).toEquiv
  contMDiff_toFun := by
    refine (Λ.toAddSubgroup.contMDiff_quotient_iff (I := 𝓘(ℝ, ℂ)) (n := ∞) le_rfl _).2 ?_
    exact (isLocalDiffeomorph_latticeTorusCover p b).contMDiff
  contMDiff_invFun := by
    refine ((isLocalDiffeomorph_latticeTorusCover p b).contMDiff_comp_iff
      (latticeTorusCover_surjective p b) le_rfl).1 ?_
    have h : (latticeTorusAddEquiv p b).symm ∘ latticeTorusCover p b = QuotientAddGroup.mk :=
      funext fun z ↦ (latticeTorusAddEquiv p b).symm_apply_eq.2 (latticeTorusAddEquiv_mk p b z).symm
    exact h ▸ (AddSubgroup.isLocalDiffeomorph_quotientMk (I := 𝓘(ℝ, ℂ)) (n := ∞)
      Λ.toAddSubgroup).contMDiff

/-- `latticeTorusDiffeomorph p b` is `latticeTorusAddEquiv p b`. -/
theorem coe_latticeTorusDiffeomorph :
    ⇑(latticeTorusDiffeomorph p b) = latticeTorusAddEquiv p b :=
  (rfl)

/-- `latticeTorusDiffeomorph p b` sends the class of `z` to `latticeTorusCover p b z`. -/
@[simp]
theorem latticeTorusDiffeomorph_mk (z : ℂ) :
    latticeTorusDiffeomorph p b (z : ℂ ⧸ Λ.toAddSubgroup) = latticeTorusCover p b z := by
  rw [coe_latticeTorusDiffeomorph, latticeTorusAddEquiv_mk]

/-- The diffeomorphism composed with the projection `ℂ → ℂ ⧸ Λ` is the covering map of the torus
after `latticeTorusEquiv p b`. -/
theorem latticeTorusDiffeomorph_comp_mk :
    latticeTorusDiffeomorph p b ∘ QuotientAddGroup.mk =
      complexPiTorusCover p ∘ (ContinuousLinearEquiv.funUnique Unit ℝ ℂ).symm ∘
        latticeTorusEquiv p b :=
  (funext (latticeTorusDiffeomorph_mk p b)).trans (coe_latticeTorusCover p b)

end SymplecticGeometry
