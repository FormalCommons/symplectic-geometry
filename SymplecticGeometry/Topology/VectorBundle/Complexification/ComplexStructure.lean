/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.Complexification
public import TauCeti.Topology.VectorBundle.Complex.Structure
public import TauCeti.Topology.VectorBundle.Complexification
public import TauCeti.Topology.VectorBundle.Conjugate
import TauCeti.Topology.VectorBundle.Section

/-!
# The complexification of a real bundle with a complex structure

Let `J` be a continuous complex structure on a real vector bundle `V`, and `J.Fiber` the complex
vector bundle it defines. The complexification `fun b ↦ ℂ ⊗[ℝ] V b` of `V` splits as the direct
sum of `J.Fiber` and of its conjugate: on each fibre, `z ⊗ v ↦ (z v, z̄ v)` is a complex-linear
isomorphism `ℂ ⊗[ℝ] V b ≃ J.Fiber b × Conjugate (J.Fiber b)`, where `z v` is the action of `ℂ`
on `J.Fiber b`, `re z • v + im z • J v`.

The inverse sends `(a, c)` to `a^(1,0) + c^(0,1)`, the sum of the `(1,0)`-part of `a` and the
`(0,1)`-part of `c` (Tau Ceti's `TauCeti.AlmostComplexStructure.holomorphicPart` and
`TauCeti.AlmostComplexStructure.antiholomorphicPart`). In the real coordinates
`u = 1 ⊗ x + i ⊗ y` of the complexification, the map is `(x, y) ↦ (x + J y, x - J y)` and its
inverse is `(a, c) ↦ ((a + c) / 2, J (c - a) / 2)`. Both are continuous on total spaces, since `J`
is, by Tau Ceti's `TauCeti.continuous_complexification_totalSpace_iff`, so the fibrewise
isomorphisms form a homeomorphism of total spaces.

## Main definitions

* `TauCeti.Bundle.ContinuousComplexStructure.complexificationEquiv`: the complex-linear
  isomorphism `ℂ ⊗[ℝ] V b ≃ J.Fiber b × Conjugate (J.Fiber b)`, `z ⊗ v ↦ (z v, z̄ v)`.
* `TauCeti.Bundle.ContinuousComplexStructure.complexificationHomeomorph`: the induced
  homeomorphism from the total space of the complexification of `V` to that of
  `J.Fiber ×ᵇ ConjugateBundle J.Fiber`, with its value on pure tensors
  (`TauCeti.Bundle.ContinuousComplexStructure.complexificationHomeomorph_tmul`).

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §15 (the complexification of a complex vector bundle is isomorphic to the
  sum of the bundle and its conjugate).
-/

public section

noncomputable section

open Bundle Module TauCeti TauCeti.Conjugate ComplexConjugate
open scoped TensorProduct

namespace TauCeti.Bundle.ContinuousComplexStructure

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)]
  [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousSMul ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  (J : ContinuousComplexStructure F V)

/-! ### The fibrewise isomorphism -/

/-- The complex-linear isomorphism `ℂ ⊗[ℝ] V b ≃ J.Fiber b × Conjugate (J.Fiber b)`,
`z ⊗ v ↦ (z v, z̄ v)`, where `ℂ` acts on `J.Fiber b` through `J b`. Its inverse sends `(a, c)`
to the sum of the `(1,0)`-part of `a` and the `(0,1)`-part of `c`. -/
def complexificationEquiv (b : B) :
    ℂ ⊗[ℝ] V b ≃ₗ[ℂ] J.Fiber b × ConjugateBundle J.Fiber b where
  __ := LinearMap.prod (((J.fiberEquiv b).symm : V b →ₗ[ℝ] J.Fiber b).liftBaseChange ℂ)
    ((toConjₗ'.toLinearMap ∘ₗ ((J.fiberEquiv b).symm : V b →ₗ[ℝ] J.Fiber b)).liftBaseChange ℂ)
  invFun p := (J.almostComplexStructureAt b).holomorphicPart (J.fiberEquiv b p.1) +
    (J.almostComplexStructureAt b).antiholomorphicPart (J.fiberEquiv b (ofConj p.2))
  left_inv u := by
    refine complexification_ext ?_ ?_ <;>
    · simp [LinearMap.liftBaseChange_complex_apply]
      module
  right_inv p := by
    ext
    · apply (J.fiberEquiv b).injective
      simp [LinearMap.liftBaseChange_complex_apply]
      module
    · apply ofConj.injective
      apply (J.fiberEquiv b).injective
      simp [LinearMap.liftBaseChange_complex_apply]
      module

/-- On a pure tensor, `J.complexificationEquiv b` is `z ⊗ v ↦ (z v, z̄ v)`. -/
@[simp]
theorem complexificationEquiv_tmul (b : B) (z : ℂ) (v : V b) :
    J.complexificationEquiv b (z ⊗ₜ[ℝ] v) =
      (z • (J.fiberEquiv b).symm v, toConj (conj z • (J.fiberEquiv b).symm v)) := by
  simp [complexificationEquiv]

/-- The inverse of `J.complexificationEquiv b` sends `(a, c)` to `a^(1,0) + c^(0,1)`. -/
theorem complexificationEquiv_symm_apply (b : B) (p : J.Fiber b × ConjugateBundle J.Fiber b) :
    (J.complexificationEquiv b).symm p =
      (J.almostComplexStructureAt b).holomorphicPart (J.fiberEquiv b p.1) +
        (J.almostComplexStructureAt b).antiholomorphicPart (J.fiberEquiv b (ofConj p.2)) :=
  (rfl)

/-- The first component of `J.complexificationEquiv b u`, read in `V b`, is `x + J y`, for
`x` and `y` the real and imaginary parts of `u`. -/
theorem fiberEquiv_complexificationEquiv_fst (b : B) (u : ℂ ⊗[ℝ] V b) :
    J.fiberEquiv b (J.complexificationEquiv b u).1 =
      realPart (V b) u + J b (imaginaryPart (V b) u) := by
  simp [complexificationEquiv, LinearMap.liftBaseChange_complex_apply]

/-- The second component of `J.complexificationEquiv b u`, read in `V b`, is `x - J y`, for
`x` and `y` the real and imaginary parts of `u`. -/
theorem fiberEquiv_ofConj_complexificationEquiv_snd (b : B) (u : ℂ ⊗[ℝ] V b) :
    J.fiberEquiv b (ofConj (J.complexificationEquiv b u).2) =
      realPart (V b) u - J b (imaginaryPart (V b) u) := by
  simp [complexificationEquiv, LinearMap.liftBaseChange_complex_apply, sub_eq_add_neg]

/-- The real part of `(J.complexificationEquiv b).symm (a, c)` is `(a + c) / 2`. -/
theorem realPart_complexificationEquiv_symm (b : B) (p : J.Fiber b × ConjugateBundle J.Fiber b) :
    realPart (V b) ((J.complexificationEquiv b).symm p) =
      (2⁻¹ : ℝ) • (J.fiberEquiv b p.1 + J.fiberEquiv b (ofConj p.2)) := by
  simp [complexificationEquiv_symm_apply]

/-- The imaginary part of `(J.complexificationEquiv b).symm (a, c)` is `J (c - a) / 2`. -/
theorem imaginaryPart_complexificationEquiv_symm (b : B)
    (p : J.Fiber b × ConjugateBundle J.Fiber b) :
    imaginaryPart (V b) ((J.complexificationEquiv b).symm p) =
      (2⁻¹ : ℝ) • J b (J.fiberEquiv b (ofConj p.2) - J.fiberEquiv b p.1) := by
  simp [complexificationEquiv_symm_apply]
  module

/-! ### The homeomorphism of total spaces -/

section Homeomorph

variable [FiniteDimensional ℝ F] (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G]
  [FiniteDimensional ℂ G] [Fact (finrank ℝ F = 2 * finrank ℂ G)]
  [∀ b, TopologicalSpace (ℂ ⊗[ℝ] V b)] [∀ b, IsComplexificationTopology (V b)]

/-- The complexification of a real vector bundle `V` with a continuous complex structure `J` is
the direct sum of the complex vector bundle `J.Fiber` and of its conjugate: the fibrewise
complex-linear isomorphisms `J.complexificationEquiv`, `z ⊗ v ↦ (z v, z̄ v)`, as a homeomorphism
of total spaces. -/
def complexificationHomeomorph :
    TotalSpace (Complexification F) (fun b ↦ ℂ ⊗[ℝ] V b) ≃ₜ
      TotalSpace (G × Conjugate G) (J.Fiber ×ᵇ ConjugateBundle J.Fiber) where
  toFun p := ⟨p.proj, J.complexificationEquiv p.proj p.snd⟩
  invFun p := ⟨p.proj, (J.complexificationEquiv p.proj).symm p.snd⟩
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := by
    obtain ⟨hre, him⟩ := (continuous_complexification_totalSpace_iff (F := F) (E := V)).mp
      continuous_id
    have hJ := (continuous_hom_bundle_iff (fun b ↦ J b)).1 J.continuous
    have hJim := hJ.comp him
    rw [(FiberBundle.Prod.isInducing_diag (F₁ := G) (E₁ := J.Fiber) (F₂ := Conjugate G)
      (E₂ := ConjugateBundle J.Fiber)).continuous_iff, Function.comp_def, continuous_prodMk]
    constructor
    · refine ((J.totalSpaceHomeomorph G).symm.continuous.comp
        (hre.add_totalSpace ℝ hJim)).congr fun p ↦ ?_
      simp only [Function.comp_apply, id_eq, totalSpaceHomeomorph_symm_apply,
        ← fiberEquiv_complexificationEquiv_fst, ContinuousLinearEquiv.symm_apply_apply]
    · refine ((ConjugateBundle.toConjHomeomorph G J.Fiber).continuous.comp
        ((J.totalSpaceHomeomorph G).symm.continuous.comp (hre.add_totalSpace ℝ
          ((continuous_const (y := (-1 : ℝ))).smul_totalSpace hJim)))).congr fun p ↦ ?_
      simp only [Function.comp_apply, id_eq, totalSpaceHomeomorph_symm_apply,
        ConjugateBundle.toConjHomeomorph_apply, neg_one_smul, ← sub_eq_add_neg,
        ← fiberEquiv_ofConj_complexificationEquiv_snd, ContinuousLinearEquiv.symm_apply_apply,
        toConj_ofConj]
  continuous_invFun := by
    have h := (FiberBundle.Prod.isInducing_diag (F₁ := G) (E₁ := J.Fiber) (F₂ := Conjugate G)
      (E₂ := ConjugateBundle J.Fiber)).continuous
    have ha : Continuous fun p : TotalSpace (G × Conjugate G) (J.Fiber ×ᵇ ConjugateBundle J.Fiber) ↦
        TotalSpace.mk' F p.proj (J.fiberEquiv p.proj p.snd.1) :=
      ((J.totalSpaceHomeomorph G).continuous.comp (continuous_fst.comp h)).congr fun p ↦ by
        simp only [Function.comp_apply, totalSpaceHomeomorph_apply]
    have hc : Continuous fun p : TotalSpace (G × Conjugate G) (J.Fiber ×ᵇ ConjugateBundle J.Fiber) ↦
        TotalSpace.mk' F p.proj (J.fiberEquiv p.proj (ofConj p.snd.2)) :=
      ((J.totalSpaceHomeomorph G).continuous.comp ((ConjugateBundle.toConjHomeomorph G
        J.Fiber).symm.continuous.comp (continuous_snd.comp h))).congr fun p ↦ by
        simp only [Function.comp_apply, totalSpaceHomeomorph_apply,
          ConjugateBundle.toConjHomeomorph_symm_apply]
    have hJ := (continuous_hom_bundle_iff (fun b ↦ J b)).1 J.continuous
    refine (continuous_complexification_totalSpace_iff (F := F) (E := V)).mpr ⟨?_, ?_⟩
    · refine ((continuous_const (y := (2⁻¹ : ℝ))).smul_totalSpace
        (ha.add_totalSpace ℝ hc)).congr fun p ↦ ?_
      rw [realPart_complexificationEquiv_symm]
    · refine ((continuous_const (y := (2⁻¹ : ℝ))).smul_totalSpace (hJ.comp
        (hc.add_totalSpace ℝ ((continuous_const (y := (-1 : ℝ))).smul_totalSpace ha)))).congr
        fun p ↦ ?_
      simp only [Function.comp_apply, imaginaryPart_complexificationEquiv_symm, neg_one_smul,
        ← sub_eq_add_neg]

@[simp]
theorem complexificationHomeomorph_apply
    (p : TotalSpace (Complexification F) fun b ↦ ℂ ⊗[ℝ] V b) :
    J.complexificationHomeomorph G p = ⟨p.proj, J.complexificationEquiv p.proj p.snd⟩ := (rfl)

@[simp]
theorem complexificationHomeomorph_symm_apply
    (p : TotalSpace (G × Conjugate G) (J.Fiber ×ᵇ ConjugateBundle J.Fiber)) :
    (J.complexificationHomeomorph G).symm p =
      ⟨p.proj, (J.complexificationEquiv p.proj).symm p.snd⟩ := (rfl)

theorem proj_complexificationHomeomorph
    (p : TotalSpace (Complexification F) fun b ↦ ℂ ⊗[ℝ] V b) :
    (J.complexificationHomeomorph G p).proj = p.proj := (rfl)

/-- On a pure tensor, `J.complexificationHomeomorph G` is `z ⊗ v ↦ (z v, z̄ v)`. -/
theorem complexificationHomeomorph_tmul (b : B) (z : ℂ) (v : V b) :
    J.complexificationHomeomorph G ⟨b, z ⊗ₜ[ℝ] v⟩ =
      ⟨b, (z • (J.fiberEquiv b).symm v, toConj (conj z • (J.fiberEquiv b).symm v))⟩ := by
  rw [complexificationHomeomorph_apply, complexificationEquiv_tmul]

end Homeomorph

end TauCeti.Bundle.ContinuousComplexStructure

end
