/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Prod
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.ComplexStructure.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Sum
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Matrix

/-!
# Direct sums of symplectic vector bundles

For two-forms `ω₁` on `V₁` and `ω₂` on `V₂` over the same base, this file defines the two-form
`ω₁.prod ω₂` on Mathlib's direct-sum bundle `V₁ ×ᵇ V₂`, whose value on a fibre is
`((v₁, v₂), (w₁, w₂)) ↦ ω₁(v₁, w₁) + ω₂(v₂, w₂)`. On each fibre it is Tau Ceti's linear
`TauCeti.SymplecticForm.prod`.

## Main definitions and results

* `ContMDiffTwoForm.prod`: the direct sum of two two-forms, with `prod_apply`,
  `bilinFormAt_prod_apply`, `prod_ext` and `neg_prod_neg`.
* `IsNondegenerate.prod` and `IsNondegenerate.symplecticFormAt_prod`: the sum of two
  symplectic structures is one, fibrewise the direct-sum symplectic form.
* `Tames.prod`, `Invariant.prod`, `Compatible.prod`: direct sums of tame, invariant and compatible
  pairs, with the direct sum `ContMDiffComplexStructure.prod` of complex structures.
* `pushforward_prodCongr`: the sum of two isomorphisms of bundles carries the sum of two forms to
  the sum of their images; `pushforward_prodComm`: the fibrewise swap carries `ω₁.prod ω₂` to
  `ω₂.prod ω₁`.
* `IsSymplecticFrameOn.prod`: symplectic frames of `ω₁` and `ω₂` give the block frame of
  `ω₁.prod ω₂`; `IsSymplecticFrameOn.stdSum`: for frames modelled on `stdForm ι` and `stdForm κ`,
  the block frame read through `StdSpace.sumEquiv ι κ` is modelled on `stdForm (ι ⊕ κ)`.
* `Bundle.frameTransition_stdSum`: the transition map between two such block frames is the map
  of Tau Ceti's `Matrix.symplecticSum` of the two transition matrices.

## Implementation notes

The form `ω₁.prod ω₂` at `x` is `ω₁ x ∘ fst + ω₂ x ∘ snd`, as continuous alternating maps. Its
smoothness combines the smoothness of `fst` and `snd` on total spaces (Tau Ceti's
`Bundle.Prod.contMDiff_fst` and `Bundle.Prod.contMDiff_snd`) with
`contMDiff_compContinuousLinearMap_totalSpace`; this needs the model fibres to be
finite-dimensional. The tameness and compatibility of sums are Tau Ceti's
`TauCeti.SymplecticForm.prod_tames` and `TauCeti.SymplecticForm.prod_compatible` on each fibre.
The maps of total spaces in `pushforward_prodCongr` and `pushforward_prodComm` are smooth by
`Bundle.Prod.contMDiff_prodCongr` and `Bundle.Prod.contMDiff_prodComm`
(`SymplecticGeometry.Geometry.Manifold.VectorBundle.Prod`).

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
  (symplectic vector bundles).
-/

public section

noncomputable section

open _root_.Bundle
open scoped Manifold

namespace SymplecticGeometry.Bundle

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M]
  {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₁ V₂ : M → Type*}
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul ℝ (V₁ x)]
  [TopologicalSpace (TotalSpace F₁ V₁)] [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
  [TopologicalSpace (TotalSpace F₂ V₂)] [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  {n m : ℕ∞}

namespace ContMDiffTwoForm

/-! ### The direct sum of two forms -/

section Prod

/-- The direct sum of a two-form `ω₁` on `V₁` and a two-form `ω₂` on `V₂`: the two-form on the
direct-sum bundle `V₁ ×ᵇ V₂` whose value at `x` on `(v₁, v₂)`, `(w₁, w₂)` is
`ω₁ x (v₁, w₁) + ω₂ x (v₂, w₂)`. -/
def prod (ω₁ : ContMDiffTwoForm I n F₁ V₁) (ω₂ : ContMDiffTwoForm I n F₂ V₂) :
    ContMDiffTwoForm I n (F₁ × F₂) (V₁ ×ᵇ V₂) where
  toFun x := (ω₁ x).compContinuousLinearMap (ContinuousLinearMap.fst ℝ (V₁ x) (V₂ x)) +
    (ω₂ x).compContinuousLinearMap (ContinuousLinearMap.snd ℝ (V₁ x) (V₂ x))
  contMDiff_toFun := by
    have h₁ := (contMDiff_compContinuousLinearMap_totalSpace (ι := Fin 2) (G := ℝ)
      (F₁ := F₁) (F₂ := F₁ × F₂) (W := Trivial M ℝ) _ ((TauCeti.contMDiff_hom_bundle_iff
        fun x ↦ ContinuousLinearMap.fst ℝ (V₁ x) (V₂ x)).2 Bundle.Prod.contMDiff_fst)).comp
      ω₁.contMDiff
    have h₂ := (contMDiff_compContinuousLinearMap_totalSpace (ι := Fin 2) (G := ℝ)
      (F₁ := F₂) (F₂ := F₁ × F₂) (W := Trivial M ℝ) _ ((TauCeti.contMDiff_hom_bundle_iff
        fun x ↦ ContinuousLinearMap.snd ℝ (V₁ x) (V₂ x)).2 Bundle.Prod.contMDiff_snd)).comp
      ω₂.contMDiff
    exact h₁.add_section h₂

/-- The direct sum `ω₁.prod ω₂` at `x` is `ω₁ x` on the first components plus `ω₂ x` on the
second. -/
theorem prod_def (ω₁ : ContMDiffTwoForm I n F₁ V₁) (ω₂ : ContMDiffTwoForm I n F₂ V₂) (x : M) :
    ω₁.prod ω₂ x = (ω₁ x).compContinuousLinearMap (ContinuousLinearMap.fst ℝ (V₁ x) (V₂ x)) +
      (ω₂ x).compContinuousLinearMap (ContinuousLinearMap.snd ℝ (V₁ x) (V₂ x)) :=
  (rfl)

/-- The direct sum takes on `(v₁, v₂)`, `(w₁, w₂)` the value `ω₁ x (v₁, w₁) + ω₂ x (v₂, w₂)`. -/
@[simp]
theorem prod_apply (ω₁ : ContMDiffTwoForm I n F₁ V₁) (ω₂ : ContMDiffTwoForm I n F₂ V₂) (x : M)
    (v w : V₁ x × V₂ x) : ω₁.prod ω₂ x ![v, w] = ω₁ x ![v.1, w.1] + ω₂ x ![v.2, w.2] := by
  rw [prod_def]
  exact ContinuousAlternatingMap.compContinuousLinearMap_fst_add_snd_apply _ _ v w

/-- The bilinear form of the direct sum is the sum of the bilinear forms of the two summands:
`(ω₁ ⊕ ω₂)((v₁, v₂), (w₁, w₂)) = ω₁(v₁, w₁) + ω₂(v₂, w₂)`. -/
theorem bilinFormAt_prod_apply (ω₁ : ContMDiffTwoForm I n F₁ V₁)
    (ω₂ : ContMDiffTwoForm I n F₂ V₂) (x : M) (v w : V₁ x × V₂ x) :
    (ω₁.prod ω₂).bilinFormAt x v w = ω₁.bilinFormAt x v.1 w.1 + ω₂.bilinFormAt x v.2 w.2 := by
  simp

/-- Two-forms on `V₁ ×ᵇ V₂` agree with a direct sum when their bilinear forms agree. -/
theorem prod_ext {ω₁ : ContMDiffTwoForm I n F₁ V₁} {ω₂ : ContMDiffTwoForm I n F₂ V₂}
    {ω : ContMDiffTwoForm I n (F₁ × F₂) (V₁ ×ᵇ V₂)}
    (h : ∀ x v w, ω.bilinFormAt x v w = ω₁.bilinFormAt x v.1 w.1 + ω₂.bilinFormAt x v.2 w.2) :
    ω = ω₁.prod ω₂ :=
  ext_bilinFormAt fun x ↦ LinearMap.ext₂ fun v w ↦ by rw [h, bilinFormAt_prod_apply]

/-- The direct sum of the negatives of two forms is the negative of their direct sum. -/
@[simp]
theorem neg_prod_neg (ω₁ : ContMDiffTwoForm I n F₁ V₁) (ω₂ : ContMDiffTwoForm I n F₂ V₂) :
    (-ω₁).prod (-ω₂) = -(ω₁.prod ω₂) :=
  (prod_ext fun x v w ↦ by
    simp only [bilinFormAt_neg, LinearMap.neg_apply, bilinFormAt_prod_apply]; ring).symm

variable {ω₁ : ContMDiffTwoForm I n F₁ V₁} {ω₂ : ContMDiffTwoForm I n F₂ V₂}

/-- The direct sum of two nondegenerate two-forms is nondegenerate. -/
theorem IsNondegenerate.prod (h₁ : ω₁.IsNondegenerate) (h₂ : ω₂.IsNondegenerate) :
    (ω₁.prod ω₂).IsNondegenerate := isNondegenerate_def.2 fun x ↦ by
  have h : (ω₁.prod ω₂).bilinFormAt x =
      ((h₁.symplecticFormAt x).prod (h₂.symplecticFormAt x)).toBilinForm :=
    LinearMap.ext₂ fun v w ↦ by
      rw [bilinFormAt_prod_apply]
      simp
  rw [h]
  exact TauCeti.SymplecticForm.nondegenerate _

/-- On each fibre, the symplectic form of the direct sum of two symplectic structures is Tau
Ceti's direct sum of their symplectic forms. -/
theorem IsNondegenerate.symplecticFormAt_prod (h₁ : ω₁.IsNondegenerate)
    (h₂ : ω₂.IsNondegenerate) (x : M) :
    (h₁.prod h₂).symplecticFormAt x =
      (h₁.symplecticFormAt x).prod (h₂.symplecticFormAt x) :=
  TauCeti.SymplecticForm.toBilinForm_injective <| LinearMap.ext₂ fun v w ↦ by
    rw [show ((h₁.prod h₂).symplecticFormAt x).toBilinForm v w =
      (ω₁.prod ω₂).bilinFormAt x v w by simp, bilinFormAt_prod_apply]
    simp

/-! ### Tame and compatible pairs -/

variable {J₁ : ContMDiffComplexStructure I m F₁ V₁} {J₂ : ContMDiffComplexStructure I m F₂ V₂}

/-- The direct sum of two tame pairs is tame. -/
theorem Tames.prod (h₁ : ω₁.Tames J₁) (h₂ : ω₂.Tames J₂) : (ω₁.prod ω₂).Tames (J₁.prod J₂) := by
  have hω₁ := h₁.isNondegenerate
  have hω₂ := h₂.isNondegenerate
  refine (hω₁.prod hω₂).tames_iff.2 fun x ↦ ?_
  rw [IsNondegenerate.symplecticFormAt_prod hω₁ hω₂,
    ContMDiffComplexStructure.almostComplexStructureAt_prod]
  exact TauCeti.SymplecticForm.prod_tames (hω₁.tames_iff.1 h₁ x) (hω₂.tames_iff.1 h₂ x)

/-- The direct sum of two invariant pairs is invariant. -/
theorem Invariant.prod (h₁ : ω₁.Invariant J₁) (h₂ : ω₂.Invariant J₂) :
    (ω₁.prod ω₂).Invariant (J₁.prod J₂) := invariant_def.2 fun x v w ↦ by
  simp only [bilinFormAt_prod_apply, ContMDiffComplexStructure.prod_apply, invariant_def.1 h₁ x,
    invariant_def.1 h₂ x]

/-- The direct sum of two compatible pairs is compatible. -/
theorem Compatible.prod (h₁ : ω₁.Compatible J₁) (h₂ : ω₂.Compatible J₂) :
    (ω₁.prod ω₂).Compatible (J₁.prod J₂) := by
  have hω₁ := h₁.isNondegenerate
  have hω₂ := h₂.isNondegenerate
  refine (hω₁.prod hω₂).compatible_iff.2 fun x ↦ ?_
  rw [IsNondegenerate.symplecticFormAt_prod hω₁ hω₂,
    ContMDiffComplexStructure.almostComplexStructureAt_prod]
  exact TauCeti.SymplecticForm.prod_compatible (h₁.compatibleAt x) (h₂.compatibleAt x)

end Prod

/-! ### Isomorphisms -/

section Pushforward

variable {F₃ F₄ : Type*}
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃] [FiniteDimensional ℝ F₃]
  [NormedAddCommGroup F₄] [NormedSpace ℝ F₄] [FiniteDimensional ℝ F₄]
  {V₃ V₄ : M → Type*}
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℝ (V₃ x)] [∀ x, TopologicalSpace (V₃ x)]
  [∀ x, IsTopologicalAddGroup (V₃ x)] [∀ x, ContinuousSMul ℝ (V₃ x)]
  [TopologicalSpace (TotalSpace F₃ V₃)] [FiberBundle F₃ V₃] [VectorBundle ℝ F₃ V₃]
  [∀ x, AddCommGroup (V₄ x)] [∀ x, Module ℝ (V₄ x)] [∀ x, TopologicalSpace (V₄ x)]
  [∀ x, IsTopologicalAddGroup (V₄ x)] [∀ x, ContinuousSMul ℝ (V₄ x)]
  [TopologicalSpace (TotalSpace F₄ V₄)] [FiberBundle F₄ V₄] [VectorBundle ℝ F₄ V₄]

/-- The direct sum of two isomorphisms of bundles carries the direct sum of two forms to the
direct sum of their images. In particular, the direct sum of two symplectic isomorphisms is a
symplectic isomorphism. -/
theorem pushforward_prodCongr (Φ₁ : ∀ x, V₁ x ≃L[ℝ] V₃ x) (Φ₂ : ∀ x, V₂ x ≃L[ℝ] V₄ x)
    (hΦ₁ : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₃)) n
      (fun p : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₃ p.proj (Φ₁ p.proj p.snd)))
    (hΦ₂ : ContMDiff (I.prod 𝓘(ℝ, F₂)) (I.prod 𝓘(ℝ, F₄)) n
      (fun p : TotalSpace F₂ V₂ ↦ TotalSpace.mk' F₄ p.proj (Φ₂ p.proj p.snd)))
    (ω₁ : ContMDiffTwoForm I n F₁ V₁) (ω₂ : ContMDiffTwoForm I n F₂ V₂) :
    pushforward (fun x ↦ (Φ₁ x).prodCongr (Φ₂ x)) (Bundle.Prod.contMDiff_prodCongr hΦ₁ hΦ₂)
        (ω₁.prod ω₂) =
      (pushforward Φ₁ hΦ₁ ω₁).prod (pushforward Φ₂ hΦ₂ ω₂) :=
  (pushforward_eq_iff _ _).2 fun x v w ↦ by
    simp only [bilinFormAt_prod_apply, ContinuousLinearEquiv.prodCongr_apply,
      bilinFormAt_pushforward_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- The fibrewise swap `V₁ ×ᵇ V₂ → V₂ ×ᵇ V₁` carries `ω₁.prod ω₂` to `ω₂.prod ω₁`, so it is a
symplectic isomorphism between them. -/
theorem pushforward_prodComm (ω₁ : ContMDiffTwoForm I n F₁ V₁)
    (ω₂ : ContMDiffTwoForm I n F₂ V₂) :
    pushforward (fun x ↦ ContinuousLinearEquiv.prodComm ℝ (V₁ x) (V₂ x))
        Bundle.Prod.contMDiff_prodComm (ω₁.prod ω₂) =
      ω₂.prod ω₁ :=
  (pushforward_eq_iff _ _).2 fun x v w ↦ by
    simp only [bilinFormAt_prod_apply, ContinuousLinearEquiv.prodComm_apply, Prod.fst_swap,
      Prod.snd_swap, add_comm]

end Pushforward

/-! ### Block frames -/

section Frame

variable {W₁ W₂ : Type*} [NormedAddCommGroup W₁] [NormedSpace ℝ W₁]
  [NormedAddCommGroup W₂] [NormedSpace ℝ W₂]
  {ω₁ : ContMDiffTwoForm I n F₁ V₁} {ω₂ : ContMDiffTwoForm I n F₂ V₂}
  {σ₁ : TauCeti.SymplecticForm W₁} {σ₂ : TauCeti.SymplecticForm W₂} {U : Set M}
  {Φ₁ : ∀ x, W₁ ≃L[ℝ] V₁ x} {Φ₂ : ∀ x, W₂ ≃L[ℝ] V₂ x}

/-- Symplectic frames `Φ₁` of `ω₁` for `σ₁` and `Φ₂` of `ω₂` for `σ₂` over `U` give the block
frame `x ↦ Φ₁ x × Φ₂ x` of `ω₁.prod ω₂` for `σ₁.prod σ₂` over `U`. -/
theorem IsSymplecticFrameOn.prod (h₁ : ω₁.IsSymplecticFrameOn σ₁ U Φ₁)
    (h₂ : ω₂.IsSymplecticFrameOn σ₂ U Φ₂) :
    (ω₁.prod ω₂).IsSymplecticFrameOn (σ₁.prod σ₂) U fun x ↦ (Φ₁ x).prodCongr (Φ₂ x) := by
  have hU : Set.MapsTo (fun p : M × (W₁ × W₂) ↦ (p.1, p.2.1)) (U ×ˢ Set.univ) (U ×ˢ Set.univ) :=
    fun p hp ↦ ⟨hp.1, Set.mem_univ _⟩
  have hU' : Set.MapsTo (fun p : M × (W₁ × W₂) ↦ (p.1, p.2.2)) (U ×ˢ Set.univ) (U ×ˢ Set.univ) :=
    fun p hp ↦ ⟨hp.1, Set.mem_univ _⟩
  refine ⟨fun p hp ↦ contMDiffWithinAt_totalSpace_prod_iff.2 ⟨?_, ?_⟩, fun x hx v w ↦ ?_⟩
  · exact h₁.contMDiffOn.comp (contMDiff_fst.prodMk
      (contDiff_fst.contMDiff.comp contMDiff_snd)).contMDiffOn hU p hp
  · exact h₂.contMDiffOn.comp (contMDiff_fst.prodMk
      (contDiff_snd.contMDiff.comp contMDiff_snd)).contMDiffOn hU' p hp
  · simp only [bilinFormAt_prod_apply, ContinuousLinearEquiv.prodCongr_apply,
      h₁.map_bilinFormAt x hx, h₂.map_bilinFormAt x hx,
      TauCeti.SymplecticForm.prod_apply]

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {Ψ₁ : ∀ x, StdSpace ι ≃L[ℝ] V₁ x} {Ψ₂ : ∀ x, StdSpace κ ≃L[ℝ] V₂ x}

/-- Symplectic frames `Ψ₁` of `ω₁` for `stdForm ι` and `Ψ₂` of `ω₂` for `stdForm κ` over `U`
give the frame `x ↦ (Ψ₁ x × Ψ₂ x) ∘ StdSpace.sumEquiv ι κ` of `ω₁.prod ω₂` for
`stdForm (ι ⊕ κ)` over `U`. -/
theorem IsSymplecticFrameOn.stdSum (h₁ : ω₁.IsSymplecticFrameOn (stdForm ι) U Ψ₁)
    (h₂ : ω₂.IsSymplecticFrameOn (stdForm κ) U Ψ₂) :
    (ω₁.prod ω₂).IsSymplecticFrameOn (stdForm (ι ⊕ κ)) U
      fun x ↦ (StdSpace.sumEquiv ι κ).trans ((Ψ₁ x).prodCongr (Ψ₂ x)) :=
  (h₁.prod h₂).precomp _ (isSymplectomorphism_sumEquiv (ι := ι) (κ := κ))

end Frame

end ContMDiffTwoForm

/-! ### Transition maps of block frames -/

section FrameTransition

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {Ψ₁ Ψ₁' : ∀ x, StdSpace ι ≃L[ℝ] V₁ x} {Ψ₂ Ψ₂' : ∀ x, StdSpace κ ≃L[ℝ] V₂ x} {x : M}
  {A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} {B : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ}

omit [TopologicalSpace M] [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul ℝ (V₁ x)]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)] in
/-- If the transition maps at `x` from `Ψ₁` to `Ψ₁'` and from `Ψ₂` to `Ψ₂'` are the maps of the
matrices `A` and `B`, then the transition map at `x` between the block frames of
`IsSymplecticFrameOn.stdSum` is the map of Tau Ceti's symplectic direct sum
`Matrix.symplecticSum A B`. -/
theorem frameTransition_stdSum
    (h₁ : (frameTransition Ψ₁ Ψ₁' x : StdSpace ι →ₗ[ℝ] StdSpace ι) = Matrix.toEuclideanLin A)
    (h₂ : (frameTransition Ψ₂ Ψ₂' x : StdSpace κ →ₗ[ℝ] StdSpace κ) = Matrix.toEuclideanLin B) :
    (frameTransition (fun y ↦ (StdSpace.sumEquiv ι κ).trans ((Ψ₁ y).prodCongr (Ψ₂ y)))
        (fun y ↦ (StdSpace.sumEquiv ι κ).trans ((Ψ₁' y).prodCongr (Ψ₂' y))) x :
        StdSpace (ι ⊕ κ) →ₗ[ℝ] StdSpace (ι ⊕ κ)) =
      Matrix.toEuclideanLin (Matrix.symplecticSum A B) := by
  refine LinearMap.ext fun z ↦ (StdSpace.sumEquiv ι κ).injective ?_
  rw [StdSpace.sumEquiv_toEuclideanLin_symplecticSum, ← h₁, ← h₂]
  simp

end FrameTransition

end SymplecticGeometry.Bundle

end
