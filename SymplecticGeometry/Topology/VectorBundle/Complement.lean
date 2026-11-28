/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Topology.VectorBundle.Complement

import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Topology.FiberBundle.Prod
import TauCeti.Topology.VectorBundle.Contractible

/-!
# Complements of a fibrewise embedding into a trivial bundle

Let `j b : E b → V` be a fibrewise injection of a finite-rank vector bundle into a
finite-dimensional inner product space, continuous on the total space. Tau Ceti's
`TauCeti.bundleComplementFiberEquiv` splits `V` as the image of `E b` plus its orthogonal
complement. Its inverse followed by the first projection sends `u ∈ V` to the vector of `E b`
whose image is the orthogonal projection of `u` onto the image of `E b`
(`TauCeti.bundleComplementFiberEquiv_symm_apply_fst`). This file shows that this left inverse of
`j` is continuous as a map from `B × V` to the total space of `E`, a consequence of the
continuity of the inverse of Tau Ceti's `TauCeti.bundleComplementHomeomorph`.

Over a contractible paracompact R₁ base the bundle of orthogonal complements is trivial (Tau Ceti's
`TauCeti.exists_continuous_frame`). So a continuous family of injective linear maps
`j y : G₁ → V` into a fixed finite-dimensional space extends, by a continuous family
`k y : G₂ → V`, to a continuous family of isomorphisms `(j y, k y) : G₁ × G₂ → V`; no inner
product on `V` is needed, since `V` is first carried to a Euclidean space.

## Main results

* `TauCeti.continuous_bundleComplementFiberEquiv_symm_fst`: `(b, u) ↦ j_b⁻¹ (P_{j(E_b)} u)` is
  continuous from `B × V` to the total space of `E`.
* `Continuous.exists_continuous_isInvertible_coprod`: over a contractible base, a continuous
  family of injective linear maps `G₁ → V` is completed to a continuous family of isomorphisms
  `G₁ × G₂ → V`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, Proposition 1.4 (complements of subbundles of a
  trivial bundle).
-/

public section

open Bundle Function

namespace TauCeti

variable {𝕜 B F V : Type*} [RCLike 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul 𝕜 (E x)]
  (j : ∀ x, E x →L[𝕜] V) (hj : Continuous (fun p : TotalSpace F E ↦ j p.proj p.snd))
  (hinj : ∀ x, Injective (j x))

include hj in
/-- The left inverse `(b, u) ↦ j_b⁻¹ (P_{j(E_b)} u)` of a continuous fibrewise embedding `j` of
a finite-rank vector bundle into a finite-dimensional inner product space, the first component of
the inverse of `TauCeti.bundleComplementFiberEquiv`, is continuous from `B × V` to the total space
of `E`. -/
theorem continuous_bundleComplementFiberEquiv_symm_fst :
    Continuous fun q : B × V ↦
      TotalSpace.mk' F q.1 ((bundleComplementFiberEquiv (F := F) j hinj q.1).symm q.2).1 := by
  let := bundleComplementFiberBundle (F := F) j hj hinj
  refine (FiberBundle.Prod.continuous_totalSpaceFst.comp
    (bundleComplementHomeomorph (F := F) j hj hinj).symm.continuous).congr fun q ↦ ?_
  exact congrArg (fun v ↦ TotalSpace.mk' F v.proj v.snd.1)
    (bundleComplementHomeomorph_symm_apply (F := F) j hj hinj q)

section ComplementFrame

variable {𝕜 B G₁ G₂ V : Type*} [RCLike 𝕜] [TopologicalSpace B] [R1Space B] [ParacompactSpace B]
  [ContractibleSpace B]
  [NormedAddCommGroup G₁] [NormedSpace 𝕜 G₁] [FiniteDimensional 𝕜 G₁]
  [NormedAddCommGroup G₂] [NormedSpace 𝕜 G₂] [FiniteDimensional 𝕜 G₂]

/-- The case of `Continuous.exists_continuous_isInvertible_coprod` with an inner product on `V`:
the frame is a frame of the bundle of orthogonal complements of the ranges of `j`. -/
private theorem exists_continuous_isInvertible_coprod_of_inner [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    (hdim : Module.finrank 𝕜 G₁ + Module.finrank 𝕜 G₂ = Module.finrank 𝕜 V)
    {j : B → G₁ →L[𝕜] V} (hj : Continuous j) (hinj : ∀ y, Injective (j y)) :
    ∃ k : B → G₂ →L[𝕜] V, Continuous k ∧ ∀ y, ((j y).coprod (k y)).IsInvertible := by
  -- `j` as a fibrewise embedding of the trivial bundle with fibre `G₁` into `V`.
  let j' : ∀ x, Trivial B G₁ x →L[𝕜] V := j
  have hj' : Continuous fun p : TotalSpace G₁ (Trivial B G₁) ↦ j' p.proj p.snd :=
    ((hj.comp continuous_fst).clm_apply continuous_snd).comp
      (Bundle.Trivial.homeomorphProd B G₁).continuous
  let := bundleComplementFiberBundle (F := G₁) j' hj' hinj
  let := bundleComplementVectorBundle (F := G₁) j' hj' hinj
  obtain ⟨ψ, hψ⟩ := exists_continuous_frame (𝕜 := 𝕜)
    (F := Fin (Module.finrank 𝕜 V - Module.finrank 𝕜 G₁) → 𝕜)
    (E := fun x ↦ (bundleComplementProjection (F := G₁) j' x).range) (f := id) continuous_id
  have hn : Module.finrank 𝕜 G₂ =
      Module.finrank 𝕜 (Fin (Module.finrank 𝕜 V - Module.finrank 𝕜 G₁) → 𝕜) := by
    rw [Module.finrank_fin_fun]
    omega
  let ι := ContinuousLinearEquiv.ofFinrankEq hn
  refine ⟨fun y ↦ (Submodule.subtypeL _).comp
      ((ψ y).toContinuousLinearMap.comp ι.toContinuousLinearMap),
    continuous_clm_apply.2 fun w ↦ ?_, fun y ↦ ?_⟩
  · exact (continuous_snd.comp (isEmbedding_totalSpace_range _
      (bundleComplementProjection (F := G₁) j')).continuous).comp
      (hψ.comp (Continuous.prodMk_left (ι w)))
  · refine ⟨((ContinuousLinearEquiv.refl 𝕜 G₁).prodCongr (ι.trans (ψ y))).trans
      (bundleComplementFiberEquiv (F := G₁) j' hinj y), ?_⟩
    ext v <;> simp [j']

/-- **Frames of a complement over a contractible base.** Let `j y : G₁ → V` be injective linear
maps into a finite-dimensional space `V`, depending continuously on a point `y` of a contractible
paracompact R₁ space, and let `G₂` be a space of the complementary dimension. Then there are linear
maps `k y : G₂ → V`, depending continuously on `y`, such that each `(j y, k y) : G₁ × G₂ → V` is an
isomorphism. -/
theorem _root_.Continuous.exists_continuous_isInvertible_coprod [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    (hdim : Module.finrank 𝕜 G₁ + Module.finrank 𝕜 G₂ = Module.finrank 𝕜 V)
    {j : B → G₁ →L[𝕜] V} (hj : Continuous j) (hinj : ∀ y, Injective (j y)) :
    ∃ k : B → G₂ →L[𝕜] V, Continuous k ∧ ∀ y, ((j y).coprod (k y)).IsInvertible := by
  -- Transport `V` to a Euclidean space, where Tau Ceti's orthogonal complements live.
  let e₀ : V ≃L[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 V)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  obtain ⟨k, hk, hkj⟩ := exists_continuous_isInvertible_coprod_of_inner (G₂ := G₂)
    (j := fun y ↦ e₀.toContinuousLinearMap.comp (j y))
    (hdim.trans finrank_euclideanSpace_fin.symm) (continuous_const.clm_comp hj)
    fun y ↦ by
      rw [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe]
      exact e₀.injective.comp (hinj y)
  refine ⟨fun y ↦ e₀.symm.toContinuousLinearMap.comp (k y), continuous_const.clm_comp hk,
    fun y ↦ ?_⟩
  have h : (j y).coprod (e₀.symm.toContinuousLinearMap.comp (k y)) =
      e₀.symm.toContinuousLinearMap.comp ((e₀.toContinuousLinearMap.comp (j y)).coprod (k y)) := by
    ext v <;> simp
  rw [h, ContinuousLinearMap.isInvertible_equiv_comp]
  exact hkj y

end ComplementFrame

end TauCeti

end
