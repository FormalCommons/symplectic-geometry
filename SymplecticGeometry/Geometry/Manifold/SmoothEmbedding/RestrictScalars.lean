/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic
import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars
import SymplecticGeometry.Geometry.Manifold.MFDeriv.RestrictScalars
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars

/-!
# Immersions and embeddings under restriction of scalars

A `C^n` immersion, `1 ≤ n`, between manifolds modelled on the trivial models over a field `𝕜'`
is a `C^n` immersion for the trivial models over a smaller field `𝕜`, when the target model is
finite-dimensional over `𝕜`: `Manifold.IsImmersion.restrictScalars`. The same then holds for
embeddings: `Manifold.IsSmoothEmbedding.restrictScalars`. For instance, a holomorphic embedding
of complex manifolds is a smooth embedding of the underlying real manifolds. The immersion
statement combines `ContMDiff.restrictScalars'`,
`MDifferentiableAt.mfderiv_modelWithCornersSelf_restrictScalars_apply` and
`ContMDiff.isImmersion_of_injective_mfderiv`.

More generally, both statements hold for any boundaryless models `I`, `I'` over `𝕜'` and their
scalar restrictions `I.restrictScalars 𝕜`, `I'.restrictScalars 𝕜`
(`Manifold.IsImmersion.restrictScalars_modelWithCorners`,
`Manifold.IsSmoothEmbedding.restrictScalars_modelWithCorners`), by Tau Ceti's
`ContMDiff.restrictScalars` and `TauCeti.injective_mfderiv_restrictScalars`. For maps into a
product `N × N'` with the product of the trivial models as target model, they give
`Manifold.IsImmersion.restrictScalars_prod` and `Manifold.IsSmoothEmbedding.restrictScalars_prod`,
since restriction of scalars commutes with products of models
(`ModelWithCorners.restrictScalars_prod`) and takes trivial models to trivial models
(`modelWithCornersSelf_restrictScalars`).

For bundled embeddings, a `C^m` embedding `f` for the trivial models over `𝕜'` gives, for every
`1 ≤ n ≤ m`, a `C^n` embedding `f.restrictScalars 𝕜 hnm hn` for the trivial models over `𝕜`, with
the same underlying map (`TauCeti.SmoothEmbedding.restrictScalars`), and likewise for maps into a
product (`TauCeti.SmoothEmbedding.restrictScalarsProd`). Lowering the order is part of the
construction, since a holomorphic embedding is analytic while the real manifolds it is used with
are often only smooth. The derivative of the restricted embedding is the derivative of `f`
(`TauCeti.SmoothEmbedding.coe_mfderiv_restrictScalars`, by Tau Ceti's
`MDifferentiableAt.mfderiv_modelWithCornersSelf_restrictScalars_apply`; for a product target,
`TauCeti.SmoothEmbedding.coe_mfderiv_restrictScalarsProd`, by its analogue
`MDifferentiableAt.mfderiv_modelWithCornersSelf_prod_restrictScalars_apply` from
`SymplecticGeometry.Geometry.Manifold.MFDeriv.RestrictScalars`), so its tangent
ranges are those of `f` (`TauCeti.SmoothEmbedding.coe_tangentRange_restrictScalars`,
`TauCeti.SmoothEmbedding.coe_tangentRange_restrictScalarsProd`): images
of `𝕜'`-linear maps, closed under multiplication by scalars of `𝕜'`
(`TauCeti.SmoothEmbedding.smul_mem_tangentRange_restrictScalars`,
`TauCeti.SmoothEmbedding.smul_mem_tangentRange_restrictScalarsProd`).
-/

public section

open scoped ContDiff Manifold

namespace Manifold

variable (𝕜 : Type*) {𝕜' : Type*} [RCLike 𝕜] [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedSpace 𝕜' E']
  [IsScalarTower 𝕜 𝕜' E'] [FiniteDimensional 𝕜 E']

section General

variable {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners 𝕜' E H} {I' : ModelWithCorners 𝕜' E' H'} [I.Boundaryless]
  [I'.Boundaryless] {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {N : Type*}
  [TopologicalSpace N] [ChartedSpace H' N] {n : ℕ∞ω} [IsManifold (I.restrictScalars 𝕜) n M]
  [IsManifold (I'.restrictScalars 𝕜) n N] {f : M → N}

/-- A `C^n` immersion, `1 ≤ n`, for boundaryless models `I`, `I'` over `𝕜'` is a `C^n` immersion
for their scalar restrictions to the smaller field `𝕜`, if the target model space is
finite-dimensional over `𝕜`. -/
theorem IsImmersion.restrictScalars_modelWithCorners (h : IsImmersion I I' n f) (hn : 1 ≤ n) :
    IsImmersion (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) n f := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  exact (h.contMDiff.restrictScalars 𝕜).isImmersion_of_injective_mfderiv hn fun x ↦
    TauCeti.injective_mfderiv_restrictScalars 𝕜 (h.mfderiv_injective hn0 x)

/-- A `C^n` embedding, `1 ≤ n`, for boundaryless models `I`, `I'` over `𝕜'` is a `C^n` embedding
for their scalar restrictions to the smaller field `𝕜`, if the target model space is
finite-dimensional over `𝕜`. -/
theorem IsSmoothEmbedding.restrictScalars_modelWithCorners (h : IsSmoothEmbedding I I' n f)
    (hn : 1 ≤ n) : IsSmoothEmbedding (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) n f :=
  ⟨h.isImmersion.restrictScalars_modelWithCorners 𝕜 hn, h.isEmbedding⟩

end General

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {N : Type*} [TopologicalSpace N]
  [ChartedSpace E' N] {n : ℕ∞ω} [IsManifold 𝓘(𝕜, E) n M] [IsManifold 𝓘(𝕜, E') n N]
  {f : M → N}

/-- A `C^n` immersion, `1 ≤ n`, for the trivial models over `𝕜'` is a `C^n` immersion for the
trivial models over the smaller field `𝕜`, if the target model is finite-dimensional over `𝕜`.
For instance, a holomorphic immersion of complex manifolds is a smooth immersion over `ℝ`. -/
theorem IsImmersion.restrictScalars (h : IsImmersion 𝓘(𝕜', E) 𝓘(𝕜', E') n f) (hn : 1 ≤ n) :
    IsImmersion 𝓘(𝕜, E) 𝓘(𝕜, E') n f := by
  have hc := h.contMDiff.restrictScalars' 𝕜
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine hc.isImmersion_of_injective_mfderiv hn fun x v w hvw ↦ h.mfderiv_injective hn0 x ?_
  have hd := (h.contMDiff x).mdifferentiableAt hn0
  exact (hd.mfderiv_modelWithCornersSelf_restrictScalars_apply 𝕜 v).symm.trans
    (hvw.trans (hd.mfderiv_modelWithCornersSelf_restrictScalars_apply 𝕜 w))

/-- A `C^n` embedding, `1 ≤ n`, for the trivial models over `𝕜'` is a `C^n` embedding for the
trivial models over the smaller field `𝕜`, if the target model is finite-dimensional over `𝕜`.
For instance, a holomorphic embedding of complex manifolds is a smooth embedding over `ℝ`. -/
theorem IsSmoothEmbedding.restrictScalars (h : IsSmoothEmbedding 𝓘(𝕜', E) 𝓘(𝕜', E') n f)
    (hn : 1 ≤ n) : IsSmoothEmbedding 𝓘(𝕜, E) 𝓘(𝕜, E') n f :=
  ⟨h.isImmersion.restrictScalars 𝕜 hn, h.isEmbedding⟩

section Prod

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [NormedSpace 𝕜' F']
  [IsScalarTower 𝕜 𝕜' F'] [FiniteDimensional 𝕜 F'] {N' : Type*} [TopologicalSpace N']
  [ChartedSpace F' N'] [IsManifold 𝓘(𝕜, F') n N'] {g : M → N × N'}

/-- A `C^n` immersion, `1 ≤ n`, into a product of manifolds, for the trivial model over `𝕜'` on
the source and the product of the trivial models over `𝕜'` on the target, is a `C^n` immersion
for the corresponding models over the smaller field `𝕜`, if both factors of the target model are
finite-dimensional over `𝕜`. For instance, a holomorphic immersion into a product of complex
manifolds is a smooth immersion over `ℝ`. -/
theorem IsImmersion.restrictScalars_prod
    (h : IsImmersion 𝓘(𝕜', E) (𝓘(𝕜', E').prod 𝓘(𝕜', F')) n g) (hn : 1 ≤ n) :
    IsImmersion 𝓘(𝕜, E) (𝓘(𝕜, E').prod 𝓘(𝕜, F')) n g := by
  have : IsManifold (𝓘(𝕜', E).restrictScalars 𝕜) n M := by
    simpa only [modelWithCornersSelf_restrictScalars] using
      (inferInstance : IsManifold 𝓘(𝕜, E) n M)
  have : IsManifold ((𝓘(𝕜', E').prod 𝓘(𝕜', F')).restrictScalars 𝕜) n (N × N') := by
    simpa only [ModelWithCorners.restrictScalars_prod, modelWithCornersSelf_restrictScalars] using
      (inferInstance : IsManifold (𝓘(𝕜, E').prod 𝓘(𝕜, F')) n (N × N'))
  simpa only [ModelWithCorners.restrictScalars_prod, modelWithCornersSelf_restrictScalars] using
    h.restrictScalars_modelWithCorners 𝕜 hn

/-- A `C^n` embedding, `1 ≤ n`, into a product of manifolds, for the trivial model over `𝕜'` on
the source and the product of the trivial models over `𝕜'` on the target, is a `C^n` embedding
for the corresponding models over the smaller field `𝕜`, if both factors of the target model are
finite-dimensional over `𝕜`. For instance, a holomorphic embedding into a product of complex
manifolds is a smooth embedding over `ℝ`. -/
theorem IsSmoothEmbedding.restrictScalars_prod
    (h : IsSmoothEmbedding 𝓘(𝕜', E) (𝓘(𝕜', E').prod 𝓘(𝕜', F')) n g) (hn : 1 ≤ n) :
    IsSmoothEmbedding 𝓘(𝕜, E) (𝓘(𝕜, E').prod 𝓘(𝕜, F')) n g :=
  ⟨h.isImmersion.restrictScalars_prod 𝕜 hn, h.isEmbedding⟩

end Prod

end Manifold

namespace TauCeti.SmoothEmbedding

variable (𝕜 : Type*) {𝕜' : Type*} [RCLike 𝕜] [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedSpace 𝕜' E']
  [IsScalarTower 𝕜 𝕜' E'] [FiniteDimensional 𝕜 E']
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {N : Type*} [TopologicalSpace N]
  [ChartedSpace E' N] {m n : ℕ∞ω} [IsManifold 𝓘(𝕜, E) n M] [IsManifold 𝓘(𝕜, E') n N]

/-- A `C^m` embedding for the trivial models over `𝕜'`, as a `C^n` embedding for the trivial
models over the smaller field `𝕜`, for `1 ≤ n ≤ m`, when the target model is finite-dimensional
over `𝕜`. The underlying map is that of `f` (`coe_restrictScalars`). For `𝕜 = ℝ` and `𝕜' = ℂ`,
this is the real form of a holomorphic embedding. -/
noncomputable def restrictScalars (f : SmoothEmbedding 𝓘(𝕜', E) 𝓘(𝕜', E') m M N) (hnm : n ≤ m)
    (hn : 1 ≤ n) : SmoothEmbedding 𝓘(𝕜, E) 𝓘(𝕜, E') n M N :=
  .ofIsSmoothEmbedding f ((f.isSmoothEmbedding.of_le hnm).restrictScalars 𝕜 hn)

variable {𝕜}

@[simp]
theorem coe_restrictScalars (f : SmoothEmbedding 𝓘(𝕜', E) 𝓘(𝕜', E') m M N) (hnm : n ≤ m)
    (hn : 1 ≤ n) : ⇑(f.restrictScalars 𝕜 hnm hn) = f :=
  coe_ofIsSmoothEmbedding _ _

theorem restrictScalars_apply (f : SmoothEmbedding 𝓘(𝕜', E) 𝓘(𝕜', E') m M N) (hnm : n ≤ m)
    (hn : 1 ≤ n) (x : M) : f.restrictScalars 𝕜 hnm hn x = f x :=
  ofIsSmoothEmbedding_apply _ _ x

/-- The derivative of `f.restrictScalars 𝕜 hnm hn` is, as a map of tangent vectors, the derivative
of `f` over `𝕜'`. For instance, the real derivative of the real form of a holomorphic embedding is
its complex derivative. -/
theorem coe_mfderiv_restrictScalars (f : SmoothEmbedding 𝓘(𝕜', E) 𝓘(𝕜', E') m M N)
    (hnm : n ≤ m) (hn : 1 ≤ n) (x : M) :
    ⇑(mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E') (f.restrictScalars 𝕜 hnm hn) x) =
      mfderiv 𝓘(𝕜', E) 𝓘(𝕜', E') f x := by
  have hd := (f.contMDiff x).mdifferentiableAt (ne_bot_of_le_ne_bot one_ne_zero (hn.trans hnm))
  rw [coe_restrictScalars]
  exact funext (hd.mfderiv_modelWithCornersSelf_restrictScalars_apply 𝕜)

/-- As sets of vectors of `E'`, the tangent ranges of `f.restrictScalars 𝕜 hnm hn` are those of
`f`. -/
theorem coe_tangentRange_restrictScalars (f : SmoothEmbedding 𝓘(𝕜', E) 𝓘(𝕜', E') m M N)
    (hnm : n ≤ m) (hn : 1 ≤ n) (x : M) (hn₀ : n ≠ 0) (hm₀ : m ≠ 0) :
    ((f.restrictScalars 𝕜 hnm hn).isImmersion.tangentRange x hn₀ :
        Set (TangentSpace 𝓘(𝕜, E') (f.restrictScalars 𝕜 hnm hn x))) =
      (f.isImmersion.tangentRange x hm₀ : Set (TangentSpace 𝓘(𝕜', E') (f x))) := by
  have h := congrFun (f.coe_mfderiv_restrictScalars (𝕜 := 𝕜) hnm hn x)
  ext v
  simp only [SetLike.mem_coe, Manifold.IsImmersion.mem_tangentRange_iff]
  exact exists_congr fun u ↦ iff_of_eq (congrArg (· = v) (h u))

/-- The tangent ranges of `f.restrictScalars 𝕜 hnm hn` are closed under multiplication by scalars
of the larger field `𝕜'`. -/
theorem smul_mem_tangentRange_restrictScalars (f : SmoothEmbedding 𝓘(𝕜', E) 𝓘(𝕜', E') m M N)
    (hnm : n ≤ m) (hn : 1 ≤ n) (x : M) (hn₀ : n ≠ 0) (c : 𝕜') {v : E'}
    (hv : v ∈ (f.restrictScalars 𝕜 hnm hn).isImmersion.tangentRange x hn₀) :
    c • v ∈ (f.restrictScalars 𝕜 hnm hn).isImmersion.tangentRange x hn₀ := by
  have h := congrFun (f.coe_mfderiv_restrictScalars (𝕜 := 𝕜) hnm hn x)
  obtain ⟨u, rfl⟩ := (Manifold.IsImmersion.mem_tangentRange_iff _ x hn₀ v).1 hv
  -- The witness lives in `TangentSpace 𝓘(𝕜, E) x`, which carries only the `𝕜`-structure.
  -- It and `TangentSpace 𝓘(𝕜', E) x` both unfold to `E`, so the `show`s let `c • u` use the
  -- `𝕜'`-action of `E`; rewriting at type `E'` instead fails on the mismatched instances.
  refine (Manifold.IsImmersion.mem_tangentRange_iff _ x hn₀ _).2 ⟨show E from c • show E from u, ?_⟩
  exact (h _).trans (((mfderiv 𝓘(𝕜', E) 𝓘(𝕜', E') f x).map_smul c u).trans
    (congrArg (c • ·) (h u).symm))

section Prod

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [NormedSpace 𝕜' F']
  [IsScalarTower 𝕜 𝕜' F'] [FiniteDimensional 𝕜 F'] {N' : Type*} [TopologicalSpace N']
  [ChartedSpace F' N'] [IsManifold 𝓘(𝕜, F') n N']

variable (𝕜) in
/-- A `C^m` embedding into a product, for the trivial model over `𝕜'` on the source and the
product of the trivial models over `𝕜'` on the target, as a `C^n` embedding for the corresponding
models over the smaller field `𝕜`, for `1 ≤ n ≤ m`, when both factors of the target model are
finite-dimensional over `𝕜`. The underlying map is that of `f` (`coe_restrictScalarsProd`). -/
noncomputable def restrictScalarsProd
    (f : SmoothEmbedding 𝓘(𝕜', E) (𝓘(𝕜', E').prod 𝓘(𝕜', F')) m M (N × N')) (hnm : n ≤ m)
    (hn : 1 ≤ n) : SmoothEmbedding 𝓘(𝕜, E) (𝓘(𝕜, E').prod 𝓘(𝕜, F')) n M (N × N') :=
  .ofIsSmoothEmbedding f ((f.isSmoothEmbedding.of_le hnm).restrictScalars_prod 𝕜 hn)

@[simp]
theorem coe_restrictScalarsProd
    (f : SmoothEmbedding 𝓘(𝕜', E) (𝓘(𝕜', E').prod 𝓘(𝕜', F')) m M (N × N')) (hnm : n ≤ m)
    (hn : 1 ≤ n) : ⇑(f.restrictScalarsProd 𝕜 hnm hn) = f :=
  coe_ofIsSmoothEmbedding _ _

theorem restrictScalarsProd_apply
    (f : SmoothEmbedding 𝓘(𝕜', E) (𝓘(𝕜', E').prod 𝓘(𝕜', F')) m M (N × N')) (hnm : n ≤ m)
    (hn : 1 ≤ n) (x : M) : f.restrictScalarsProd 𝕜 hnm hn x = f x :=
  ofIsSmoothEmbedding_apply _ _ x

/-- The derivative of `f.restrictScalarsProd 𝕜 hnm hn` is, as a map of tangent vectors, the
derivative of `f` over `𝕜'`. -/
theorem coe_mfderiv_restrictScalarsProd
    (f : SmoothEmbedding 𝓘(𝕜', E) (𝓘(𝕜', E').prod 𝓘(𝕜', F')) m M (N × N')) (hnm : n ≤ m)
    (hn : 1 ≤ n) (x : M) :
    ⇑(mfderiv 𝓘(𝕜, E) (𝓘(𝕜, E').prod 𝓘(𝕜, F')) (f.restrictScalarsProd 𝕜 hnm hn) x) =
      mfderiv 𝓘(𝕜', E) (𝓘(𝕜', E').prod 𝓘(𝕜', F')) f x := by
  have hd := (f.contMDiff x).mdifferentiableAt (ne_bot_of_le_ne_bot one_ne_zero (hn.trans hnm))
  rw [coe_restrictScalarsProd]
  exact funext (hd.mfderiv_modelWithCornersSelf_prod_restrictScalars_apply 𝕜)

/-- As sets of vectors of `E' × F'`, the tangent ranges of `f.restrictScalarsProd 𝕜 hnm hn` are
those of `f`. -/
theorem coe_tangentRange_restrictScalarsProd
    (f : SmoothEmbedding 𝓘(𝕜', E) (𝓘(𝕜', E').prod 𝓘(𝕜', F')) m M (N × N')) (hnm : n ≤ m)
    (hn : 1 ≤ n) (x : M) (hn₀ : n ≠ 0) (hm₀ : m ≠ 0) :
    ((f.restrictScalarsProd 𝕜 hnm hn).isImmersion.tangentRange x hn₀ :
        Set (TangentSpace (𝓘(𝕜, E').prod 𝓘(𝕜, F')) (f.restrictScalarsProd 𝕜 hnm hn x))) =
      (f.isImmersion.tangentRange x hm₀ : Set (TangentSpace (𝓘(𝕜', E').prod 𝓘(𝕜', F')) (f x))) := by
  have h := congrFun (f.coe_mfderiv_restrictScalarsProd (𝕜 := 𝕜) hnm hn x)
  ext v
  simp only [SetLike.mem_coe, Manifold.IsImmersion.mem_tangentRange_iff]
  exact exists_congr fun u ↦ iff_of_eq (congrArg (· = v) (h u))

/-- The tangent ranges of `f.restrictScalarsProd 𝕜 hnm hn` are closed under multiplication by
scalars of the larger field `𝕜'`. -/
theorem smul_mem_tangentRange_restrictScalarsProd
    (f : SmoothEmbedding 𝓘(𝕜', E) (𝓘(𝕜', E').prod 𝓘(𝕜', F')) m M (N × N')) (hnm : n ≤ m)
    (hn : 1 ≤ n) (x : M) (hn₀ : n ≠ 0) (c : 𝕜') {v : E' × F'}
    (hv : v ∈ (f.restrictScalarsProd 𝕜 hnm hn).isImmersion.tangentRange x hn₀) :
    c • v ∈ (f.restrictScalarsProd 𝕜 hnm hn).isImmersion.tangentRange x hn₀ := by
  have h := congrFun (f.coe_mfderiv_restrictScalarsProd (𝕜 := 𝕜) hnm hn x)
  obtain ⟨u, rfl⟩ := (Manifold.IsImmersion.mem_tangentRange_iff _ x hn₀ v).1 hv
  -- The witness lives in `TangentSpace 𝓘(𝕜, E) x`, which carries only the `𝕜`-structure.
  -- It and `TangentSpace 𝓘(𝕜', E) x` both unfold to `E`, so the `show`s let `c • u` use the
  -- `𝕜'`-action of `E`; rewriting at type `E'` instead fails on the mismatched instances.
  refine (Manifold.IsImmersion.mem_tangentRange_iff _ x hn₀ _).2 ⟨show E from c • show E from u, ?_⟩
  exact (h _).trans (((mfderiv 𝓘(𝕜', E) (𝓘(𝕜', E').prod 𝓘(𝕜', F')) f x).map_smul c u).trans
    (congrArg (c • ·) (h u).symm))

end Prod

end TauCeti.SmoothEmbedding

end
