/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.RestrictScalars
import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Restricting the scalars of `C^n` sections and coordinate changes

Let `𝕜'` be a normed algebra over `𝕜`, and let `B` be a manifold modelled on a normed space `EB`
over both fields. Tau Ceti's `ContMDiffSection.restrictScalars` regards a `C^n` section of a fibre
bundle over `B`, for a boundaryless model `IB` over `𝕜'`, as a `C^n` section for the model
`IB.restrictScalars 𝕜`. This file states it for the model `𝓘(𝕜', EB)`, whose restriction is
`𝓘(𝕜, EB)` by `modelWithCornersSelf_restrictScalars`, with the model `𝓘(𝕜, EB)` itself in the
type of the section. Tau Ceti's `ContMDiffVectorBundle.restrictScalars_modelWithCornersSelf` gives
the bundle the matching `C^n` structure over `𝕜`.

The main example is a holomorphic section of a holomorphic vector bundle over a complex manifold,
which is a smooth section of the underlying real vector bundle over the underlying real manifold.

Conversely, let `E` be a vector bundle over `𝕜'` with finite-dimensional model `F`, which is also a
vector bundle over the complete field `𝕜` with the same trivializations, and is `C^n` over `𝕜`, for
a model over `𝕜`. Then its coordinate changes over `𝕜'` are `C^n` over `𝕜`
(`contMDiffOn_coordChangeL_of_restrictScalars`): restricting their scalars gives the coordinate
changes over `𝕜` (`Bundle.Trivialization.restrictScalars_coordChangeL`), and in finite dimension a
family of `𝕜'`-linear maps is `C^n` over `𝕜` as soon as its scalar restriction is
(`contMDiffOn_clm_restrictScalars_iff`). The main example is a complex vector
bundle whose underlying real bundle is smooth.

In the same way, a family of continuous `𝕜'`-linear maps `φ x : E x →L[𝕜'] E' x` between vector
bundles over `𝕜'`, with models finite-dimensional over `𝕜`, whose map of total spaces is `C^n` over
`𝕜` along the fibre over a point, has coordinate expressions in the trivializations at that point
that are `C^n` over `𝕜` there
(`contMDiffAt_continuousLinearMapAt_comp_symmL_of_restrictScalars`). Here neither bundle needs a
`C^n` structure. The proof that the scalar restrictions of these expressions are `C^n` follows
Tau Ceti's `TauCeti.contMDiffAt_hom_bundle_prod_iff`, read on a constant section.

## Main results

* `ContMDiffSection.restrictScalars'`: a `C^n` section for the model `𝓘(𝕜', EB)`, as a `C^n`
  section for the model `𝓘(𝕜, EB)`.
* `contMDiffOn_coordChangeL_of_restrictScalars`: the coordinate changes over `𝕜'` of a bundle
  with finite-dimensional model that is `C^n` over `𝕜` are `C^n` over `𝕜`.
* `contMDiffAt_continuousLinearMapAt_comp_symmL_of_restrictScalars`: the coordinate expressions
  over `𝕜'` at a point of a fibrewise linear map that is `C^n` over `𝕜` along the fibre over that
  point are `C^n` over `𝕜` there.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Section 2.2.
-/

public section

open Bundle
open scoped Manifold

section Section

variable (𝕜 : Type*) {𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [NormedSpace 𝕜' EB] [IsScalarTower 𝕜 𝕜' EB] {B : Type*} [TopologicalSpace B]
  [ChartedSpace EB B] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E] {n : WithTop ℕ∞}

namespace ContMDiffSection

/-- A `C^n` section for the model `𝓘(𝕜', EB)`, as a `C^n` section for the model `𝓘(𝕜, EB)` over
the smaller field `𝕜`. For instance, a holomorphic section of a holomorphic vector bundle, as a
smooth section of the underlying real vector bundle. -/
def restrictScalars' (s : ContMDiffSection 𝓘(𝕜', EB) F n E) :
    ContMDiffSection 𝓘(𝕜, EB) F n E where
  toFun := s
  contMDiff_toFun := by
    simpa only [modelWithCornersSelf_restrictScalars, coe_restrictScalars] using
      (s.restrictScalars 𝕜).contMDiff

/-- Restricting the scalars does not change the underlying section. -/
@[simp]
theorem coe_restrictScalars' (s : ContMDiffSection 𝓘(𝕜', EB) F n E) :
    ⇑(s.restrictScalars' 𝕜) = s :=
  (rfl)

/-- The value of a section with its scalars restricted is that of the section. -/
theorem restrictScalars'_apply (s : ContMDiffSection 𝓘(𝕜', EB) F n E) (x : B) :
    s.restrictScalars' 𝕜 x = s x :=
  (rfl)

end ContMDiffSection

end Section

section CoordChange

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {n : WithTop ℕ∞}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜' F] [NormedSpace 𝕜 F] [IsScalarTower 𝕜 𝕜' F]
  [FiniteDimensional 𝕜 F] {E : B → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜' (E x)]
  [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜' F E] [VectorBundle 𝕜 F E] [ContMDiffVectorBundle n F E IB]

/-- For a vector bundle over `𝕜'` with finite-dimensional model, which is a `C^n` vector bundle
over the smaller field `𝕜` with the same trivializations, the coordinate changes over `𝕜'` are
`C^n` over `𝕜`. For instance, the complex coordinate changes of a complex vector bundle whose
underlying real bundle is smooth are smooth. -/
theorem contMDiffOn_coordChangeL_of_restrictScalars (e e' : Trivialization F (π F E))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] :
    ContMDiffOn IB 𝓘(𝕜, F →L[𝕜'] F) n (fun b ↦ (e.coordChangeL 𝕜' e' b : F →L[𝕜'] F))
      (e.baseSet ∩ e'.baseSet) :=
  contMDiffOn_clm_restrictScalars_iff.1 <| (contMDiffOn_coordChangeL (IB := IB) e e').congr
    fun _ _ ↦ Trivialization.restrictScalars_coordChangeL 𝕜 𝕜' e e'

end CoordChange


section Coordinates

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {n : WithTop ℕ∞}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜' F] [NormedSpace 𝕜 F] [IsScalarTower 𝕜 𝕜' F]
  [FiniteDimensional 𝕜 F] {E : B → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜' (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜' F E]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜' F'] [NormedSpace 𝕜 F']
  [IsScalarTower 𝕜 𝕜' F'] [FiniteDimensional 𝕜 F'] {E' : B → Type*}
  [∀ x, AddCommMonoid (E' x)] [∀ x, Module 𝕜' (E' x)] [∀ x, TopologicalSpace (E' x)]
  [TopologicalSpace (TotalSpace F' E')] [FiberBundle F' E'] [VectorBundle 𝕜' F' E']

/-- **A `C^n` fibrewise linear map has `C^n` coordinates.** Let `φ x : E x →L[𝕜'] E' x` be
continuous linear maps of the fibres of two vector bundles over `𝕜'`, whose models are
finite-dimensional over the smaller complete field `𝕜`. If the map of total spaces induced by `φ`
is `C^n` over `𝕜` at each point of the fibre over `a`, then its expression `t' ∘ φ x ∘ t⁻¹` in
the trivializations `t`, `t'` at `a` is a family of continuous `𝕜'`-linear maps `F → F'` that is
`C^n` over `𝕜` at `a`. Neither bundle needs a `C^n` structure: smoothness on total spaces is read
in the charts of the trivializations. -/
theorem contMDiffAt_continuousLinearMapAt_comp_symmL_of_restrictScalars
    (φ : ∀ x, E x →L[𝕜'] E' x) (a : B)
    (hφ : ∀ v : E a, ContMDiffAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F')) n
      (fun p : TotalSpace F E ↦ TotalSpace.mk' F' p.proj (φ p.proj p.snd)) ⟨a, v⟩) :
    ContMDiffAt IB 𝓘(𝕜, F →L[𝕜'] F') n
      (fun x ↦ ((trivializationAt F' E' a).continuousLinearMapAt 𝕜' x).comp
        ((φ x).comp ((trivializationAt F E a).symmL 𝕜' x))) a := by
  set t := trivializationAt F E a
  set t' := trivializationAt F' E' a
  have ht : a ∈ t.baseSet := mem_baseSet_trivializationAt F E a
  have ht' : a ∈ t'.baseSet := mem_baseSet_trivializationAt F' E' a
  -- It suffices that the scalar restrictions of the expressions are `C^n`, applied to each `w`.
  refine contMDiffAt_clm_restrictScalars_iff.1 (TauCeti.contMDiffAt_clm_apply.2 fun w ↦ ?_)
  -- The section `x ↦ t.symm x w` is `C^n` near `a`: read in `t`, it is constant.
  have hs : ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t.symm x w)) a := by
    rw [contMDiffAt_section_iff]
    refine (contMDiffAt_const (c := w)).congr_of_eventuallyEq ?_
    filter_upwards [t.open_baseSet.mem_nhds ht] with x hx
    exact congr(Prod.snd $(t.apply_mk_symm hx w))
  -- Applying `φ` to this section and reading the result in `t'` gives the coordinate expression.
  have h := (contMDiffAt_totalSpace_iff.1 ((hφ _).comp a hs)).2
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [t.open_baseSet.mem_nhds ht, t'.open_baseSet.mem_nhds ht'] with x hx hx'
  simp [t, t', t.symmL_apply hx, Trivialization.continuousLinearMapAt_apply_of_mem 𝕜' t' hx']

end Coordinates

end
