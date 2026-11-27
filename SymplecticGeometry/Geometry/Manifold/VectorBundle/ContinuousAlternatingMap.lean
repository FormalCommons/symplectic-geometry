/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Topology.VectorBundle.FiniteDimensional
public import TauCeti.Analysis.Calculus.ContDiff.ContinuousAlternatingMap
public import TauCeti.Analysis.Normed.Module.Alternating.Curry
public import TauCeti.Geometry.Manifold.ContMDiff.ContinuousAlternatingMap
public import TauCeti.LinearAlgebra.BilinearMap.Multilinear
public import TauCeti.Topology.Algebra.Module.FiniteDimension
import SymplecticGeometry.Topology.Algebra.Module.BilinearForm
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic
import SymplecticGeometry.Topology.FiberBundle.Basic

/-!
# Precomposition, flat maps and bilinear maps in bundles of continuous alternating maps

For vector bundles `V₁`, `V₂` and `W` over `M` and a `C^n` section `L` of the bundle of
continuous linear maps `V₂ x →L V₁ x`, the map `α ↦ α ∘ L` from the total space of the bundle of
continuous alternating maps `V₁ x [⋀^ι]→L W x` to that of `V₂ x [⋀^ι]→L W x` is `C^n`
(`SymplecticGeometry.contMDiff_compContinuousLinearMap_totalSpace`). It holds for any arity `ι`
and any coefficient bundle `W`, and asks no regularity of the bundles themselves.

The proof reads the map in the fibre coordinates of the trivializations at a point, where it is
Tau Ceti's `ContinuousAlternatingMap.compContinuousLinearMapCLM`, a `C^n` map of the model spaces.

A section of the bundle of continuous alternating maps that reads as a constant in the
trivializations at each point, on the common base set of the trivializations at that point, is
`C^n` (`SymplecticGeometry.contMDiff_continuousAlternatingMap_bundle_of_inCoordinates_eq_const`).

The file also passes between alternating maps of two vectors and alternating bilinear maps on the
fibres, along a map `b : N → M` into the base, so that both a section over `M` (`b = id`) and a
point of a total space (`b` the projection) are covered:

* `Bundle.flatAt F α`: for an alternating map `α` of two vectors of `V x` with values in a normed
  space `G`, the continuous bilinear map `(v, w) ↦ α ![v, w]` (`Bundle.flatAt_apply`). The fibre
  carries no norm, so it is Tau Ceti's `ContinuousAlternatingMap.flatL` read through the fibre
  equivalence of `trivializationAt F V x`. By `SymplecticGeometry.contMDiffAt_sectionAlong_flatAt`,
  the flat maps of a `C^n` family of such maps along `b` form a `C^n` family along `b`.
* `Bundle.alternatingMapOfBilin F β hβ`: for a continuous bilinear map `β` on a fibre of finite
  dimension that vanishes on the diagonal, the continuous alternating map `v ↦ β (v 0) (v 1)`
  (`Bundle.alternatingMapOfBilin_apply`), with its two round trips with `flatAt`. By
  `SymplecticGeometry.contMDiffAt_sectionAlong_continuousAlternatingMap_of_bilinear`, a family of
  alternating maps along `b` whose values come from a `C^n` family of bilinear maps is `C^n`.

The coefficients of `flatAt` form the trivial bundle with fibre `G`, since the flat map is read
through a trivialization of `V` alone; the two-forms of this library take values in `ℝ`. The other
declarations allow any coefficient bundle `W`.

## Implementation notes

The proof of `contMDiffAt_sectionAlong_flatAt` is that of Tau Ceti's
`TauCeti.SmoothTwoForm.contMDiffAt_sectionAlong_flatL`
(`TauCeti/Geometry/Symplectic/Manifold/Flat.lean`) with the tangent bundle replaced by `V`. The
proof of `contMDiffAt_sectionAlong_continuousAlternatingMap_of_bilinear` is that of Tau Ceti's
`TauCeti.contMDiffAt_continuousAlternatingMap_bundle_of_bilinear`
(`TauCeti/Geometry/Manifold/VectorBundle/ContinuousAlternatingMap.lean`), its case `b = id`, with
the sections of that proof composed with `b`. The proof of
`SymplecticGeometry.contMDiff_continuousAlternatingMap_bundle_of_inCoordinates_eq_const` is that
of Tau Ceti's `TauCeti.contMDiff_hom_bundle_of_inCoordinates_eq_const`
(`TauCeti/Geometry/Manifold/VectorBundle/Hom.lean`), with the bundle of continuous linear maps
replaced by that of continuous alternating maps.
-/

public section

open Bundle
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] {I : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace M] [ChartedSpace HB M]
  {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {V₁ V₂ : M → Type*} [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, IsTopologicalAddGroup (V₁ x)]
  [∀ x, ContinuousSMul 𝕜 (V₁ x)] [TopologicalSpace (TotalSpace F₁ V₁)]
  [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]
  {ι G : Type*} [Fintype ι] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {W : M → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul 𝕜 (W x)] [TopologicalSpace (TotalSpace G W)]
  [FiberBundle G W] [VectorBundle 𝕜 G W] {n : ℕ∞}

namespace SymplecticGeometry

/-- Composing alternating maps on the fibres of `V₁` with a `C^n` family of linear maps
`L x : V₂ x → V₁ x` is a `C^n` map between the total spaces of the bundles of alternating maps
on `V₁` and on `V₂`. -/
theorem contMDiff_compContinuousLinearMap_totalSpace (L : ∀ x, V₂ x →L[𝕜] V₁ x)
    (hL : ContMDiff I (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₁)) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun x ↦ V₂ x →L[𝕜] V₁ x) x (L x))) :
    ContMDiff (I.prod 𝓘(𝕜, F₁ [⋀^ι]→L[𝕜] G)) (I.prod 𝓘(𝕜, F₂ [⋀^ι]→L[𝕜] G)) n
      (fun p : TotalSpace (F₁ [⋀^ι]→L[𝕜] G) (fun x ↦ V₁ x [⋀^ι]→L[𝕜] W x) ↦
        TotalSpace.mk' (F₂ [⋀^ι]→L[𝕜] G) (E := fun x ↦ V₂ x [⋀^ι]→L[𝕜] W x) p.proj
          (p.snd.compContinuousLinearMap (L p.proj))) := by
  intro p₀
  rw [contMDiffAt_continuousAlternatingMap_bundle]
  refine ⟨(contMDiff_proj _).contMDiffAt, ?_⟩
  have hp := (contMDiffAt_continuousAlternatingMap_bundle (IB := I) (ι := ι)
    (F₁ := F₁) (F₂ := G) (E₁ := V₁) (E₂ := W) (n := n) id (x₀ := p₀)).1 contMDiffAt_id
  have hl := ((contMDiffAt_hom_bundle _).1 (hL p₀.proj)).2.comp p₀
    (contMDiff_proj _).contMDiffAt
  have hc := ((ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM (𝕜 := 𝕜)
    (E := F₂) (F := F₁) (G := G) (ι := ι) n).contMDiff.contMDiffAt.comp p₀ hl).clm_apply hp.2
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [hp.1.continuousAt.eventually_mem_baseSet_trivializationAt F₁ V₁] with p hp
  ext v
  simp only [ContinuousAlternatingMap.inCoordinates, ContinuousLinearMap.inCoordinates,
    Function.comp_apply, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 2
  ext i
  simp only [Function.comp_apply, ContinuousLinearMap.coe_comp]
  exact (Trivialization.symmL_continuousLinearMapAt _ hp _).symm

omit [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul 𝕜 (V₁ x)] in
/-- A section of the bundle of continuous alternating maps `V₁ x [⋀^ι]→L W x` is `C^n` if, read
in the trivializations at each point `a`, it is a constant `c a` on the common base set of those
trivializations. The constant may depend on `a`, and no regularity of the bundles is needed. -/
theorem contMDiff_continuousAlternatingMap_bundle_of_inCoordinates_eq_const {n : WithTop ℕ∞}
    {ϕ : ∀ x, V₁ x [⋀^ι]→L[𝕜] W x} {c : M → F₁ [⋀^ι]→L[𝕜] G}
    (hϕ : ∀ a x, x ∈ (trivializationAt F₁ V₁ a).baseSet → x ∈ (trivializationAt G W a).baseSet →
      ContinuousAlternatingMap.inCoordinates F₁ G a x a x (ϕ x) = c a) :
    ContMDiff I (I.prod 𝓘(𝕜, F₁ [⋀^ι]→L[𝕜] G)) n
      (fun x ↦ TotalSpace.mk' (F₁ [⋀^ι]→L[𝕜] G) (E := fun x ↦ V₁ x [⋀^ι]→L[𝕜] W x) x (ϕ x)) := by
  intro a
  rw [contMDiffAt_continuousAlternatingMap_bundle]
  refine ⟨contMDiffAt_id, (contMDiffAt_const (c := c a)).congr_of_eventuallyEq ?_⟩
  filter_upwards [(trivializationAt F₁ V₁ a).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt F₁ V₁ a),
    (trivializationAt G W a).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt G W a)] with x hx₁ hx₂
  exact hϕ a x hx₁ hx₂

end SymplecticGeometry

/-! ### Flat maps and alternating bilinear maps on the fibres -/

section TwoForms

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN] [TopologicalSpace HN]
  {IN : ModelWithCorners 𝕜 EN HN} [TopologicalSpace N] [ChartedSpace HN N]

namespace Bundle

variable (F) in
/-- The flat map `v ↦ α(v, ·)` of an alternating map `α` of two vectors of the fibre `V x`, as a
continuous bilinear map `V x →L V x →L G`. The fibre carries no norm, so this is Tau Ceti's
`ContinuousAlternatingMap.flatL` read through the fibre equivalence of `trivializationAt F V x`;
`flatAt_apply` shows that the choice does not matter. -/
noncomputable def flatAt {x : M} (α : V x [⋀^Fin 2]→L[𝕜] Trivial M G x) :
    V x →L[𝕜] V x →L[𝕜] G :=
  let e := VectorBundle.continuousLinearEquivAt 𝕜 F V x
  e.symm.bilinearCongr (ContinuousAlternatingMap.flatL 𝕜 F G (α.compContinuousLinearMap e.symm))

/-- The flat map evaluates as the form: `α♭ v w = α ![v, w]`. -/
@[simp]
theorem flatAt_apply {x : M} (α : V x [⋀^Fin 2]→L[𝕜] Trivial M G x) (v w : V x) :
    flatAt F α v w = α ![v, w] := by
  simp only [flatAt, ContinuousLinearEquiv.bilinearCongr_apply, ContinuousLinearEquiv.symm_symm,
    ContinuousAlternatingMap.flatL_apply_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  ext i
  fin_cases i <;> simp [Trivialization.symm_apply_apply_mk _
    (FiberBundle.mem_baseSet_trivializationAt F V x)]

/-- The flat map of an alternating map vanishes on the diagonal: `α♭ v v = 0`. -/
theorem flatAt_apply_self {x : M} (α : V x [⋀^Fin 2]→L[𝕜] Trivial M G x) (v : V x) :
    flatAt F α v v = 0 := by
  simp [α.map_eq_zero_of_eq ![v, v] (i := 0) (j := 1) rfl (by decide)]

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)] [CompleteSpace 𝕜]
  [FiniteDimensional 𝕜 F]

variable (F) in
/-- The continuous alternating map `v ↦ β (v 0) (v 1)` of a continuous bilinear map `β` on a
fibre of a bundle of finite rank that vanishes on the diagonal, `β v v = 0`. -/
noncomputable def alternatingMapOfBilin {x : M} (β : V x →L[𝕜] V x →L[𝕜] W x)
    (hβ : ∀ v, β v v = 0) :
    V x [⋀^Fin 2]→L[𝕜] W x :=
  haveI := VectorBundle.finiteDimensional (R := 𝕜) (F := F) (E := V) x
  haveI := FiberBundle.t2Space (E := V) F x
  AlternatingMap.toContinuousAlternatingMap
    (LinearMap.IsAlt.toAlternatingMap (ω := β.toLinearMap₁₂) hβ)

/-- The alternating map of a bilinear map `β` takes the value `β (v 0) (v 1)` on `v`. -/
@[simp]
theorem alternatingMapOfBilin_apply {x : M} (β : V x →L[𝕜] V x →L[𝕜] W x)
    (hβ : ∀ v, β v v = 0) (v : Fin 2 → V x) :
    alternatingMapOfBilin F β hβ v = β (v 0) (v 1) :=
  by
  simp only [alternatingMapOfBilin, AlternatingMap.coe_toContinuousAlternatingMap]
  exact LinearMap.IsAlt.toAlternatingMap_apply _ v

/-- The flat map of the alternating map of a bilinear map `β` is `β`. -/
@[simp]
theorem flatAt_alternatingMapOfBilin {x : M} (β : V x →L[𝕜] V x →L[𝕜] Trivial M G x)
    (hβ : ∀ v, β v v = 0) : flatAt F (alternatingMapOfBilin F β hβ) = β := by
  ext v w
  simp

/-- The alternating map of the flat map of `α` is `α`. -/
@[simp]
theorem alternatingMapOfBilin_flatAt {x : M} (α : V x [⋀^Fin 2]→L[𝕜] Trivial M G x)
    (hα : ∀ v, flatAt F α v v = 0) : alternatingMapOfBilin F (flatAt F α) hα = α := by
  ext v w
  rw [alternatingMapOfBilin_apply, flatAt_apply]
  simp

end Bundle

namespace SymplecticGeometry

/-- **Flat maps along a map into the base.** Let `α y` be alternating maps of two vectors of the
fibres `V (b y)` along a map `b : N → M`, depending `C^n` on `y` at `y₀`. Then their flat maps
`v ↦ α y (v, ·)` depend `C^n` on `y` at `y₀`, as maps into the bundle of bilinear maps along
`b`. -/
theorem contMDiffAt_sectionAlong_flatAt {b : N → M}
    {α : ∀ y, V (b y) [⋀^Fin 2]→L[𝕜] Trivial M G (b y)} {y₀ : N}
    (hα : ContMDiffAt IN (I.prod 𝓘(𝕜, F [⋀^Fin 2]→L[𝕜] G)) n
      (fun y ↦ TotalSpace.mk' (F [⋀^Fin 2]→L[𝕜] G)
        (E := fun x ↦ V x [⋀^Fin 2]→L[𝕜] Trivial M G x) (b y) (α y)) y₀) :
    ContMDiffAt IN (I.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] G)) n
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] G)
        (E := fun x ↦ V x →L[𝕜] V x →L[𝕜] G) (b y) (Bundle.flatAt F (α y))) y₀ := by
  rw [contMDiffAt_hom_bundle]
  have hα' := (contMDiffAt_continuousAlternatingMap_bundle _).1 hα
  refine ⟨hα'.1, ?_⟩
  -- In coordinates, the flat map is `flatL` applied to the coordinate expression of the form.
  refine ((ContinuousAlternatingMap.flatL 𝕜 F G).contDiff.comp_contMDiffAt
    hα'.2).congr_of_eventuallyEq ?_
  filter_upwards [hα'.1.continuousAt.eventually_mem_baseSet_trivializationAt F V] with y
    (hy : b y ∈ (trivializationAt F V (b y₀)).baseSet)
  ext v w
  rw [inCoordinates_apply_eq₂ (E₃ := Trivial M G) hy hy (Set.mem_univ _), Function.comp_apply,
    ContinuousAlternatingMap.flatL_apply_apply, Bundle.flatAt_apply]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
    Trivial.continuousLinearMapAt_trivialization, ContinuousAlternatingMap.inCoordinates,
    ContinuousLinearMap.id_compContinuousAlternatingMap,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, LinearMap.id_coe, id_eq]
  congr 1
  ext i
  fin_cases i <;> exact (Trivialization.symmL_apply _ hy _).symm

omit [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul 𝕜 (V₁ x)] in
/-- **Alternating maps from bilinear maps, along a map into the base.** Let `α y` be alternating
maps of two vectors of the fibres `V₁ (b y)` along a map `b : N → M`, given by bilinear maps
`β y` as `α y v = β y (v 0) (v 1)`. If the `β y` depend `C^n` on `y` at `y₀`, so do the `α y`. -/
theorem contMDiffAt_sectionAlong_continuousAlternatingMap_of_bilinear [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 F₁] {b : N → M}
    {α : ∀ y, V₁ (b y) [⋀^Fin 2]→L[𝕜] W (b y)}
    {β : ∀ y, V₁ (b y) →L[𝕜] V₁ (b y) →L[𝕜] W (b y)} {y₀ : N}
    (hβ : ContMDiffAt IN (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₁ →L[𝕜] G)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₁ →L[𝕜] G)
        (E := fun x ↦ V₁ x →L[𝕜] V₁ x →L[𝕜] W x) (b y) (β y)) y₀)
    (hα : ∀ y v, α y v = β y (v 0) (v 1)) :
    ContMDiffAt IN (I.prod 𝓘(𝕜, F₁ [⋀^Fin 2]→L[𝕜] G)) n
      (fun y ↦ TotalSpace.mk' (F₁ [⋀^Fin 2]→L[𝕜] G)
        (E := fun x ↦ V₁ x [⋀^Fin 2]→L[𝕜] W x) (b y) (α y)) y₀ := by
  have hb : ContMDiffAt IN I n b y₀ := ((contMDiffAt_hom_bundle _).1 hβ).1
  rw [contMDiffAt_continuousAlternatingMap_bundle]
  refine ⟨hb, TauCeti.contMDiffAt_continuousAlternatingMap_apply.2 fun v ↦ ?_⟩
  let e := trivializationAt F₁ V₁ (b y₀)
  have he : b y₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F₁ V₁ (b y₀)
  -- The sections `x ↦ e.symm x (v i)` of `V₁` near `b y₀`, composed with `b`.
  have hs (i : Fin 2) : ContMDiffAt IN (I.prod 𝓘(𝕜, F₁)) n
      (fun y ↦ TotalSpace.mk' F₁ (b y) (e.symm (b y) (v i))) y₀ := by
    refine ContMDiffAt.comp (g := fun x ↦ TotalSpace.mk' F₁ x (e.symm x (v i))) y₀ ?_ hb
    rw [contMDiffAt_section_iff]
    refine (contMDiffAt_const (c := v i)).congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds he] with x hx
    exact congr(Prod.snd $(e.apply_mk_symm hx (v i)))
  have hc := (contMDiffAt_totalSpace_iff.1 (hβ.clm_bundle_apply₂ (hs 0) (hs 1))).2
  refine hc.congr_of_eventuallyEq ?_
  let e' := trivializationAt G W (b y₀)
  filter_upwards [hb.continuousAt.eventually_mem_baseSet_trivializationAt F₁ V₁,
    hb.continuousAt.eventually_mem_baseSet_trivializationAt G W] with y
    (hy : b y ∈ e.baseSet) (hy' : b y ∈ e'.baseSet)
  simp only [ContinuousAlternatingMap.inCoordinates,
    ContinuousLinearMap.compContinuousAlternatingMap_coe,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, hα, Function.comp_apply]
  rw [Trivialization.symmL_apply _ hy, Trivialization.symmL_apply _ hy]
  exact e'.continuousLinearMapAt_apply_of_mem 𝕜 hy' _

end SymplecticGeometry

end TwoForms

end
