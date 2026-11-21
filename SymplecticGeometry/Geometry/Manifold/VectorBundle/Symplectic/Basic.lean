/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Analysis.Calculus.ContDiff.ContinuousAlternatingMap
public import TauCeti.Analysis.Normed.Module.Alternating.Curry
public import TauCeti.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Map
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.LinearAlgebra.BilinearMap.Multilinear
public import TauCeti.Topology.Algebra.Module.BilinearForm
public import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Two-forms on a vector bundle

A two-form of regularity `C^n` on a real vector bundle `V → M` is a `C^n` section of Mathlib's
bundle of continuous alternating maps `V x [⋀^Fin 2]→L[ℝ] ℝ`
(`SymplecticGeometry.Bundle.ContMDiffTwoForm`). It is an `abbrev` of the type of sections, so the
module structure of `ContMDiffSection` applies to it. A symplectic structure on `V` is such a form
that is nondegenerate on every fibre (`ContMDiffTwoForm.IsNondegenerate`); it is a predicate, not
a new type, as for Tau Ceti's `TauCeti.SmoothTwoForm.IsNondegenerate` on the tangent bundle.

Nothing is assumed about the rank of `V` or the dimension of `M`, except where a proof needs it:
openness of nondegeneracy needs finite rank, and transport along an isomorphism of bundles needs
finite rank of its source, for Tau Ceti's `TauCeti.contMDiff_hom_bundle_iff`. A nondegenerate form
forces even rank, so no hypothesis on the rank is needed, and rank zero is allowed.

## Main definitions and results

* `ContMDiffTwoForm.bilinFormAt`: the bilinear form `(v, w) ↦ ω x ![v, w]` on the fibre `V x`.
* `ContMDiffTwoForm.flat` and `ContMDiffTwoForm.contMDiff_flat`: the flat map `v ↦ ω(v, ·)` at
  each point, a `C^n` section of the bundle of continuous bilinear forms on `V`.
* `ContMDiffTwoForm.IsNondegenerate`, with `isNondegenerate_iff_separatingLeft` and
  `IsNondegenerate.symplecticFormAt`, the Tau Ceti symplectic form on each fibre.
* `isOpen_setOf_nondegenerate`: for finite rank, the fibrewise nondegenerate alternating maps are
  open in the total space of the bundle of alternating maps.
* `ContMDiffTwoForm.const`: the constant form of a symplectic form on the fibre of a trivial
  bundle, which is nondegenerate.
* `ContMDiffTwoForm.pushforward`: the transport `ω ↦ ω(Φ⁻¹ ·, Φ⁻¹ ·)` along an isomorphism `Φ`
  of vector bundles, as a linear equivalence that preserves nondegeneracy. It is Tau Ceti's
  `ContMDiffSection.mapEquiv`, using `contMDiff_compContinuousLinearMap_totalSpace`: composing
  alternating maps with a `C^n` family of linear maps is `C^n` on total spaces.
* `ContMDiffTwoForm.tangentEquiv`: on the tangent bundle, smooth two-forms are Tau Ceti's
  `TauCeti.SmoothTwoForm`, with the same nondegenerate ones.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
  (symplectic vector bundles).
-/

public section

noncomputable section

open Bundle
open scoped Manifold

namespace SymplecticGeometry

namespace Bundle

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M]

section CompContinuousLinearMap

variable {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {V₁ V₂ : M → Type*} [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, IsTopologicalAddGroup (V₁ x)]
  [∀ x, ContinuousSMul ℝ (V₁ x)] [TopologicalSpace (TotalSpace F₁ V₁)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  {ι G : Type*} [Fintype ι] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {W : M → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul ℝ (W x)] [TopologicalSpace (TotalSpace G W)]
  [FiberBundle G W] [VectorBundle ℝ G W] {n : ℕ∞}

/-- Composing alternating maps on the fibres of `V₁` with a `C^n` family of linear maps
`L x : V₂ x → V₁ x` is a `C^n` map between the total spaces of the bundles of alternating maps
on `V₁` and on `V₂`. -/
theorem contMDiff_compContinuousLinearMap_totalSpace (L : ∀ x, V₂ x →L[ℝ] V₁ x)
    (hL : ContMDiff I (I.prod 𝓘(ℝ, F₂ →L[ℝ] F₁)) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[ℝ] F₁) (E := fun x ↦ V₂ x →L[ℝ] V₁ x) x (L x))) :
    ContMDiff (I.prod 𝓘(ℝ, F₁ [⋀^ι]→L[ℝ] G)) (I.prod 𝓘(ℝ, F₂ [⋀^ι]→L[ℝ] G)) n
      (fun p : TotalSpace (F₁ [⋀^ι]→L[ℝ] G) (fun x ↦ V₁ x [⋀^ι]→L[ℝ] W x) ↦
        TotalSpace.mk' (F₂ [⋀^ι]→L[ℝ] G) (E := fun x ↦ V₂ x [⋀^ι]→L[ℝ] W x) p.proj
          (p.snd.compContinuousLinearMap (L p.proj))) := by
  intro p₀
  rw [contMDiffAt_continuousAlternatingMap_bundle]
  refine ⟨(contMDiff_proj _).contMDiffAt, ?_⟩
  have hp := (contMDiffAt_continuousAlternatingMap_bundle (IB := I) (ι := ι)
    (F₁ := F₁) (F₂ := G) (E₁ := V₁) (E₂ := W) (n := n) id (x₀ := p₀)).1 contMDiffAt_id
  have hl := ((contMDiffAt_hom_bundle _).1 (hL p₀.proj)).2.comp p₀
    (contMDiff_proj _).contMDiffAt
  have hc := ((ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM (𝕜 := ℝ)
    (E := F₂) (F := F₁) (G := G) (ι := ι) n).contMDiff.contMDiffAt.comp p₀ hl).clm_apply hp.2
  refine hc.congr_of_eventuallyEq ?_
  have hmem : (trivializationAt F₁ V₁ p₀.proj).baseSet ∈ nhds p₀.proj :=
    (trivializationAt F₁ V₁ p₀.proj).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt F₁ V₁ p₀.proj)
  filter_upwards [hp.1.continuousAt.preimage_mem_nhds hmem] with p hp
  ext v
  simp only [ContinuousAlternatingMap.inCoordinates, ContinuousLinearMap.inCoordinates,
    Function.comp_apply, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 2
  ext i
  simp only [Function.comp_apply, ContinuousLinearMap.coe_comp]
  exact (Trivialization.symmL_continuousLinearMapAt _ hp _).symm

end CompContinuousLinearMap

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ∞}

/-- A `C^n` two-form on a vector bundle `V`: a `C^n` section of the bundle of continuous
alternating maps of two vectors from the fibres of `V` to `ℝ`. -/
abbrev ContMDiffTwoForm (I : ModelWithCorners ℝ EB HB) (n : ℕ∞) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] (V : M → Type*) [∀ x, AddCommGroup (V x)]
    [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
    [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle ℝ F V] :=
  Cₛ^n⟮I; F [⋀^Fin 2]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x⟯

namespace ContMDiffTwoForm

variable (ω : ContMDiffTwoForm I n F V)

/-- The bilinear form of a two-form on the fibre over `x`. -/
def bilinFormAt (x : M) : LinearMap.BilinForm ℝ (V x) :=
  MultilinearMap.toBilinMap (ω x).toMultilinearMap

/-- The bilinear form at `x` is the bilinear map of the value of `ω` at `x`. -/
theorem bilinFormAt_def (x : M) :
    ω.bilinFormAt x = MultilinearMap.toBilinMap (ω x).toMultilinearMap :=
  (rfl)

/-- The bilinear form at `x` evaluates as the form: `ω_x(v, w) = ω x ![v, w]`. -/
@[simp]
theorem bilinFormAt_apply (x : M) (v w : V x) : ω.bilinFormAt x v w = ω x ![v, w] :=
  MultilinearMap.toBilinMap_apply _ v w

/-- The bilinear form of a two-form on a fibre is alternating. -/
theorem isAlt_bilinFormAt (x : M) : (ω.bilinFormAt x).IsAlt :=
  AlternatingMap.isAlt_toBilinMap (ω x).toAlternatingMap

/-- The bilinear form of a sum of two-forms is the sum of their bilinear forms. -/
@[simp]
theorem bilinFormAt_add (ω' : ContMDiffTwoForm I n F V) (x : M) :
    (ω + ω').bilinFormAt x = ω.bilinFormAt x + ω'.bilinFormAt x := by
  ext v w
  simp

/-- The bilinear form of a scalar multiple of a two-form is the scalar multiple of its bilinear
form. -/
@[simp]
theorem bilinFormAt_smul (c : ℝ) (x : M) : (c • ω).bilinFormAt x = c • ω.bilinFormAt x := by
  ext v w
  simp

/-- The bilinear form of the negative of a two-form is the negative of its bilinear form. -/
@[simp]
theorem bilinFormAt_neg (x : M) : (-ω).bilinFormAt x = -ω.bilinFormAt x := by
  ext v w
  simp

/-! ### The flat map -/

/-- The flat map `v ↦ ω(v, ·)` of a two-form on the fibre over `x`, a point of the bundle of
continuous bilinear forms on `V`. The fibre carries no norm, so this is Tau Ceti's
`ContinuousAlternatingMap.flatL` read through the fibre coordinates of
`trivializationAt F V x`; `flat_apply` shows that the choice does not matter. -/
def flat (x : M) : V x →L[ℝ] V x →L[ℝ] ℝ :=
  let e := (trivializationAt F V x).continuousLinearEquivAt ℝ x
    (FiberBundle.mem_baseSet_trivializationAt F V x)
  (e.arrowCongr (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))).symm
    (ContinuousAlternatingMap.flatL ℝ F ℝ ((ω x).compContinuousLinearMap e.symm))

/-- The flat map evaluates as the form: `ω♭_x v w = ω_x(v, w)`. -/
@[simp]
theorem flat_apply (x : M) (v w : V x) : ω.flat x v w = ω x ![v, w] := by
  simp only [flat, ContinuousLinearEquiv.arrowCongr, ContinuousLinearEquiv.arrowCongrSL_symm_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousAlternatingMap.flatL_apply_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousLinearEquiv.refl_symm,
    ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_apply]
  congr 1
  ext i
  fin_cases i <;> simp [Trivialization.symm_apply_apply_mk _
    (FiberBundle.mem_baseSet_trivializationAt F V x)]

/-- The flat map at `x` is the continuous form of the bilinear form at `x`. -/
theorem toBilinForm_flat (x : M) : (ω.flat x).toBilinForm = ω.bilinFormAt x := by
  ext v w
  simp

/-- The flat maps of a `C^n` two-form form a `C^n` section of the bundle of continuous bilinear
forms on `V`. -/
theorem contMDiff_flat :
    ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) x (ω.flat x)) := by
  intro x₀
  rw [contMDiffAt_hom_bundle]
  have hω := (contMDiffAt_continuousAlternatingMap_bundle _).1 (ω.contMDiff x₀)
  refine ⟨contMDiffAt_id, ?_⟩
  refine ((ContinuousAlternatingMap.flatL ℝ F ℝ).contDiff.comp_contMDiffAt
    hω.2).congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt F V x₀).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt F V x₀)] with x hx
  ext v w
  rw [inCoordinates_apply_eq₂ (E₃ := Trivial M ℝ) hx hx (Set.mem_univ _), Function.comp_apply,
    ContinuousAlternatingMap.flatL_apply_apply, flat_apply]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
    Trivial.continuousLinearMapAt_trivialization, ContinuousAlternatingMap.inCoordinates,
    ContinuousLinearMap.id_compContinuousAlternatingMap,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, LinearMap.id_coe, id_eq]
  congr 1
  ext i
  fin_cases i <;> exact (Trivialization.symmL_apply _ hx _).symm

/-! ### Nondegeneracy -/

/-- A two-form on a vector bundle is nondegenerate when its bilinear form on every fibre is
nondegenerate. -/
def IsNondegenerate : Prop :=
  ∀ x, (ω.bilinFormAt x).Nondegenerate

variable {ω}

/-- A two-form is nondegenerate exactly when its bilinear form on each fibre is. -/
theorem isNondegenerate_def : ω.IsNondegenerate ↔ ∀ x, (ω.bilinFormAt x).Nondegenerate :=
  Iff.rfl

/-- A nondegenerate two-form is nondegenerate on the fibre over each point. -/
theorem IsNondegenerate.nondegenerate_bilinFormAt (h : ω.IsNondegenerate) (x : M) :
    (ω.bilinFormAt x).Nondegenerate :=
  h x

/-- Nondegeneracy in terms of the vectors that pair to zero with every vector. For an
alternating form this one-sided condition is enough. -/
theorem isNondegenerate_iff_separatingLeft :
    ω.IsNondegenerate ↔ ∀ x (v : V x), (∀ w, ω x ![v, w] = 0) → v = 0 := by
  refine forall_congr' fun x ↦ ?_
  refine ((ω.isAlt_bilinFormAt x).isRefl.nondegenerate_iff_separatingLeft).trans ?_
  simp only [LinearMap.SeparatingLeft, bilinFormAt_apply]

/-- A two-form is nondegenerate exactly when its bilinear form on each fibre has trivial kernel. -/
theorem isNondegenerate_iff_forall_ker_bilinFormAt_eq_bot :
    ω.IsNondegenerate ↔ ∀ x, LinearMap.ker (ω.bilinFormAt x) = ⊥ := by
  simp only [isNondegenerate_iff_separatingLeft, LinearMap.ker_eq_bot', LinearMap.ext_iff,
    bilinFormAt_apply, LinearMap.zero_apply]

/-- The negative of a nondegenerate two-form is nondegenerate. -/
theorem IsNondegenerate.neg (h : ω.IsNondegenerate) : (-ω).IsNondegenerate := by
  rw [isNondegenerate_iff_separatingLeft] at h ⊢
  exact fun x v hv ↦ h x v fun w ↦ by simpa using hv w

/-- The symplectic form on the fibre over `x` of a nondegenerate two-form. -/
def IsNondegenerate.symplecticFormAt (h : ω.IsNondegenerate) (x : M) :
    TauCeti.SymplecticForm (V x) where
  toBilinForm := ω.bilinFormAt x
  isAlt := ω.isAlt_bilinFormAt x
  nondegenerate := h x

/-- The symplectic form on a fibre evaluates as the two-form. -/
@[simp]
theorem IsNondegenerate.symplecticFormAt_apply (h : ω.IsNondegenerate) (x : M) (v w : V x) :
    h.symplecticFormAt x v w = ω x ![v, w] :=
  ω.bilinFormAt_apply x v w

end ContMDiffTwoForm

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
/-- On a bundle of finite rank, the alternating maps of two vectors on a fibre whose bilinear form
is nondegenerate form an open subset of the total space of the bundle of alternating maps. -/
theorem isOpen_setOf_nondegenerate [FiniteDimensional ℝ F] :
    IsOpen {p : TotalSpace (F [⋀^Fin 2]→L[ℝ] ℝ) (fun x ↦ V x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x) |
      LinearMap.BilinForm.Nondegenerate (MultilinearMap.toBilinMap p.snd.toMultilinearMap)} := by
  rw [isOpen_iff_mem_nhds]
  intro p₀ hp₀
  let e := trivializationAt (F [⋀^Fin 2]→L[ℝ] ℝ)
    (fun x ↦ V x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x) p₀.proj
  have hT : IsOpen {A : F [⋀^Fin 2]→L[ℝ] ℝ |
      LinearMap.BilinForm.Nondegenerate (MultilinearMap.toBilinMap A.toMultilinearMap)} :=
    TauCeti.isOpen_setOf_nondegenerate fun v w ↦ by
      simpa using continuous_eval_const ![v, w]
  -- In the fibre coordinates of `e`, a form becomes its pull-back by a linear equivalence.
  have key : ∀ q ∈ e.source,
      (LinearMap.BilinForm.Nondegenerate (MultilinearMap.toBilinMap q.snd.toMultilinearMap) ↔
        LinearMap.BilinForm.Nondegenerate
          (MultilinearMap.toBilinMap (e q).2.toMultilinearMap)) := by
    intro q hq
    have hy : q.proj ∈ (trivializationAt F V p₀.proj).baseSet := by
      simpa [e] using hq
    let L := ((trivializationAt F V p₀.proj).continuousLinearEquivAt ℝ q.proj hy).toLinearEquiv
    have heq : MultilinearMap.toBilinMap (e q).2.toMultilinearMap =
        LinearMap.BilinForm.congr L (MultilinearMap.toBilinMap q.snd.toMultilinearMap) := by
      ext v w
      simp only [e, FiberBundle.trivializationAt_continuousAlternatingMap_apply,
        ContinuousAlternatingMap.inCoordinates, MultilinearMap.toBilinMap_apply,
        LinearMap.BilinForm.congr_apply, Trivial.fiberBundle_trivializationAt',
        Trivial.continuousLinearMapAt_trivialization,
        ContinuousLinearMap.id_compContinuousAlternatingMap]
      change (q.snd.compContinuousLinearMap _) ![v, w] = q.snd ![L.symm v, L.symm w]
      rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
      congr 1
      ext i
      fin_cases i <;> simp [L, Trivialization.symmL_apply _ hy]
    rw [heq, LinearMap.BilinForm.nondegenerate_congr_iff]
  have hU := e.continuousOn.isOpen_inter_preimage e.open_source (hT.preimage continuous_snd)
  have hp₀e : p₀ ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
  refine Filter.mem_of_superset (hU.mem_nhds ⟨hp₀e, (key p₀ hp₀e).1 hp₀⟩) ?_
  rintro q ⟨hq, hq'⟩
  exact (key q hq).2 hq'

namespace ContMDiffTwoForm

/-! ### Constant forms on trivial bundles -/

section Const

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- The constant two-form on the trivial bundle `M × W` given by a symplectic form `σ` on the
finite-dimensional normed space `W`. For `σ = stdForm ι` this is the standard form on
`Trivial M (StdSpace ι)`. -/
def const (σ : TauCeti.SymplecticForm W) : ContMDiffTwoForm I n W (Trivial M W) where
  toFun _ := AlternatingMap.toContinuousAlternatingMap σ.isAlt.toAlternatingMap
  contMDiff_toFun x₀ := by
    rw [contMDiffAt_continuousAlternatingMap_bundle]
    refine ⟨contMDiffAt_id, (contMDiffAt_const (c := AlternatingMap.toContinuousAlternatingMap
      σ.isAlt.toAlternatingMap)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x ↦ ?_)⟩
    ext v
    simp [ContinuousAlternatingMap.inCoordinates]

/-- The constant form takes the value `σ(v 0, v 1)` at every point. -/
@[simp]
theorem const_apply (σ : TauCeti.SymplecticForm W) (x : M) (v : Fin 2 → W) :
    (const (I := I) (n := n) σ) x v = σ (v 0) (v 1) := by
  change AlternatingMap.toContinuousAlternatingMap _ v = _
  rw [AlternatingMap.coe_toContinuousAlternatingMap]
  exact LinearMap.IsAlt.toAlternatingMap_apply σ.isAlt v

/-- The bilinear form of the constant form at every point is `σ`. -/
@[simp]
theorem bilinFormAt_const (σ : TauCeti.SymplecticForm W) (x : M) :
    (const (I := I) (n := n) σ).bilinFormAt x = σ.toBilinForm := by
  ext v w
  simp

/-- The constant form of a symplectic form is nondegenerate. -/
theorem isNondegenerate_const (σ : TauCeti.SymplecticForm W) :
    (const (I := I) (n := n) (M := M) σ).IsNondegenerate := fun x ↦ by
  rw [bilinFormAt_const]
  exact σ.nondegenerate

end Const

/-! ### Transport along isomorphisms of bundles -/

section Pushforward

variable {F₁ F₂ F₃ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  {V₁ V₂ V₃ : M → Type*}
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, IsTopologicalAddGroup (V₁ x)]
  [∀ x, ContinuousSMul ℝ (V₁ x)] [TopologicalSpace (TotalSpace F₁ V₁)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul ℝ (V₂ x)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℝ (V₃ x)]
  [∀ x, TopologicalSpace (V₃ x)] [∀ x, IsTopologicalAddGroup (V₃ x)]
  [∀ x, ContinuousSMul ℝ (V₃ x)] [TopologicalSpace (TotalSpace F₃ V₃)]
  [FiberBundle F₃ V₃] [VectorBundle ℝ F₃ V₃]
  [FiniteDimensional ℝ F₁]
  (Φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
  (hΦ : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) n
    (fun p : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ p.proj (Φ p.proj p.snd)))

omit [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul ℝ (V₁ x)] in
include hΦ in
/-- A `C^n` fibrewise equivalence is a `C^n` section of the bundle of linear maps. -/
private theorem contMDiff_hom_of_equiv :
    ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := fun x ↦ V₁ x →L[ℝ] V₂ x) x
        (Φ x : V₁ x →L[ℝ] V₂ x)) :=
  (TauCeti.contMDiff_hom_bundle_iff (fun x ↦ (Φ x : V₁ x →L[ℝ] V₂ x))).2 hΦ

include hΦ in
/-- The fibrewise inverse of a `C^n` fibrewise equivalence is a `C^n` section of the bundle of
linear maps. -/
private theorem contMDiff_hom_of_equiv_symm :
    ContMDiff I (I.prod 𝓘(ℝ, F₂ →L[ℝ] F₁)) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[ℝ] F₁) (E := fun x ↦ V₂ x →L[ℝ] V₁ x) x
        ((Φ x).symm : V₂ x →L[ℝ] V₁ x)) := by
  have := FiniteDimensional.completeSpace ℝ F₁
  simpa only [ContinuousLinearMap.inverse_equiv] using
    (contMDiff_hom_of_equiv Φ hΦ).clm_bundle_inverse
      fun _ ↦ ContinuousLinearMap.isInvertible_equiv

/-- The fibrewise map `ω ↦ ω ∘ (Φ⁻¹ × Φ⁻¹)` of alternating maps, as a linear equivalence. -/
private def pushforwardFiber (x : M) :
    (V₁ x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x) ≃ₗ[ℝ] (V₂ x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x) where
  toFun ω := ω.compContinuousLinearMap ((Φ x).symm : V₂ x →L[ℝ] V₁ x)
  invFun ω := ω.compContinuousLinearMap (Φ x : V₁ x →L[ℝ] V₂ x)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/-- The transport `ω ↦ ω(Φ⁻¹ ·, Φ⁻¹ ·)` of two-forms along a `C^n` isomorphism of vector
bundles `Φ`, given by fibrewise equivalences whose map of total spaces is `C^n`. -/
def pushforward : ContMDiffTwoForm I n F₁ V₁ ≃ₗ[ℝ] ContMDiffTwoForm I n F₂ V₂ :=
  ContMDiffSection.mapEquiv (pushforwardFiber Φ)
    (contMDiff_compContinuousLinearMap_totalSpace _ (contMDiff_hom_of_equiv_symm Φ hΦ))
    (contMDiff_compContinuousLinearMap_totalSpace _ (contMDiff_hom_of_equiv Φ hΦ))

/-- The transported form at `x` is `ω_x(Φ_x⁻¹ ·, Φ_x⁻¹ ·)`. -/
@[simp]
theorem pushforward_apply (ω : ContMDiffTwoForm I n F₁ V₁) (x : M) :
    pushforward Φ hΦ ω x = (ω x).compContinuousLinearMap ((Φ x).symm : V₂ x →L[ℝ] V₁ x) :=
  ContMDiffSection.mapEquiv_apply _ _ _ ω x

/-- The inverse transport pulls a form back by `Φ`: its value at `x` is `ω_x(Φ_x ·, Φ_x ·)`. -/
@[simp]
theorem pushforward_symm_apply (ω : ContMDiffTwoForm I n F₂ V₂) (x : M) :
    (pushforward Φ hΦ).symm ω x = (ω x).compContinuousLinearMap (Φ x : V₁ x →L[ℝ] V₂ x) := by
  have h := congr($((pushforward Φ hΦ).apply_symm_apply ω) x)
  rw [pushforward_apply] at h
  rw [← h]
  ext v
  simp

/-- The bilinear form of the transported form at `x` is the bilinear form of `ω` moved along `Φ
x`. -/
theorem bilinFormAt_pushforward (ω : ContMDiffTwoForm I n F₁ V₁) (x : M) :
    (pushforward Φ hΦ ω).bilinFormAt x =
      LinearMap.BilinForm.congr (Φ x).toLinearEquiv (ω.bilinFormAt x) := by
  ext u v
  simp only [bilinFormAt_apply, pushforward_apply, LinearMap.BilinForm.congr_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- A two-form is nondegenerate exactly when its transport along an isomorphism of bundles is. -/
theorem isNondegenerate_pushforward_iff {ω : ContMDiffTwoForm I n F₁ V₁} :
    (pushforward Φ hΦ ω).IsNondegenerate ↔ ω.IsNondegenerate :=
  forall_congr' fun x ↦ by
    rw [bilinFormAt_pushforward, LinearMap.BilinForm.nondegenerate_congr_iff]

/-- Transport along an isomorphism of bundles preserves nondegeneracy. -/
theorem IsNondegenerate.pushforward {ω : ContMDiffTwoForm I n F₁ V₁} (h : ω.IsNondegenerate) :
    (ContMDiffTwoForm.pushforward Φ hΦ ω).IsNondegenerate :=
  (isNondegenerate_pushforward_iff Φ hΦ).2 h

omit [FiniteDimensional ℝ F₁] in
/-- Transport along the identity is the identity. -/
@[simp]
theorem pushforward_refl [FiniteDimensional ℝ F]
    (h : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) n
      (fun p : TotalSpace F V ↦
        TotalSpace.mk' F p.proj (ContinuousLinearEquiv.refl ℝ (V p.proj) p.snd))) :
    pushforward (fun x ↦ ContinuousLinearEquiv.refl ℝ (V x)) h =
      LinearEquiv.refl ℝ (ContMDiffTwoForm I n F V) := by
  ext ω x v
  simp

/-- Transport along a composite of isomorphisms is the composite of the transports. -/
theorem pushforward_trans [FiniteDimensional ℝ F₂] (Ψ : ∀ x, V₂ x ≃L[ℝ] V₃ x)
    (hΨ : ContMDiff (I.prod 𝓘(ℝ, F₂)) (I.prod 𝓘(ℝ, F₃)) n
      (fun p : TotalSpace F₂ V₂ ↦ TotalSpace.mk' F₃ p.proj (Ψ p.proj p.snd)))
    (h : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₃)) n
      (fun p : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₃ p.proj (((Φ p.proj).trans (Ψ p.proj)) p.snd))) :
    pushforward (fun x ↦ (Φ x).trans (Ψ x)) h =
      (pushforward Φ hΦ).trans (pushforward Ψ hΨ) := by
  ext ω x v
  simp [Function.comp_def]

end Pushforward

/-! ### Two-forms on the tangent bundle -/

section Tangent

variable [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- On the tangent bundle, smooth two-forms in the sense of this file are Tau Ceti's smooth
two-forms `TauCeti.SmoothTwoForm`. -/
def tangentEquiv :
    ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := M)) ≃ₗ[ℝ] TauCeti.SmoothTwoForm I M where
  toFun ω := TauCeti.SmoothForm.ofContMDiffSection ω
  invFun φ := φ.toContMDiffSection
  map_add' ω ω' := TauCeti.SmoothForm.toContMDiffSection_injective (by simp)
  map_smul' c ω := TauCeti.SmoothForm.toContMDiffSection_injective (by simp)
  left_inv ω := TauCeti.SmoothForm.toContMDiffSection_ofContMDiffSection ω
  right_inv φ := TauCeti.SmoothForm.ofContMDiffSection_toContMDiffSection φ

/-- The Tau Ceti form of a two-form on the tangent bundle has the same values. -/
@[simp]
theorem tangentEquiv_apply (ω : ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := M))) (x : M) :
    (tangentEquiv ω).val x = ω x := by
  rw [← TauCeti.SmoothForm.toContMDiffSection_apply]
  exact congr($(TauCeti.SmoothForm.toContMDiffSection_ofContMDiffSection ω) x)

/-- The two-form of a Tau Ceti smooth two-form has the same values. -/
@[simp]
theorem tangentEquiv_symm_apply (φ : TauCeti.SmoothTwoForm I M) (x : M) :
    tangentEquiv.symm φ x = φ.val x :=
  TauCeti.SmoothForm.toContMDiffSection_apply φ x

/-- A two-form on the tangent bundle is nondegenerate exactly when the corresponding Tau Ceti
two-form is. -/
@[simp]
theorem isNondegenerate_tangentEquiv_iff {ω : ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := M))} :
    (tangentEquiv ω).IsNondegenerate ↔ ω.IsNondegenerate := by
  simp [TauCeti.SmoothTwoForm.isNondegenerate_iff_separatingLeft,
    isNondegenerate_iff_separatingLeft, TauCeti.SmoothBundleForm.eval₂_apply]

end Tangent

end ContMDiffTwoForm

end Bundle

end SymplecticGeometry
