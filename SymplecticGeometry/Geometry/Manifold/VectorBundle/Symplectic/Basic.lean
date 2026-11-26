/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import SymplecticGeometry.Topology.FiberBundle.Basic
public import SymplecticGeometry.Topology.VectorBundle.Frame
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hom
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Section
public import TauCeti.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Map.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Trivial
public import TauCeti.Geometry.Symplectic.SymplecticTransport
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import TauCeti.LinearAlgebra.BilinearMap.Multilinear
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic
public import SymplecticGeometry.Topology.Algebra.Module.BilinearForm
public import TauCeti.Topology.Algebra.Module.FiniteDimension
import SymplecticGeometry.LinearAlgebra.Symplectic.Darboux
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Matrix
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity

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
finite rank of its source, for Tau Ceti's `TauCeti.contMDiff_hom_bundle_iff`. No statement needs the
rank to be even (for finite rank, a nondegenerate form forces it), and rank zero is allowed.

## Main definitions and results

* `ContMDiffTwoForm.bilinFormAt`: the bilinear form `(v, w) ↦ ω x ![v, w]` on the fibre `V x`.
* `ContMDiffTwoForm.flat` and `ContMDiffTwoForm.contMDiff_flat`: the flat map `v ↦ ω(v, ·)` at
  each point, a `C^n` section of the bundle of continuous bilinear forms on `V`; and
  `ContMDiffTwoForm.contMDiffOn_bilinFormAt` and `ContMDiffTwoForm.contMDiff_bilinFormAt`:
  pairing `C^n` sections with `ω` gives a `C^n` function.
* `ContMDiffTwoForm.IsNondegenerate`, with `isNondegenerate_iff_separatingLeft` and
  `IsNondegenerate.symplecticFormAt`, the Tau Ceti symplectic form on each fibre.
* `isOpen_setOf_nondegenerate`: for finite rank, the fibrewise nondegenerate alternating maps are
  open in the total space of the bundle of alternating maps.
* `ContMDiffTwoForm.ofBilinearSection`: for finite rank, the two-form of a `C^n` bilinear section
  that vanishes on the diagonal.
* `ContMDiffTwoForm.const`: the constant form of a symplectic form on the fibre of a trivial
  bundle, which is nondegenerate.
* `ContMDiffTwoForm.pushforward`: the transport `ω ↦ ω(Φ⁻¹ ·, Φ⁻¹ ·)` along an isomorphism `Φ`
  of vector bundles, as a linear equivalence that preserves nondegeneracy. It is Tau Ceti's
  `ContMDiffSection.mapEquiv`, with smoothness on total spaces from
  `contMDiff_compContinuousLinearMap_totalSpace` and `contMDiff_hom_bundle_symm`.
* `ContMDiffTwoForm.compContinuousLinearMap`: the pull-back `ω ↦ ω(L ·, L ·)` along a `C^n`
  family of linear maps `L` between bundles, which need not be invertible.
* `ContMDiffTwoForm.tangentEquiv`: on the tangent bundle, smooth two-forms are Tau Ceti's
  `TauCeti.SmoothTwoForm`, with the same nondegenerate ones.
* `ContMDiffTwoForm.pushforward_eq_iff`: an isomorphism `Φ` of bundles transports `ω₁` to `ω₂`
  exactly when `ω₂(Φ v, Φ w) = ω₁(v, w)` on every fibre. Symplectic isomorphisms are stated in
  this unbundled form.
* `ContMDiffTwoForm.IsSymplecticFrameOn`: a `C^n` family of linear equivalences from a model
  symplectic vector space `(W, σ)` to the fibres over a set `U`, carrying `σ` to `ω`; with
  `isSymplecticFrameOn_const` on trivial bundles.
* `ContMDiffTwoForm.exists_isSymplecticFrameOn_of_darboux`: sections `aᵢ`, `bᵢ` (`i : κ`) of a
  bundle of rank `2 |κ|` that are `C^n` on a set `U` and satisfy the Darboux relations at every
  point of `U` give a symplectic frame over `U` for `stdForm κ`, which is
  `(x, y) ↦ ∑ᵢ (xᵢ aᵢ + yᵢ bᵢ)` on the fibres over `U`.
* `Bundle.frameTransition` (of `Topology/VectorBundle/Frame.lean`), the transition map `Φ'ₓ⁻¹ ∘ Φₓ`
  between two frames: over an open set it depends `C^n` on the point when both frames do
  (`Bundle.contMDiffOn_frameTransition`), and for
  symplectic frames it is a linear symplectomorphism of `(W, σ)`
  (`IsSymplecticFrameOn.isSymplectomorphism_frameTransition`,
  `IsSymplecticFrameOn.contMDiffOn_frameTransition`).
* `ContMDiffTwoForm.IsSymplecticFrameOn.exists_frameTransition`: two symplectic frames for
  `stdForm κ` differ, along a continuous map into the intersection of their open sets, by a
  continuous map into the symplectic matrices `TauCeti.GLSymplectic κ ℝ`.
* `ContMDiffTwoForm.exists_pushforward_eq_of_frameTransition_eq`: symplectic frames of two forms
  over the two sets of an open cover, with equal transition maps on the overlap, give a symplectic
  isomorphism between the forms; its smoothness over each set is
  `Bundle.contMDiffOn_totalSpaceMk_symm_trans`.
* `ContMDiffTwoForm.isNondegenerate_iff_forall_ne_zero_of_finrank_eq_two`: on a bundle of rank
  two, a two-form is nondegenerate exactly when it vanishes nowhere.

## Implementation notes

This file carries Tau Ceti's two-forms on the tangent bundle over to an arbitrary vector bundle.
At each point, the flat map and the two-form of a bilinear section are the maps
`Bundle.flatAt` and `Bundle.alternatingMapOfBilin` of
`Geometry/Manifold/VectorBundle/ContinuousAlternatingMap.lean`, and their smoothness is the case
`b = id` of the lemmas there. The constant form `ContMDiffTwoForm.const` is smooth by
`contMDiff_continuousAlternatingMap_bundle_of_inCoordinates_eq_const` from the same file, since
in the trivializations of a trivial bundle it reads as `σ` everywhere. The nondegeneracy
API adapts Tau Ceti's for
`TauCeti.SmoothTwoForm.IsNondegenerate` (`TauCeti/Geometry/Symplectic/Manifold/TwoForm.lean`).
The rank-two criterion `isNondegenerate_iff_forall_ne_zero_of_finrank_eq_two` takes over the
fibrewise step of `TauCeti.SmoothTwoForm.isNondegenerate_iff_forall_ne_zero_of_finrank_eq_two`
(`TauCeti/Geometry/Symplectic/Manifold/Surface.lean`).

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

/-- The bilinear form of the zero two-form is zero. -/
@[simp]
theorem bilinFormAt_zero (x : M) : (0 : ContMDiffTwoForm I n F V).bilinFormAt x = 0 := by
  ext v w
  simp

/-- The bilinear form of the negative of a two-form is the negative of its bilinear form. -/
@[simp]
theorem bilinFormAt_neg (x : M) : (-ω).bilinFormAt x = -ω.bilinFormAt x := by
  ext v w
  simp

/-- The bilinear form of a difference of two-forms is the difference of their bilinear forms. -/
@[simp]
theorem bilinFormAt_sub (ω' : ContMDiffTwoForm I n F V) (x : M) :
    (ω - ω').bilinFormAt x = ω.bilinFormAt x - ω'.bilinFormAt x := by
  ext v w
  simp

/-- On a fibre, two two-forms have the same bilinear form exactly when they agree there. -/
@[simp]
theorem bilinFormAt_inj (ω' : ContMDiffTwoForm I n F V) (x : M) :
    ω.bilinFormAt x = ω'.bilinFormAt x ↔ ω x = ω' x :=
  ⟨fun h ↦ ContinuousAlternatingMap.toAlternatingMap_injective <|
    AlternatingMap.coe_multilinearMap_injective <| MultilinearMap.toBilinMap_injective h,
    fun h ↦ by rw [bilinFormAt_def, bilinFormAt_def, h]⟩

variable {ω} in
/-- Two-forms with the same bilinear form on every fibre are equal. -/
theorem ext_bilinFormAt {ω' : ContMDiffTwoForm I n F V}
    (h : ∀ x, ω.bilinFormAt x = ω'.bilinFormAt x) : ω = ω' :=
  ContMDiffSection.ext fun x ↦ (bilinFormAt_inj ω ω' x).1 (h x)

/-- The bilinear form of a two-form vanishes on a fibre exactly when the form vanishes there. -/
@[simp]
theorem bilinFormAt_eq_zero_iff (x : M) : ω.bilinFormAt x = 0 ↔ ω x = 0 := by
  rw [← bilinFormAt_zero (I := I) (n := n) (F := F) x, bilinFormAt_inj, ContMDiffSection.coe_zero,
    Pi.zero_apply]

/-! ### The flat map -/

/-- The flat map `v ↦ ω(v, ·)` of a two-form on the fibre over `x`, a point of the bundle of
continuous bilinear forms on `V`: the flat map `Bundle.flatAt` of the value of `ω` at `x`. -/
def flat (x : M) : V x →L[ℝ] V x →L[ℝ] ℝ :=
  _root_.Bundle.flatAt F (ω x)

/-- The flat map of `ω` at `x` is the flat map of the value of `ω` at `x`. -/
theorem flat_def (x : M) : ω.flat x = _root_.Bundle.flatAt F (ω x) :=
  (rfl)

/-- The flat map evaluates as the form: `ω♭_x v w = ω_x(v, w)`. -/
@[simp]
theorem flat_apply (x : M) (v w : V x) : ω.flat x v w = ω x ![v, w] := by
  rw [flat_def, _root_.Bundle.flatAt_apply]

/-- The flat map at `x` is the continuous form of the bilinear form at `x`. -/
theorem toBilinForm_flat (x : M) : (ω.flat x).toBilinForm = ω.bilinFormAt x := by
  ext v w
  simp

/-- The orthogonal of a submodule for the flat map of `ω` at `x` is its `ω`-orthogonal. -/
theorem orthogonal_flat (x : M) (N : Submodule ℝ (V x)) :
    LinearMap.BilinForm.orthogonal (ω.flat x).toLinearMap₁₂ N = (ω.bilinFormAt x).orthogonal N := by
  rw [← toBilinForm_flat, ContinuousLinearMap.toBilinForm]

/-- The flat maps of a `C^n` two-form form a `C^n` section of the bundle of continuous bilinear
forms on `V`. -/
theorem contMDiff_flat :
    ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) x (ω.flat x)) :=
  fun x₀ ↦ by
    simpa only [id_eq, ← flat_def] using contMDiffAt_sectionAlong_flatAt (b := id) (ω.contMDiff x₀)

/-- Pairing two sections that are `C^n` on a set `s` with a `C^n` two-form gives a function that
is `C^n` on `s`: `y ↦ ω_y(u y, v y)`. -/
theorem contMDiffOn_bilinFormAt {s : Set M} {u v : ∀ x, V x} (hu : CMDiff[s] n (T% u))
    (hv : CMDiff[s] n (T% v)) : CMDiff[s] n (fun x ↦ ω.bilinFormAt x (u x) (v x)) := by
  simpa using ω.contMDiff_flat.contMDiffOn.clm_bundle_apply₂_trivial hu hv

/-- Pairing two `C^n` sections with a `C^n` two-form gives a `C^n` function:
`y ↦ ω_y(u y, v y)`. -/
theorem contMDiff_bilinFormAt {u v : ∀ x, V x} (hu : CMDiff n (T% u)) (hv : CMDiff n (T% v)) :
    CMDiff n (fun x ↦ ω.bilinFormAt x (u x) (v x)) :=
  contMDiffOn_univ.1 (ω.contMDiffOn_bilinFormAt hu.contMDiffOn hv.contMDiffOn)

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

/-- A two-form whose fibre over every point is isomorphic to a symplectic vector space
`(W, σ)`, by a linear isomorphism that carries `σ` to the form, is nondegenerate. -/
theorem isNondegenerate_of_forall_exists {W : Type*} [AddCommGroup W] [Module ℝ W]
    (σ : TauCeti.SymplecticForm W)
    (h : ∀ x, ∃ Θ : W ≃ₗ[ℝ] V x, ∀ v w, ω.bilinFormAt x (Θ v) (Θ w) = σ v w) :
    ω.IsNondegenerate := by
  refine isNondegenerate_iff_separatingLeft.2 fun x v hv ↦ ?_
  obtain ⟨Θ, hΘ⟩ := h x
  obtain ⟨u, rfl⟩ := Θ.surjective v
  refine (map_eq_zero_iff Θ Θ.injective).2 (σ.nondegenerate.1 u fun u' ↦ ?_)
  refine (hΘ u u').symm.trans ?_
  rw [bilinFormAt_apply]
  exact hv (Θ u')

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

/-- The symplectic form on a fibre evaluates as the two-form.

This is not `@[simp]`: `simp` proves it with `IsNondegenerate.toBilinForm_symplecticFormAt` and
`bilinFormAt_apply`. -/
theorem IsNondegenerate.symplecticFormAt_apply (h : ω.IsNondegenerate) (x : M) (v w : V x) :
    h.symplecticFormAt x v w = ω x ![v, w] :=
  ω.bilinFormAt_apply x v w

/-- The bilinear form of the symplectic form on a fibre is that of the two-form.

`simp` evaluates the symplectic form through this lemma: a `TauCeti.SymplecticForm` applies to
vectors through its bilinear form, so `simp` turns `h.symplecticFormAt x v w` into
`ω.bilinFormAt x v w`, which the lemmas on `bilinFormAt` then evaluate. -/
@[simp]
theorem IsNondegenerate.toBilinForm_symplecticFormAt (h : ω.IsNondegenerate) (x : M) :
    (h.symplecticFormAt x).toBilinForm = ω.bilinFormAt x :=
  (rfl)

end ContMDiffTwoForm

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
/-- On a bundle of finite rank, the alternating maps of two vectors on a fibre whose bilinear form
is nondegenerate form an open subset of the total space of the bundle of alternating maps. -/
theorem isOpen_setOf_nondegenerate [FiniteDimensional ℝ F] :
    IsOpen {p : TotalSpace (F [⋀^Fin 2]→L[ℝ] ℝ) (fun x ↦ V x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x) |
      LinearMap.BilinForm.Nondegenerate (MultilinearMap.toBilinMap p.snd.toMultilinearMap)} := by
  refine FiberBundle.isOpen_of_forall_mem_iff_snd_mem
    ContinuousAlternatingMap.isOpen_setOf_nondegenerate_toBilinMap fun b q hq ↦ ?_
  -- In the fibre coordinates of the trivialization, a form becomes its pull-back by a linear
  -- equivalence.
  have hy : q.proj ∈ (trivializationAt F V b).baseSet := by
    simpa using hq
  let L := ((trivializationAt F V b).continuousLinearEquivAt ℝ q.proj hy).toLinearEquiv
  have heq : MultilinearMap.toBilinMap ((trivializationAt (F [⋀^Fin 2]→L[ℝ] ℝ)
      (fun x ↦ V x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x) b) q).2.toMultilinearMap =
      LinearMap.BilinForm.congr L (MultilinearMap.toBilinMap q.snd.toMultilinearMap) := by
    ext v w
    simp only [FiberBundle.trivializationAt_continuousAlternatingMap_apply,
      ContinuousAlternatingMap.inCoordinates, MultilinearMap.toBilinMap_apply,
      LinearMap.BilinForm.congr_apply, Trivial.fiberBundle_trivializationAt',
      Trivial.continuousLinearMapAt_trivialization,
      ContinuousLinearMap.id_compContinuousAlternatingMap, ContinuousMultilinearMap.coe_coe,
      ContinuousAlternatingMap.coe_toContinuousMultilinearMap,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    ext i
    fin_cases i <;> simp [L, Trivialization.symmL_apply _ hy]
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, heq, LinearMap.BilinForm.nondegenerate_congr_iff]

namespace ContMDiffTwoForm

/-! ### Two-forms from alternating bilinear sections -/

section OfBilinearSection

variable [FiniteDimensional ℝ F]

/-- On a bundle of finite rank, the two-form `(v, w) ↦ β(v, w)` of a `C^n` bilinear section `β`
that vanishes on the diagonal, `β(v, v) = 0`. -/
def ofBilinearSection (β : TauCeti.Manifold.BilinearSection I F V ℝ n)
    (hβ : ∀ x (v : V x), β x v v = 0) : ContMDiffTwoForm I n F V where
  toFun x := _root_.Bundle.alternatingMapOfBilin F (β x) (hβ x)
  contMDiff_toFun x :=
    contMDiffAt_sectionAlong_continuousAlternatingMap_of_bilinear (b := id) (β.contMDiff x)
      fun _ v ↦ _root_.Bundle.alternatingMapOfBilin_apply _ _ v

/-- The two-form of a bilinear section `β` takes the value `β(v 0, v 1)` on `v`. -/
@[simp]
theorem ofBilinearSection_apply (β : TauCeti.Manifold.BilinearSection I F V ℝ n)
    (hβ : ∀ x (v : V x), β x v v = 0) (x : M) (v : Fin 2 → V x) :
    ofBilinearSection β hβ x v = β x (v 0) (v 1) :=
  _root_.Bundle.alternatingMapOfBilin_apply _ _ v

/-- The bilinear form on the fibre over `x` of the two-form of a bilinear section `β` is `β x`. -/
@[simp]
theorem bilinFormAt_ofBilinearSection (β : TauCeti.Manifold.BilinearSection I F V ℝ n)
    (hβ : ∀ x (v : V x), β x v v = 0) (x : M) :
    (ofBilinearSection β hβ).bilinFormAt x = (β x).toBilinForm := by
  ext v w
  simp

end OfBilinearSection

/-! ### Constant forms on trivial bundles -/

section Const

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- The constant two-form on the trivial bundle `M × W` given by a symplectic form `σ` on the
finite-dimensional normed space `W`. For `σ = stdForm ι` this is the standard form on
`Trivial M (StdSpace ι)`. -/
def const (σ : TauCeti.SymplecticForm W) : ContMDiffTwoForm I n W (Trivial M W) where
  toFun _ := AlternatingMap.toContinuousAlternatingMap σ.isAlt.toAlternatingMap
  contMDiff_toFun := contMDiff_continuousAlternatingMap_bundle_of_inCoordinates_eq_const
    (c := fun _ ↦ AlternatingMap.toContinuousAlternatingMap σ.isAlt.toAlternatingMap)
    fun _ _ _ _ ↦ by ext v; simp [ContinuousAlternatingMap.inCoordinates]

/-- At every point, the constant form is `σ` as a continuous alternating map. -/
theorem const_def (σ : TauCeti.SymplecticForm W) (x : M) :
    (const (I := I) (n := n) σ) x =
      AlternatingMap.toContinuousAlternatingMap σ.isAlt.toAlternatingMap :=
  (rfl)

/-- The constant form takes the value `σ(v 0, v 1)` at every point. -/
@[simp]
theorem const_apply (σ : TauCeti.SymplecticForm W) (x : M) (v : Fin 2 → W) :
    (const (I := I) (n := n) σ) x v = σ (v 0) (v 1) := by
  rw [const_def, AlternatingMap.coe_toContinuousAlternatingMap]
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

/-! ### Pulling back along linear bundle maps -/

section CompContinuousLinearMap

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] {V₂ : M → Type*}
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul ℝ (V₂ x)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  (L : ∀ x, V₂ x →L[ℝ] V x)
  (hL : ContMDiff I (I.prod 𝓘(ℝ, F₂ →L[ℝ] F)) n
    (fun x ↦ TotalSpace.mk' (F₂ →L[ℝ] F) (E := fun x ↦ V₂ x →L[ℝ] V x) x (L x)))

/-- The pull-back `ω ↦ ω(L ·, L ·)` of two-forms along a `C^n` family of linear maps
`L x : V₂ x → V x` between the fibres of two bundles over the same base. Unlike `pushforward`,
it does not need the maps `L x` to be invertible. -/
def compContinuousLinearMap : ContMDiffTwoForm I n F V →ₗ[ℝ] ContMDiffTwoForm I n F₂ V₂ :=
  ContMDiffSection.mapLinearMap
    (fun x ↦ ContinuousAlternatingMap.compContinuousLinearMapₗ (L x))
    (contMDiff_compContinuousLinearMap_totalSpace _ hL)

/-- The pulled-back form at `x` is `ω_x(L_x ·, L_x ·)`. -/
@[simp]
theorem compContinuousLinearMap_apply (ω : ContMDiffTwoForm I n F V) (x : M) :
    compContinuousLinearMap L hL ω x = (ω x).compContinuousLinearMap (L x) :=
  ContMDiffSection.mapLinearMap_apply _ _ ω x

/-- The pulled-back form takes on `u`, `v` the value of `ω` on `L_x u`, `L_x v`. -/
theorem bilinFormAt_compContinuousLinearMap (ω : ContMDiffTwoForm I n F V) (x : M)
    (u v : V₂ x) :
    (compContinuousLinearMap L hL ω).bilinFormAt x u v = ω.bilinFormAt x (L x u) (L x v) := by
  simp only [bilinFormAt_apply, compContinuousLinearMap_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  exact (FinVec.etaExpand_eq _).symm

end CompContinuousLinearMap

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

/-- The transport `ω ↦ ω(Φ⁻¹ ·, Φ⁻¹ ·)` of two-forms along a `C^n` isomorphism of vector
bundles `Φ`, given by fibrewise equivalences whose map of total spaces is `C^n`. -/
def pushforward : ContMDiffTwoForm I n F₁ V₁ ≃ₗ[ℝ] ContMDiffTwoForm I n F₂ V₂ :=
  ContMDiffSection.mapEquiv
    (fun x ↦ { (Φ x).continuousAlternatingMapCongrLeftEquiv,
      ContinuousAlternatingMap.compContinuousLinearMapₗ ((Φ x).symm : V₂ x →L[ℝ] V₁ x) with })
    (contMDiff_compContinuousLinearMap_totalSpace _ (contMDiff_hom_bundle_symm Φ hΦ))
    (contMDiff_compContinuousLinearMap_totalSpace _
      ((TauCeti.contMDiff_hom_bundle_iff fun x ↦ (Φ x : V₁ x →L[ℝ] V₂ x)).2 hΦ))

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

/-- The transport along `Φ` is the pull-back along the inverses `Φ_x⁻¹`. -/
theorem pushforward_eq_compContinuousLinearMap (ω : ContMDiffTwoForm I n F₁ V₁) :
    pushforward Φ hΦ ω = compContinuousLinearMap (fun x ↦ ((Φ x).symm : V₂ x →L[ℝ] V₁ x))
      (contMDiff_hom_bundle_symm Φ hΦ) ω :=
  ContMDiffSection.ext fun x ↦ by rw [pushforward_apply, compContinuousLinearMap_apply]

/-- The bilinear form of the transported form at `x` is the bilinear form of `ω` moved along `Φ
x`. -/
theorem bilinFormAt_pushforward (ω : ContMDiffTwoForm I n F₁ V₁) (x : M) :
    (pushforward Φ hΦ ω).bilinFormAt x =
      LinearMap.BilinForm.congr (Φ x).toLinearEquiv (ω.bilinFormAt x) := by
  ext u v
  rw [pushforward_eq_compContinuousLinearMap, bilinFormAt_compContinuousLinearMap]
  simp

/-- The transported form takes on `u`, `v` the value of `ω` on `Φ_x⁻¹ u`, `Φ_x⁻¹ v`. -/
theorem bilinFormAt_pushforward_apply (ω : ContMDiffTwoForm I n F₁ V₁) (x : M) (u v : V₂ x) :
    (pushforward Φ hΦ ω).bilinFormAt x u v = ω.bilinFormAt x ((Φ x).symm u) ((Φ x).symm v) := by
  simp [bilinFormAt_pushforward]

/-- The transport of `ω₁` along `Φ` is `ω₂` exactly when `Φ` carries `ω₁` to `ω₂` on every fibre,
`ω₂(Φ v, Φ w) = ω₁(v, w)`: that is, when `Φ` is a symplectic isomorphism from `ω₁` to `ω₂`. -/
theorem pushforward_eq_iff {ω₁ : ContMDiffTwoForm I n F₁ V₁} {ω₂ : ContMDiffTwoForm I n F₂ V₂} :
    pushforward Φ hΦ ω₁ = ω₂ ↔
      ∀ x v w, ω₂.bilinFormAt x (Φ x v) (Φ x w) = ω₁.bilinFormAt x v w := by
  refine ⟨?_, fun h ↦ ext_bilinFormAt fun x ↦ ?_⟩
  · rintro rfl x v w
    simp [bilinFormAt_pushforward]
  · ext v w
    rw [bilinFormAt_pushforward, LinearMap.BilinForm.congr_apply, ← h]
    simp

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

/-- The two-form on the tangent bundle of a Tau Ceti smooth two-form is nondegenerate exactly when
that form is. -/
@[simp]
theorem isNondegenerate_tangentEquiv_symm_iff {φ : TauCeti.SmoothTwoForm I M} :
    (tangentEquiv.symm φ).IsNondegenerate ↔ φ.IsNondegenerate := by
  rw [← isNondegenerate_tangentEquiv_iff, LinearEquiv.apply_symm_apply]

end Tangent

/-! ### Forms of rank two -/

variable {ω : ContMDiffTwoForm I n F V} in
/-- On a bundle of rank two, a two-form is nondegenerate exactly when it vanishes nowhere. -/
theorem isNondegenerate_iff_forall_ne_zero_of_finrank_eq_two (hF : Module.finrank ℝ F = 2) :
    ω.IsNondegenerate ↔ ∀ x, ω x ≠ 0 := by
  refine forall_congr' fun x ↦ ?_
  have hx : Module.finrank ℝ (V x) = 2 := (VectorBundle.finrank_eq ℝ F V x).trans hF
  rw [(ω.isAlt_bilinFormAt x).nondegenerate_iff_ne_zero_of_finrank_eq_two hx, ne_eq, ne_eq,
    bilinFormAt_eq_zero_iff]

end ContMDiffTwoForm

/-! ### Smoothness of transition maps between frames -/

section ContMDiffFrameTransition

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {Φ Φ' : ∀ x, W ≃L[ℝ] V x} {U : Set M} {n : WithTop ℕ∞}

/-- Over an open set `U`, if two frames `Φ` and `Φ'` with model fibre `W` of finite dimension
depend `C^n` on `(x, v) ∈ U × W`, then so does their transition map, as a map from `U` to
`W →L[ℝ] W`. -/
theorem contMDiffOn_frameTransition
    (hΦ : ContMDiffOn (I.prod 𝓘(ℝ, W)) (I.prod 𝓘(ℝ, F)) n
      (fun p : M × W ↦ TotalSpace.mk' F p.1 (Φ p.1 p.2)) (U ×ˢ Set.univ))
    (hΦ' : ContMDiffOn (I.prod 𝓘(ℝ, W)) (I.prod 𝓘(ℝ, F)) n
      (fun p : M × W ↦ TotalSpace.mk' F p.1 (Φ' p.1 p.2)) (U ×ˢ Set.univ))
    (hU : IsOpen U) :
    ContMDiffOn I 𝓘(ℝ, W →L[ℝ] W) n (fun x ↦ (frameTransition Φ Φ' x : W →L[ℝ] W)) U := by
  intro x hx
  have hom {Ψ : ∀ x, W ≃L[ℝ] V x} (hΨ : ContMDiffOn (I.prod 𝓘(ℝ, W)) (I.prod 𝓘(ℝ, F)) n
      (fun p : M × W ↦ TotalSpace.mk' F p.1 (Ψ p.1 p.2)) (U ×ˢ Set.univ)) :=
    ((contMDiffOn_hom_trivial_iff (fun y ↦ (Ψ y : W →L[ℝ] V y)) hU).2 hΨ).contMDiffAt
      (hU.mem_nhds hx)
  have hcomp := ((hom hΦ').clm_bundle_inverse
    ContinuousLinearMap.isInvertible_equiv).clm_bundle_comp (hom hΦ)
  rw [contMDiffAt_hom_bundle] at hcomp
  refine (hcomp.2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_)).contMDiffWithinAt
  ext v
  simp [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.inverse_equiv]

/-- Over an open set `U`, if a frame `Φ` of `V` and a frame `Ψ` of `V₂`, with the same model fibre
`W` of finite dimension, depend `C^n` on `(x, v) ∈ U × W`, then the fibrewise map `Ψₓ ∘ Φₓ⁻¹` from
`V` to `V₂` is `C^n` on the part of the total space of `V` over `U`. -/
theorem contMDiffOn_totalSpaceMk_symm_trans {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    {V₂ : M → Type*} [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
    [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
    [∀ x, ContinuousSMul ℝ (V₂ x)] [TopologicalSpace (TotalSpace F₂ V₂)]
    [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂] {Ψ : ∀ x, W ≃L[ℝ] V₂ x}
    (hΦ : ContMDiffOn (I.prod 𝓘(ℝ, W)) (I.prod 𝓘(ℝ, F)) n
      (fun p : M × W ↦ TotalSpace.mk' F p.1 (Φ p.1 p.2)) (U ×ˢ Set.univ))
    (hΨ : ContMDiffOn (I.prod 𝓘(ℝ, W)) (I.prod 𝓘(ℝ, F₂)) n
      (fun p : M × W ↦ TotalSpace.mk' F₂ p.1 (Ψ p.1 p.2)) (U ×ˢ Set.univ))
    (hU : IsOpen U) :
    ContMDiffOn (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F₂)) n
      (fun p : TotalSpace F V ↦ TotalSpace.mk' F₂ p.proj ((Φ p.proj).symm.trans (Ψ p.proj) p.snd))
      (TotalSpace.proj ⁻¹' U) := by
  intro p hp
  -- The fibre `F` is `W` through the frame and the trivialization at `p.proj`.
  have : FiniteDimensional ℝ F :=
    ((Φ p.proj).trans (VectorBundle.continuousLinearEquivAt ℝ F V p.proj)).finiteDimensional
  have hΦx := ((contMDiffOn_hom_trivial_iff (fun y ↦ (Φ y : W →L[ℝ] V y)) hU).2
    hΦ).contMDiffAt (hU.mem_nhds hp)
  have hΨx := ((contMDiffOn_hom_trivial_iff (fun y ↦ (Ψ y : W →L[ℝ] V₂ y)) hU).2
    hΨ).contMDiffAt (hU.mem_nhds hp)
  have hcomp := hΨx.clm_bundle_comp (hΦx.clm_bundle_inverse
    ContinuousLinearMap.isInvertible_equiv)
  simp only [ContinuousLinearMap.inverse_equiv] at hcomp
  exact ((TauCeti.contMDiffAt_hom_bundle_iff
    (fun y ↦ (Ψ y : W →L[ℝ] V₂ y).comp ((Φ y).symm : V y →L[ℝ] W)) p.proj).1
    hcomp p.snd).contMDiffWithinAt

end ContMDiffFrameTransition

namespace ContMDiffTwoForm

/-! ### Symplectic frames -/

section Frame

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A symplectic frame of the two-form `ω` over the set `U`, modelled on the symplectic vector
space `(W, σ)`: a family of linear equivalences `Φ x : W ≃L[ℝ] V x` that depends `C^n` on
`(x, v) ∈ U × W` and carries `σ` to `ω` on each fibre over `U`. The values of `Φ` off `U` play no
role. -/
structure IsSymplecticFrameOn (ω : ContMDiffTwoForm I n F V) (σ : TauCeti.SymplecticForm W)
    (U : Set M) (Φ : ∀ x, W ≃L[ℝ] V x) : Prop where
  /-- The frame depends `C^n` on the point of `U` and the vector of `W`. -/
  contMDiffOn : ContMDiffOn (I.prod 𝓘(ℝ, W)) (I.prod 𝓘(ℝ, F)) n
    (fun p : M × W ↦ TotalSpace.mk' F p.1 (Φ p.1 p.2)) (U ×ˢ Set.univ)
  /-- The frame carries `σ` to `ω` on each fibre over `U`. -/
  map_bilinFormAt : ∀ x ∈ U, ∀ v w, ω.bilinFormAt x (Φ x v) (Φ x w) = σ v w

variable {ω : ContMDiffTwoForm I n F V} {σ : TauCeti.SymplecticForm W} {U U' : Set M}
  {Φ Φ' : ∀ x, W ≃L[ℝ] V x} {x : M}

namespace IsSymplecticFrameOn

/-- A symplectic frame over `U` is one over every smaller set. -/
theorem mono (h : ω.IsSymplecticFrameOn σ U Φ) (hU : U' ⊆ U) : ω.IsSymplecticFrameOn σ U' Φ :=
  ⟨h.contMDiffOn.mono (Set.prod_mono hU subset_rfl), fun x hx ↦ h.map_bilinFormAt x (hU hx)⟩

/-- Over a point of `U`, the bilinear form of `ω` is `σ` moved along the frame. -/
theorem bilinFormAt_eq (h : ω.IsSymplecticFrameOn σ U Φ) (hx : x ∈ U) :
    ω.bilinFormAt x = LinearMap.BilinForm.congr (Φ x).toLinearEquiv σ.toBilinForm := by
  ext v w
  rw [LinearMap.BilinForm.congr_apply]
  conv_lhs => rw [← (Φ x).apply_symm_apply v, ← (Φ x).apply_symm_apply w]
  exact h.map_bilinFormAt x hx _ _

/-- A two-form with a symplectic frame over `U` is nondegenerate on the fibres over `U`. -/
theorem nondegenerate_bilinFormAt (h : ω.IsSymplecticFrameOn σ U Φ) (hx : x ∈ U) :
    (ω.bilinFormAt x).Nondegenerate := by
  rw [h.bilinFormAt_eq hx, LinearMap.BilinForm.nondegenerate_congr_iff]
  exact σ.nondegenerate

/-- At a point of `U`, a symplectic frame of a nondegenerate form is a linear symplectomorphism
from `σ` to the symplectic form of the fibre. -/
theorem isSymplectomorphism (h : ω.IsSymplecticFrameOn σ U Φ) (hω : ω.IsNondegenerate)
    (hx : x ∈ U) : σ.IsSymplectomorphism (hω.symplecticFormAt x) (Φ x).toLinearEquiv :=
  TauCeti.SymplecticForm.isSymplectomorphism_iff.2 fun v w ↦ by
    simpa using h.map_bilinFormAt x hx v w

/-- At a point of `U`, the transition map between two symplectic frames of the same form for `σ`
preserves `σ`. -/
theorem isSymplectomorphism_frameTransition (h : ω.IsSymplecticFrameOn σ U Φ)
    (h' : ω.IsSymplecticFrameOn σ U Φ') (hx : x ∈ U) :
    σ.IsSymplectomorphism σ (frameTransition Φ Φ' x).toLinearEquiv :=
  TauCeti.SymplecticForm.isSymplectomorphism_iff.2 fun v w ↦ by
    rw [← h'.map_bilinFormAt x hx]
    simp only [ContinuousLinearEquiv.coe_toLinearEquiv, frameTransition_apply,
      ContinuousLinearEquiv.apply_symm_apply]
    exact h.map_bilinFormAt x hx v w

/-- Over an open set, the transition map between two symplectic frames depends `C^n` on the
point. -/
theorem contMDiffOn_frameTransition [FiniteDimensional ℝ W] (h : ω.IsSymplecticFrameOn σ U Φ)
    (h' : ω.IsSymplecticFrameOn σ U Φ') (hU : IsOpen U) :
    ContMDiffOn I 𝓘(ℝ, W →L[ℝ] W) n (fun x ↦ (frameTransition Φ Φ' x : W →L[ℝ] W)) U :=
  Bundle.contMDiffOn_frameTransition h.contMDiffOn h'.contMDiffOn hU

/-- Two symplectic frames `Φ`, `Φ'` for `stdForm κ`, over open sets that contain the image of a
continuous map `γ : X → M`, differ along `γ` by a continuous map `Ψ` into the symplectic
matrices: `Φ' = Φ ∘ Ψ` along `γ`. -/
theorem exists_frameTransition {κ : Type*} [Fintype κ] [DecidableEq κ] {X : Type*}
    [TopologicalSpace X] {U U' : Set M} (hU : IsOpen U) (hU' : IsOpen U')
    {Φ Φ' : ∀ x, StdSpace κ ≃L[ℝ] V x} (h : ω.IsSymplecticFrameOn (stdForm κ) U Φ)
    (h' : ω.IsSymplecticFrameOn (stdForm κ) U' Φ') (γ : C(X, M)) (hγ : ∀ y, γ y ∈ U ∩ U') :
    ∃ Ψ : C(X, TauCeti.GLSymplectic κ ℝ), ∀ y v,
      Φ' (γ y) v = Φ (γ y) (Matrix.toEuclideanLin (Ψ y : GL (κ ⊕ κ) ℝ) v) := by
  have hT : Continuous fun y ↦ (frameTransition Φ' Φ (γ y) : StdSpace κ →L[ℝ] StdSpace κ) :=
    ((h'.mono Set.inter_subset_right).contMDiffOn_frameTransition (h.mono Set.inter_subset_left)
      (hU.inter hU')).continuousOn.comp_continuous γ.continuous hγ
  have hmem (y : X) : Matrix.GeneralLinearGroup.ofEuclideanCLE (frameTransition Φ' Φ (γ y)) ∈
      TauCeti.GLSymplectic κ ℝ := by
    rw [mem_GLSymplectic_iff_isSymplectomorphism,
      Matrix.GeneralLinearGroup.toEuclideanCLE_ofEuclideanCLE]
    exact (h'.mono Set.inter_subset_right).isSymplectomorphism_frameTransition
      (h.mono Set.inter_subset_left) (hγ y)
  refine ⟨⟨fun y ↦ ⟨_, hmem y⟩,
    (Matrix.GeneralLinearGroup.continuous_ofEuclideanCLE hT).subtype_mk _⟩, fun y v ↦ ?_⟩
  simp only [ContinuousMap.coe_mk]
  rw [← Matrix.toEuclideanCLM_apply, Matrix.GeneralLinearGroup.toEuclideanCLM_ofEuclideanCLE,
    ContinuousLinearEquiv.coe_coe, frameTransition_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- Precomposing a symplectic frame for `σ` with linear symplectomorphisms `P x` from `(W', σ')`
to `(W, σ)` that depend `C^n` on the point `x` of `U` gives a symplectic frame for `σ'`. -/
theorem precomp_of_contMDiffOn {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W']
    {σ' : TauCeti.SymplecticForm W'} (h : ω.IsSymplecticFrameOn σ U Φ) {P : M → W' ≃L[ℝ] W}
    (hP : ContMDiffOn I 𝓘(ℝ, W' →L[ℝ] W) n (fun x ↦ (P x : W' →L[ℝ] W)) U)
    (hPσ : ∀ x ∈ U, σ'.IsSymplectomorphism σ (P x).toLinearEquiv) :
    ω.IsSymplecticFrameOn σ' U fun x ↦ (P x).trans (Φ x) := by
  refine ⟨h.contMDiffOn.comp (contMDiff_fst.contMDiffOn.prodMk
    ((hP.comp contMDiff_fst.contMDiffOn fun (p : M × W') (hp : p ∈ U ×ˢ Set.univ) ↦ hp.1).clm_apply
      contMDiff_snd.contMDiffOn))
    fun p hp ↦ ⟨hp.1, Set.mem_univ _⟩, fun x hx v w ↦ ?_⟩
  rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
    h.map_bilinFormAt x hx]
  exact (hPσ x hx).apply v w

/-- Precomposing a symplectic frame for `σ` with a linear symplectomorphism `e` from `(W', σ')`
to `(W, σ)` gives a symplectic frame for `σ'`. -/
theorem precomp {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W']
    {σ' : TauCeti.SymplecticForm W'} (h : ω.IsSymplecticFrameOn σ U Φ) (e : W' ≃L[ℝ] W)
    (he : σ'.IsSymplectomorphism σ e.toLinearEquiv) :
    ω.IsSymplecticFrameOn σ' U fun x ↦ e.trans (Φ x) :=
  h.precomp_of_contMDiffOn (P := fun _ ↦ e) contMDiffOn_const fun _ _ ↦ he

/-- A symplectic frame over `U`, restricted to a subset `S` of `U`, is continuous as a map from
`S × W` to the total space. -/
theorem continuous_restrict (h : ω.IsSymplecticFrameOn σ U Φ) {S : Set M} (hS : S ⊆ U) :
    Continuous fun q : S × W ↦ TotalSpace.mk' F (q.1 : M) (Φ q.1 q.2) :=
  h.contMDiffOn.continuousOn.comp_continuous
    ((continuous_subtypeVal.comp continuous_fst).prodMk continuous_snd)
    fun q ↦ ⟨hS q.1.property, Set.mem_univ _⟩

end IsSymplecticFrameOn

/-- On the trivial bundle with fibre `W'` and the constant form of `ω'`, a linear symplectomorphism
`e` from `(W, σ)` to `(W', ω')` is a symplectic frame over all of `M`. -/
theorem isSymplecticFrameOn_const {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W']
    [FiniteDimensional ℝ W'] {ω' : TauCeti.SymplecticForm W'} {e : W ≃L[ℝ] W'}
    (he : σ.IsSymplectomorphism ω' e.toLinearEquiv) :
    (const (I := I) (n := n) (M := M) ω').IsSymplecticFrameOn σ Set.univ fun _ ↦ e := by
  refine ⟨(Trivial.contMDiff_comp_mk_iff.2
      (TauCeti.contMDiff_bundleMap_of_constant_coordinates (E₁ := Trivial M W)
        (E₂ := Trivial M W') (fun _ ↦ e) (e : W →L[ℝ] W') fun _ _ _ _ ↦ by simp)).contMDiffOn,
    fun x _ v w ↦ ?_⟩
  rw [bilinFormAt_const]
  exact he.apply v w

/-- **Symplectic frames from Darboux sections.** Let `aᵢ`, `bᵢ` (`i : κ`) be sections of a bundle
of rank `2 |κ|` that are `Cⁿ` on a set `U` and satisfy the Darboux relations `ω(aᵢ, aⱼ) = 0`,
`ω(bᵢ, bⱼ) = 0` and `ω(aᵢ, bⱼ) = δᵢⱼ` at every point of `U`. Then there is a symplectic frame
`Φ` of `ω` over `U` for the standard form `stdForm κ` that is `(x, y) ↦ ∑ᵢ (xᵢ aᵢ + yᵢ bᵢ)` on
the fibres over `U`. -/
theorem exists_isSymplecticFrameOn_of_darboux [FiniteDimensional ℝ F] {κ : Type*}
    [Fintype κ] [DecidableEq κ] (hF : Module.finrank ℝ F = 2 * Fintype.card κ) {U : Set M}
    {a b : κ → ∀ x, V x} (ha : ∀ i, CMDiff[U] n (T% (a i))) (hb : ∀ i, CMDiff[U] n (T% (b i)))
    (haa : ∀ x ∈ U, ∀ i j, ω.bilinFormAt x (a i x) (a j x) = 0)
    (hbb : ∀ x ∈ U, ∀ i j, ω.bilinFormAt x (b i x) (b j x) = 0)
    (hab : ∀ x ∈ U, ∀ i j, ω.bilinFormAt x (a i x) (b j x) = if i = j then 1 else 0) :
    ∃ Φ : ∀ x, StdSpace κ ≃L[ℝ] V x, ω.IsSymplecticFrameOn (stdForm κ) U Φ ∧
      ∀ x ∈ U, ∀ v, Φ x v = ∑ i, (v.x i • a i x + v.y i • b i x) := by
  classical
  -- The frame as a linear map on each fibre.
  let L (x : M) : StdSpace κ →ₗ[ℝ] V x := ∑ i,
    (((LinearMap.proj i).comp StdSpace.x).smulRight (a i x) +
      ((LinearMap.proj i).comp StdSpace.y).smulRight (b i x))
  have hL (x : M) (v : StdSpace κ) : L x v = ∑ i, (v.x i • a i x + v.y i • b i x) := by
    simp [L]
  have hω (x : M) (hx : x ∈ U) (v w : StdSpace κ) :
      ω.bilinFormAt x (L x v) (L x w) = stdForm κ v w := by
    have h₁ := (ω.bilinFormAt x).apply_sum_smul_add_smul_eq_left_coeff (hbb x hx) (hab x hx)
      v.x v.y
    have h₂ := (ω.isAlt_bilinFormAt x).apply_sum_smul_add_smul_eq_neg_right_coeff (haa x hx)
      (hab x hx) v.x v.y
    rw [hL x v, hL x w, map_sum, stdForm_apply]
    simp only [map_add, map_smul, h₁, h₂, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hinj (x : M) (hx : x ∈ U) : Function.Injective (L x) := by
    refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
    refine (stdForm κ).nondegenerate.1 v fun w ↦ ?_
    simpa [hv] using (hω x hx v w).symm
  have := VectorBundle.finiteDimensional ℝ F V
  have hdim (x : M) : Module.finrank ℝ (StdSpace κ) = Module.finrank ℝ (V x) := by
    rw [finrank_stdSpace, VectorBundle.finrank_eq ℝ F V x, hF]
  have := FiberBundle.t2Space F (E := V)
  -- Off `U`, the values of the frame play no role.
  let Φ (x : M) : StdSpace κ ≃L[ℝ] V x :=
    if hx : x ∈ U then
      (LinearEquiv.ofInjectiveOfFinrankEq (L x) (hinj x hx) (hdim x)).toContinuousLinearEquiv
    else ContinuousLinearEquiv.ofFinrankEq (hdim x)
  have hΦL (x : M) (hx : x ∈ U) (v : StdSpace κ) : Φ x v = L x v := by
    simp only [Φ, hx, ↓reduceDIte]
    rw [LinearEquiv.coe_toContinuousLinearEquiv',
      ← LinearEquiv.coe_coe, LinearEquiv.coe_ofInjectiveOfFinrankEq]
  have hΦ (x : M) (hx : x ∈ U) (v : StdSpace κ) :
      Φ x v = ∑ i, (v.x i • a i x + v.y i • b i x) := by
    rw [hΦL x hx, hL]
  refine ⟨Φ, ⟨?_, fun x hx v w ↦ ?_⟩, hΦ⟩
  · -- Each term of the sum is `Cⁿ` in the point and the vector.
    have hc (f : StdSpace κ →ₗ[ℝ] ℝ) :
        ContMDiff (I.prod 𝓘(ℝ, StdSpace κ)) 𝓘(ℝ) n fun p : M × StdSpace κ ↦ f p.2 :=
      f.toContinuousLinearMap.contDiff.contMDiff.comp contMDiff_snd
    have hfst : Set.MapsTo Prod.fst (U ×ˢ Set.univ : Set (M × StdSpace κ)) U := fun p hp ↦ hp.1
    have hterm (f : StdSpace κ →ₗ[ℝ] ℝ) (s : ∀ x, V x) (hs : CMDiff[U] n (T% s)) :
        ContMDiffOn (I.prod 𝓘(ℝ, StdSpace κ)) (I.prod 𝓘(ℝ, F)) n
          (fun p : M × StdSpace κ ↦ TotalSpace.mk' F p.1 (f p.2 • s p.1)) (U ×ˢ Set.univ) :=
      (hc f).contMDiffOn.smul_totalSpace (hs.comp contMDiff_fst.contMDiffOn hfst)
    refine ContMDiffOn.congr ?_ fun p hp ↦ by rw [hΦ p.1 hp.1 p.2]
    refine ContMDiffOn.sum_sectionAlong (b := Prod.fst) _ _ contMDiff_fst.contMDiffOn
      fun i _ ↦ ?_
    exact (hterm ((LinearMap.proj i).comp StdSpace.x) _ (ha i)).add_sectionAlong
      (hterm ((LinearMap.proj i).comp StdSpace.y) _ (hb i))
  · rw [hΦL x hx, hΦL x hx, hω x hx]

section Trans

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] {V₂ : M → Type*}
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul ℝ (V₂ x)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂] [FiniteDimensional ℝ F]

/-- Composing a symplectic frame of `ω` with a symplectic isomorphism `Ψ` from `ω` to `ω₂` gives a
symplectic frame of `ω₂`. -/
theorem IsSymplecticFrameOn.trans (h : ω.IsSymplecticFrameOn σ U Φ) (Ψ : ∀ x, V x ≃L[ℝ] V₂ x)
    (hΨ : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F₂)) n
      (fun p : TotalSpace F V ↦ TotalSpace.mk' F₂ p.proj (Ψ p.proj p.snd)))
    {ω₂ : ContMDiffTwoForm I n F₂ V₂} (hω₂ : pushforward Ψ hΨ ω = ω₂) :
    ω₂.IsSymplecticFrameOn σ U fun x ↦ (Φ x).trans (Ψ x) := by
  refine ⟨hΨ.comp_contMDiffOn h.contMDiffOn, fun x hx v w ↦ ?_⟩
  rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
    (pushforward_eq_iff Ψ hΨ).1 hω₂, h.map_bilinFormAt x hx]

/-- Gluing of symplectic isomorphisms. Let `U` and `U'` be open sets that cover `M`, let `Φ₁`,
`Φ₁'` be symplectic frames of `ω` for `σ` over `U` and `U'`, and `Φ₂`, `Φ₂'` frames of `ω₂` for
`σ` over `U` and `U'`, with the same transition maps over `U ∩ U'`: `Φ₁ₓ⁻¹ ∘ Φ₁'ₓ = Φ₂ₓ⁻¹ ∘ Φ₂'ₓ`.
Then there is a symplectic isomorphism `Ψ` from `ω` to `ω₂`, `C^n` on total spaces, that is
`Φ₂ₓ ∘ Φ₁ₓ⁻¹` over `U` and `Φ₂'ₓ ∘ Φ₁'ₓ⁻¹` over `U'`. -/
theorem exists_pushforward_eq_of_frameTransition_eq
    {ω₂ : ContMDiffTwoForm I n F₂ V₂} {Φ₁ Φ₁' : ∀ x, W ≃L[ℝ] V x} {Φ₂ Φ₂' : ∀ x, W ≃L[ℝ] V₂ x}
    (h₁ : ω.IsSymplecticFrameOn σ U Φ₁) (h₁' : ω.IsSymplecticFrameOn σ U' Φ₁')
    (h₂ : ω₂.IsSymplecticFrameOn σ U Φ₂) (h₂' : ω₂.IsSymplecticFrameOn σ U' Φ₂')
    (hU : IsOpen U) (hU' : IsOpen U') (hcover : U ∪ U' = Set.univ)
    (htrans : ∀ x ∈ U ∩ U', frameTransition Φ₁' Φ₁ x = frameTransition Φ₂' Φ₂ x) :
    ∃ (Ψ : ∀ x, V x ≃L[ℝ] V₂ x) (hΨ : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F₂)) n
      (fun p : TotalSpace F V ↦ TotalSpace.mk' F₂ p.proj (Ψ p.proj p.snd))),
      pushforward Ψ hΨ ω = ω₂ ∧ (∀ x ∈ U, Ψ x = (Φ₁ x).symm.trans (Φ₂ x)) ∧
        ∀ x ∈ U', Ψ x = (Φ₁' x).symm.trans (Φ₂' x) := by
  classical
  -- Over `U ∩ U'` the two local isomorphisms agree, since the transition maps do.
  have hagree : ∀ x ∈ U ∩ U', (Φ₁ x).symm.trans (Φ₂ x) = (Φ₁' x).symm.trans (Φ₂' x) := by
    intro x hx
    ext v
    have h := congr($(htrans x hx) ((Φ₁' x).symm v))
    simp only [frameTransition_apply, ContinuousLinearEquiv.apply_symm_apply] at h
    simp [h]
  let Ψ : ∀ x, V x ≃L[ℝ] V₂ x := fun x ↦
    if x ∈ U then (Φ₁ x).symm.trans (Φ₂ x) else (Φ₁' x).symm.trans (Φ₂' x)
  have hΨU : ∀ x ∈ U, Ψ x = (Φ₁ x).symm.trans (Φ₂ x) := fun x hx ↦ ite_eq_left hx
  have hΨU' : ∀ x ∈ U', Ψ x = (Φ₁' x).symm.trans (Φ₂' x) := fun x hx ↦ by
    by_cases hxU : x ∈ U
    · rw [hΨU x hxU, hagree x ⟨hxU, hx⟩]
    · exact ite_eq_right hxU
  -- Smoothness on total spaces is local; over `U` and over `U'` it is that of the local formula.
  have hloc {U₀ : Set M} {A : ∀ x, W ≃L[ℝ] V x} {B : ∀ x, W ≃L[ℝ] V₂ x}
      (hA : ω.IsSymplecticFrameOn σ U₀ A) (hB : ω₂.IsSymplecticFrameOn σ U₀ B) (hU₀ : IsOpen U₀)
      (hΨ₀ : ∀ x ∈ U₀, Ψ x = (A x).symm.trans (B x)) :
      ContMDiffOn (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F₂)) n
        (fun p : TotalSpace F V ↦ TotalSpace.mk' F₂ p.proj (Ψ p.proj p.snd))
        (TotalSpace.proj ⁻¹' U₀) := fun p hp ↦ by
    -- The model fibre `W` is `F` through the frame and the trivialization at `p.proj`.
    have : FiniteDimensional ℝ W :=
      ((A p.proj).trans (VectorBundle.continuousLinearEquivAt ℝ F V p.proj)).symm.finiteDimensional
    exact ((Bundle.contMDiffOn_totalSpaceMk_symm_trans hA.contMDiffOn hB.contMDiffOn hU₀).congr
      fun q hq ↦ by rw [hΨ₀ _ hq]) p hp
  have hΨ : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F₂)) n
      (fun p : TotalSpace F V ↦ TotalSpace.mk' F₂ p.proj (Ψ p.proj p.snd)) :=
    contMDiff_of_contMDiffOn_union_of_isOpen (hloc h₁ h₂ hU hΨU) (hloc h₁' h₂' hU' hΨU')
      (by rw [← Set.preimage_union, hcover, Set.preimage_univ])
      (hU.preimage (FiberBundle.continuous_proj F V))
      (hU'.preimage (FiberBundle.continuous_proj F V))
  refine ⟨Ψ, hΨ, (pushforward_eq_iff Ψ hΨ).2 fun x v w ↦ ?_, hΨU, hΨU'⟩
  rcases (Set.ext_iff.1 hcover x).2 (Set.mem_univ _) with hx | hx
  · rw [hΨU x hx, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
      h₂.map_bilinFormAt x hx, ← h₁.map_bilinFormAt x hx]
    simp
  · rw [hΨU' x hx, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
      h₂'.map_bilinFormAt x hx, ← h₁'.map_bilinFormAt x hx]
    simp

end Trans

end Frame

end ContMDiffTwoForm

end Bundle

end SymplecticGeometry
