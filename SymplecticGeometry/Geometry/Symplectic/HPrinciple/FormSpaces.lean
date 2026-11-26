/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Basic
public import SymplecticGeometry.Geometry.Manifold.DeRham.Basic
import SymplecticGeometry.Geometry.Manifold.DeRham.Map
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic
public import TauCeti.Topology.CWComplex.Classical.CWType
import SymplecticGeometry.AlgebraicTopology.Homotopy.Domination
import SymplecticGeometry.Analysis.LocallyConvex.CWType
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import SymplecticGeometry.Geometry.Manifold.IsManifold.SecondCountable
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Topology
import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.CompletelyMetrizable

/-!
# The spaces of nondegenerate and of symplectic forms

Gromov's h-principle compares, on an open manifold `M`, two spaces of smooth two-forms: all
nondegenerate ones, and the symplectic ones in a fixed de Rham class.
Both are subsets of the type `Bundle.ContMDiffTwoForm I ⊤ E (TangentSpace I)` of smooth two-forms
on the tangent bundle, which is given the frame topology (`ContMDiffSection.frameTopology`) of a
covering frame system where a topology is needed; closedness and the class are read
through the linear equivalence `Bundle.ContMDiffTwoForm.tangentEquiv` with Tau Ceti's
`TauCeti.SmoothTwoForm`.

## Main definitions and results

* `nondegenerateForms I M`: the smooth two-forms on the tangent bundle that are nondegenerate on
  every tangent space, with `mem_nondegenerateForms`.
* `symplecticFormsInClass α`: for a smooth two-form `α` on `M`, the two-forms `ω` such that the
  Tau Ceti form of `ω` is symplectic and differs from `α` by an exact form, with
  `mem_symplecticFormsInClass`.
* `symplecticFormsInClass_subset_nondegenerateForms`: the second space lies in the first.
* `symplecticFormsInClass_congr`: the space depends on `α` only through its class modulo exact
  forms; `symplecticFormsInClass_eq_of_mk_eq` states this for de Rham classes of closed forms.
* `ContMDiffTwoForm.nondegenerate_bilinFormAt_tangentEquiv_symm_mpullback_timeSlice` and
  `ContMDiffTwoForm.tangentEquiv_symm_mpullback_timeSlice_zero`: the pull-back along a slice of a
  smooth isotopy of `M` into itself keeps nondegeneracy, and at time `0` of an isotopy from the
  identity it is the identity.
* `cwType_of_mpullback_timeSlice_mem`: when a smooth isotopy from the identity of `M` ends at a
  map `j` whose image has compact closure, a set `S` of nondegenerate forms inside a convex set `C`
  has CW type, provided the slices of the isotopy pull suitably nondegenerate forms of `C` into `S`.
* `cwType_nondegenerateForms`: when a smooth isotopy from the identity of `M` ends at a map
  `j` whose image has compact closure, the space of nondegenerate forms has CW type.
* `cwType_symplecticFormsInClass`: under the same hypothesis, for a closed two-form `α`, the
  space of symplectic forms in the class of `α` has CW type.

## Implementation notes

The space of symplectic forms is indexed by a representative `α` of the class rather than by
the class itself, since it is defined by a condition on `tangentEquiv ω - α`; for `α` that is not
closed the space is empty, as an exact form is closed. Both spaces are sets, so as types they
are the subtypes `{ω // ω ∈ nondegenerateForms I M}` and so on, with the subspace topology.

For `cwType_of_mpullback_timeSlice_mem`, the set `S` is dominated by the set `O` of forms of
`C` that are nondegenerate on the compact set `K = closure (range j)`: the inclusion goes into
`O`, pull-back along `j` comes back, and pull-back along the slices of the isotopy, run
backwards, is a homotopy from their composite to the identity. Each slice is an immersion of `M`
into itself, so its differential is invertible and it pulls a form nondegenerate at `h (t, x)`
back to one nondegenerate at `x`. The set `O` is the intersection of `C` with a set that is
open in the frame topology, which is metrizable and locally convex, so `O` has CW type by
`Convex.cwType_inter`, and `TauCeti.CWType.of_comp_homotopic_id` concludes. Metrizability uses
that `M` is second countable, as `j` embeds it into the compact set `K`
(`Topology.IsInducing.secondCountableTopology_of_isCompact_closure`).

`cwType_nondegenerateForms` applies it with `C` the whole space. `cwType_symplecticFormsInClass`
takes for `C` the convex set of forms `σ` with `tangentEquiv σ - α` exact, a translate of the
subspace of exact forms. Its forms are closed, as `α` is, so the slices of the isotopy pull them
back to closed forms, and to forms in the same class, by homotopy invariance along the
reparametrised isotopy (`TauCeti.SmoothForm.mpullback_sub_mpullback_timeSlice_mem_exactForms`).
Hence the slices take the forms of `C` that stay nondegenerate to symplectic forms in the class
of `α`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.3.
* [Y. Eliashberg and N. Mishachev, *Introduction to the h-principle*][EliashbergMishachev2002],
  §10.2.
* J. Milnor, *On spaces having the homotopy type of a CW-complex*, Trans. Amer. Math. Soc. 90
  (1959), 272–280, for the domination argument.
-/

public section

noncomputable section

open Bundle SymplecticGeometry.Bundle
open scoped Manifold

namespace SymplecticGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- The smooth two-forms on the tangent bundle of `M` that are nondegenerate on every tangent
space. -/
def nondegenerateForms : Set (ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))) :=
  {ω | ω.IsNondegenerate}

variable {I M}

@[simp]
theorem mem_nondegenerateForms {ω : ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))} :
    ω ∈ nondegenerateForms I M ↔ ω.IsNondegenerate :=
  Iff.rfl

/-- The smooth two-forms `ω` on the tangent bundle of `M` that are symplectic, as Tau Ceti forms
`tangentEquiv ω`, and lie in the class of `α` modulo exact forms, that is,
`tangentEquiv ω - α` is exact. -/
def symplecticFormsInClass (α : TauCeti.SmoothTwoForm I M) :
    Set (ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))) :=
  {ω | (ContMDiffTwoForm.tangentEquiv ω).IsSymplectic ∧
    ContMDiffTwoForm.tangentEquiv ω - α ∈ TauCeti.exactForms I M 2}

@[simp]
theorem mem_symplecticFormsInClass {α : TauCeti.SmoothTwoForm I M}
    {ω : ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))} :
    ω ∈ symplecticFormsInClass α ↔ (ContMDiffTwoForm.tangentEquiv ω).IsSymplectic ∧
      ContMDiffTwoForm.tangentEquiv ω - α ∈ TauCeti.exactForms I M 2 :=
  Iff.rfl

/-- A symplectic form in a class is nondegenerate. -/
theorem symplecticFormsInClass_subset_nondegenerateForms (α : TauCeti.SmoothTwoForm I M) :
    symplecticFormsInClass α ⊆ nondegenerateForms I M := fun _ hω ↦
  ContMDiffTwoForm.isNondegenerate_tangentEquiv_iff.mp hω.1.isNondegenerate

/-- The space of symplectic forms in the class of `α` depends on `α` only modulo exact forms. -/
theorem symplecticFormsInClass_congr {α β : TauCeti.SmoothTwoForm I M}
    (h : α - β ∈ TauCeti.exactForms I M 2) :
    symplecticFormsInClass α = symplecticFormsInClass β := by
  ext ω
  simp only [mem_symplecticFormsInClass, and_congr_right_iff]
  intro _
  constructor <;> intro hω
  · simpa using add_mem hω h
  · simpa using sub_mem hω h

/-- For closed forms `α` and `β` with the same de Rham class, the spaces of symplectic forms in
their classes agree. -/
theorem symplecticFormsInClass_eq_of_mk_eq {α β : TauCeti.closedForms I M 2}
    (h : TauCeti.deRhamCohomology.mk I 2 α = TauCeti.deRhamCohomology.mk I 2 β) :
    symplecticFormsInClass α.val = symplecticFormsInClass β.val :=
  symplecticFormsInClass_congr ((TauCeti.deRhamCohomology.mk_eq_mk_iff I 2 α β).mp h)

section CWType

open TopologicalSpace
open scoped ContDiff

variable [FiniteDimensional ℝ E] {ι : Type*}
  (e : ι → Trivialization (E [⋀^Fin 2]→L[ℝ] ℝ)
    (π (E [⋀^Fin 2]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- The pull-back along the slice at time `t` of a smooth isotopy `h` of `M` into itself takes a
two-form on the tangent bundle that is nondegenerate at `h (t, x)` to one that is nondegenerate
at `x`, since the slice is an immersion between manifolds of one dimension. -/
theorem Bundle.ContMDiffTwoForm.nondegenerate_bilinFormAt_tangentEquiv_symm_mpullback_timeSlice
    {f₀ f₁ : C^∞⟮I, M; I, M⟯} (h : TauCeti.SmoothIsotopy f₀ f₁)
    {σ : ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))} {t : unitInterval} {x : M}
    (hσ : (σ.bilinFormAt (h (t, x))).Nondegenerate) :
    ((ContMDiffTwoForm.tangentEquiv.symm (TauCeti.SmoothForm.mpullback (h.timeSlice t)
      (h.timeSlice t).contMDiff (ContMDiffTwoForm.tangentEquiv σ))).bilinFormAt
        x).Nondegenerate := by
  rw [ContMDiffTwoForm.bilinFormAt_tangentEquiv_symm]
  refine TauCeti.SmoothTwoForm.nondegenerate_bilinFormAt_mpullback_of_isImmersionAt _
    (((h.timeSlice t).isSmoothEmbedding).isImmersion.isImmersionAt x) (by simp) rfl ?_
  rwa [ContMDiffTwoForm.bilinFormAt_tangentEquiv, TauCeti.SmoothIsotopy.timeSlice_apply]

omit [FiniteDimensional ℝ E] in
/-- The pull-back along the slice at time `0` of a smooth isotopy from the identity of `M` is the
identity on two-forms on the tangent bundle. -/
theorem Bundle.ContMDiffTwoForm.tangentEquiv_symm_mpullback_timeSlice_zero
    {j : C^∞⟮I, M; I, M⟯} (h : TauCeti.SmoothIsotopy (ContMDiffMap.id) j)
    (σ : ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))) :
    ContMDiffTwoForm.tangentEquiv.symm (TauCeti.SmoothForm.mpullback (h.timeSlice 0)
      (h.timeSlice 0).contMDiff (ContMDiffTwoForm.tangentEquiv σ)) = σ := by
  have h0 : (h.timeSlice 0 : M → M) = id := funext fun x ↦ by simp
  rw [TauCeti.SmoothForm.mpullback_congr _ contMDiff_id h0, TauCeti.SmoothForm.mpullback_id,
    LinearMap.id_apply, LinearEquiv.symm_apply_apply]

/-- Let `h` be a smooth isotopy from the identity of `M` to a map `j` whose image has compact
closure, `C` a convex set of two-forms on the tangent bundle and `S` a set of nondegenerate forms
contained in `C`. Suppose that pulling back along the slice of `h` at any time `t` takes every
form of `C` that is nondegenerate at all points `h (t, x)` into `S`. Then `S`, in the frame
topology of a covering frame system, has CW type. -/
theorem cwType_of_mpullback_timeSlice_mem (hcover : ∀ x, ∃ i, x ∈ U i) {j : C^∞⟮I, M; I, M⟯}
    (h : TauCeti.SmoothIsotopy (ContMDiffMap.id) j) (hj : IsCompact (closure (Set.range j)))
    {C S : Set (ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M)))} (hC : Convex ℝ C)
    (hSC : S ⊆ C) (hSnd : S ⊆ nondegenerateForms I M)
    (hS : ∀ σ ∈ C, ∀ t : unitInterval, (∀ x, (σ.bilinFormAt (h (t, x))).Nondegenerate) →
      ContMDiffTwoForm.tangentEquiv.symm (TauCeti.SmoothForm.mpullback (h.timeSlice t)
        (h.timeSlice t).contMDiff (ContMDiffTwoForm.tangentEquiv σ)) ∈ S) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e U hU
    TauCeti.CWType S := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e U hU
  have := ContMDiffSection.isTopologicalAddGroup_frameTopology (I := I)
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e U hU
  have := ContMDiffSection.continuousSMul_frameTopology (𝕜 := ℝ) (I := I)
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e U hU
  have := ContMDiffSection.locallyConvexSpace_frameTopology (I := I)
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e U hU
  have : SecondCountableTopology H := I.secondCountableTopology
  have : SecondCountableTopology M :=
    h.isSmoothEmbedding_right.isEmbedding.isInducing.secondCountableTopology_of_isCompact_closure
      (H := H) hj
  have := ContMDiffSection.metrizableSpace_frameTopology (I := I)
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e U hU hcover
  -- The pull-back along the slice of `h` at time `t`.
  let P : ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M)) × unitInterval →
      ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M)) := fun q ↦
    ContMDiffTwoForm.tangentEquiv.symm (TauCeti.SmoothForm.mpullback (h.timeSlice q.2)
      (h.timeSlice q.2).contMDiff (ContMDiffTwoForm.tangentEquiv q.1))
  have hP : Continuous P :=
    ContMDiffTwoForm.continuous_tangentEquiv_symm_mpullback e U hU e U hU h hcover
  let K := closure (Set.range j)
  let O := C ∩
    {σ : ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M)) |
      ∀ x ∈ K, (σ.bilinFormAt x).Nondegenerate}
  have : TauCeti.CWType O := Convex.cwType_inter hC
    (ContMDiffTwoForm.isOpen_setOfPred_forall_mem_nondegenerate e U hU hcover hj)
  let i : C(S, O) :=
    ⟨fun σ ↦ ⟨σ, hSC σ.property, fun x _ ↦ (hSnd σ.property).nondegenerate_bilinFormAt x⟩,
      by fun_prop⟩
  let r : C(O, S) :=
    ⟨fun σ ↦ ⟨P (σ, 1), hS _ σ.property.1 1 fun x ↦ σ.property.2 _ (subset_closure ⟨x, by simp⟩)⟩,
      (hP.comp (continuous_subtypeVal.prodMk continuous_const)).subtype_mk _⟩
  refine TauCeti.CWType.of_comp_homotopic_id (i := i) (r := r) ⟨{
    toFun := fun q ↦ ⟨P (q.2, unitInterval.symm q.1), hS _ (hSC q.2.property) _ fun _ ↦
      (hSnd q.2.property).nondegenerate_bilinFormAt _⟩
    continuous_toFun := (hP.comp ((continuous_subtypeVal.comp continuous_snd).prodMk
      (unitInterval.continuous_symm.comp continuous_fst))).subtype_mk _
    map_zero_left := fun σ ↦ by simp [i, r]
    map_one_left := fun σ ↦ Subtype.ext (by
      simpa [P] using ContMDiffTwoForm.tangentEquiv_symm_mpullback_timeSlice_zero h σ) }⟩

/-- Let `M` compress into a compact set: some smooth isotopy `h` from the identity of `M` ends
at a map `j` whose image has compact closure. Then the space of nondegenerate two-forms on the
tangent bundle of `M`, in the frame topology of a covering frame system, has CW type.

Some hypothesis of this kind is needed. For `M` a disjoint union of countably many copies of
`ℝ²ⁿ` with `n ≥ 1`, the signs of `ωⁿ` at the origins of the copies retract the space continuously
onto the Cantor set `{±1}^ℕ`. A space of CW type cannot do this: a map from the Cantor set into a
CW complex has compact image, which meets only finitely many path components, so it cannot be
injective on the uncountably many path components of the Cantor set. -/
theorem cwType_nondegenerateForms (hcover : ∀ x, ∃ i, x ∈ U i) {j : C^∞⟮I, M; I, M⟯}
    (h : TauCeti.SmoothIsotopy (ContMDiffMap.id) j) (hj : IsCompact (closure (Set.range j))) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e U hU
    TauCeti.CWType (nondegenerateForms I M) :=
  cwType_of_mpullback_timeSlice_mem e U hU hcover h hj convex_univ (Set.subset_univ _) le_rfl
    fun _ _ _ hnd ↦ ContMDiffTwoForm.isNondegenerate_def.2 fun _ ↦
      ContMDiffTwoForm.nondegenerate_bilinFormAt_tangentEquiv_symm_mpullback_timeSlice h (hnd _)

/-- Let `M` compress into a compact set: some smooth isotopy `h` from the identity of `M` ends
at a map `j` whose image has compact closure. Then, for a closed two-form `α`, the space of
symplectic forms in the class of `α`, in the frame topology of a covering frame system, has
CW type.

Some hypothesis of this kind is needed. For `M` a disjoint union of countably many copies of
`ℝ²ⁿ` with `n ≥ 1`, and `α = 0`, the signs of `ωⁿ` at the origins of the copies retract this
space continuously onto the Cantor set `{±1}^ℕ`, which no space of CW type does, as for
`cwType_nondegenerateForms`. -/
theorem cwType_symplecticFormsInClass (hcover : ∀ x, ∃ i, x ∈ U i)
    {α : TauCeti.SmoothTwoForm I M} (hα : α ∈ TauCeti.closedForms I M 2) {j : C^∞⟮I, M; I, M⟯}
    (h : TauCeti.SmoothIsotopy (ContMDiffMap.id) j) (hj : IsCompact (closure (Set.range j))) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e U hU
    TauCeti.CWType (symplecticFormsInClass α) := by
  -- The forms whose Tau Ceti form lies in the class of `α`, a translate of a subspace.
  let C := {σ : ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M)) |
    ContMDiffTwoForm.tangentEquiv σ - α ∈ TauCeti.exactForms I M 2}
  have hC : Convex ℝ C := by
    simpa [C, Set.preimage, sub_eq_neg_add] using
      ((TauCeti.exactForms I M 2).convex.translate_preimage_right (-α)).linear_preimage
        ContMDiffTwoForm.tangentEquiv.toLinearMap
  refine cwType_of_mpullback_timeSlice_mem e U hU hcover h hj hC (fun _ hω ↦ hω.2)
    (symplecticFormsInClass_subset_nondegenerateForms α) fun σ hσ t hnd ↦ ?_
  -- The slices of `h` keep `C` and pull forms nondegenerate on their image back to symplectic
  -- forms.
  have hcl : ContMDiffTwoForm.tangentEquiv σ ∈ TauCeti.closedForms I M 2 := by
    simpa using add_mem (TauCeti.exactForms_le_closedForms I 2 hσ) hα
  have hex := TauCeti.SmoothForm.mpullback_sub_mpullback_timeSlice_mem_exactForms h t hcl
  rw [TauCeti.SmoothForm.mpullback_congr _ contMDiff_id (funext ContMDiffMap.id_apply),
    TauCeti.SmoothForm.mpullback_id, LinearMap.id_apply] at hex
  simp only [mem_symplecticFormsInClass, LinearEquiv.apply_symm_apply]
  refine ⟨⟨(TauCeti.SmoothForm.isClosed_iff_mem_closedForms _).2
    (TauCeti.SmoothForm.mpullback_mem_closedForms _ _ hcl), ?_⟩, ?_⟩
  · rw [← LinearEquiv.apply_symm_apply ContMDiffTwoForm.tangentEquiv
      (TauCeti.SmoothForm.mpullback _ _ _), ContMDiffTwoForm.isNondegenerate_tangentEquiv_iff]
    exact ContMDiffTwoForm.isNondegenerate_def.2 fun x ↦
      ContMDiffTwoForm.nondegenerate_bilinFormAt_tangentEquiv_symm_mpullback_timeSlice h (hnd x)
  · simpa using sub_mem hσ hex

end CWType

end SymplecticGeometry

end
