/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.HPrinciple.FormSpaces
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Components
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Topology
import SymplecticGeometry.Geometry.Symplectic.Manifold.Opens
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Comp
import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover
import TauCeti.Topology.Homeomorph.Pi

/-!
# The spaces of nondegenerate and of symplectic forms over the components

Let `U : ι → Opens M` be an open cover of a manifold `M`, such as the connected components
`ConnectedComponents.opens` of `M` (with `IsOpenCover.mk ConnectedComponents.iSup_opens`).
Nondegeneracy of a two-form is a pointwise condition and restriction to an open subset does not
change the form at a point, so a two-form is nondegenerate exactly when each of its restrictions
to the `U i` is, and so is a symplectic form (`Symplectic/Manifold/Opens.lean`). Exactness can be
tested on the `U i` when they are moreover pairwise disjoint (`DifferentialForm/Components.lean`),
so membership in the spaces of `HPrinciple/FormSpaces.lean` is tested on the members of the
cover. For the connected components of `M`, restriction identifies the two-forms on `M` with the
families of two-forms on the components, also as topological spaces for the frame topologies,
and so identifies each of the two spaces on `M` with the product of the spaces on the components.

## Main results

* `mem_nondegenerateForms_iff_forall_restrict`: a two-form on the tangent bundle of `M` is in
  `nondegenerateForms I M` exactly when each of its restrictions is in the space of nondegenerate
  forms on `U i`.
* `mem_symplecticFormsInClass_iff_forall_restrict`: for a pairwise disjoint open cover, a two-form
  is in `symplecticFormsInClass α` exactly when each restriction is in the space of symplectic
  forms in the class of the restriction of `α`.
* `continuous_tangentEquiv_symm_ofDisjointCover_opens`: gluing a family of two-forms on the
  components of `M` by `TauCeti.SmoothForm.ofDisjointCover` is continuous into the frame topology
  of any frame system on `M`.
* `restrictComponentsHomeomorph`: for covering frames on `M`, restriction to the components is a
  homeomorphism onto the product of the two-forms on the components, with
  `restrictComponentsHomeomorph_apply` and `restrictComponentsHomeomorph_symm_apply`.
* `nondegenerateFormsHomeomorphPi` and `symplecticFormsInClassHomeomorphPi`: its restrictions to
  `nondegenerateForms I M` and to `symplecticFormsInClass α`, onto the products of the spaces of
  nondegenerate forms, and of symplectic forms in the class of the restriction of `α`, on the
  components; `nondegenerateFormsHomeomorphPi_inclusion` says that they carry the inclusion of the
  second space into the first to the product of the inclusions on the components.

The restriction of a two-form `ω` on the tangent bundle is read through
`Bundle.ContMDiffTwoForm.tangentEquiv`, as in
`Bundle.ContMDiffTwoForm.continuous_tangentEquiv_symm_mpullback_subtypeVal`.

## Implementation notes

Each component `c.opens` carries `Bundle.ContMDiffTwoForm.trivializationAtFrameTopology`, the
frame topology of the trivializations `trivializationAt` at its points; `M` is assumed locally
connected, so that its components are open. The continuity of gluing compares the frame topology
on `M` with that of frames whose domains each lie in one component and on which the frame
coordinates of a form are those of its restriction
(`Bundle.ContMDiffTwoForm.exists_frameCoordinates_eq_frameCoordinates_mpullback_subtypeVal`);
they cover `M`, so their topology is the finer one (`ContMDiffSection.frameTopology_le_of_cover`).
On such a domain the frame coordinates of the glued form are those of one form of the family,
composed with an inclusion, as in the proof of Tau Ceti's
`ContMDiffSection.frameTopology_le_of_refinement`, which this argument adapts.

The homeomorphisms of the two spaces restrict `restrictComponentsHomeomorph` with Mathlib's
`Homeomorph.sets`, onto the subspace `Set.univ.pi` of the product, and then pass to the product
of subspaces by Tau Ceti's `Homeomorph.Set.univPi`, whose underlying equivalence is
`Equiv.Set.univPi`. They need no instance on the components beyond those of open
submanifolds; a statement about each component, such as `cwType_nondegenerateForms`, brings
what it needs of `c.opens` itself.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.3.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Chapters 14 and 17.
-/

public section

open Bundle Function SymplecticGeometry.Bundle TopologicalSpace
open scoped Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  {ι : Type*} {U : ι → Opens M}

namespace SymplecticGeometry

/-- A smooth two-form `ω` on the tangent bundle of `M` is nondegenerate exactly when, for each
member `U i` of an open cover of `M`, its restriction to `U i` is nondegenerate. -/
theorem mem_nondegenerateForms_iff_forall_restrict (hcover : IsOpenCover U)
    {ω : ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))} :
    ω ∈ nondegenerateForms I M ↔
      ∀ i, ContMDiffTwoForm.tangentEquiv.symm (TauCeti.SmoothForm.mpullback
        (Subtype.val : U i → M) contMDiff_subtypeVal (ContMDiffTwoForm.tangentEquiv ω)) ∈
          nondegenerateForms I (U i) := by
  simp only [mem_nondegenerateForms, ContMDiffTwoForm.isNondegenerate_tangentEquiv_symm_iff,
    ← TauCeti.SmoothTwoForm.isNondegenerate_iff_forall_mpullback_subtypeVal hcover,
    ContMDiffTwoForm.isNondegenerate_tangentEquiv_iff]

/-- For pairwise disjoint open subsets `U i` covering `M` and a smooth two-form `α` on `M`, a
smooth two-form `ω` on the tangent bundle of `M` is symplectic in the class of `α` exactly when,
for each `i`, its restriction to `U i` is symplectic in the class of the restriction of `α`. -/
theorem mem_symplecticFormsInClass_iff_forall_restrict (hU : Pairwise (Disjoint on U))
    (hcover : IsOpenCover U) {α : TauCeti.SmoothTwoForm I M}
    {ω : ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))} :
    ω ∈ symplecticFormsInClass α ↔
      ∀ i, ContMDiffTwoForm.tangentEquiv.symm (TauCeti.SmoothForm.mpullback
        (Subtype.val : U i → M) contMDiff_subtypeVal (ContMDiffTwoForm.tangentEquiv ω)) ∈
          symplecticFormsInClass
            (TauCeti.SmoothForm.mpullback (Subtype.val : U i → M) contMDiff_subtypeVal α) := by
  simp only [mem_symplecticFormsInClass, LinearEquiv.apply_symm_apply, ← map_sub, forall_and,
    ← TauCeti.SmoothTwoForm.isSymplectic_iff_forall_mpullback_subtypeVal hcover,
    ← TauCeti.SmoothForm.mem_exactForms_iff_forall_mpullback_subtypeVal hU hcover]

section Homeomorph

open scoped TauCeti.ManifoldWeakWhitney

variable [FiniteDimensional ℝ E] [LocallyConnectedSpace M] {κ : Type*}
  (e : κ → Trivialization (E [⋀^Fin 2]→L[ℝ] ℝ)
    (π (E [⋀^Fin 2]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x)))
  [∀ i, MemTrivializationAtlas (e i)]
  (W : κ → Opens M) (hW : ∀ i, (W i : Set M) ⊆ (e i).baseSet)

/-- Gluing smooth two-forms on the tangent bundles of the connected components `c.opens` of `M`
into a two-form on the tangent bundle of `M`, by `TauCeti.SmoothForm.ofDisjointCover`, is
continuous from the product of the topologies `ContMDiffTwoForm.trivializationAtFrameTopology` of
the `c.opens` to the frame topology of any frame system `e i` over `W i` of the two-forms on `M`. -/
theorem continuous_tangentEquiv_symm_ofDisjointCover_opens :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e W hW
    let _ (c : ConnectedComponents M) := ContMDiffTwoForm.trivializationAtFrameTopology I c.opens
    Continuous fun σ : ∀ c : ConnectedComponents M,
        ContMDiffTwoForm I ⊤ E (TangentSpace I (M := c.opens)) ↦
      (ContMDiffTwoForm.tangentEquiv.symm (TauCeti.SmoothForm.ofDisjointCover
        ConnectedComponents.pairwise_disjoint_opens (IsOpenCover.mk ConnectedComponents.iSup_opens)
          fun c ↦ ContMDiffTwoForm.tangentEquiv (σ c)) :
        ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))) := by
  let eC (c : ConnectedComponents M) (x : c.opens) := trivializationAt (E [⋀^Fin 2]→L[ℝ] ℝ)
    (fun y : c.opens ↦ TangentSpace I y [⋀^Fin 2]→L[ℝ] Trivial c.opens ℝ y) x
  let UC (c : ConnectedComponents M) (x : c.opens) : Opens c.opens := ⟨_, (eC c x).open_baseSet⟩
  -- Frames on `M` whose domains `D x` each lie in the component of `x`, where the frame
  -- coordinates of a form are those of its restriction to that component.
  choose D hxD hDU hD hD' hDω using fun x : M ↦
    ContMDiffTwoForm.exists_frameCoordinates_eq_frameCoordinates_mpullback_subtypeVal (I := I)
      (U := (ConnectedComponents.mk x).opens) ⟨x, ConnectedComponents.mem_opens.2 rfl⟩
  have key :
      let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) _ D hD
      let _ (c : ConnectedComponents M) :=
        ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (eC c) (UC c)
          fun _ ↦ subset_rfl
      Continuous fun σ : ∀ c : ConnectedComponents M,
          ContMDiffTwoForm I ⊤ E (TangentSpace I (M := c.opens)) ↦
        (ContMDiffTwoForm.tangentEquiv.symm (TauCeti.SmoothForm.ofDisjointCover
          ConnectedComponents.pairwise_disjoint_opens
            (IsOpenCover.mk ConnectedComponents.iSup_opens)
            fun c ↦ ContMDiffTwoForm.tangentEquiv (σ c)) :
          ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))) := by
    intro _ _
    refine (ContMDiffSection.continuous_frameTopology_iff_frameCoordinates _ D hD).mpr fun x ↦ ?_
    set c := ConnectedComponents.mk x
    -- On `D x`, the frame coordinates of the glued form are those of its `c`-th form, composed
    -- with the inclusion `j` of `D x` into its preimage in `c.opens`.
    let j : C^((⊤ : ℕ∞) : WithTop ℕ∞)⟮I, D x; I,
        (D x).comap (⟨Subtype.val, continuous_subtypeVal⟩ : C(c.opens, M))⟯ :=
      ⟨fun z ↦ ⟨Opens.inclusion (hDU x) z, z.property⟩,
        (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).mp (contMDiff_inclusion (hDU x))⟩
    refine ((ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp
      (((ContMDiffSection.continuous_frameCoordinates_of_cover (eC c) (UC c)
        (fun _ ↦ subset_rfl) (fun y ↦ ⟨y, FiberBundle.mem_baseSet_trivializationAt' y⟩) _ _
          (hD' x)).comp (continuous_apply c)).prodMk (continuous_const (y := j))))).congr
            fun σ ↦ ContMDiffMap.ext fun z ↦ ?_
    rw [Function.comp_apply, hDω x _ z z.property, LinearEquiv.apply_symm_apply,
      TauCeti.SmoothForm.mpullback_subtypeVal_ofDisjointCover,
      LinearEquiv.symm_apply_apply, ContMDiffMap.comp_apply]
    -- `j z` is `⟨⟨z, _⟩, _⟩` by the definition of `j`.
    rfl
  intro _ tC
  -- The topology on each factor is the frame topology of the frames `eC c` over `UC c`.
  rw [show tC = fun c ↦ ContMDiffSection.frameTopology (eC c) (UC c) fun _ ↦ subset_rfl from
    funext fun c ↦ ContMDiffTwoForm.trivializationAtFrameTopology_def I c.opens]
  exact continuous_le_rng
    (ContMDiffSection.frameTopology_le_of_cover _ D hD (fun x ↦ ⟨x, hxD x⟩) e W hW) key

/-- For covering frames `e i` over `W i` on the two-forms of `M`, restriction to the connected
components is a homeomorphism from the smooth two-forms on the tangent bundle of `M` onto the
product, over the components `c`, of the smooth two-forms on the tangent bundle of `c.opens`.
Each factor carries `ContMDiffTwoForm.trivializationAtFrameTopology`. The inverse glues a family
of forms by `TauCeti.SmoothForm.ofDisjointCover` (`restrictComponentsHomeomorph_symm_apply`). -/
noncomputable def restrictComponentsHomeomorph (hcover : ∀ x, ∃ i, x ∈ W i) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e W hW
    let _ (c : ConnectedComponents M) := ContMDiffTwoForm.trivializationAtFrameTopology I c.opens
    ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M)) ≃ₜ
      ∀ c : ConnectedComponents M, ContMDiffTwoForm I ⊤ E (TangentSpace I (M := c.opens)) := by
  intro _ _
  let Φ := ContMDiffTwoForm.tangentEquiv (I := I) (M := M) ≪≫ₗ
    TauCeti.SmoothForm.disjointCoverEquiv ℝ 2 ConnectedComponents.pairwise_disjoint_opens
      (IsOpenCover.mk ConnectedComponents.iSup_opens) ≪≫ₗ
        LinearEquiv.piCongrRight fun c ↦ ContMDiffTwoForm.tangentEquiv.symm
  refine ⟨Φ.toEquiv, continuous_pi fun c ↦ ?_,
    (continuous_tangentEquiv_symm_ofDisjointCover_opens e W hW).congr fun σ ↦ ?_⟩
  · have h := ContMDiffTwoForm.continuous_tangentEquiv_symm_mpullback_subtypeVal e W hW
      (fun x : c.opens ↦ trivializationAt _ _ x)
      (fun x ↦ ⟨_, (trivializationAt (E [⋀^Fin 2]→L[ℝ] ℝ)
        (fun y : c.opens ↦ TangentSpace I y [⋀^Fin 2]→L[ℝ] Trivial c.opens ℝ y) x).open_baseSet⟩)
      (fun _ ↦ subset_rfl) hcover
    rw [← ContMDiffTwoForm.trivializationAtFrameTopology_def] at h
    refine h.congr fun ω ↦ ?_
    simp [Φ]
  · exact (Φ.symm_apply_eq.mpr (funext fun c ↦ by simp [Φ])).symm

@[simp]
theorem restrictComponentsHomeomorph_apply (hcover : ∀ x, ∃ i, x ∈ W i)
    (ω : ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))) (c : ConnectedComponents M) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e W hW
    let _ (c : ConnectedComponents M) := ContMDiffTwoForm.trivializationAtFrameTopology I c.opens
    restrictComponentsHomeomorph e W hW hcover ω c =
      ContMDiffTwoForm.tangentEquiv.symm (TauCeti.SmoothForm.mpullback
        (Subtype.val : c.opens → M) contMDiff_subtypeVal (ContMDiffTwoForm.tangentEquiv ω)) := by
  intro _ _
  exact congrArg ContMDiffTwoForm.tangentEquiv.symm
    (TauCeti.SmoothForm.disjointCoverEquiv_apply _ _ _ c)

@[simp]
theorem restrictComponentsHomeomorph_symm_apply (hcover : ∀ x, ∃ i, x ∈ W i)
    (σ : ∀ c : ConnectedComponents M, ContMDiffTwoForm I ⊤ E (TangentSpace I (M := c.opens))) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e W hW
    let _ (c : ConnectedComponents M) := ContMDiffTwoForm.trivializationAtFrameTopology I c.opens
    (restrictComponentsHomeomorph e W hW hcover).symm σ =
      ContMDiffTwoForm.tangentEquiv.symm (TauCeti.SmoothForm.ofDisjointCover
        ConnectedComponents.pairwise_disjoint_opens (IsOpenCover.mk ConnectedComponents.iSup_opens)
          fun c ↦ ContMDiffTwoForm.tangentEquiv (σ c)) := by
  intro _ _
  refine (Homeomorph.symm_apply_eq _).mpr (funext fun c ↦ ?_)
  simp

/-- For covering frames `e i` over `W i` on the two-forms of `M`, restriction to the connected
components is a homeomorphism from the nondegenerate two-forms on the tangent bundle of `M`
onto the product, over the components `c`, of the nondegenerate two-forms on the tangent bundle
of `c.opens`, with the topologies of `restrictComponentsHomeomorph`. -/
noncomputable def nondegenerateFormsHomeomorphPi (hcover : ∀ x, ∃ i, x ∈ W i) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e W hW
    let _ (c : ConnectedComponents M) := ContMDiffTwoForm.trivializationAtFrameTopology I c.opens
    nondegenerateForms I M ≃ₜ ∀ c : ConnectedComponents M, nondegenerateForms I c.opens := by
  intro _ _
  exact ((restrictComponentsHomeomorph e W hW hcover).sets (s := nondegenerateForms I M)
    (t := Set.univ.pi fun c : ConnectedComponents M ↦ nondegenerateForms I c.opens)
    (Set.ext fun ω ↦ by
      simp [mem_nondegenerateForms_iff_forall_restrict
        (IsOpenCover.mk ConnectedComponents.iSup_opens)])).trans (Homeomorph.Set.univPi _)

@[simp]
theorem coe_nondegenerateFormsHomeomorphPi_apply (hcover : ∀ x, ∃ i, x ∈ W i)
    (ω : nondegenerateForms I M) (c : ConnectedComponents M) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e W hW
    let _ (c : ConnectedComponents M) := ContMDiffTwoForm.trivializationAtFrameTopology I c.opens
    (nondegenerateFormsHomeomorphPi e W hW hcover ω c : ContMDiffTwoForm I ⊤ E
      (TangentSpace I (M := c.opens))) = restrictComponentsHomeomorph e W hW hcover ω c := by
  intro _ _
  rw [nondegenerateFormsHomeomorphPi, Homeomorph.trans_apply, Homeomorph.Set.coe_univPi_apply,
    Homeomorph.subtype_apply_coe]

@[simp]
theorem coe_nondegenerateFormsHomeomorphPi_symm_apply (hcover : ∀ x, ∃ i, x ∈ W i)
    (σ : ∀ c : ConnectedComponents M, nondegenerateForms I c.opens) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e W hW
    let _ (c : ConnectedComponents M) := ContMDiffTwoForm.trivializationAtFrameTopology I c.opens
    ((nondegenerateFormsHomeomorphPi e W hW hcover).symm σ :
      ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))) =
        (restrictComponentsHomeomorph e W hW hcover).symm fun c ↦ σ c := by
  intro _ _
  simp [nondegenerateFormsHomeomorphPi]

/-- For covering frames `e i` over `W i` on the two-forms of `M` and a smooth two-form `α` on
`M`, restriction to the connected components is a homeomorphism from the symplectic forms on the
tangent bundle of `M` in the class of `α` onto the product, over the components `c`, of the
symplectic forms on the tangent bundle of `c.opens` in the class of the restriction of `α`, with
the topologies of `restrictComponentsHomeomorph`. -/
noncomputable def symplecticFormsInClassHomeomorphPi (hcover : ∀ x, ∃ i, x ∈ W i)
    (α : TauCeti.SmoothTwoForm I M) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e W hW
    let _ (c : ConnectedComponents M) := ContMDiffTwoForm.trivializationAtFrameTopology I c.opens
    symplecticFormsInClass α ≃ₜ ∀ c : ConnectedComponents M, symplecticFormsInClass
      (TauCeti.SmoothForm.mpullback (Subtype.val : c.opens → M) contMDiff_subtypeVal α) := by
  intro _ _
  exact ((restrictComponentsHomeomorph e W hW hcover).sets (s := symplecticFormsInClass α)
    (t := Set.univ.pi fun c : ConnectedComponents M ↦ symplecticFormsInClass
      (TauCeti.SmoothForm.mpullback (Subtype.val : c.opens → M) contMDiff_subtypeVal α))
    (Set.ext fun ω ↦ by
      simp [mem_symplecticFormsInClass_iff_forall_restrict
        ConnectedComponents.pairwise_disjoint_opens
        (IsOpenCover.mk ConnectedComponents.iSup_opens)])).trans (Homeomorph.Set.univPi _)

@[simp]
theorem coe_symplecticFormsInClassHomeomorphPi_apply (hcover : ∀ x, ∃ i, x ∈ W i)
    (α : TauCeti.SmoothTwoForm I M) (ω : symplecticFormsInClass α) (c : ConnectedComponents M) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e W hW
    let _ (c : ConnectedComponents M) := ContMDiffTwoForm.trivializationAtFrameTopology I c.opens
    (symplecticFormsInClassHomeomorphPi e W hW hcover α ω c : ContMDiffTwoForm I ⊤ E
      (TangentSpace I (M := c.opens))) = restrictComponentsHomeomorph e W hW hcover ω c := by
  intro _ _
  rw [symplecticFormsInClassHomeomorphPi, Homeomorph.trans_apply, Homeomorph.Set.coe_univPi_apply,
    Homeomorph.subtype_apply_coe]

@[simp]
theorem coe_symplecticFormsInClassHomeomorphPi_symm_apply (hcover : ∀ x, ∃ i, x ∈ W i)
    (α : TauCeti.SmoothTwoForm I M)
    (σ : ∀ c : ConnectedComponents M, symplecticFormsInClass
      (TauCeti.SmoothForm.mpullback (Subtype.val : c.opens → M) contMDiff_subtypeVal α)) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e W hW
    let _ (c : ConnectedComponents M) := ContMDiffTwoForm.trivializationAtFrameTopology I c.opens
    ((symplecticFormsInClassHomeomorphPi e W hW hcover α).symm σ :
      ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))) =
        (restrictComponentsHomeomorph e W hW hcover).symm fun c ↦ σ c := by
  intro _ _
  simp [symplecticFormsInClassHomeomorphPi]

/-- The homeomorphisms `nondegenerateFormsHomeomorphPi` and `symplecticFormsInClassHomeomorphPi`
carry the inclusion of the symplectic forms in the class of `α` into the nondegenerate forms on
`M` to the product of these inclusions on the components. -/
theorem nondegenerateFormsHomeomorphPi_inclusion (hcover : ∀ x, ∃ i, x ∈ W i)
    (α : TauCeti.SmoothTwoForm I M) (ω : symplecticFormsInClass α) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e W hW
    let _ (c : ConnectedComponents M) := ContMDiffTwoForm.trivializationAtFrameTopology I c.opens
    nondegenerateFormsHomeomorphPi e W hW hcover
        (Set.inclusion (symplecticFormsInClass_subset_nondegenerateForms α) ω) =
      fun c ↦ Set.inclusion (symplecticFormsInClass_subset_nondegenerateForms _)
        (symplecticFormsInClassHomeomorphPi e W hW hcover α ω c) := by
  intro _ _
  funext c
  apply Subtype.ext
  rw [coe_nondegenerateFormsHomeomorphPi_apply, coe_symplecticFormsInClassHomeomorphPi_apply,
    Set.coe_inclusion]

end Homeomorph

end SymplecticGeometry

end
