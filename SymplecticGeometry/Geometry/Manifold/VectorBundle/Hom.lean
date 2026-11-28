/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Trivial
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Fibrewise linear maps as sections of hom bundles

Let `Φ x : V₁ x ≃L V₂ x` be fibrewise equivalences of vector bundles whose map of total spaces is
`C^n`, with `V₁` of finite rank. Then the fibrewise inverses `(Φ x)⁻¹` form a `C^n` section of the
bundle of continuous linear maps `V₂ x →L V₁ x` (`contMDiff_hom_bundle_symm`). The forward maps
`Φ x` form a `C^n` section by Tau Ceti's `TauCeti.contMDiff_hom_bundle_iff`, and so do their
inverses by Tau Ceti's `ContMDiff.clm_bundle_equiv_symm`. As in
`TauCeti.contMDiff_bundle_symm`, only the source bundle `V₁` needs finite rank.

A map `g` out of the total space of the trivial bundle with fibre `W` over `M` is `C^n` (at a
point, within a set, on a set) exactly when `(x, v) ↦ g ⟨x, v⟩` is, as a map on `M × W`
(`Bundle.Trivial.contMDiff_comp_mk_iff` and its `At`, `WithinAt` and `On` forms). These are
Mathlib's `Diffeomorph.contMDiff_comp_diffeomorph_iff` and its variants, applied to the inverse of
Tau Ceti's `Bundle.Trivial.diffeomorphProd`, with the composite written out.

For a family `Φ x : W →L V x` out of a fixed space `W` of finite dimension, the file also reads
the smoothness of `Φ` as a section of the hom bundle from the trivial bundle with fibre `W` on the
product `M × W` (`contMDiffAt_hom_trivial_iff`, and `contMDiffOn_hom_trivial_iff` over an open
set), through
`TauCeti.contMDiffAt_hom_bundle_iff` and `Bundle.Trivial.contMDiffAt_comp_mk_iff` above.

A fibrewise map `φ x : E₁ x → E₂ x` of fibre bundles is `C^n` on total spaces when, near each
point `a` of the base, it is read in the trivializations at `a` as a family of continuous linear
maps of the models that is `C^n` at `a` (`Bundle.contMDiff_bundleMap_of_coordinates`). The proof
is that of Tau Ceti's `TauCeti.contMDiff_bundleMap_of_constant_coordinates`, for a fixed linear
map, with the family in place of that map.

A family `A x : V x →L V' x` can be tested on a `C^n` local frame `s` of `V` on an open set
`u`: if each `x ↦ A x (s i x)` is `C^n` on `u`, then `A` is a `C^n` section of the hom bundle
on `u` (`IsLocalFrameOn.contMDiffOn_hom_bundle`), and its map of total spaces is `C^n` over `u`
(`IsLocalFrameOn.contMDiffOn_bundleMap`). Near a point, each vector of the local frame of a
trivialization is a combination of the `s i` whose coefficients are `C^n` by Tau Ceti's
`IsLocalFrameOn.contMDiffOn_coeff`, so `A` is `C^n` on that frame, and Tau Ceti's
`TauCeti.Manifold.contMDiffOn_hom_of_localFrame` and `TauCeti.contMDiffAt_hom_bundle_iff`
conclude. Out of a bundle whose model fibre has dimension one, it is enough to test `A` on one
section that is `C^n` and nowhere zero on `u` (`ContMDiffOn.hom_bundle_of_finrank_eq_one` and
`ContMDiffOn.bundleMap_of_finrank_eq_one`), since such a section is a local frame by Tau Ceti's
`IsLocalFrameOn.of_finrank_eq_one`.
-/

public section

open Bundle
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] {I : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace M] [ChartedSpace HB M]
  {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {V₁ V₂ : M → Type*} [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, IsTopologicalAddGroup (V₁ x)]
  [∀ x, ContinuousSMul 𝕜 (V₁ x)] [TopologicalSpace (TotalSpace F₁ V₁)]
  [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul 𝕜 (V₂ x)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂] {n : WithTop ℕ∞}

namespace SymplecticGeometry

/-- The fibrewise inverses of fibrewise equivalences `Φ x : V₁ x ≃L V₂ x` whose map of total
spaces is `C^n` form a `C^n` section of the bundle of continuous linear maps `V₂ x →L V₁ x`, when
`V₁` has finite rank. -/
theorem contMDiff_hom_bundle_symm (Φ : ∀ x, V₁ x ≃L[𝕜] V₂ x)
    (hΦ : ContMDiff (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) n
      (fun p : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ p.proj (Φ p.proj p.snd))) :
    ContMDiff I (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₁)) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun x ↦ V₂ x →L[𝕜] V₁ x) x
        ((Φ x).symm : V₂ x →L[𝕜] V₁ x)) := by
  have := FiniteDimensional.completeSpace 𝕜 F₁
  exact ((TauCeti.contMDiff_hom_bundle_iff fun x ↦ (Φ x : V₁ x →L[𝕜] V₂ x)).2
    hΦ).clm_bundle_equiv_symm

end SymplecticGeometry

section Trivial

omit [FiniteDimensional 𝕜 F₁]

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W] [FiniteDimensional 𝕜 W]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 W] in
/-- A map `g` out of the total space of the trivial bundle with fibre `W` is `C^n` within
`(fun p ↦ (p.proj, p.snd)) ⁻¹' s` at `⟨x, v⟩` exactly when `(y, w) ↦ g ⟨y, w⟩`, as a map on
`M × W`, is `C^n` within `s` at `(x, v)`. -/
theorem Bundle.Trivial.contMDiffWithinAt_comp_mk_iff {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace 𝕜 EN] [TopologicalSpace HN] {J : ModelWithCorners 𝕜 EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] {g : TotalSpace W (Trivial M W) → N} {s : Set (M × W)} {x : M} {v : W} :
    ContMDiffWithinAt (I.prod 𝓘(𝕜, W)) J n (fun p : M × W ↦ g ⟨p.1, p.2⟩) s (x, v) ↔
      ContMDiffWithinAt (I.prod 𝓘(𝕜, W)) J n g
        ((fun p : TotalSpace W (Trivial M W) ↦ (p.proj, p.snd)) ⁻¹' s) ⟨x, v⟩ := by
  simpa only [Function.comp_def, diffeomorphProd_symm_apply, Diffeomorph.symm_symm,
    funext (diffeomorphProd_apply I M W n)] using
    (diffeomorphProd I M W n).symm.contMDiffWithinAt_comp_diffeomorph_iff le_rfl

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 W] in
/-- A map `g` out of the total space of the trivial bundle with fibre `W` is `C^n` at `⟨x, v⟩`
exactly when `(y, w) ↦ g ⟨y, w⟩`, as a map on `M × W`, is `C^n` at `(x, v)`. -/
theorem Bundle.Trivial.contMDiffAt_comp_mk_iff {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace 𝕜 EN] [TopologicalSpace HN] {J : ModelWithCorners 𝕜 EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] {g : TotalSpace W (Trivial M W) → N} {x : M} {v : W} :
    ContMDiffAt (I.prod 𝓘(𝕜, W)) J n (fun p : M × W ↦ g ⟨p.1, p.2⟩) (x, v) ↔
      ContMDiffAt (I.prod 𝓘(𝕜, W)) J n g ⟨x, v⟩ := by
  simpa only [Function.comp_def, diffeomorphProd_symm_apply] using
    (diffeomorphProd I M W n).symm.contMDiffAt_comp_diffeomorph_iff le_rfl

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 W] in
/-- A map `g` out of the total space of the trivial bundle with fibre `W` is `C^n` on
`(fun p ↦ (p.proj, p.snd)) ⁻¹' s` exactly when `(y, w) ↦ g ⟨y, w⟩`, as a map on `M × W`, is
`C^n` on `s`. -/
theorem Bundle.Trivial.contMDiffOn_comp_mk_iff {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace 𝕜 EN] [TopologicalSpace HN] {J : ModelWithCorners 𝕜 EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] {g : TotalSpace W (Trivial M W) → N} {s : Set (M × W)} :
    ContMDiffOn (I.prod 𝓘(𝕜, W)) J n (fun p : M × W ↦ g ⟨p.1, p.2⟩) s ↔
      ContMDiffOn (I.prod 𝓘(𝕜, W)) J n g
        ((fun p : TotalSpace W (Trivial M W) ↦ (p.proj, p.snd)) ⁻¹' s) :=
  ⟨fun h p hp ↦ contMDiffWithinAt_comp_mk_iff.1 (h (p.proj, p.snd) hp),
    fun h q hq ↦ contMDiffWithinAt_comp_mk_iff.2 (h ⟨q.1, q.2⟩ hq)⟩

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 W] in
/-- A map `g` out of the total space of the trivial bundle with fibre `W` is `C^n` exactly when
`(y, w) ↦ g ⟨y, w⟩`, as a map on `M × W`, is `C^n`. -/
theorem Bundle.Trivial.contMDiff_comp_mk_iff {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace 𝕜 EN] [TopologicalSpace HN] {J : ModelWithCorners 𝕜 EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] {g : TotalSpace W (Trivial M W) → N} :
    ContMDiff (I.prod 𝓘(𝕜, W)) J n (fun p : M × W ↦ g ⟨p.1, p.2⟩) ↔
      ContMDiff (I.prod 𝓘(𝕜, W)) J n g := by
  simpa only [Function.comp_def, diffeomorphProd_symm_apply] using
    (diffeomorphProd I M W n).symm.contMDiff_comp_diffeomorph_iff le_rfl

namespace SymplecticGeometry

/-- A family of continuous linear maps `Φ x : W →L V₂ x` from a fixed space `W` of finite
dimension is a `C^n` section at `x` of the bundle of continuous linear maps from the trivial bundle
with fibre `W` to `V₂` exactly when `(y, v) ↦ Φ y v`, as a map from `M × W` to the total space of
`V₂`, is `C^n` at `(x, v)` for every `v`. -/
theorem contMDiffAt_hom_trivial_iff (Φ : ∀ x, W →L[𝕜] V₂ x) (x : M) :
    ContMDiffAt I (I.prod 𝓘(𝕜, W →L[𝕜] F₂)) n
        (fun y ↦ TotalSpace.mk' (W →L[𝕜] F₂) (E := fun y ↦ Trivial M W y →L[𝕜] V₂ y) y
          (Φ y : W →L[𝕜] V₂ y)) x ↔
      ∀ v : W, ContMDiffAt (I.prod 𝓘(𝕜, W)) (I.prod 𝓘(𝕜, F₂)) n
        (fun p : M × W ↦ TotalSpace.mk' F₂ p.1 (Φ p.1 p.2)) (x, v) := by
  rw [TauCeti.contMDiffAt_hom_bundle_iff]
  exact forall_congr' fun v ↦ Trivial.contMDiffAt_comp_mk_iff.symm

/-- A family of continuous linear maps `Φ x : W →L V₂ x` from a fixed space `W` of finite
dimension is a `C^n` section on an open set `U` of the bundle of continuous linear maps from the
trivial bundle with fibre `W` to `V₂` exactly when `(y, v) ↦ Φ y v`, as a map from `M × W` to the
total space of `V₂`, is `C^n` on `U ×ˢ univ`. -/
theorem contMDiffOn_hom_trivial_iff (Φ : ∀ x, W →L[𝕜] V₂ x) {U : Set M} (hU : IsOpen U) :
    ContMDiffOn I (I.prod 𝓘(𝕜, W →L[𝕜] F₂)) n
        (fun y ↦ TotalSpace.mk' (W →L[𝕜] F₂) (E := fun y ↦ Trivial M W y →L[𝕜] V₂ y) y
          (Φ y : W →L[𝕜] V₂ y)) U ↔
      ContMDiffOn (I.prod 𝓘(𝕜, W)) (I.prod 𝓘(𝕜, F₂)) n
        (fun p : M × W ↦ TotalSpace.mk' F₂ p.1 (Φ p.1 p.2)) (U ×ˢ Set.univ) := by
  refine ⟨fun h p hp ↦ ?_, fun h x hx ↦ ?_⟩
  · exact ((contMDiffAt_hom_trivial_iff Φ p.1).1 (h.contMDiffAt (hU.mem_nhds hp.1))
      p.2).contMDiffWithinAt
  · exact ((contMDiffAt_hom_trivial_iff Φ x).2 fun v ↦
      h.contMDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hx, Set.mem_univ v⟩)).contMDiffWithinAt

end SymplecticGeometry

end Trivial


section Coordinates

variable {𝕜 B EB HB F₁ F₂ : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₁ E₂ : B → Type*} [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂] {n : WithTop ℕ∞}

/-- **A fibrewise map with `C^n` coordinates is `C^n`.** Let `φ x : E₁ x → E₂ x` be maps of the
fibres of two fibre bundles. Suppose that for each point `a` of the base there is a family of
continuous linear maps `A x : F₁ →L F₂`, `C^n` at `a`, such that, read in the trivializations at
`a`, the map `φ x` is `A x` at every point `x` of both base sets. Then the map of total spaces
induced by `φ` is `C^n`. -/
theorem Bundle.contMDiff_bundleMap_of_coordinates (φ : ∀ x, E₁ x → E₂ x)
    (hφ : ∀ a, ∃ A : B → F₁ →L[𝕜] F₂, ContMDiffAt IB 𝓘(𝕜, F₁ →L[𝕜] F₂) n A a ∧
      ∀ x ∈ (trivializationAt F₁ E₁ a).baseSet ∩ (trivializationAt F₂ E₂ a).baseSet, ∀ v,
        (trivializationAt F₂ E₂ a ⟨x, φ x v⟩).2 = A x (trivializationAt F₁ E₁ a ⟨x, v⟩).2) :
    ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n
      (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ (E := E₂) p.proj (φ p.proj p.snd)) := by
  intro p
  obtain ⟨A, hA, hφA⟩ := hφ p.proj
  rw [contMDiffAt_totalSpace_iff]
  refine ⟨contMDiffAt_proj _, ?_⟩
  have hc := (contMDiffAt_totalSpace_iff.mp
    (contMDiffAt_id (I := IB.prod 𝓘(𝕜, F₁)) (x := p) (n := n))).2
  refine ((hA.comp p (contMDiffAt_proj E₁)).clm_apply hc).congr_of_eventuallyEq ?_
  have hb := ((FiberBundle.continuous_proj F₁ E₁).continuousAt).preimage_mem_nhds
    (((trivializationAt F₁ E₁ p.proj).open_baseSet.inter
      (trivializationAt F₂ E₂ p.proj).open_baseSet).mem_nhds
        ⟨mem_baseSet_trivializationAt F₁ E₁ p.proj,
          mem_baseSet_trivializationAt F₂ E₂ p.proj⟩)
  filter_upwards [hb] with q hq
  exact hφA q.proj hq q.snd

end Coordinates

section LineBundle

variable {𝕜 B EB HB F F' : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {V' : B → Type*} [∀ x, AddCommGroup (V' x)] [∀ x, Module 𝕜 (V' x)]
  [∀ x, TopologicalSpace (V' x)] [∀ x, IsTopologicalAddGroup (V' x)]
  [∀ x, ContinuousSMul 𝕜 (V' x)] [TopologicalSpace (TotalSpace F' V')]
  [FiberBundle F' V'] [VectorBundle 𝕜 F' V'] {n : WithTop ℕ∞}
  [ContMDiffVectorBundle n F V IB] [ContMDiffVectorBundle n F' V' IB]

/-- **Testing a hom-bundle section on a local frame.** Let `s` be a `C^n` local frame of `V` on
an open set `u`. A family `A x : V x →L V' x` is a `C^n` section of the hom bundle on `u` as
soon as `x ↦ A x (s i x)` is `C^n` on `u` for every `i`. -/
theorem IsLocalFrameOn.contMDiffOn_hom_bundle [FiniteDimensional 𝕜 F] {ι : Type*}
    {u : Set B} {s : ι → ∀ x, V x} (hs : IsLocalFrameOn IB F n s u) (hu : IsOpen u)
    {A : ∀ x, V x →L[𝕜] V' x}
    (hA : ∀ i, ContMDiffOn IB (IB.prod 𝓘(𝕜, F')) n
      (fun x ↦ TotalSpace.mk' F' x (A x (s i x))) u) :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F →L[𝕜] F')) n
      (fun x ↦ TotalSpace.mk' (F →L[𝕜] F') (E := fun x ↦ V x →L[𝕜] V' x) x (A x)) u := by
  intro x hx
  let := hs.fintypeOfFiniteDimensional hx
  let e := trivializationAt F V x
  let e' := trivializationAt F' V' x
  let b := Module.finBasis 𝕜 F
  set W := u ∩ e.baseSet ∩ e'.baseSet
  have hW : IsOpen W := (hu.inter e.open_baseSet).inter e'.open_baseSet
  have hxW : x ∈ W := ⟨⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩,
    FiberBundle.mem_baseSet_trivializationAt' x⟩
  refine ((TauCeti.Manifold.contMDiffOn_hom_of_localFrame b (e' := e') (f := id) (u := W)
    contMDiffOn_id (fun y hy ↦ ⟨hy.1.2, hy.2⟩) fun j ↦ ?_).contMDiffAt
      (hW.mem_nhds hxW)).contMDiffWithinAt
  -- On `W`, the frame vector of `e` is the sum of its coefficients in `s` times the `s i`, so `A`
  -- sends it to the sum of those coefficients times the `A (s i y)`.
  have hsU := hs.mono (Set.inter_subset_left (t := e.baseSet))
  have hc (i : ι) : ContMDiffOn IB 𝓘(𝕜) n (fun y ↦ hsU.coeff i y (e.localFrame b j y))
      (u ∩ e.baseSet) :=
    hsU.contMDiffOn_coeff (hu.inter e.open_baseSet) le_rfl
      ((e.contMDiffOn_localFrame_baseSet n b j).mono Set.inter_subset_right) i
  refine (ContMDiffOn.sum_section (s := Finset.univ) fun i _ ↦
    ((hc i).mono fun y (hy : y ∈ W) ↦ hy.1).smul_section
      ((hA i).mono fun y (hy : y ∈ W) ↦ hy.1.1)).congr fun y hy ↦ ?_
  simp only [id]
  nth_rw 1 [hsU.coeff_sum_eq (e.localFrame b j) hy.1]
  simp [map_sum, map_smul]

/-- **Testing a map out of a bundle on a local frame.** Let `s` be a `C^n` local frame of `V` on
an open set `u`. For a family `A x : V x →L V' x` such that `x ↦ A x (s i x)` is `C^n` on `u`
for every `i`, the map of total spaces `⟨x, v⟩ ↦ ⟨x, A x v⟩` is `C^n` over `u`. -/
theorem IsLocalFrameOn.contMDiffOn_bundleMap [FiniteDimensional 𝕜 F] {ι : Type*}
    {u : Set B} {s : ι → ∀ x, V x} (hs : IsLocalFrameOn IB F n s u) (hu : IsOpen u)
    {A : ∀ x, V x →L[𝕜] V' x}
    (hA : ∀ i, ContMDiffOn IB (IB.prod 𝓘(𝕜, F')) n
      (fun x ↦ TotalSpace.mk' F' x (A x (s i x))) u) :
    ContMDiffOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F')) n
      (fun p : TotalSpace F V ↦ TotalSpace.mk' F' p.proj (A p.proj p.snd))
      (TotalSpace.proj ⁻¹' u) := fun p hp ↦
  ((TauCeti.contMDiffAt_hom_bundle_iff A p.proj).1
    ((hs.contMDiffOn_hom_bundle hu hA).contMDiffAt (hu.mem_nhds hp)) p.snd).contMDiffWithinAt

/-- **Testing a hom-bundle section out of a line bundle on one section.** Let `V` have model
fibre `F` of dimension one, and let `s` be a section of `V` that is `C^n` and nowhere zero on an
open set `u`. A family `A x : V x →L V' x` is a `C^n` section of the hom bundle on `u` as soon as
`x ↦ A x (s x)` is `C^n` on `u`. -/
theorem ContMDiffOn.hom_bundle_of_finrank_eq_one (hF : Module.finrank 𝕜 F = 1)
    {u : Set B} (hu : IsOpen u) {s : ∀ x, V x}
    (hs : ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u)
    (hs₀ : ∀ x ∈ u, s x ≠ 0) {A : ∀ x, V x →L[𝕜] V' x}
    (hA : ContMDiffOn IB (IB.prod 𝓘(𝕜, F')) n (fun x ↦ TotalSpace.mk' F' x (A x (s x))) u) :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F →L[𝕜] F')) n
      (fun x ↦ TotalSpace.mk' (F →L[𝕜] F') (E := fun x ↦ V x →L[𝕜] V' x) x (A x)) u :=
  have : FiniteDimensional 𝕜 F := Module.finite_of_finrank_eq_succ hF
  (IsLocalFrameOn.of_finrank_eq_one (ι := Unit) hF hs hs₀).contMDiffOn_hom_bundle hu fun _ ↦ hA

/-- **Testing a map out of a line bundle on one section.** Let `V` have model fibre `F` of
dimension one, and let `s` be a section of `V` that is `C^n` and nowhere zero on an open set `u`.
For a family `A x : V x →L V' x` such that `x ↦ A x (s x)` is `C^n` on `u`, the map of total spaces
`⟨x, v⟩ ↦ ⟨x, A x v⟩` is `C^n` over `u`. -/
theorem ContMDiffOn.bundleMap_of_finrank_eq_one (hF : Module.finrank 𝕜 F = 1)
    {u : Set B} (hu : IsOpen u) {s : ∀ x, V x}
    (hs : ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u)
    (hs₀ : ∀ x ∈ u, s x ≠ 0) {A : ∀ x, V x →L[𝕜] V' x}
    (hA : ContMDiffOn IB (IB.prod 𝓘(𝕜, F')) n (fun x ↦ TotalSpace.mk' F' x (A x (s x))) u) :
    ContMDiffOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F')) n
      (fun p : TotalSpace F V ↦ TotalSpace.mk' F' p.proj (A p.proj p.snd))
      (TotalSpace.proj ⁻¹' u) :=
  have : FiniteDimensional 𝕜 F := Module.finite_of_finrank_eq_succ hF
  (IsLocalFrameOn.of_finrank_eq_one (ι := Unit) hF hs hs₀).contMDiffOn_bundleMap hu fun _ ↦ hA

end LineBundle

end
