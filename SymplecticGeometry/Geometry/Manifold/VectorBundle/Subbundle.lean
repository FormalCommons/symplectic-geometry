/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.ComplementarySubbundle

/-!
# Images, sums and reindexing of smooth subbundles

Let `V` be a family of subspaces of the fibres of a vector bundle `E` with `C^n` local frames
(Tau Ceti's `TauCeti.HasLocalContMDiffSubbundleFrames`). This file shows that three operations
keep such frames:

* reindexing the frames along an equivalence of index types
  (`TauCeti.HasLocalContMDiffSubbundleFrames.of_equiv`, whose proof is that of Tau Ceti's
  continuous counterpart `TauCeti.HasLocalSubbundleFrames.of_equiv`);
* taking the image of `V` under a family of fibrewise linear maps `P x : E₁ x → E₂ x` that is a
  `C^n` map of total spaces and injective on each `V x`
  (`TauCeti.HasLocalContMDiffSubbundleFrames.map`): the images of a frame of `V` are a frame of
  the image;
* the sum `V ⊔ W` of two such families that meet only in `0` in every fibre
  (`TauCeti.HasLocalContMDiffSubbundleFrames.sup` and, with frames indexed by `Fin (r + s)`,
  `TauCeti.HasLocalContMDiffSubbundleFrames.sup_fin`): a frame of `V` followed by one of `W` is a
  frame of the sum.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Lemma 10.32,
  the local frame criterion for subbundles.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti.HasLocalContMDiffSubbundleFrames

section OfEquiv

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] {n : ℕ∞ω}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : B → Type*}
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜' (E x)] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
  {ι ι' : Type*} {V : Π x, Submodule 𝕜' (E x)}

/-- `C^n` local frames indexed by `ι` give `C^n` local frames indexed by any type equivalent
to `ι`. -/
theorem of_equiv (hV : HasLocalContMDiffSubbundleFrames IB n F ι V) (e : ι ≃ ι') :
    HasLocalContMDiffSubbundleFrames IB n F ι' V :=
    hasLocalContMDiffSubbundleFrames_iff.mpr fun x ↦ by
  obtain ⟨U, hU, hx, X, hX, hXs⟩ := hasLocalContMDiffSubbundleFrames_iff.mp hV x
  exact ⟨U, hU, hx, X ∘ e.symm, hX.comp_equiv e.symm, fun i ↦ hXs _⟩

end OfEquiv

section Operations

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] {n : ℕ∞ω}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : B → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
  {ι ι' : Type*} {V W : Π x, Submodule 𝕜 (E x)}

/-- **The sum of two smooth subbundles meeting in `0`.** If the families of subspaces `V` and
`W` of the fibres of `E` have `C^n` local frames indexed by `ι` and `ι'`, and `V x` and `W x`
meet only in `0` for every `x`, then `V ⊔ W` has `C^n` local frames indexed by `ι ⊕ ι'`: a frame
of `V` followed by a frame of `W`. -/
theorem sup (hV : HasLocalContMDiffSubbundleFrames IB n F ι V)
    (hW : HasLocalContMDiffSubbundleFrames IB n F ι' W) (hVW : ∀ x, Disjoint (V x) (W x)) :
    HasLocalContMDiffSubbundleFrames IB n F (ι ⊕ ι') fun x ↦ V x ⊔ W x :=
    hasLocalContMDiffSubbundleFrames_iff.mpr fun x ↦ by
  obtain ⟨U, hU, hx, X, hX, hXs⟩ := hasLocalContMDiffSubbundleFrames_iff.mp hV x
  obtain ⟨U', hU', hx', Y, hY, hYs⟩ := hasLocalContMDiffSubbundleFrames_iff.mp hW x
  refine ⟨U ∩ U', hU.inter hU', ⟨hx, hx'⟩, Sum.elim X Y,
    ⟨fun i ↦ ?_, fun {y} hy ↦ ?_, fun {y} hy ↦ ?_⟩, fun i ↦ ?_⟩
  · cases i with
    | inl i => exact (hX.continuousOn i).mono inter_subset_left
    | inr i => exact (hY.continuousOn i).mono inter_subset_right
  · have h := (hX.linearIndependent hy.1).sum_type (hY.linearIndependent hy.2)
      (by rw [hX.span_eq hy.1, hY.span_eq hy.2]; exact hVW y)
    convert h using 1
    ext (i | i) <;> rfl
  · have h : (range fun i ↦ Sum.elim X Y i y) = range (X · y) ∪ range (Y · y) := by
      rw [← Sum.elim_range]
      congr 1
      ext (i | i) <;> rfl
    rw [h, Submodule.span_union, hX.span_eq hy.1, hY.span_eq hy.2]
  · cases i with
    | inl i => exact (hXs i).mono inter_subset_left
    | inr i => exact (hYs i).mono inter_subset_right

/-- **The sum of two smooth subbundles meeting in `0`, with frames indexed by `Fin`.** If `V`
and `W` have `C^n` local frames of sizes `r` and `s`, and `V x` and `W x` meet only in `0` for
every `x`, then `V ⊔ W` has `C^n` local frames of size `r + s`. -/
theorem sup_fin {r s : ℕ} (hV : HasLocalContMDiffSubbundleFrames IB n F (Fin r) V)
    (hW : HasLocalContMDiffSubbundleFrames IB n F (Fin s) W) (hVW : ∀ x, Disjoint (V x) (W x)) :
    HasLocalContMDiffSubbundleFrames IB n F (Fin (r + s)) fun x ↦ V x ⊔ W x :=
  (hV.sup hW hVW).of_equiv finSumFinEquiv

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]

/-- **The image of a smooth subbundle under a smooth bundle map.** Let `P x : E x → E₂ x` be
linear maps such that `p ↦ ⟨p.proj, P p.proj p.snd⟩` is a `C^n` map of total spaces, and `V` a
family of subspaces of the fibres of `E` with `C^n` local frames indexed by `ι`, on which every
`P x` is injective. Then the images `(V x).map (P x)` have `C^n` local frames indexed by `ι`: the
images of the frames of `V`. -/
theorem map {P : Π x, E x →ₗ[𝕜] E₂ x}
    (hP : ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F₂)) n
      (fun p : TotalSpace F E ↦ (⟨p.proj, P p.proj p.snd⟩ : TotalSpace F₂ E₂)))
    (hV : HasLocalContMDiffSubbundleFrames IB n F ι V)
    (hPV : ∀ x, Disjoint (V x) (LinearMap.ker (P x))) :
    HasLocalContMDiffSubbundleFrames IB n F₂ ι fun x ↦ (V x).map (P x) :=
    hasLocalContMDiffSubbundleFrames_iff.mpr fun x ↦ by
  obtain ⟨U, hU, hx, X, hX, hXs⟩ := hasLocalContMDiffSubbundleFrames_iff.mp hV x
  have hY (i : ι) : CMDiff[U] n (T% (fun y ↦ P y (X i y))) := hP.comp_contMDiffOn (hXs i)
  refine ⟨U, hU, hx, fun i y ↦ P y (X i y),
    ⟨fun i ↦ (hY i).continuousOn, fun {y} hy ↦ ?_, fun {y} hy ↦ ?_⟩, hY⟩
  · exact (hX.linearIndependent hy).map (by rw [hX.span_eq hy]; exact hPV y)
  · rw [← hX.span_eq hy, Submodule.map_span, ← range_comp]
    rfl

end Operations

section IsCompl

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] {n : ℕ∞ω}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul 𝕜 (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E] [ContMDiffVectorBundle n F E IB]
  {ι ι' : Type*} [Finite ι] [Finite ι'] {V W : Π x, Submodule 𝕜 (E x)}

/-- **Projecting onto a smooth subbundle along a complementary one is smooth, in `E`.** If `V`
and `W` have `C^n` local frames and are complementary in every fibre of a `C^n` vector bundle
`E`, the projection of `E` onto `V` along `W` is a `C^n` map from the total space of `E` to
itself. This is Tau Ceti's
`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiff_totalSpace_projectionOnto_of_isCompl`
followed by the inclusion of `V` into `E`. -/
theorem contMDiff_totalSpace_projection_of_isCompl
    (hV : HasLocalContMDiffSubbundleFrames IB n F ι V)
    (hW : HasLocalContMDiffSubbundleFrames IB n F ι' W) (hVW : ∀ x, IsCompl (V x) (W x)) :
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
      (fun w : TotalSpace F E ↦
        (⟨w.proj, (V w.proj).projection (W w.proj) (hVW w.proj) w.snd⟩ : TotalSpace F E)) := by
  have := Fintype.ofFinite ι
  let := subbundleTopology F (F' := ι → 𝕜) V
  let := hV.fiberBundle
  exact hV.contMDiff_totalSpace_inclusion.comp
    (hV.contMDiff_totalSpace_projectionOnto_of_isCompl hW hVW)

end IsCompl

end TauCeti.HasLocalContMDiffSubbundleFrames

end
