/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Lefschetz.Basic
public import TauCeti.Geometry.Manifold.Morse.Bott.Count
public import TauCeti.Geometry.Manifold.Morse.Bott.Submersion
public import TauCeti.Geometry.Manifold.Morse.Projectivization
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse

/-!
# The Morse–Bott function `μ ∘ π` of a Lefschetz fibration

Let `μ` be Tau Ceti's moment function on `ℂℙ¹ = ℙ ℂ (Fin 2 → ℂ)` with the weights `(0, 1)`,
`[z₀ : z₁] ↦ ‖z₁‖² / (‖z₀‖² + ‖z₁‖²)`, a Morse function whose critical points are the two
coordinate points `c 0 = [1 : 0]` and `c 1 = [0 : 1]`, of index `0` and `2`. For a smooth map
`π : X → ℂℙ¹` for which `c 0` and `c 1` are regular values, the critical points of `μ ∘ π` off
the critical set `criticalSet π` of `π` are exactly the points of the two fibres `π⁻¹(c k)`. A
point of `criticalSet π` need not be a critical point of `μ ∘ π`, since `dπ` may there have rank
one, but it is one when `π` is a Lefschetz fibration, whose derivative vanishes at its critical
points. This file defines, for every such smooth `π`, a family of smooth embeddings indexed by
`Fin 2 ⊕ criticalSet π`:

* the piece `inl k` is the fibre `π⁻¹(c k)` with Tau Ceti's regular-fibre atlas
  `TauCeti.regularFiberChartedSpace`, embedded by its inclusion;
* the piece `inr p` is the point `p`, embedded from the trivial space `Fin 0 → ℝ`.

When `π` is a Lefschetz fibration and the two fibres are connected, this family exhibits `μ ∘ π`
as a Morse–Bott function, with index `2 * k` along the fibre over `c k` and index `2` at each
critical point of `π`. Along the fibres this is Tau Ceti's
`TauCeti.isNondegenerateCriticalSubmanifold_comp_regularFiber`, with the index of `μ` from
`TauCeti.manifoldMorseIndex_projectiveMomentFunction_natCast_complex`; at a critical point of `π`
it is `SymplecticGeometry.IsLefschetzFibration.manifoldMorseIndex_comp`, since `μ` has nonzero
derivative at the critical values, which are not coordinate points. Elsewhere `π` is a submersion
and `μ ∘ π` has no critical points (`TauCeti.IsRegularPoint.mem_criticalPoints_comp_iff`). The
family is assembled by `TauCeti.IsMorseBottFamily.of_pairwise_disjoint`. It has the form that
Euler's equality for Morse–Bott functions
(`TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_eq_sum`) takes, and gives the
Euler characteristic count of a Lefschetz fibration.

The proof follows the one of Tau Ceti's `TauCeti.IsMorse.isMorseBottFamily_comp`, for a
submersion, adding the critical points of `π` as pieces of their own.

## Main definitions

* `SymplecticGeometry.MomentPullback.coordinatePoint k`: the coordinate point `[e_k]` of `ℂℙ¹`.
* `SymplecticGeometry.MomentPullback.Piece I π j`: the source of the piece `j`, the fibre
  `π⁻¹(c k)` for `j = inl k` and `Fin 0 → ℝ` for `j = inr p`.
* `SymplecticGeometry.MomentPullback.chartedSpace` and
  `SymplecticGeometry.MomentPullback.embedding`: their atlases and their embeddings into `X`.
* `SymplecticGeometry.MomentPullback.index j`: `2 * k` for `j = inl k` and `2` for `j = inr p`.

## Main results

* `SymplecticGeometry.IsLefschetzFibration.manifoldMorseIndex_projectiveMomentFunction_comp`: at
  each critical point `p` of a Lefschetz fibration `π` with `π p` not a coordinate point, `μ ∘ π`
  has a nondegenerate critical point of Morse index `2`.
* `SymplecticGeometry.IsLefschetzFibration.isMorseBottFamily_momentPullback`: the family exhibits
  `μ ∘ π` as a Morse–Bott function.
* `SymplecticGeometry.IsLefschetzFibration.manifoldMorseIndex_momentPullback`: the Morse index of
  `μ ∘ π` along the piece `j` is `index j`.
* `SymplecticGeometry.IsLefschetzFibration.index_isMorseBottFamily_momentPullback`: the index
  that Tau Ceti's `TauCeti.IsMorseBottFamily.index` gives the piece `j` is also `index j`.

## References

* R. Gompf, A. Stipsicz, *4-Manifolds and Kirby Calculus*, AMS (1999), §8.2.
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], Section 7.4.
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public section

open Set Function TauCeti Projectivization
open scoped Manifold LinearAlgebra.Projectivization

noncomputable section

namespace SymplecticGeometry

namespace MomentPullback

open scoped ContDiff

/-- The coordinate point `[e_k]` of `ℂℙ¹`: `[1 : 0]` for `k = 0` and `[0 : 1]` for `k = 1`. These
are the critical points of the moment function with weights `(0, 1)`. -/
def coordinatePoint (k : Fin 2) : ℙ ℂ (Fin 2 → ℂ) :=
  mk ℂ (Pi.single k 1) (by simp)

theorem coordinatePoint_def (k : Fin 2) :
    coordinatePoint k = mk ℂ (Pi.single k 1) (by simp) :=
  (rfl)

/-- The moment function with the weights `(0, 1)` takes the value `k` at `[e_k]`. -/
@[simp]
theorem projectiveMomentFunction_coordinatePoint (k : Fin 2) :
    projectiveMomentFunction ℂ (fun i : Fin 2 ↦ ((i : ℕ) : ℝ)) (coordinatePoint k) = k := by
  rw [coordinatePoint_def, projectiveMomentFunction_mk_single]

theorem coordinatePoint_injective : Injective coordinatePoint := fun k k' h ↦
  mk_single_injective (by simpa only [coordinatePoint_def] using h)

/-- The critical points of the moment function with the weights `(0, 1)` are the two coordinate
points. -/
theorem criticalPoints_projectiveMomentFunction_eq_range_coordinatePoint :
    criticalPoints 𝓘(ℝ, Fin 1 → ℂ) (projectiveMomentFunction ℂ fun i : Fin 2 ↦ ((i : ℕ) : ℝ)) =
      range coordinatePoint :=
  TauCeti.criticalPoints_projectiveMomentFunction
    (Nat.cast_injective.comp Fin.val_injective)

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  (π : X → ℙ ℂ (Fin 2 → ℂ))

/-- The dimension of the piece `j`: that of a regular fibre, `dim X - 2`, for the fibres, and `0`
for the critical points of `π`. -/
@[expose] def dim : Fin 2 ⊕ criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π → ℕ
  | .inl _ => Module.finrank ℝ E - Module.finrank ℝ (Fin 1 → ℂ)
  | .inr _ => 0

@[simp]
theorem dim_inl (k : Fin 2) :
    dim I π (.inl k) = Module.finrank ℝ E - Module.finrank ℝ (Fin 1 → ℂ) :=
  (rfl)

@[simp]
theorem dim_inr (p : criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π) : dim I π (.inr p) = 0 :=
  (rfl)

/-- The piece of a critical point of `π` has dimension zero, so its model space
`Fin (dim I π (.inr p)) → ℝ` is a point. -/
instance (p : criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π) : IsEmpty (Fin (dim I π (.inr p))) :=
  inferInstanceAs (IsEmpty (Fin 0))

/-- The source of the piece `j`: the fibre `π⁻¹(c k)` over the coordinate point `c k` for
`j = inl k`, and the trivial space `Fin 0 → ℝ` for `j = inr p`. -/
@[expose] def Piece : Fin 2 ⊕ criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π → Type
  | .inl k => {x : X // π x = coordinatePoint k}
  | .inr p => Fin (dim I π (.inr p)) → ℝ

instance : ∀ j, TopologicalSpace (Piece I π j)
  | .inl k => inferInstanceAs (TopologicalSpace {x : X // π x = coordinatePoint k})
  | .inr p => inferInstanceAs (TopologicalSpace (Fin (dim I π (.inr p)) → ℝ))

/-- The piece of a critical point of `π` has exactly one point. -/
instance (p : criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π) : Unique (Piece I π (.inr p)) :=
  inferInstanceAs (Unique (Fin 0 → ℝ))

/-- The Morse index of `μ ∘ π` along the piece `j`: `2 * k` along the fibre over `c k`, the index
of the moment function at `c k`, and `2` at the critical points of `π`. -/
def index : Fin 2 ⊕ criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π → ℕ
  | .inl k => 2 * k
  | .inr _ => 2

@[simp]
theorem index_inl (k : Fin 2) : index I π (.inl k) = 2 * k :=
  (rfl)

@[simp]
theorem index_inr (p : criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π) : index I π (.inr p) = 2 :=
  (rfl)

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ X] {I π}
  (hπ : ContMDiff I 𝓘(ℝ, Fin 1 → ℂ) ∞ π)
  (hreg : ∀ k, IsRegularValue I 𝓘(ℝ, Fin 1 → ℂ) π (coordinatePoint k))

/-- The atlases of the pieces: Tau Ceti's regular-fibre atlas on the fibres, and the model space
itself on the points. -/
@[expose, instance_reducible]
def chartedSpace : ∀ j, ChartedSpace (Fin (dim I π j) → ℝ) (Piece I π j)
  | .inl k => regularFiberChartedSpace (by simp) hπ BoundarylessManifold.isInteriorPoint (hreg k)
  | .inr p => chartedSpaceSelf (Fin (dim I π (.inr p)) → ℝ)

omit [IsManifold I ∞ X] in
/-- On the fibre over `c k`, the atlas is Tau Ceti's regular-fibre atlas. -/
theorem chartedSpace_inl (k : Fin 2) :
    chartedSpace hπ hreg (.inl k) =
      regularFiberChartedSpace (by simp) hπ BoundarylessManifold.isInteriorPoint (hreg k) :=
  (rfl)

omit [IsManifold I ∞ X] in
/-- On the piece of a critical point, the atlas is that of the model space itself. -/
theorem chartedSpace_inr (p : criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π) :
    chartedSpace hπ hreg (.inr p) = chartedSpaceSelf (Fin (dim I π (.inr p)) → ℝ) :=
  (rfl)

/-- Each piece is a smooth manifold. -/
theorem isManifold :
    letI := chartedSpace hπ hreg
    ∀ j, IsManifold 𝓘(ℝ, Fin (dim I π j) → ℝ) ∞ (Piece I π j) := by
  let := chartedSpace hπ hreg
  rintro (k | p)
  · exact isManifold_regularFiber (by simp) hπ BoundarylessManifold.isInteriorPoint (hreg k)
  · exact inferInstanceAs (IsManifold 𝓘(ℝ, Fin 0 → ℝ) ∞ (Fin 0 → ℝ))

/-- The embeddings of the pieces into `X`: the inclusion of the fibre over `c k` for `inl k`, and
the constant map at `p` for `inr p`. -/
def embedding :
    letI := chartedSpace hπ hreg
    ∀ j, SmoothEmbedding 𝓘(ℝ, Fin (dim I π j) → ℝ) I ∞ (Piece I π j) X :=
  letI := chartedSpace hπ hreg
  fun
  | .inl k => SmoothEmbedding.ofIsSmoothEmbedding _
      (isSmoothEmbedding_coe_regularFiber (by simp) hπ BoundarylessManifold.isInteriorPoint
        (hreg k))
  | .inr p => SmoothEmbedding.ofIsSmoothEmbedding _
      (isSmoothEmbedding_const_of_subsingleton (by simp) (p : X))

@[simp]
theorem embedding_inl_apply (k : Fin 2) (x : Piece I π (.inl k)) :
    embedding hπ hreg (.inl k) x = (x : {x : X // π x = coordinatePoint k}).val := by
  let := chartedSpace hπ hreg
  simp only [embedding]
  exact SmoothEmbedding.ofIsSmoothEmbedding_apply _ _ _

@[simp]
theorem embedding_inr_apply (p : criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π) (x : Piece I π (.inr p)) :
    embedding hπ hreg (.inr p) x = p := by
  let := chartedSpace hπ hreg
  simp only [embedding]
  exact SmoothEmbedding.ofIsSmoothEmbedding_apply _ _ _

/-- The image of the piece `inl k` is the fibre over `c k`. -/
@[simp]
theorem range_embedding_inl (k : Fin 2) :
    range (embedding hπ hreg (.inl k)) = π ⁻¹' {coordinatePoint k} := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨(⟨x, hx⟩ : {x : X // π x = coordinatePoint k}), embedding_inl_apply ..⟩⟩
  rintro ⟨y, rfl⟩
  rw [embedding_inl_apply]
  exact (y : {x : X // π x = coordinatePoint k}).property

/-- The image of the piece `inr p` is the point `p`. -/
@[simp]
theorem range_embedding_inr (p : criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π) :
    range (embedding hπ hreg (.inr p)) = {(p : X)} := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨(0 : Fin (dim I π (.inr p)) → ℝ), (embedding_inr_apply ..).trans hx.symm⟩⟩
  rintro ⟨y, rfl⟩
  exact embedding_inr_apply ..

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ X] in
/-- When the coordinate points are regular values of `π`, no critical value of `π` is a
coordinate point. -/
theorem apply_notMem_range_coordinatePoint
    (hreg : ∀ k, IsRegularValue I 𝓘(ℝ, Fin 1 → ℂ) π (coordinatePoint k)) {p : X}
    (hp : p ∈ criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π) : π p ∉ range coordinatePoint :=
  fun ⟨k, hk⟩ ↦ (hreg k).apply_ne_of_mem_criticalSet hp hk.symm

end MomentPullback

namespace IsLefschetzFibration

open MomentPullback

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] {X : Type}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I (⊤ : ℕ∞) X]
  {ω : SmoothTwoForm I X} {J : SmoothAlmostComplexStructure I X} {π : X → ℙ ℂ (Fin 2 → ℂ)}
  (h : IsLefschetzFibration ω J π)

include h

omit [FiniteDimensional ℝ E] in
/-- A critical point `p` of a Lefschetz fibration `π` whose critical value `π p` is not a
coordinate point is a nondegenerate critical point of `μ ∘ π` of Morse index `2`. -/
theorem manifoldMorseIndex_projectiveMomentFunction_comp
    {p : X} (hp : p ∈ criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π) (hp' : π p ∉ range coordinatePoint) :
    IsManifoldNondegenerateCriticalPoint I
        ((projectiveMomentFunction ℂ fun i : Fin 2 ↦ ((i : ℕ) : ℝ)) ∘ π) p ∧
      manifoldMorseIndex I ((projectiveMomentFunction ℂ fun i : Fin 2 ↦ ((i : ℕ) : ℝ)) ∘ π) p =
        2 := by
  refine h.manifoldMorseIndex_comp hp (contMDiff_projectiveMomentFunction _ _) fun h0 ↦ ?_
  refine hp' ?_
  rw [← criticalPoints_projectiveMomentFunction_eq_range_coordinatePoint]
  exact mem_criticalPoints_iff_mfderiv_eq_zero.2 h0

variable (hreg : ∀ k, IsRegularValue I 𝓘(ℝ, Fin 1 → ℂ) π (coordinatePoint k))

include hreg

/-- **`μ ∘ π` is Morse–Bott.** Let `π` be a Lefschetz fibration of a finite-dimensional
boundaryless manifold `X` over `ℂℙ¹`, for which the coordinate points `c 0 = [1 : 0]` and
`c 1 = [0 : 1]` are regular values with connected (in particular nonempty) fibres, and let `μ` be
the moment function with weights `(0, 1)`. Then the fibres over `c 0` and `c 1`, with their
regular-fibre atlases, and the critical points of `π` exhibit `μ ∘ π` as a Morse–Bott function. -/
theorem isMorseBottFamily_momentPullback (hconn : ∀ k, IsConnected (π ⁻¹' {coordinatePoint k})) :
    letI := MomentPullback.chartedSpace h.contMDiff hreg
    IsMorseBottFamily (MomentPullback.embedding h.contMDiff hreg)
      ((projectiveMomentFunction ℂ fun i : Fin 2 ↦ ((i : ℕ) : ℝ)) ∘ π) := by
  let := MomentPullback.chartedSpace h.contMDiff hreg
  have hne : ∀ j, Nonempty (Piece I π j)
    | .inl k => (hconn k).nonempty.to_subtype
    | .inr _ => inferInstance
  have hpre : ∀ j, PreconnectedSpace (Piece I π j)
    | .inl k => isPreconnected_iff_preconnectedSpace.1 (hconn k).isPreconnected
    | .inr _ => inferInstanceAs (PreconnectedSpace (Fin 0 → ℝ))
  have hπ : ContMDiff I 𝓘(ℝ, Fin 1 → ℂ) (⊤ : ℕ∞) π := h.contMDiff
  refine IsMorseBottFamily.of_pairwise_disjoint (by simp)
    ((contMDiff_projectiveMomentFunction _).comp hπ) ?_ ?_ ?_
  · rintro (k | p)
    · exact isNondegenerateCriticalSubmanifold_comp_regularFiber (by simp) hπ (hreg k)
        (isManifoldNondegenerateCriticalPoint_projectiveMomentFunction fun i hi ↦
          fun hik ↦ hi (Fin.ext (Nat.cast_injective hik)))
    · refine SmoothEmbedding.isNondegenerateCriticalSubmanifold_iff_of_subsingleton.2 fun z ↦ ?_
      rw [embedding_inr_apply]
      exact (h.manifoldMorseIndex_projectiveMomentFunction_comp p.property
        (apply_notMem_range_coordinatePoint hreg p.property)).1
  · rintro (k | p) (k' | p') hne'
    · rw [onFun, range_embedding_inl, range_embedding_inl]
      refine disjoint_left.2 fun x hx hx' ↦ hne' ?_
      exact congrArg Sum.inl (coordinatePoint_injective (hx.symm.trans hx'))
    · rw [onFun, range_embedding_inl, range_embedding_inr, disjoint_singleton_right]
      exact fun hx ↦ (hreg k).notMem_criticalSet hx p'.property
    · rw [onFun, range_embedding_inl, range_embedding_inr, disjoint_singleton_left]
      exact fun hx ↦ (hreg k').notMem_criticalSet hx p.property
    · rw [onFun, range_embedding_inr, range_embedding_inr, disjoint_singleton]
      exact fun hpp ↦ hne' (congrArg Sum.inr (Subtype.ext hpp))
  · intro x hx
    rw [mem_iUnion]
    by_cases hc : x ∈ criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π
    · exact ⟨.inr ⟨x, hc⟩, by rw [range_embedding_inr]; rfl⟩
    · have hreg' : IsRegularPoint I 𝓘(ℝ, Fin 1 → ℂ) π x := not_not.1 (mt mem_criticalSet_iff.2 hc)
      rw [hreg'.mem_criticalPoints_comp_iff ((hπ x).mdifferentiableAt (by simp))
        ((contMDiff_projectiveMomentFunction (r := 1) _ _).mdifferentiableAt one_ne_zero),
        criticalPoints_projectiveMomentFunction_eq_range_coordinatePoint] at hx
      obtain ⟨k, hk⟩ := hx
      exact ⟨.inl k, by rw [range_embedding_inl]; exact hk.symm⟩

/-- **The Morse index of `μ ∘ π` along its pieces.** In the setting of
`SymplecticGeometry.IsLefschetzFibration.isMorseBottFamily_momentPullback`, the Morse index of
`μ ∘ π` is `2 * k` at every point of the fibre over the coordinate point `c k`, and `2` at every
critical point of `π`. -/
theorem manifoldMorseIndex_momentPullback :
    letI := MomentPullback.chartedSpace h.contMDiff hreg
    ∀ j s, manifoldMorseIndex I ((projectiveMomentFunction ℂ fun i : Fin 2 ↦ ((i : ℕ) : ℝ)) ∘ π)
      (MomentPullback.embedding h.contMDiff hreg j s) = MomentPullback.index I π j := by
  let := MomentPullback.chartedSpace h.contMDiff hreg
  rintro (k | p) s
  · rw [embedding_inl_apply, index_inl]
    set x := (s : {x : X // π x = coordinatePoint k})
    have hx := x.property
    rw [((hreg k).isRegularPoint hx).manifoldMorseIndex_comp
      (contMDiff_projectiveMomentFunction _ _) ((h.contMDiff x.val).of_le (by simp)) (by
        rw [hx, criticalPoints_projectiveMomentFunction_eq_range_coordinatePoint]
        exact mem_range_self k), hx, coordinatePoint_def,
      manifoldMorseIndex_projectiveMomentFunction_natCast_complex]
  · rw [embedding_inr_apply, index_inr]
    exact (h.manifoldMorseIndex_projectiveMomentFunction_comp p.property
        (apply_notMem_range_coordinatePoint hreg p.property)).2

/-- **The index of the Morse–Bott family of `μ ∘ π`.** In the setting of
`SymplecticGeometry.IsLefschetzFibration.isMorseBottFamily_momentPullback`, the index that
`TauCeti.IsMorseBottFamily.index` gives the piece `j` of that family is
`MomentPullback.index I π j`: `2 * k` for the fibre over `c k`, and `2` for a critical point
of `π`. -/
theorem index_isMorseBottFamily_momentPullback
    (hconn : ∀ k, IsConnected (π ⁻¹' {coordinatePoint k})) (j) :
    letI := MomentPullback.chartedSpace h.contMDiff hreg
    (h.isMorseBottFamily_momentPullback hreg hconn).index j = MomentPullback.index I π j :=
  letI := MomentPullback.chartedSpace h.contMDiff hreg
  ((h.isMorseBottFamily_momentPullback hreg hconn).index_def j).trans
    (h.manifoldMorseIndex_momentPullback hreg j _)

end IsLefschetzFibration

end SymplecticGeometry

end
