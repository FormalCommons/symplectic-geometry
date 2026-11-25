/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Topology.Connected.Clopen
public import SymplecticGeometry.Geometry.Manifold.Submersion.RadialTrivialization
public import SymplecticGeometry.Topology.FiberBundle.ChangeModelFiber
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# The fibres of a proper submersion over a connected base

Let `e` be a trivialization of a map `proj : P → B` with model fibre `Z`, smooth on its source
with a smooth inverse on its target. For a point `b` of its base set and a manifold structure on
the fibre `TauCeti.MapFiber proj b` whose inclusion into `P` is a smooth embedding, the fibre
coordinate of `e` is a diffeomorphism of the fibre onto `Z`
(`Bundle.Trivialization.mapFiberDiffeomorph`). Its underlying homeomorphism is
`Bundle.Trivialization.mapFiberHomeomorph`.

A smooth proper submersion `f : P → B` from a σ-compact manifold is smoothly locally trivial,
with the fibre over a value `b₀` as model fibre
(`Manifold.IsSubmersion.exists_trivialization_of_isProperMap`). So, with the regular-fibre atlas
`TauCeti.regularFiberChartedSpace` on each fibre, the fibres over the points of a neighbourhood
of `b₀` are diffeomorphic to the fibre over `b₀`. Over a connected base, being diffeomorphic is
then an equivalence relation with open classes, so it has one class
(`PreconnectedSpace.induction₂'`). Points outside the range of `f` need no trivialization: the
range is open, since a submersion is an open map, and closed, since `f` is proper, so it is
empty or all of `B`, and if it is empty every fibre is empty. This is Ehresmann's fibration
theorem in the form that all fibres are diffeomorphic
(`Manifold.IsSubmersion.nonempty_diffeomorph_mapFiber`).

## Main definitions

* `Bundle.Trivialization.mapFiberDiffeomorph`: the fibre over a point of the base set of a
  smooth trivialization, diffeomorphic to the model fibre.

## Main results

* `Manifold.IsSubmersion.nonempty_diffeomorph_mapFiber`: any two fibres of a smooth proper
  submersion from a σ-compact manifold to a connected manifold are diffeomorphic.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.1.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §9.
-/

public section

noncomputable section

open Function Bundle Set Filter
open scoped ContDiff Manifold Topology

namespace Bundle.Trivialization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {EZ : Type*} [NormedAddCommGroup EZ] [NormedSpace 𝕜 EZ] {HZ : Type*} [TopologicalSpace HZ]
  {IZ : ModelWithCorners 𝕜 EZ HZ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace HZ Z]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP] {HP : Type*} [TopologicalSpace HP]
  {IP : ModelWithCorners 𝕜 EP HP} {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF}
  {proj : P → B} (e : Trivialization Z proj) {b : B} [ChartedSpace HF (TauCeti.MapFiber proj b)]

/-- Let `e` be a trivialization of `proj : P → B` with model fibre `Z`, `C^n` on its source with
a `C^n` inverse on its target, and let `b` be a point of its base set. If the fibre
`TauCeti.MapFiber proj b` carries a manifold structure for which its inclusion into `P` is a
`C^n` embedding, then the fibre coordinate `x ↦ (e x).2` of `e` is a `C^n` diffeomorphism from
the fibre onto `Z`, with inverse `v ↦ e.symm (b, v)`. -/
def mapFiberDiffeomorph (he : ContMDiffOn IP (IB.prod IZ) n e e.source)
    (he' : ContMDiffOn (IB.prod IZ) IP n e.toOpenPartialHomeomorph.symm e.target)
    (hb : b ∈ e.baseSet)
    (hι : Manifold.IsSmoothEmbedding IF IP n (Subtype.val : TauCeti.MapFiber proj b → P)) :
    TauCeti.MapFiber proj b ≃ₘ^n⟮IF, IZ⟯ Z where
  toFun x := (e x).2
  invFun v := ⟨e.toOpenPartialHomeomorph.symm (b, v), e.proj_symm_apply' hb⟩
  left_inv x := by simpa using (e.mapFiberHomeomorph hb).symm_apply_apply x
  right_inv v := by simpa using (e.mapFiberHomeomorph hb).apply_symm_apply v
  contMDiff_toFun :=
    (he.comp_contMDiff hι.contMDiff fun x ↦ e.mem_source.2 (x.property.symm ▸ hb)).snd
  contMDiff_invFun := hι.contMDiff_iff_comp.2 <|
    he'.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) fun _ ↦ e.mem_target.2 hb

@[simp]
theorem mapFiberDiffeomorph_apply (he : ContMDiffOn IP (IB.prod IZ) n e e.source)
    (he' : ContMDiffOn (IB.prod IZ) IP n e.toOpenPartialHomeomorph.symm e.target)
    (hb : b ∈ e.baseSet)
    (hι : Manifold.IsSmoothEmbedding IF IP n (Subtype.val : TauCeti.MapFiber proj b → P))
    (x : TauCeti.MapFiber proj b) :
    e.mapFiberDiffeomorph he he' hb hι x = (e x).2 :=
  (rfl)

@[simp]
theorem mapFiberDiffeomorph_symm_apply (he : ContMDiffOn IP (IB.prod IZ) n e e.source)
    (he' : ContMDiffOn (IB.prod IZ) IP n e.toOpenPartialHomeomorph.symm e.target)
    (hb : b ∈ e.baseSet)
    (hι : Manifold.IsSmoothEmbedding IF IP n (Subtype.val : TauCeti.MapFiber proj b → P))
    (v : Z) :
    (e.mapFiberDiffeomorph he he' hb hι).symm v =
      ⟨e.toOpenPartialHomeomorph.symm (b, v), e.proj_symm_apply' hb⟩ :=
  (rfl)

theorem toHomeomorph_mapFiberDiffeomorph (he : ContMDiffOn IP (IB.prod IZ) n e e.source)
    (he' : ContMDiffOn (IB.prod IZ) IP n e.toOpenPartialHomeomorph.symm e.target)
    (hb : b ∈ e.baseSet)
    (hι : Manifold.IsSmoothEmbedding IF IP n (Subtype.val : TauCeti.MapFiber proj b → P)) :
    (e.mapFiberDiffeomorph he he' hb hι).toHomeomorph = e.mapFiberHomeomorph hb :=
  Homeomorph.ext fun x ↦ (e.mapFiberHomeomorph_apply hb x).symm

end Bundle.Trivialization

namespace Manifold.IsSubmersion

open TauCeti Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P] [I.Boundaryless]
  [T2Space P] [SigmaCompactSpace P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {B : Type*} [TopologicalSpace B] [ChartedSpace G B] [IsManifold J ∞ B] [J.Boundaryless]
  [T2Space B] {f : P → B}

/-- The regular-fibre atlas on the fibre of a smooth submersion `f` over a point `b`. -/
local notation "fiberAtlas" hf:max b:max => regularFiberChartedSpace (m := ∞) (c := b) (by simp)
  (IsSubmersion.contMDiff hf) BoundarylessManifold.isInteriorPoint
  (IsSubmersion.isRegularValue hf (by simp) b)

/-- Over the points of a neighbourhood of a value `b₀` of a smooth proper submersion `f`, the
fibres of `f`, with their regular-fibre atlases, are diffeomorphic to the fibre over `b₀`. -/
private theorem eventually_nonempty_diffeomorph_mapFiber (hf : IsSubmersion I J ∞ f)
    (hfp : IsProperMap f) {b₀ : B} (hb₀ : b₀ ∈ range f) :
    ∀ᶠ b in 𝓝 b₀,
      letI := fiberAtlas hf b₀
      letI := fiberAtlas hf b
      Nonempty (MapFiber f b ≃ₘ⟮𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ),
        𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ)⟯ MapFiber f b₀) := by
  let := fiberAtlas hf b₀
  obtain ⟨e, hb₀e, he, he'⟩ := hf.exists_trivialization_of_isProperMap hfp hb₀
  filter_upwards [e.open_baseSet.mem_nhds hb₀e] with b hb
  let := fiberAtlas hf b
  exact ⟨e.mapFiberDiffeomorph he he' hb (isSmoothEmbedding_coe_regularFiber (by simp)
    hf.contMDiff BoundarylessManifold.isInteriorPoint (hf.isRegularValue (by simp) b))⟩

/-- **Ehresmann's fibration theorem: the fibres of a proper submersion are diffeomorphic.** Let
`f : P → B` be a smooth proper submersion from a σ-compact Hausdorff manifold to a connected
Hausdorff manifold, both finite-dimensional and boundaryless. Give each fibre
`TauCeti.MapFiber f b` its regular-fibre atlas `TauCeti.regularFiberChartedSpace`. Then any two
fibres of `f` are smoothly diffeomorphic.

If `f` is not surjective, then `P` is empty, and so are all the fibres. -/
theorem nonempty_diffeomorph_mapFiber [ConnectedSpace B] (hf : IsSubmersion I J ∞ f)
    (hfp : IsProperMap f) (b₀ b₁ : B) :
    letI := fiberAtlas hf b₀
    letI := fiberAtlas hf b₁
    Nonempty (MapFiber f b₀ ≃ₘ⟮𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ)⟯ MapFiber f b₁) := by
  -- The range of `f` is clopen, so it is empty or everything.
  have hclopen : IsClopen (range f) := by
    rw [← image_univ]
    exact ⟨hfp.isClosedMap _ isClosed_univ, hf.isOpenMap _ isOpen_univ⟩
  rcases isClopen_iff.1 hclopen with h | h
  · have (b : B) : IsEmpty (MapFiber f b) :=
      ⟨fun x ↦ (h ▸ mem_range_self x.val : f x.val ∈ (∅ : Set B))⟩
    let := fiberAtlas hf b₀
    let := fiberAtlas hf b₁
    exact ⟨.empty⟩
  · refine PreconnectedSpace.induction₂' (fun b₀ b₁ ↦
      letI := fiberAtlas hf b₀
      letI := fiberAtlas hf b₁
      Nonempty (MapFiber f b₀ ≃ₘ⟮𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ),
        𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ)⟯ MapFiber f b₁)) (fun b ↦ ?_) ⟨?_⟩ b₀ b₁
    · filter_upwards [eventually_nonempty_diffeomorph_mapFiber hf hfp (h ▸ mem_univ b)]
        with b' ⟨φ⟩
      let := fiberAtlas hf b
      let := fiberAtlas hf b'
      exact ⟨⟨φ.symm⟩, ⟨φ⟩⟩
    · rintro a b c ⟨φ⟩ ⟨ψ⟩
      let := fiberAtlas hf a
      let := fiberAtlas hf b
      let := fiberAtlas hf c
      exact ⟨φ.trans ψ⟩

end Manifold.IsSubmersion

end
