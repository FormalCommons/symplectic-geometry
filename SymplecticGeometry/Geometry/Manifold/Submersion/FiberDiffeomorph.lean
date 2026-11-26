/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.LocalAtTarget
public import TauCeti.Topology.Maps.Proper.Basic
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.MapFiber
public import SymplecticGeometry.Geometry.Manifold.RegularValue.RestrictPreimage
public import SymplecticGeometry.Geometry.Manifold.Submersion.RadialTrivialization

/-!
# The fibres of a proper submersion over a connected base

A smooth proper submersion `f : P → B` from a σ-compact manifold is smoothly locally trivial,
with the fibre over a value `b₀` as model fibre
(`Manifold.IsSubmersion.exists_trivialization_of_isProperMap`). So, with the regular-fibre atlas
`TauCeti.regularFiberChartedSpace` on each fibre, the fibres over the points of a neighbourhood
of `b₀` are diffeomorphic to the fibre over `b₀`, by the fibre coordinate of such a
trivialization (`Bundle.Trivialization.mapFiberDiffeomorph`). The same holds near a point `b₀`
outside the range of `f`: the range is closed, since `f` is proper, so all fibres near `b₀` are
empty. Over a preconnected base, being diffeomorphic is then an equivalence relation with open
classes, so it has one class (`PreconnectedSpace.induction₂'`). This is Ehresmann's fibration
theorem in the form that all fibres are diffeomorphic
(`Manifold.IsSubmersion.nonempty_diffeomorph_mapFiber`).

A smooth proper map `f : M → N` that need not be a submersion restricts, over an open
preconnected set `R` of regular values, to a smooth proper submersion `f⁻¹(R) → R`, whose fibres
are those of `f` (`TauCeti.regularFiberRestrictPreimageDiffeomorph`). So the fibres of `f` over
the points of `R` are pairwise diffeomorphic
(`ContMDiff.nonempty_diffeomorph_fiber_of_isProperMap`).

## Main results

* `Manifold.IsSubmersion.eventually_nonempty_diffeomorph_mapFiber`: the fibres of a smooth proper
  submersion near any point `b₀` are diffeomorphic to the fibre over `b₀`.
* `Manifold.IsSubmersion.nonempty_diffeomorph_mapFiber`: any two fibres of a smooth proper
  submersion from a σ-compact manifold to a connected manifold are diffeomorphic.
* `ContMDiff.nonempty_diffeomorph_fiber_of_isProperMap`: the fibres of a smooth proper map over
  the points of an open preconnected set of regular values are diffeomorphic.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.1.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §9.
-/

public section

noncomputable section

open Function Bundle Set Filter
open scoped ContDiff Manifold Topology

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

/-- Over the points of a neighbourhood of any point `b₀`, the fibres of a smooth proper
submersion `f`, with their regular-fibre atlases, are diffeomorphic to the fibre over `b₀`. -/
theorem eventually_nonempty_diffeomorph_mapFiber (hf : IsSubmersion I J ∞ f)
    (hfp : IsProperMap f) (b₀ : B) :
    ∀ᶠ b in 𝓝 b₀,
      letI := fiberAtlas hf b₀
      letI := fiberAtlas hf b
      Nonempty (MapFiber f b ≃ₘ⟮𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ),
        𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ)⟯ MapFiber f b₀) := by
  let := fiberAtlas hf b₀
  by_cases hb₀ : b₀ ∈ range f
  · obtain ⟨e, hb₀e, he, he'⟩ := hf.exists_trivialization_of_isProperMap hfp hb₀
    filter_upwards [e.open_baseSet.mem_nhds hb₀e] with b hb
    let := fiberAtlas hf b
    exact ⟨e.mapFiberDiffeomorph he he' hb (isSmoothEmbedding_coe_regularFiber (by simp)
      hf.contMDiff BoundarylessManifold.isInteriorPoint (hf.isRegularValue (by simp) b))⟩
  · -- Off the range of `f`, which is closed, all fibres are empty.
    filter_upwards [hfp.isClosedMap.isClosed_range.isOpen_compl.mem_nhds hb₀] with b hb
    have hempty (c : B) (hc : c ∉ range f) : IsEmpty (MapFiber f c) :=
      ⟨fun x ↦ hc ⟨x.val, x.property⟩⟩
    have := hempty b hb
    have := hempty b₀ hb₀
    let := fiberAtlas hf b
    exact ⟨.empty⟩

/-- **Ehresmann's fibration theorem: the fibres of a proper submersion are diffeomorphic.** Let
`f : P → B` be a smooth proper submersion from a σ-compact Hausdorff manifold to a connected
Hausdorff manifold, both finite-dimensional and boundaryless. Give each fibre
`TauCeti.MapFiber f b` its regular-fibre atlas `TauCeti.regularFiberChartedSpace`. Then any two
fibres of `f` are smoothly diffeomorphic.

If `f` is not surjective, then `P` is empty, and so are all the fibres. -/
theorem nonempty_diffeomorph_mapFiber [PreconnectedSpace B] (hf : IsSubmersion I J ∞ f)
    (hfp : IsProperMap f) (b₀ b₁ : B) :
    letI := fiberAtlas hf b₀
    letI := fiberAtlas hf b₁
    Nonempty (MapFiber f b₀ ≃ₘ⟮𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ)⟯ MapFiber f b₁) := by
  refine PreconnectedSpace.induction₂' (fun b₀ b₁ ↦
    letI := fiberAtlas hf b₀
    letI := fiberAtlas hf b₁
    Nonempty (MapFiber f b₀ ≃ₘ⟮𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ)⟯ MapFiber f b₁)) (fun b ↦ ?_) ⟨?_⟩ b₀ b₁
  · filter_upwards [eventually_nonempty_diffeomorph_mapFiber hf hfp b] with b' ⟨φ⟩
    let := fiberAtlas hf b
    let := fiberAtlas hf b'
    exact ⟨⟨φ.symm⟩, ⟨φ⟩⟩
  · rintro a b c ⟨φ⟩ ⟨ψ⟩
    let := fiberAtlas hf a
    let := fiberAtlas hf b
    let := fiberAtlas hf c
    exact ⟨φ.trans ψ⟩

end Manifold.IsSubmersion

namespace ContMDiff

open TauCeti Module TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [J.Boundaryless]
  [T2Space N] [SecondCountableTopology N] {f : M → N}

/-- **The fibres of a proper map over a connected set of regular values are diffeomorphic.**
Let `f : M → N` be a smooth proper map between Hausdorff boundaryless finite-dimensional
manifolds, `N` second countable, and let `R` be an open preconnected set of regular values of
`f`. Give the fibre `{x // f x = y}` over each `y ∈ R` its regular-fibre atlas
`TauCeti.regularFiberChartedSpace`. Then the fibres over any two points of `R` are smoothly
diffeomorphic. -/
theorem nonempty_diffeomorph_fiber_of_isProperMap (hf : ContMDiff I J ∞ f) (hfp : IsProperMap f)
    (R : Opens N) (hR : IsPreconnected (R : Set N)) (hreg : ∀ y ∈ R, IsRegularValue I J f y)
    {y₀ y₁ : N} (h₀ : y₀ ∈ R) (h₁ : y₁ ∈ R) :
    letI := regularFiberChartedSpace (m := ∞) (by simp) hf BoundarylessManifold.isInteriorPoint
      (hreg y₀ h₀)
    letI := regularFiberChartedSpace (m := ∞) (by simp) hf BoundarylessManifold.isInteriorPoint
      (hreg y₁ h₁)
    Nonempty ({x // f x = y₀} ≃ₘ⟮𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ)⟯ {x // f x = y₁}) := by
  -- The restriction of `f` over `R`.
  let P : Opens M := ⟨f ⁻¹' R, R.isOpen.preimage hf.continuous⟩
  let g : P → R := (R : Set N).restrictPreimage f
  have hg : Manifold.IsSubmersion I J ∞ g :=
    ((hf.restrictPreimage R).isSubmersionOfComplement_of_surjective_mfderiv (by simp)
      fun x ↦ isRegularPoint_iff.1 ((isRegularPoint_restrictPreimage_iff hf.continuous R).2
        (isRegularValue_iff.1 (hreg _ x.property) x rfl))).isSubmersion
  have hgp : IsProperMap g := hfp.restrictPreimage _
  have : PreconnectedSpace R := isPreconnected_iff_preconnectedSpace.1 hR
  -- `R` is σ-compact, as a locally compact second-countable space, and so is `P`.
  have := J.locallyCompactSpace
  have := ChartedSpace.locallyCompactSpace G R
  have : SigmaCompactSpace P := hgp.sigmaCompactSpace
  let := regularFiberChartedSpace (m := ∞) (by simp) hf BoundarylessManifold.isInteriorPoint
    (hreg y₀ h₀)
  let := regularFiberChartedSpace (m := ∞) (by simp) hf BoundarylessManifold.isInteriorPoint
    (hreg y₁ h₁)
  let := regularFiberChartedSpace (m := ∞) (by simp) hg.contMDiff
    BoundarylessManifold.isInteriorPoint (hg.isRegularValue (by simp) ⟨y₀, h₀⟩)
  let := regularFiberChartedSpace (m := ∞) (by simp) hg.contMDiff
    BoundarylessManifold.isInteriorPoint (hg.isRegularValue (by simp) ⟨y₁, h₁⟩)
  obtain ⟨φ⟩ := hg.nonempty_diffeomorph_mapFiber hgp ⟨y₀, h₀⟩ ⟨y₁, h₁⟩
  exact ⟨((regularFiberRestrictPreimageDiffeomorph (by simp) hf
    BoundarylessManifold.isInteriorPoint (hreg y₀ h₀) R h₀).symm.trans φ).trans
    (regularFiberRestrictPreimageDiffeomorph (by simp) hf BoundarylessManifold.isInteriorPoint
      (hreg y₁ h₁) R h₁)⟩

end ContMDiff

end
