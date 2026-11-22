/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
public import Mathlib.Analysis.Convex.Star
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# Smoothly contractible manifolds and finite good covers

A manifold `N` is *smoothly contractible* (`SymplecticGeometry.IsSmoothlyContractible I N`) if a
smooth map `F : N × [0, 1] → N` joins a constant map `F (·, 0) = c` to the identity
`F (·, 1) = id`. A *finite good cover* of `M` (`SymplecticGeometry.IsFiniteGoodCover`) is a
finite family of open sets covering `M` such that every nonempty intersection of a nonempty
subfamily is smoothly contractible, and `SymplecticGeometry.HasFiniteGoodCover I M` says that `M`
has one.

## Main results

* `SymplecticGeometry.IsSmoothlyContractible.of_diffeomorph`: smooth contractibility is invariant
  under diffeomorphisms.
* `SymplecticGeometry.IsSmoothlyContractible.of_starConvex_image`: a nonempty open set `U ⊆ M`
  carried by a map `φ`, smooth on `U` and with a smooth left inverse on `φ '' U`, onto a
  star-convex subset of a normed space is smoothly contractible, by straight lines.
* `StarConvex.isSmoothlyContractible`, `Convex.isSmoothlyContractible` and
  `SymplecticGeometry.IsSmoothlyContractible.of_starConvex_image_extChartAt`: its cases for an
  open set of the model space with star-convex image, a nonempty open convex set of a normed
  space, and an open set inside a chart with star-convex image.
* `StarConvex.lineContraction`: the straight-line contraction `(x, s) ↦ c + s • (x - c)` of an
  open set of a normed space, star-convex about `c`, with `StarConvex.contMDiff_lineContraction`
  and its ends `StarConvex.lineContraction_zero` and `StarConvex.lineContraction_one`. Its
  smoothness, and that of the lines in `of_starConvex_image`, comes from `ContMDiff.lineMap`:
  `x ↦ AffineMap.lineMap (f₁ x) (f₂ x) (g x)` is smooth for smooth `f₁`, `f₂` and `g`.
* `SymplecticGeometry.exists_mem_isSmoothlyContractible`: every point has a smoothly contractible
  open neighbourhood, and `SymplecticGeometry.IsSmoothlyContractible.connectedSpace`: a smoothly
  contractible manifold is connected.
* `SymplecticGeometry.IsFiniteGoodCover.hasFiniteGoodCover` and
  `SymplecticGeometry.IsSmoothlyContractible.hasFiniteGoodCover`.

The straight-line contraction adapts the proof of Tau Ceti's
`TauCeti.exists_contMDiff_contraction_of_starConvex_image_extChartAt`, here on `[0, 1]` without a
smooth reparametrization of time, and through any map with a smooth left inverse instead of an
extended chart.

## References

* [A. Weil, *Sur les théorèmes de de Rham*][Weil1952], §1 (convex covers), §2 (contractions).
* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §5 (good covers).
-/

public section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}

section Contractible

variable (I) in
/-- A manifold `N` modelled on `I` is *smoothly contractible* if there are a point `c : N` and a
smooth map `F : N × [0, 1] → N` with `F (x, 0) = c` and `F (x, 1) = x` for every `x`. -/
def IsSmoothlyContractible (N : Type*) [TopologicalSpace N] [ChartedSpace H N] : Prop :=
  ∃ (c : N) (F : N × unitInterval → N), ContMDiff (I.prod (𝓡∂ 1)) I ∞ F ∧
    (∀ x, F (x, 0) = c) ∧ ∀ x, F (x, 1) = x

/-- Unfolds `IsSmoothlyContractible` into a contraction `F` to a point `c`. -/
theorem isSmoothlyContractible_def {N : Type*} [TopologicalSpace N] [ChartedSpace H N] :
    IsSmoothlyContractible I N ↔ ∃ (c : N) (F : N × unitInterval → N),
      ContMDiff (I.prod (𝓡∂ 1)) I ∞ F ∧ (∀ x, F (x, 0) = c) ∧ ∀ x, F (x, 1) = x :=
  Iff.rfl

variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N]

/-- A smoothly contractible manifold is nonempty. -/
theorem IsSmoothlyContractible.nonempty (h : IsSmoothlyContractible I N) : Nonempty N :=
  let ⟨c, _⟩ := h
  ⟨c⟩

/-- A smoothly contractible manifold is connected: the contraction joins every point to the
centre. -/
theorem IsSmoothlyContractible.connectedSpace (h : IsSmoothlyContractible I N) :
    ConnectedSpace N := by
  obtain ⟨c, F, hF, h₀, h₁⟩ := h
  have : PreconnectedSpace N := ⟨isPreconnected_of_forall c fun y _ ↦
    ⟨range fun s ↦ F (y, s), subset_univ _, ⟨0, h₀ y⟩, ⟨1, h₁ y⟩,
      isPreconnected_range (hF.continuous.comp (continuous_const.prodMk continuous_id))⟩⟩
  exact ⟨⟨c⟩⟩

/-- Smooth contractibility is invariant under diffeomorphisms. -/
theorem IsSmoothlyContractible.of_diffeomorph {E' H' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {N' : Type*}
    [TopologicalSpace N'] [ChartedSpace H' N'] (h : IsSmoothlyContractible I N)
    (e : N ≃ₘ⟮I, J⟯ N') : IsSmoothlyContractible J N' := by
  obtain ⟨c, F, hF, h₀, h₁⟩ := h
  refine ⟨e c, fun p ↦ e (F (e.symm p.1, p.2)), ?_, fun x ↦ by simp [h₀], fun x ↦ by simp [h₁]⟩
  exact e.contMDiff.comp (hF.comp ((e.symm.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- For smooth maps `f₁ f₂ : M → E'` to a real normed space and a smooth `g : M → ℝ`, the map
`x ↦ AffineMap.lineMap (f₁ x) (f₂ x) (g x)`, that is `x ↦ f₁ x + g x • (f₂ x - f₁ x)`, is
smooth. This is the manifold version of Mathlib's `ContDiff.lineMap`. -/
theorem _root_.ContMDiff.lineMap {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {n : WithTop ℕ∞} {f₁ f₂ : M → E'} {g : M → ℝ} (h₁ : ContMDiff I 𝓘(ℝ, E') n f₁)
    (h₂ : ContMDiff I 𝓘(ℝ, E') n f₂) (hg : ContMDiff I 𝓘(ℝ) n g) :
    ContMDiff I 𝓘(ℝ, E') n fun x ↦ AffineMap.lineMap (f₁ x) (f₂ x) (g x) :=
  AffineMap.contDiff_lineMap_uncurry.comp_contMDiff (h₁.prodMk_space (h₂.prodMk_space hg))

/-- **Straight-line contraction.** Let `U` be a nonempty open subset of `M`, and `φ : M → E'` a
map to a real normed space, smooth on `U`, with a left inverse `ψ` on `U` that is smooth on
`φ '' U`. If `φ '' U` is star-convex, then `U` is smoothly contractible, by
`(x, t) ↦ ψ (c + t • (φ x - c))`. -/
theorem IsSmoothlyContractible.of_starConvex_image {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] {U : Opens M} {φ : M → E'} {ψ : E' → M} {c : E'}
    (hφ : ContMDiffOn I 𝓘(ℝ, E') ∞ φ U) (hψ : ContMDiffOn 𝓘(ℝ, E') I ∞ ψ (φ '' U))
    (hψφ : LeftInvOn ψ φ U) (hc : StarConvex ℝ c (φ '' U)) (hne : (U : Set M).Nonempty) :
    IsSmoothlyContractible I U := by
  have hcU : c ∈ φ '' U := hc.mem (hne.image φ)
  have hψU : MapsTo ψ (φ '' U) U := by
    rintro _ ⟨y, hy, rfl⟩
    rwa [hψφ hy]
  -- The straight line from `c` to `φ x`, at time `t`.
  let G : U × unitInterval → E' := fun p ↦ AffineMap.lineMap c (φ p.1) (p.2 : ℝ)
  have hG : ∀ p, G p ∈ φ '' U := fun p ↦
    hc.segment_subset (mem_image_of_mem φ p.1.property) (lineMap_mem_segment ℝ _ _ p.2.property)
  have hGs : ContMDiff (I.prod (𝓡∂ 1)) 𝓘(ℝ, E') ∞ G :=
    contMDiff_const.lineMap
      ((hφ.comp_contMDiff contMDiff_subtypeVal fun x ↦ x.property).comp contMDiff_fst)
      ((contMDiff_subtypeVal_Icc (x := 0) (y := 1)).comp contMDiff_snd)
  obtain ⟨x₀, hx₀, hφx₀⟩ := hcU
  refine ⟨⟨x₀, hx₀⟩, fun p ↦ ⟨ψ (G p), hψU (hG p)⟩, ?_, fun x ↦ ?_, fun x ↦ ?_⟩
  · rw [← ContMDiff.subtypeVal_comp_iff]
    exact hψ.comp_contMDiff hGs hG
  · ext
    simp [G, ← hφx₀, hψφ hx₀]
  · ext
    simp [G, hψφ x.property]

/-- An open subset of the domain of the extended chart at `x` whose image under that chart is
star-convex is smoothly contractible. -/
theorem IsSmoothlyContractible.of_starConvex_image_extChartAt [IsManifold I ∞ M] {x : M}
    {U : Opens M} (hU : (U : Set M) ⊆ (extChartAt I x).source) {c : E}
    (hc : StarConvex ℝ c (extChartAt I x '' U)) (hne : (U : Set M).Nonempty) :
    IsSmoothlyContractible I U :=
  .of_starConvex_image (contMDiffOn_extChartAt.mono (extChartAt_source I x ▸ hU))
    ((contMDiffOn_extChartAt_symm x).mono ((extChartAt I x).mapsTo.mono_left hU).image_subset)
    (fun _ hy ↦ (extChartAt I x).left_inv (hU hy)) hc hne

/-- Every point of a manifold has a smoothly contractible open neighbourhood. -/
theorem exists_mem_isSmoothlyContractible [IsManifold I ∞ M] (x : M) :
    ∃ U : Opens M, x ∈ U ∧ IsSmoothlyContractible I U := by
  set e := extChartAt I x
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.1 (extChartAt_target_mem_nhdsWithin (I := I) x)
  let U : Opens M := ⟨e.source ∩ e ⁻¹' Metric.ball (e x) ε,
    isOpen_extChartAt_preimage' x Metric.isOpen_ball⟩
  have hxU : x ∈ U := ⟨mem_extChartAt_source x, Metric.mem_ball_self hε⟩
  have himage : e '' U = Metric.ball (e x) ε ∩ range I := by
    refine Subset.antisymm ?_ fun z hz ↦ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨hy.2, extChartAt_target_subset_range x (e.map_source hy.1)⟩
    · have hz' := hsub hz
      refine ⟨e.symm z, ⟨e.map_target hz', ?_⟩, e.right_inv hz'⟩
      simpa only [mem_preimage, e.right_inv hz'] using hz.1
  refine ⟨U, hxU, .of_starConvex_image_extChartAt (fun y hy ↦ hy.1) (c := e x) ?_ ⟨x, hxU⟩⟩
  rw [himage]
  exact ((convex_ball _ _).inter I.convex_range).starConvex
    ⟨Metric.mem_ball_self hε, mem_range_self _⟩

end Contractible

section GoodCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable (I) in
/-- A finite family `U` of open subsets of `M` is a *finite good cover* if it covers `M` and the
intersection of each nonempty subfamily, when it is nonempty, is smoothly contractible. -/
def IsFiniteGoodCover {ι : Type*} [Finite ι] (U : ι → Opens M) : Prop :=
  (⨆ i, U i) = ⊤ ∧ ∀ s : Finset ι, s.Nonempty → ((⨅ i ∈ s, U i : Opens M) : Set M).Nonempty →
    IsSmoothlyContractible I (⨅ i ∈ s, U i : Opens M)

/-- Unfolds `IsFiniteGoodCover` into its two clauses: covering, and contractible intersections. -/
theorem isFiniteGoodCover_def {ι : Type*} [Finite ι] (U : ι → Opens M) :
    IsFiniteGoodCover I U ↔ (⨆ i, U i) = ⊤ ∧ ∀ s : Finset ι, s.Nonempty →
      ((⨅ i ∈ s, U i : Opens M) : Set M).Nonempty →
      IsSmoothlyContractible I (⨅ i ∈ s, U i : Opens M) :=
  Iff.rfl

/-- The sets of a finite good cover cover the manifold. -/
theorem IsFiniteGoodCover.iSup_eq_top {ι : Type*} [Finite ι] {U : ι → Opens M}
    (hU : IsFiniteGoodCover I U) : (⨆ i, U i) = ⊤ :=
  hU.1

/-- In a finite good cover, the intersection of a nonempty subfamily is smoothly contractible
when it is nonempty. -/
theorem IsFiniteGoodCover.isSmoothlyContractible {ι : Type*} [Finite ι] {U : ι → Opens M}
    (hU : IsFiniteGoodCover I U) {s : Finset ι} (hs : s.Nonempty)
    (hne : ((⨅ i ∈ s, U i : Opens M) : Set M).Nonempty) :
    IsSmoothlyContractible I (⨅ i ∈ s, U i : Opens M) :=
  hU.2 s hs hne

variable (I M) in
/-- A manifold `M` *has a finite good cover* if some family of open sets indexed by `Fin n` is a
finite good cover of `M`. -/
def HasFiniteGoodCover : Prop :=
  ∃ (n : ℕ) (U : Fin n → Opens M), IsFiniteGoodCover I U

/-- Unfolds `HasFiniteGoodCover`: some family indexed by `Fin n` is a finite good cover. -/
theorem hasFiniteGoodCover_def :
    HasFiniteGoodCover I M ↔ ∃ (n : ℕ) (U : Fin n → Opens M), IsFiniteGoodCover I U :=
  Iff.rfl

/-- A finite good cover stays one when it is reindexed by an equivalence. -/
theorem IsFiniteGoodCover.comp_equiv {ι κ : Type*} [Finite ι] [Finite κ] {U : ι → Opens M}
    (hU : IsFiniteGoodCover I U) (e : κ ≃ ι) : IsFiniteGoodCover I fun k ↦ U (e k) := by
  classical
  refine ⟨by simpa [e.iSup_comp (g := U)] using hU.iSup_eq_top, fun s hs hne ↦ ?_⟩
  have h : (⨅ k ∈ s, U (e k)) = ⨅ i ∈ s.image e, U i := Finset.iInf_finset_image.symm
  rw [h] at hne ⊢
  exact hU.isSmoothlyContractible (hs.image e) hne

/-- A manifold with a finite good cover, indexed by any finite type, has a finite good cover. -/
theorem IsFiniteGoodCover.hasFiniteGoodCover {ι : Type*} [Finite ι] {U : ι → Opens M}
    (hU : IsFiniteGoodCover I U) : HasFiniteGoodCover I M :=
  let e := Finite.equivFin ι
  ⟨_, fun k ↦ U (e.symm k), hU.comp_equiv e.symm⟩

/-- A smoothly contractible manifold has a finite good cover: the cover by the whole space. -/
theorem IsSmoothlyContractible.hasFiniteGoodCover (h : IsSmoothlyContractible I M) :
    HasFiniteGoodCover I M := by
  obtain ⟨c, F, hF, h₀, h₁⟩ := h
  refine IsFiniteGoodCover.hasFiniteGoodCover (ι := Unit) (U := fun _ ↦ ⊤)
    ⟨iSup_const, fun s _ _ ↦ ?_⟩
  rw [show (⨅ i ∈ s, (fun _ ↦ ⊤ : Unit → Opens M) i) = ⊤ by simp]
  refine ⟨⟨c, trivial⟩, fun p ↦ ⟨F (p.1, p.2), trivial⟩, ?_, fun x ↦ ?_, fun x ↦ ?_⟩
  · rw [← ContMDiff.subtypeVal_comp_iff]
    exact hF.comp ((contMDiff_subtypeVal.comp contMDiff_fst).prodMk contMDiff_snd)
  · ext
    simp [h₀]
  · ext
    simp [h₁]

end GoodCover

end SymplecticGeometry

open SymplecticGeometry

/-- A nonempty open subset `U` of the model space of `I` whose image `I '' U` is star-convex is
smoothly contractible. -/
theorem StarConvex.isSmoothlyContractible {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {U : Opens H} {c : E}
    (hU : StarConvex ℝ c (I '' U)) (hne : (U : Set H).Nonempty) : IsSmoothlyContractible I U :=
  .of_starConvex_image I.contMDiff.contMDiffOn (I.contMDiffOn_symm.mono (image_subset_range _ _))
    (fun _ _ ↦ I.left_inv _) hU hne

/-- A nonempty open convex subset of a real normed space is smoothly contractible. -/
theorem Convex.isSmoothlyContractible {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Opens E} (hU : Convex ℝ (U : Set E)) (hne : (U : Set E).Nonempty) :
    IsSmoothlyContractible 𝓘(ℝ, E) U := by
  obtain ⟨c, hc⟩ := hne
  exact StarConvex.isSmoothlyContractible (by simpa using hU.starConvex hc) ⟨c, hc⟩

namespace StarConvex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {U : Opens V} {c : V}

/-- The **straight-line contraction** of an open set `U` of a real normed space that is
star-convex about `c`: the map `U × [0, 1] → U` taking `(x, s)` to
`AffineMap.lineMap c x s = c + s • (x - c)`. -/
def lineContraction (hU : StarConvex ℝ c (U : Set V)) : U × unitInterval → U := fun p ↦
  ⟨AffineMap.lineMap c (p.1 : V) (p.2 : ℝ),
    hU.segment_subset p.1.property (lineMap_mem_segment ℝ _ _ p.2.property)⟩

@[simp]
theorem coe_lineContraction (hU : StarConvex ℝ c (U : Set V)) (p : U × unitInterval) :
    (hU.lineContraction p : V) = AffineMap.lineMap c (p.1 : V) (p.2 : ℝ) :=
  (rfl)

/-- At time `0`, the straight-line contraction is the constant map at the centre. -/
theorem lineContraction_zero (hU : StarConvex ℝ c (U : Set V)) (hc : c ∈ U) (x : U) :
    hU.lineContraction (x, 0) = ⟨c, hc⟩ :=
  Subtype.ext (by simp)

/-- At time `1`, the straight-line contraction is the identity. -/
@[simp]
theorem lineContraction_one (hU : StarConvex ℝ c (U : Set V)) (x : U) :
    hU.lineContraction (x, 1) = x :=
  Subtype.ext (by simp)

/-- The straight-line contraction is smooth. -/
theorem contMDiff_lineContraction (hU : StarConvex ℝ c (U : Set V)) :
    ContMDiff (𝓘(ℝ, V).prod (𝓡∂ 1)) 𝓘(ℝ, V) ∞ hU.lineContraction := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  exact contMDiff_const.lineMap ((contMDiff_subtypeVal (U := U)).comp contMDiff_fst)
    ((contMDiff_subtypeVal_Icc (x := 0) (y := 1)).comp contMDiff_snd)

end StarConvex

end
