/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.ContMDiffMap.Chart.CodRestrict
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Opens
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Comp
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph

/-!
# Restricting, precomposing and postcomposing smooth isotopies

Operations on a smooth isotopy `F : [0, 1] × P → M` of embeddings
(`TauCeti.SmoothIsotopy`), each of which keeps the motion and changes its source or its target:

* restriction to an open subset of the source, when `P` is an open set `W` of a manifold and
  `V ⊆ W` is open: the slices are precomposed with the inclusion `V → W`, a local diffeomorphism
  and a topological embedding;
* corestriction to an open subset `U` of `M` containing the motion: each slice is a smooth
  embedding into `U` (`Manifold.IsSmoothEmbedding.codRestrict`);
* postcomposition with a smooth embedding `e : M → Q`, where `Q` may be modelled on another model
  than `M`. Tau Ceti's `TauCeti.SmoothIsotopy.postcomp` needs the same model on both sides, as it
  allows a map `e` that is a local diffeomorphism only along the motion. Here `P` and `Q` are
  boundaryless and `Q` has a finite-dimensional model, so that composites of smooth embeddings are
  smooth embeddings (`Manifold.IsSmoothEmbedding.comp_of_boundaryless`). As in Tau Ceti's
  `postcomp`, the endpoints are given as bundled maps that agree with `e ∘ f₀` and `e ∘ f₁`;
* precomposition with a smooth embedding `χ : Q → P`, where `Q` may be modelled on another model
  than `P`; restriction is the case of the inclusion of an open set. Here `Q` and `M` are
  boundaryless and `M` has a finite-dimensional model, so that the slices `F_t ∘ χ` are smooth
  embeddings (`Manifold.IsSmoothEmbedding.comp_of_boundaryless`). The endpoints are given as
  bundled maps that agree with `f₀ ∘ χ` and `f₁ ∘ χ`.

## Main definitions

* `TauCeti.SmoothIsotopy.restrict G h`: the restriction of an isotopy `G` of an open `W ⊆ P` to
  an open `V ⊆ W`.
* `TauCeti.SmoothIsotopy.codRestrict F U h`: an isotopy whose motion lies in the open `U ⊆ M`, as
  an isotopy into `U`.
* `TauCeti.SmoothIsotopy.postcompSmoothEmbedding F e he hn g₀ g₁ hg₀ hg₁`: the isotopy
  `(t, x) ↦ e (F (t, x))`, from `g₀ = e ∘ f₀` to `g₁ = e ∘ f₁`.
* `TauCeti.SmoothIsotopy.precompSmoothEmbedding F χ hχ hn g₀ g₁ hg₀ hg₁`: the isotopy
  `(t, y) ↦ F (t, χ y)`, from `g₀ = f₀ ∘ χ` to `g₁ = f₁ ∘ χ`.
-/

public noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti.SmoothIsotopy

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  {n : ℕ∞ω}

/-! ### Restriction to an open subset of the source -/

section Restrict

variable [IsManifold J n P] {V W : Opens P} {g₀ g₁ : C^n⟮J, W; I, M⟯}

/-- The **restriction** of a smooth isotopy `G` of an open set `W ⊆ P` to an open set `V ⊆ W`:
the isotopy `(t, x) ↦ G (t, x)` of `V`, from the restriction of `g₀` to that of `g₁`. -/
def restrict (G : SmoothIsotopy g₀ g₁) (h : V ≤ W) :
    SmoothIsotopy (g₀.comp (SmoothEmbedding.inclusion h).toContMDiffMap)
      (g₁.comp (SmoothEmbedding.inclusion h).toContMDiffMap) where
  toContMDiffMap := ⟨fun p ↦ G (p.1, Opens.inclusion h p.2),
    G.contMDiff.comp (contMDiff_fst.prodMk ((contMDiff_inclusion h).comp contMDiff_snd))⟩
  map_zero_left x := (G.apply_zero _).trans (by simp)
  map_one_left x := (G.apply_one _).trans (by simp)
  isSmoothEmbedding t := isSmoothEmbedding_comp_isLocalDiffeomorph (f := fun y ↦ G (t, y))
    (isLocalDiffeomorph_inclusion h) (Topology.IsEmbedding.inclusion h) (G.isSmoothEmbedding t)

@[simp]
theorem restrict_apply (G : SmoothIsotopy g₀ g₁) (h : V ≤ W) (p : unitInterval × V) :
    G.restrict h p = G (p.1, Opens.inclusion h p.2) := by
  rw [← toContMDiffMap_apply]
  rfl

end Restrict

/-! ### Corestriction to an open subset of the target -/

section CodRestrict

variable [IsManifold I n M] {f₀ f₁ : C^n⟮J, P; I, M⟯}

/-- The **corestriction** of a smooth isotopy `F` whose motion lies in an open set `U ⊆ M`: the
isotopy `(t, x) ↦ F (t, x)` into `U`, from the corestriction of `f₀` to that of `f₁`. -/
def codRestrict (F : SmoothIsotopy f₀ f₁) (U : Opens M) (h : ∀ p, F p ∈ U) :
    SmoothIsotopy (f₀.codRestrict U fun x ↦ F.apply_zero x ▸ h (0, x))
      (f₁.codRestrict U fun x ↦ F.apply_one x ▸ h (1, x)) where
  toContMDiffMap := F.toContMDiffMap.codRestrict U h
  map_zero_left x := Subtype.ext <| by
    simp only [ContMDiffMap.coe_codRestrict_apply, toContMDiffMap_apply, apply_zero]
  map_one_left x := Subtype.ext <| by
    simp only [ContMDiffMap.coe_codRestrict_apply, toContMDiffMap_apply, apply_one]
  isSmoothEmbedding t := by
    -- the slice of the corestriction is the slice of `F` with values in `U`
    rw [show (fun x ↦ F.toContMDiffMap.codRestrict U h (t, x)) = fun x ↦ ⟨F (t, x), h (t, x)⟩ from
      funext fun x ↦ Subtype.ext (ContMDiffMap.coe_codRestrict_apply _ _ _ _)]
    exact (F.isSmoothEmbedding t).codRestrict U fun x ↦ h (t, x)

@[simp]
theorem coe_codRestrict_apply (F : SmoothIsotopy f₀ f₁) (U : Opens M) (h : ∀ p, F p ∈ U)
    (p : unitInterval × P) : (F.codRestrict U h p : M) = F p := by
  rw [← toContMDiffMap_apply, codRestrict, ContMDiffMap.coe_codRestrict_apply, toContMDiffMap_apply]

end CodRestrict

/-! ### Postcomposition with a smooth embedding -/

section Postcomp

variable {E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
  [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''} {Q : Type*} [TopologicalSpace Q]
  [ChartedSpace H'' Q] [J.Boundaryless] [K.Boundaryless] [IsManifold J n P] [IsManifold K n Q]
  {f₀ f₁ : C^n⟮J, P; I, M⟯}

/-- The **postcomposition** of a smooth isotopy `F` from a boundaryless manifold with a `C^n`
smooth embedding `e : M → Q`, `1 ≤ n`, into a boundaryless manifold with a finite-dimensional
model: the isotopy `(t, x) ↦ e (F (t, x))`. Its endpoints are given as bundled maps `g₀`, `g₁`
that agree with `e ∘ f₀` and `e ∘ f₁`. -/
def postcompSmoothEmbedding (F : SmoothIsotopy f₀ f₁) (e : M → Q)
    (he : Manifold.IsSmoothEmbedding I K n e) (hn : 1 ≤ n) (g₀ g₁ : C^n⟮J, P; K, Q⟯)
    (hg₀ : ∀ x, g₀ x = e (f₀ x)) (hg₁ : ∀ x, g₁ x = e (f₁ x)) : SmoothIsotopy g₀ g₁ where
  toContMDiffMap := ⟨fun p ↦ e (F p), he.contMDiff.comp F.contMDiff⟩
  map_zero_left x := (congrArg e (F.apply_zero x)).trans (hg₀ x).symm
  map_one_left x := (congrArg e (F.apply_one x)).trans (hg₁ x).symm
  isSmoothEmbedding t := he.comp_of_boundaryless (F.isSmoothEmbedding t) hn

@[simp]
theorem postcompSmoothEmbedding_apply (F : SmoothIsotopy f₀ f₁) (e : M → Q)
    (he : Manifold.IsSmoothEmbedding I K n e) (hn : 1 ≤ n) (g₀ g₁ : C^n⟮J, P; K, Q⟯)
    (hg₀ : ∀ x, g₀ x = e (f₀ x)) (hg₁ : ∀ x, g₁ x = e (f₁ x)) (p : unitInterval × P) :
    F.postcompSmoothEmbedding e he hn g₀ g₁ hg₀ hg₁ p = e (F p) :=
  (rfl)

end Postcomp

/-! ### Precomposition with a smooth embedding -/

section Precomp

variable {E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ E'' H''} {Q : Type*} [TopologicalSpace Q] [ChartedSpace H'' Q]
  [FiniteDimensional ℝ E] [I.Boundaryless] [K.Boundaryless] [IsManifold I n M] [IsManifold K n Q]
  {f₀ f₁ : C^n⟮J, P; I, M⟯}

/-- The **precomposition** of a smooth isotopy `F : [0, 1] × P → M` with a `C^n` smooth embedding
`χ : Q → P`, `1 ≤ n`: the isotopy `(t, y) ↦ F (t, χ y)`. Here `Q` and `M` have no boundary, and
`M` has a finite-dimensional model. Its endpoints are given as bundled maps `g₀`, `g₁` that agree
with `f₀ ∘ χ` and `f₁ ∘ χ`. -/
def precompSmoothEmbedding (F : SmoothIsotopy f₀ f₁) (χ : Q → P)
    (hχ : Manifold.IsSmoothEmbedding K J n χ) (hn : 1 ≤ n)
    (g₀ g₁ : C^n⟮K, Q; I, M⟯) (hg₀ : ∀ y, g₀ y = f₀ (χ y)) (hg₁ : ∀ y, g₁ y = f₁ (χ y)) :
    SmoothIsotopy g₀ g₁ where
  toContMDiffMap := ⟨fun p ↦ F (p.1, χ p.2),
    F.contMDiff.comp (contMDiff_fst.prodMk (hχ.contMDiff.comp contMDiff_snd))⟩
  map_zero_left y := (F.apply_zero (χ y)).trans (hg₀ y).symm
  map_one_left y := (F.apply_one (χ y)).trans (hg₁ y).symm
  isSmoothEmbedding t := (F.isSmoothEmbedding t).comp_of_boundaryless hχ hn

@[simp]
theorem precompSmoothEmbedding_apply (F : SmoothIsotopy f₀ f₁) (χ : Q → P)
    (hχ : Manifold.IsSmoothEmbedding K J n χ) (hn : 1 ≤ n)
    (g₀ g₁ : C^n⟮K, Q; I, M⟯) (hg₀ : ∀ y, g₀ y = f₀ (χ y)) (hg₁ : ∀ y, g₁ y = f₁ (χ y))
    (p : unitInterval × Q) :
    F.precompSmoothEmbedding χ hχ hn g₀ g₁ hg₀ hg₁ p = F (p.1, χ p.2) :=
  (rfl)

end Precomp

end TauCeti.SmoothIsotopy

end
