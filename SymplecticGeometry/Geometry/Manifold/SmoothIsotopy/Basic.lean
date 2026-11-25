/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.ContMDiffMap.Chart.CodRestrict
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Opens
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Comp
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph

/-!
# Restricting and composing smooth isotopies

Three operations on a smooth isotopy `F : [0, 1] × P → M` of embeddings
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
  `postcomp`, the endpoints are given as bundled maps that agree with `e ∘ f₀` and `e ∘ f₁`.

The file also makes a smooth isotopy out of a smooth embedding `f : P → M` and a diffeotopy `Φ`
of `P`: the motion `(t, x) ↦ f (Φ (t, x))`. Its construction follows Tau Ceti's
`TauCeti.Diffeotopy.smoothIsotopy`, which moves `f` by a diffeotopy of `M` instead.

## Main definitions

* `TauCeti.SmoothIsotopy.restrict G h`: the restriction of an isotopy `G` of an open `W ⊆ P` to
  an open `V ⊆ W`.
* `TauCeti.SmoothIsotopy.codRestrict F U h`: an isotopy whose motion lies in the open `U ⊆ M`, as
  an isotopy into `U`.
* `TauCeti.SmoothIsotopy.postcompSmoothEmbedding F e he hn g₀ g₁ hg₀ hg₁`: the isotopy
  `(t, x) ↦ e (F (t, x))`, from `g₀ = e ∘ f₀` to `g₁ = e ∘ f₁`.
* `TauCeti.Diffeotopy.precompSmoothIsotopy Φ f`: the isotopy `(t, x) ↦ f (Φ (t, x))` of a smooth
  embedding `f` by a diffeotopy `Φ` of its source, from `f` to `f ∘ Φ₁`.
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

end TauCeti.SmoothIsotopy


/-! ### Precomposition with a diffeotopy of the source -/

namespace TauCeti.Diffeotopy

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  {n : ℕ∞ω} [IsManifold J n P]

/-- The smooth isotopy `(t, x) ↦ f (Φ (t, x))` of a smooth embedding `f : P → M` given by a
diffeotopy `Φ` of its source, from `f` to `f ∘ Φ₁`. It is the source-side counterpart of Tau
Ceti's `TauCeti.Diffeotopy.smoothIsotopy`, which moves `f` by a diffeotopy of its target. -/
def precompSmoothIsotopy (Φ : Diffeotopy J n P) (f : SmoothEmbedding J I n P M) :
    SmoothIsotopy f.toContMDiffMap (f.compDiffeomorph Φ.final).toContMDiffMap where
  toContMDiffMap := ⟨fun p ↦ f (Φ p), f.contMDiff.comp Φ.contMDiff⟩
  map_zero_left x := congrArg f (Φ.apply_zero x)
  map_one_left x := by simp [Φ.final_apply]
  isSmoothEmbedding t := by
    dsimp
    simpa only [Function.comp_def, Diffeotopy.timeSlice_apply] using
      isSmoothEmbedding_comp_diffeomorph (Φ.timeSlice t) f.isSmoothEmbedding

@[simp]
theorem precompSmoothIsotopy_apply (Φ : Diffeotopy J n P) (f : SmoothEmbedding J I n P M)
    (p : unitInterval × P) : Φ.precompSmoothIsotopy f p = f (Φ p) :=
  (rfl)

end TauCeti.Diffeotopy

end
