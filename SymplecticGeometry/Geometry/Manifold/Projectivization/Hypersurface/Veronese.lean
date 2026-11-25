/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.Basic
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Pullback
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.RestrictScalars
import SymplecticGeometry.LinearAlgebra.Pi.LinearForm
import SymplecticGeometry.LinearAlgebra.Projectivization.VeroneseLinearForm
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.Projectivization.Veronese
public import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Manifold.TubularNeighborhood.Existence

/-!
# A hypersurface as a hyperplane section of a Veronese variety

Let `X ⊆ ℂℙⁿ⁺¹` be a smooth projective hypersurface of degree `d ≠ 0`, cut out by `f`. The
Veronese map of degree `d` sends `[v]` to the point whose homogeneous coordinates are the `D`
monomials of degree `d` in `v`, and `f` is a linear form `ℓ` in these monomials. Composing the
Veronese map with a linear change of coordinates whose coordinate `0` is `ℓ` gives a closed
holomorphic embedding `ν : ℂℙⁿ⁺¹ → ℂℙᴰ⁻¹` (`SmoothProjectiveHypersurface.veroneseMap`) whose image
`Y` meets the coordinate hyperplane `{x₀ = 0}` exactly in `ν(X)`. This places `X` in the setting
of Tau Ceti's Lefschetz hyperplane theorems (`TauCeti.isIso_homologyMap_notMem_affineOpen` and its
neighbours), as in the proof of the Lefschetz theorem for hypersurfaces in Milnor's *Morse
Theory*, §7:

* the affine part `Z` of `Y` in the chart `x₀ ≠ 0` is the image of the open set
  `ℂℙⁿ⁺¹ \ X`, so it is a complex manifold of dimension `n + 1`, carried by the homeomorphism
  `SmoothProjectiveHypersurface.veroneseAffineHomeomorph`, and its inclusion into `ℂᴰ⁻¹` is
  holomorphic with injective differential, since `ν` is an immersion;
* a tubular neighbourhood of `X` in `ℂℙⁿ⁺¹` (Tau Ceti's
  `TauCeti.SmoothEmbedding.exists_homotopyEquiv_subset`, applied to `X` as a real submanifold)
  is carried by `ν` to a neighbourhood of `Y ∩ {x₀ = 0}` in `Y` whose inclusion is a homotopy
  equivalence.

## Main declarations

* `SymplecticGeometry.SmoothProjectiveHypersurface.veroneseEquiv`: a linear isomorphism of the
  space of monomials with `Fin (D - 1 + 1) → ℂ` whose coordinate `0` is the linear form of the
  polynomial.
* `SymplecticGeometry.SmoothProjectiveHypersurface.veroneseMap` and `veroneseImage`: the
  composite `ν` and its image `Y`, with `veroneseImage_inter_hyperplane`.
* `SymplecticGeometry.SmoothProjectiveHypersurface.veroneseHomeomorph`: `ℂℙⁿ⁺¹ ≃ₜ Y`, and
  `veroneseHyperplaneHomeomorph`, its restriction `X ≃ₜ Y ∩ {x₀ = 0}`.
* `SymplecticGeometry.SmoothProjectiveHypersurface.veroneseAffine`: the affine part `Z`, with its
  manifold structure, `contMDiff_coe_veroneseAffine`, `isImmersion_coe_veroneseAffine` and
  `injective_mfderiv_coe_veroneseAffine`.
* `SymplecticGeometry.SmoothProjectiveHypersurface.exists_homotopyEquiv_nhds`: the neighbourhood
  of `Y ∩ {x₀ = 0}`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton (1963), §7.
* [A. Andreotti, T. Frankel, *The Lefschetz theorem on hyperplane sections*][AndreottiFrankel1959].
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Theorem 6.24.
-/

public section

open MvPolynomial Set Projectivization TauCeti Function Topology Manifold
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace SymplecticGeometry

namespace SmoothProjectiveHypersurface

variable {n d : ℕ} (X : SmoothProjectiveHypersurface n d)

/-- A linear isomorphism from the space of monomials of degree `d` in `n + 2` variables to
`Fin (D - 1 + 1) → ℂ`, `D` its dimension, whose coordinate `0` is the linear form of the
polynomial of the hypersurface (`veroneseEquiv_apply_zero`). -/
noncomputable def veroneseEquiv :
    (Fin (veroneseDim (n + 2) d) → ℂ) ≃ₗ[ℂ] Fin (veroneseDim (n + 2) d - 1 + 1) → ℂ :=
  (LinearEquiv.exists_apply_eq_sum_mul
    (X.isHomogeneous.veroneseLinearForm_coeff_ne_zero X.poly_ne_zero)
    (Fin.cast (Nat.sub_one_add_one (NeZero.ne _)) 0)).choose.trans
      (finSubOneAddOneLinearEquiv ℂ _)

/-- Coordinate `0` of `veroneseEquiv` is the linear form of the polynomial. -/
theorem veroneseEquiv_apply_zero (w : Fin (veroneseDim (n + 2) d) → ℂ) :
    X.veroneseEquiv w 0 = eval w (veroneseLinearForm d X.poly) := by
  rw [veroneseEquiv, LinearEquiv.trans_apply, finSubOneAddOneLinearEquiv_apply,
    (LinearEquiv.exists_apply_eq_sum_mul
      (X.isHomogeneous.veroneseLinearForm_coeff_ne_zero X.poly_ne_zero) _).choose_spec,
    eval_veroneseLinearForm]

/-- On the monomials of `v`, coordinate `0` of `veroneseEquiv` is the polynomial at `v`. -/
@[simp]
theorem veroneseEquiv_veroneseMonomials_zero (v : Fin (n + 2) → ℂ) :
    X.veroneseEquiv (veroneseMonomials d v) 0 = eval v X.poly := by
  rw [veroneseEquiv_apply_zero, eval_veroneseMonomials_veroneseLinearForm X.isHomogeneous]

/-- The Veronese map of degree `d` followed by the change of coordinates `veroneseEquiv`, a map
`ℂℙⁿ⁺¹ → ℂℙᴰ⁻¹`. Its coordinate `0` vanishes exactly on the hypersurface
(`veroneseMap_mem_affineOpen_iff`). -/
noncomputable def veroneseMap :
    ℙ ℂ (Fin (n + 2) → ℂ) → ℙ ℂ (Fin (veroneseDim (n + 2) d - 1 + 1) → ℂ) :=
  map (X.veroneseEquiv : _ →ₗ[ℂ] _) X.veroneseEquiv.injective ∘ veronese ℂ d

theorem veroneseMap_def :
    X.veroneseMap = map (X.veroneseEquiv : _ →ₗ[ℂ] _) X.veroneseEquiv.injective ∘ veronese ℂ d :=
  (rfl)

/-- `veroneseMap` sends the line through `v` to the line through the image of the monomials of
`v` under `veroneseEquiv`. -/
theorem veroneseMap_mk {v : Fin (n + 2) → ℂ} (hv : v ≠ 0) :
    X.veroneseMap (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (X.veroneseEquiv (veroneseMonomials d v))
        ((map_ne_zero_iff _ X.veroneseEquiv.injective).2 (veroneseMonomials_ne_zero d hv)) := by
  simp [veroneseMap_def, veronese_mk, map_mk]

/-- A point of `ℂℙⁿ⁺¹` is sent by `veroneseMap` into the affine chart `x₀ ≠ 0` exactly when it is
off the hypersurface. -/
theorem veroneseMap_mem_affineOpen_iff {x : ℙ ℂ (Fin (n + 2) → ℂ)} :
    X.veroneseMap x ∈ affineOpen 0 ↔ x ∉ X.carrier := by
  induction x using Projectivization.ind with | h v hv => ?_
  rw [veroneseMap_mk, mk_mem_affineOpen_iff, veroneseEquiv_veroneseMonomials_zero,
    X.mem_carrier_mk_iff hv]

/-- `veroneseMap` is holomorphic, and indeed `C^r` for every `r`. -/
theorem contMDiff_veroneseMap (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (veroneseDim (n + 2) d - 1) → ℂ) r X.veroneseMap :=
  contMDiff_map_comp_veronese _ _ r

/-- The image `Y` of `veroneseMap`. -/
noncomputable def veroneseImage : Set (ℙ ℂ (Fin (veroneseDim (n + 2) d - 1 + 1) → ℂ)) :=
  range X.veroneseMap

theorem veroneseImage_def : X.veroneseImage = range X.veroneseMap :=
  (rfl)

/-- The image of the hypersurface lies in the hyperplane `x₀ = 0`, and the rest of `ℂℙⁿ⁺¹` in the
affine chart `x₀ ≠ 0`: so `Y ∩ {x₀ = 0}` is the image of the hypersurface. -/
theorem veroneseImage_inter_hyperplane :
    X.veroneseImage ∩ (affineOpen 0)ᶜ = X.veroneseMap '' X.carrier := by
  ext y
  simp only [veroneseImage_def, mem_inter_iff, mem_range, mem_compl_iff, mem_image]
  constructor
  · rintro ⟨⟨x, rfl⟩, hy⟩
    exact ⟨x, not_not.1 (mt X.veroneseMap_mem_affineOpen_iff.2 hy), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, fun h ↦ X.veroneseMap_mem_affineOpen_iff.1 h hx⟩

/-- The part of `Y` in the affine chart `x₀ ≠ 0` is the image of the complement of the
hypersurface. -/
theorem veroneseImage_inter_affineOpen :
    X.veroneseImage ∩ affineOpen 0 = X.veroneseMap '' X.carrierᶜ := by
  ext y
  simp only [veroneseImage_def, mem_inter_iff, mem_range, mem_image, mem_compl_iff]
  constructor
  · rintro ⟨⟨x, rfl⟩, hy⟩
    exact ⟨x, X.veroneseMap_mem_affineOpen_iff.1 hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, X.veroneseMap_mem_affineOpen_iff.2 hx⟩

/-- The affine part `Z ⊆ ℂᴰ⁻¹` of `Y` in the chart `x₀ ≠ 0`. -/
noncomputable def veroneseAffine : Set (Fin (veroneseDim (n + 2) d - 1) → ℂ) :=
  affineChart 0 '' (X.veroneseImage ∩ affineOpen 0)

theorem veroneseAffine_def :
    X.veroneseAffine = affineChart 0 '' (X.veroneseImage ∩ affineOpen 0) :=
  (rfl)

/-- The complement of the hypersurface, an open subset of `ℂℙⁿ⁺¹`. -/
def complOpens : TopologicalSpace.Opens (ℙ ℂ (Fin (n + 2) → ℂ)) :=
  ⟨X.carrierᶜ, by rw [carrier_def]; exact (isClosed_complexProjectiveZeroLocus _).isOpen_compl⟩

@[simp]
theorem mem_complOpens_iff {x : ℙ ℂ (Fin (n + 2) → ℂ)} : x ∈ X.complOpens ↔ x ∉ X.carrier :=
  Iff.rfl

/-- The hypersurface has an open neighbourhood in `ℂℙⁿ⁺¹` onto which its inclusion is a homotopy
equivalence: a tubular neighbourhood of `X`, seen as a real submanifold. -/
theorem exists_isOpen_homotopyEquiv :
    ∃ W : Set (ℙ ℂ (Fin (n + 2) → ℂ)), IsOpen W ∧
      ∃ e : ContinuousMap.HomotopyEquiv X W, ∀ x, (e.toFun x : ℙ ℂ (Fin (n + 2) → ℂ)) = x := by
  -- The inclusion of `X` is a holomorphic embedding, so a smooth embedding over `ℝ`.
  let _ : IsManifold 𝓘(ℝ, Fin (n + 1 - Fintype.card Unit) → ℂ) ∞ X :=
    ((X.instIsManifold).of_le (m := ∞) (by simp)).restrictScalars ℝ
  have h := (X.embedding.isSmoothEmbedding.of_le (n := ∞) (by simp)).restrictScalars ℝ (by simp)
  rw [coe_embedding] at h
  let f : SmoothEmbedding 𝓘(ℝ, Fin (n + 1 - Fintype.card Unit) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ X
      (ℙ ℂ (Fin (n + 2) → ℂ)) :=
    .ofIsSmoothEmbedding _ h
  obtain ⟨W, hW, -, e, he⟩ := f.exists_homotopyEquiv_subset isOpen_univ (subset_univ _)
  exact ⟨W, hW, e, fun x ↦ (he x).trans (SmoothEmbedding.ofIsSmoothEmbedding_apply _ _ x)⟩

section Degree

variable [NeZero d]

/-- For `d ≠ 0`, `veroneseMap` is a closed embedding. -/
theorem isClosedEmbedding_veroneseMap : IsClosedEmbedding X.veroneseMap :=
  isClosedEmbedding_map_comp_veronese (NeZero.ne d) _ _

/-- The Veronese image `Y` is closed in `ℂℙᴰ⁻¹`. -/
theorem isClosed_veroneseImage : IsClosed X.veroneseImage :=
  X.isClosedEmbedding_veroneseMap.isClosed_range

/-- `veroneseMap` is a holomorphic immersion. -/
theorem isImmersion_veroneseMap {r : ℕ∞ω} (hr : 1 ≤ r) :
    IsImmersion 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (veroneseDim (n + 2) d - 1) → ℂ) r
      X.veroneseMap :=
  isImmersion_map_comp_veronese (NeZero.ne d) _ _ hr

/-- `ℂℙⁿ⁺¹` is homeomorphic to the image `Y` of `veroneseMap`. -/
noncomputable def veroneseHomeomorph : ℙ ℂ (Fin (n + 2) → ℂ) ≃ₜ X.veroneseImage :=
  X.isClosedEmbedding_veroneseMap.isEmbedding.toHomeomorph

@[simp]
theorem coe_veroneseHomeomorph_apply (x : ℙ ℂ (Fin (n + 2) → ℂ)) :
    (X.veroneseHomeomorph x : ℙ ℂ (Fin (veroneseDim (n + 2) d - 1 + 1) → ℂ)) = X.veroneseMap x :=
  (rfl)

/-- `veroneseHomeomorph` restricts to a homeomorphism from the hypersurface onto the hyperplane
section `Y ∩ {x₀ = 0}`, seen as a subset of `Y`. -/
noncomputable def veroneseHyperplaneHomeomorph :
    X ≃ₜ {y : X.veroneseImage |
      (y : ℙ ℂ (Fin (veroneseDim (n + 2) d - 1 + 1) → ℂ)) ∉ affineOpen 0} :=
  X.veroneseHomeomorph.subtype fun _ ↦
    not_not.symm.trans (not_congr X.veroneseMap_mem_affineOpen_iff).symm

@[simp]
theorem coe_veroneseHyperplaneHomeomorph_apply (x : X) :
    (X.veroneseHyperplaneHomeomorph x : X.veroneseImage) = X.veroneseHomeomorph x :=
  (rfl)

/-- The hyperplane section `Y ∩ {x₀ = 0}` has a neighbourhood `W` in `Y` whose inclusion is a
homotopy equivalence: the image under `veroneseHomeomorph` of a tubular neighbourhood of the
hypersurface. -/
theorem exists_homotopyEquiv_nhds :
    ∃ (W : Set X.veroneseImage)
      (hAW : {y : X.veroneseImage |
        (y : ℙ ℂ (Fin (veroneseDim (n + 2) d - 1 + 1) → ℂ)) ∉ affineOpen 0} ⊆ W),
      W ∈ 𝓝ˢ {y : X.veroneseImage |
        (y : ℙ ℂ (Fin (veroneseDim (n + 2) d - 1 + 1) → ℂ)) ∉ affineOpen 0} ∧
      ∃ e : ContinuousMap.HomotopyEquiv {y : X.veroneseImage |
          (y : ℙ ℂ (Fin (veroneseDim (n + 2) d - 1 + 1) → ℂ)) ∉ affineOpen 0} W,
        e.toFun = ContinuousMap.inclusion hAW := by
  obtain ⟨U, hU, e, he⟩ := X.exists_isOpen_homotopyEquiv
  have hAW : {y : X.veroneseImage |
      (y : ℙ ℂ (Fin (veroneseDim (n + 2) d - 1 + 1) → ℂ)) ∉ affineOpen 0} ⊆
        X.veroneseHomeomorph '' U := fun y hy ↦ by
    refine ⟨X.veroneseHyperplaneHomeomorph.symm ⟨y, hy⟩,
      by simpa [he] using (e.toFun _).property, ?_⟩
    rw [← coe_veroneseHyperplaneHomeomorph_apply, Homeomorph.apply_symm_apply]
  refine ⟨_, hAW, (X.veroneseHomeomorph.isOpenMap U hU).mem_nhdsSet.2 hAW,
    X.veroneseHyperplaneHomeomorph.symm.toHomotopyEquiv.trans
      (e.trans (X.veroneseHomeomorph.image U).toHomotopyEquiv), ?_⟩
  ext y
  simp only [ContinuousMap.HomotopyEquiv.trans_apply, Homeomorph.coe_toHomotopyEquiv,
    Homeomorph.image_apply_coe, ContinuousMap.inclusion_apply_coe]
  rw [he, ← coe_veroneseHyperplaneHomeomorph_apply, Homeomorph.apply_symm_apply]

/-- The homeomorphism from the complement of the hypersurface onto the affine part `Z` of `Y`,
`x ↦ affineChart 0 (veroneseMap x)`. -/
noncomputable def veroneseAffineHomeomorph : X.complOpens ≃ₜ X.veroneseAffine :=
  ((X.isClosedEmbedding_veroneseMap.isEmbedding.comp IsEmbedding.subtypeVal).toHomeomorph.trans
    (Homeomorph.setCongr (by
      rw [range_comp, Subtype.range_coe, X.veroneseImage_inter_affineOpen]; rfl))).trans
    (interAffineOpenHomeomorph X.veroneseAffine_def.symm)

@[simp]
theorem coe_veroneseAffineHomeomorph_apply (x : X.complOpens) :
    (X.veroneseAffineHomeomorph x : Fin (veroneseDim (n + 2) d - 1) → ℂ) =
      affineChart 0 (X.veroneseMap x) := by
  simp only [veroneseAffineHomeomorph, Homeomorph.trans_apply, coe_interAffineOpenHomeomorph_apply]
  rfl

/-- The atlas of the affine part `Z` of `Y`, carried from the complement of the hypersurface by
`veroneseAffineHomeomorph`. -/
noncomputable instance : ChartedSpace (Fin (n + 1) → ℂ) X.veroneseAffine :=
  X.veroneseAffineHomeomorph.symm.pullbackChartedSpace

/-- The affine part `Z` of `Y` is a complex manifold of dimension `n + 1`. -/
instance (r : ℕ∞ω) : IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) r X.veroneseAffine :=
  X.veroneseAffineHomeomorph.symm.pullback_isManifold _ _

/-- `veroneseAffineHomeomorph` is a diffeomorphism; this is its inverse. -/
noncomputable def veroneseAffineDiffeomorph (r : ℕ∞ω) :
    X.veroneseAffine ≃ₘ^r⟮𝓘(ℂ, Fin (n + 1) → ℂ), 𝓘(ℂ, Fin (n + 1) → ℂ)⟯ X.complOpens :=
  X.veroneseAffineHomeomorph.symm.pullbackDiffeomorph _ r

@[simp]
theorem coe_veroneseAffineDiffeomorph (r : ℕ∞ω) :
    ⇑(X.veroneseAffineDiffeomorph r) = X.veroneseAffineHomeomorph.symm :=
  Homeomorph.coe_pullbackDiffeomorph _ _ _

/-- The inclusion of `Z` into `ℂᴰ⁻¹` is `affineChart 0 ∘ veroneseMap`, read through
`veroneseAffineHomeomorph`. -/
theorem coe_veroneseAffine_eq_comp :
    (Subtype.val : X.veroneseAffine → Fin (veroneseDim (n + 2) d - 1) → ℂ) =
      (affineChart 0 ∘ X.veroneseMap ∘ Subtype.val) ∘ X.veroneseAffineHomeomorph.symm := by
  ext1 z
  rw [comp_apply, comp_apply, comp_apply, ← coe_veroneseAffineHomeomorph_apply,
    Homeomorph.apply_symm_apply]

/-- The inclusion of the affine part `Z` of `Y` into `ℂᴰ⁻¹` is holomorphic. -/
theorem contMDiff_coe_veroneseAffine (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (veroneseDim (n + 2) d - 1) → ℂ) r
      (Subtype.val : X.veroneseAffine → Fin (veroneseDim (n + 2) d - 1) → ℂ) := by
  rw [coe_veroneseAffine_eq_comp, ← X.coe_veroneseAffineDiffeomorph r]
  refine ContMDiff.comp ?_ (X.veroneseAffineDiffeomorph r).contMDiff
  exact (contMDiffOn_affineChart 0 r).comp_contMDiff
    ((X.contMDiff_veroneseMap r).comp contMDiff_subtypeVal)
    fun x ↦ X.veroneseMap_mem_affineOpen_iff.2 x.property

/-- The inclusion of the affine part `Z` of `Y` into `ℂᴰ⁻¹` is a holomorphic immersion. -/
theorem isImmersion_coe_veroneseAffine {r : ℕ∞ω} (hr : 1 ≤ r) :
    IsImmersion 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (veroneseDim (n + 2) d - 1) → ℂ) r
      (Subtype.val : X.veroneseAffine → Fin (veroneseDim (n + 2) d - 1) → ℂ) := by
  rw [coe_veroneseAffine_eq_comp]
  refine X.veroneseAffineHomeomorph.symm.isImmersion_comp_pullbackChartedSpace_iff.2 ?_
  refine isImmersion_isLocalDiffeomorphAt_comp (fun x ↦ ?_) ?_
  · rw [← coe_affineOpenPartialHomeomorph]
    exact (affineOpenPartialHomeomorph 0).isLocalDiffeomorphAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, Fin (veroneseDim (n + 2) d - 1) → ℂ)) (n := r)
        (affineOpenPartialHomeomorph_mem_atlas 0))
      (by simpa using X.veroneseMap_mem_affineOpen_iff.2 x.property)
  · exact isImmersion_comp_isLocalDiffeomorph isLocalDiffeomorph_subtype_val
      (X.isImmersion_veroneseMap hr)

/-- The inclusion of the affine part `Z` of `Y` into `ℂᴰ⁻¹` has injective differential. -/
theorem injective_mfderiv_coe_veroneseAffine (z : X.veroneseAffine) :
    Injective (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (veroneseDim (n + 2) d - 1) → ℂ)
      (Subtype.val : X.veroneseAffine → Fin (veroneseDim (n + 2) d - 1) → ℂ) z) :=
  (X.isImmersion_coe_veroneseAffine le_rfl).mfderiv_injective one_ne_zero z

end Degree

end SmoothProjectiveHypersurface

end SymplecticGeometry

end
