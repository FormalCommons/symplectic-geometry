/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Instances.Cylinder
public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import TauCeti.Geometry.Manifold.Projectivization.Map
public import TauCeti.Geometry.Manifold.Projectivization.MFDeriv
public import TauCeti.Geometry.Manifold.Submersion.Split
public import TauCeti.Geometry.Sphere.LinearIsometry
public import SymplecticGeometry.Analysis.Complex.Euclidean.Space
public import SymplecticGeometry.Geometry.Manifold.Instances.ComplexProjectiveSpace.Projectivization
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import TauCeti.Analysis.InnerProductSpace.Radial.Rescale
import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.Instances.Sphere
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Opens
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars

/-!
# The Hopf maps

This file makes the two quotient maps onto projective space into smooth submersions of the
underlying real manifolds, using Tau Ceti's affine charts of `ℙ 𝕜 (Fin (n + 1) → 𝕜)`.

* `Projectivization.mkNonzero 𝕜 n` is the projection `v ↦ [v]` from the punctured space
  `TauCeti.puncturedSpace (Fin (n + 1) → 𝕜)` onto `ℙ 𝕜 (Fin (n + 1) → 𝕜)`, for a nontrivially
  normed field `𝕜` that is a finite-dimensional normed `ℝ`-algebra, such as `ℝ` or `ℂ`. It is
  smooth of every order (`contMDiff_mkNonzero`), holomorphic over `𝕜` itself
  (`contMDiff_mkNonzero_self`). Its derivative at `v`, over `𝕜` and over `ℝ` alike, is Tau
  Ceti's derivative `Projectivization.mfderivMk v` of the projection `w ↦ [w]`
  (`mfderiv_mkNonzero_self`, `mfderiv_mkNonzero`, with their `_apply` forms). Since `[c • w] = [w]`,
  `mfderivMk (c • v) (c • w) = mfderivMk v w` for `v ≠ 0` and `c ≠ 0` (`mfderivMk_smul_smul`).
  By Tau Ceti's `Projectivization.surjective_mfderivMk` and `Projectivization.ker_mfderivMk`,
  `mkNonzero` is regular at every point (`isRegularPoint_mkNonzero`), so a submersion
  (`isSubmersion_mkNonzero`), and the kernel of its real derivative at `v` is the line `𝕜 ∙ v`
  (`ker_mfderiv_mkNonzero`). Its fibre over `[v]` is the punctured line of the nonzero multiples
  of `v` (`preimage_mkNonzero_singleton_mk`). For `𝕜 = ℂ` and `n = 1` it is the pencil
  `[z₀ : z₁]` on `ℂ² ∖ 0`. A group acting on `V` by additive maps acts on
  `TauCeti.puncturedSpace V` (`TauCeti.puncturedSpace.instMulAction`, `coe_smul`); when it acts
  `𝕜`-linearly on `𝕜ⁿ⁺¹`, `mkNonzero` is equivariant (`mkNonzero_smul`).
* `Projectivization.affineLift 𝕜 j` is the section `w ↦ Fin.insertNth j 1 w` of `mkNonzero` over
  the affine chart of `j`: `mkNonzero 𝕜 n ∘ affineLift 𝕜 j = (affineChart j).symm`
  (`mkNonzero_comp_affineLift`). It is holomorphic over `𝕜` (`contMDiff_affineLift_self`), smooth
  for the real structures (`contMDiff_affineLift`), and its real derivative sends `u` to
  `Fin.insertNth j 0 u` (`mfderiv_affineLift_apply`).
* For the same real structures, the map of projective spaces induced by an injective linear map
  and the inverse of each affine chart are smooth of every order
  (`contMDiff_map_restrictScalars`, `contMDiff_affineChart_symm_restrictScalars`), by
  `ContMDiff.restrictScalars'` applied to `contMDiff_map` and `contMDiff_affineChart_symm`.
* `SymplecticGeometry.sphereHopf n` is the Hopf map `S²ⁿ⁺¹ → ℂPⁿ` from the unit sphere of
  `StdSpace (Fin (n + 1))`, sending `x` to the complex line through
  `(TauCeti.complexToRealEuclidean _)⁻¹ x`. It is `mkNonzero ℂ n` after the inclusion
  `sphereToPuncturedSpace n` of the sphere into `ℂⁿ⁺¹ ∖ 0`.
* `SymplecticGeometry.radialProjection n` is the projection `z ↦ ẑ / ‖ẑ‖` of `ℂⁿ⁺¹ ∖ 0` onto
  the sphere, the sphere component of Tau Ceti's polar coordinates
  `TauCeti.sphereProdRealDiffeomorph`. Since `sphereHopf n ∘ radialProjection n = mkNonzero ℂ n`
  (`sphereHopf_comp_radialProjection`), the Hopf map is surjective (`surjective_sphereHopf`) and
  a submersion (`isSubmersion_sphereHopf`, by Tau Ceti's `Manifold.IsSubmersion.of_comp`). Read
  in `StdSpace (Fin (n + 1))`, the derivative of
  the radial projection at `z` sends `v` to `v̂ / ‖ẑ‖ - (⟪ẑ, v̂⟫ / ‖ẑ‖ ^ 3) ẑ`
  (`mvfderiv_radialProjection`).
* Two points of the sphere have the same image exactly when they lie on one orbit of the circle
  action of the rotations `stdRotation _ t`, `x ↦ cos t • x + sin t • J₀ x`
  (`sphereHopf_eq_sphereHopf_iff`).
* Identifying the unit sphere of `StdSpace (Fin (n + 1))` with that of
  `EuclideanSpace ℂ (Fin (n + 1))` by the inverse of the isometry
  `TauCeti.complexToRealEuclideanIsometry`, the Hopf map is Tau Ceti's Hopf projection
  `TauCeti.ComplexProjectiveSpace.mk n` followed by the diffeomorphism
  `TauCeti.ComplexProjectiveSpace.diffeomorphProjectivization n`
  (`sphereHopf_eq_diffeomorphProjectivization_mk`).

Mathlib's charts on the sphere need its dimension in the form
`finrank ℝ (StdSpace (Fin (n + 1))) = 2 * n + 1 + 1`, which the scoped instance
`SymplecticGeometry.fact_finrank_stdSpace_fin_succ` gives.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 0,
  §1.
-/

public section

open Set Function Module TopologicalSpace Manifold
open scoped Manifold ContDiff LinearAlgebra.Projectivization Topology InnerProductSpace

namespace TauCeti.puncturedSpace

variable {G V : Type*} [Group G] [AddMonoid V] [TopologicalSpace V] [T1Space V]
  [DistribMulAction G V]

/-- A group acting on `V` by additive maps acts on the punctured space `V ∖ {0}`, since
`g • v ≠ 0` when `v ≠ 0`. -/
instance instMulAction : MulAction G (puncturedSpace V) where
  smul g v := ⟨g • (v : V), mem_puncturedSpace.2 ((smul_ne_zero_iff_ne g).2
    (mem_puncturedSpace.1 v.property))⟩
  one_smul v := Subtype.ext (one_smul G (v : V))
  mul_smul g h v := Subtype.ext (mul_smul g h (v : V))

/-- The action on the punctured space is the restriction of the action on `V`. -/
@[simp, norm_cast]
theorem coe_smul (g : G) (v : puncturedSpace V) :
    ((g • v : puncturedSpace V) : V) = g • (v : V) :=
  (rfl)

end TauCeti.puncturedSpace

namespace Projectivization

section MkNonzero

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] (n : ℕ)

/-- The projection `v ↦ [v]` from the nonzero vectors of `𝕜ⁿ⁺¹` onto the projective space
`ℙ 𝕜 (Fin (n + 1) → 𝕜)`. -/
noncomputable def mkNonzero (v : TauCeti.puncturedSpace (Fin (n + 1) → 𝕜)) :
    ℙ 𝕜 (Fin (n + 1) → 𝕜) :=
  mk 𝕜 (v : Fin (n + 1) → 𝕜) (TauCeti.mem_puncturedSpace.1 v.property)

variable {𝕜 n}

/-- `mkNonzero 𝕜 n v` is the line `[v]` spanned by `v`. -/
@[simp]
theorem mkNonzero_apply (v : TauCeti.puncturedSpace (Fin (n + 1) → 𝕜)) :
    mkNonzero 𝕜 n v = mk 𝕜 (v : Fin (n + 1) → 𝕜) (TauCeti.mem_puncturedSpace.1 v.property) :=
  (rfl)

/-- `mkNonzero` is `Projectivization.mk'` on the same nonzero vector. -/
theorem mkNonzero_eq_mk' (v : TauCeti.puncturedSpace (Fin (n + 1) → 𝕜)) :
    mkNonzero 𝕜 n v = mk' 𝕜 ⟨(v : Fin (n + 1) → 𝕜), TauCeti.mem_puncturedSpace.1 v.property⟩ :=
  (rfl)

/-- The fibre of `mkNonzero` over the line `[v]` is the punctured line through `v`: the nonzero
vectors of the form `c • v`. -/
theorem preimage_mkNonzero_singleton_mk {v : Fin (n + 1) → 𝕜} (hv : v ≠ 0) :
    mkNonzero 𝕜 n ⁻¹' {mk 𝕜 v hv} =
      {z : TauCeti.puncturedSpace (Fin (n + 1) → 𝕜) | ∃ c : 𝕜, (z : Fin (n + 1) → 𝕜) = c • v} := by
  ext z
  simp only [mem_preimage, mem_singleton_iff, mkNonzero_apply, mk_eq_mk_iff', mem_ofPred_eq]
  exact exists_congr fun _ ↦ eq_comm

/-- `mkNonzero` is equivariant for a group acting `𝕜`-linearly on `𝕜ⁿ⁺¹`: the group acts on the
punctured space by restriction and on `ℙ 𝕜 (Fin (n + 1) → 𝕜)` by `g • [v] = [g • v]`. -/
theorem mkNonzero_smul {G : Type*} [Group G] [DistribMulAction G (Fin (n + 1) → 𝕜)]
    [SMulCommClass G 𝕜 (Fin (n + 1) → 𝕜)] (g : G)
    (v : TauCeti.puncturedSpace (Fin (n + 1) → 𝕜)) :
    mkNonzero 𝕜 n (g • v) = g • mkNonzero 𝕜 n v := by
  simp only [mkNonzero_apply, TauCeti.puncturedSpace.coe_smul, smul_mk]

variable (𝕜 n) in
/-- Every point of projective space is the line through a nonzero vector. -/
theorem surjective_mkNonzero : Surjective (mkNonzero 𝕜 n) := fun x ↦
  ⟨⟨x.rep, TauCeti.mem_puncturedSpace.2 x.rep_ne_zero⟩, mk_rep x⟩

/-- Over `𝕜` itself, `mkNonzero` is `C^r` for every `r`; over `ℂ` it is holomorphic. -/
theorem contMDiff_mkNonzero_self (r : ℕ∞ω) :
    ContMDiff 𝓘(𝕜, Fin (n + 1) → 𝕜) 𝓘(𝕜, Fin n → 𝕜) r (mkNonzero 𝕜 n) := fun _ ↦
  contMDiffAt_of_eventually_eq_mk (F := Subtype.val) contMDiff_subtypeVal.contMDiffAt
    (Filter.Eventually.of_forall fun w ↦ ⟨TauCeti.mem_puncturedSpace.1 w.property, rfl⟩)

/-- Over `𝕜` itself, the derivative of `mkNonzero` at `v` is Tau Ceti's derivative
`Projectivization.mfderivMk v` of the projection `w ↦ [w]`. -/
theorem mfderiv_mkNonzero_self_apply (v : TauCeti.puncturedSpace (Fin (n + 1) → 𝕜))
    (w : Fin (n + 1) → 𝕜) :
    mfderiv 𝓘(𝕜, Fin (n + 1) → 𝕜) 𝓘(𝕜, Fin n → 𝕜) (mkNonzero 𝕜 n) v w =
      mfderivMk (v : Fin (n + 1) → 𝕜) w := by
  have h := mfderiv_eq_mfderivMk_comp (f := mkNonzero 𝕜 n) (F := Subtype.val) (x := v)
    mdifferentiableAt_subtypeVal
    (Filter.Eventually.of_forall fun w ↦ ⟨_, mkNonzero_apply w⟩)
  -- `rw [ContinuousLinearMap.comp_apply]` fails here, as the tangent spaces in `h` are not
  -- syntactically the model spaces; the composite applied to `w` unfolds to the same term.
  exact (DFunLike.congr_fun h w).trans
    (congrArg (mfderivMk (v : Fin (n + 1) → 𝕜)) (TauCeti.Manifold.mfderiv_subtype_val_apply v w))

/-- Over `𝕜` itself, the derivative of `mkNonzero` at `v` is Tau Ceti's derivative
`Projectivization.mfderivMk v` of the projection `w ↦ [w]`, as a continuous linear map. -/
theorem mfderiv_mkNonzero_self (v : TauCeti.puncturedSpace (Fin (n + 1) → 𝕜)) :
    mfderiv 𝓘(𝕜, Fin (n + 1) → 𝕜) 𝓘(𝕜, Fin n → 𝕜) (mkNonzero 𝕜 n) v =
      mfderivMk (v : Fin (n + 1) → 𝕜) :=
  ContinuousLinearMap.ext (mfderiv_mkNonzero_self_apply v)

/-- The derivative of the projection `w ↦ [w]` is homogeneous of degree zero: for `v ≠ 0` and
`c ≠ 0`, its derivative at `c • v` sends `c • w` to the image of `w` under its derivative at `v`.
This is the chain rule for `[c • w] = [w]`. -/
theorem mfderivMk_smul_smul {v : Fin (n + 1) → 𝕜} (hv : v ≠ 0) {c : 𝕜} (hc : c ≠ 0)
    (w : Fin (n + 1) → 𝕜) :
    mfderivMk (c • v) (c • w) = mfderivMk v w := by
  set z : TauCeti.puncturedSpace (Fin (n + 1) → 𝕜) := ⟨v, TauCeti.mem_puncturedSpace.2 hv⟩
  let L : (Fin (n + 1) → 𝕜) →L[𝕜] Fin (n + 1) → 𝕜 := c • ContinuousLinearMap.id 𝕜 _
  -- `mkNonzero` sends `x` to `[L x] = [c • x]`, so the chain rule computes its derivative at `v`
  -- through the derivative of the projection at `c • v`.
  have h := mfderiv_eq_mfderivMk_comp (f := mkNonzero 𝕜 n) (x := z)
    ((L.contMDiff.comp contMDiff_subtypeVal).mdifferentiableAt one_ne_zero)
    (Filter.Eventually.of_forall fun x ↦ ⟨by
      simpa [L, hc] using TauCeti.mem_puncturedSpace.1 x.property, by
      rw [mkNonzero_apply, mk_eq_mk_iff']
      exact ⟨c⁻¹, by simp [L, smul_smul, hc]⟩⟩)
  have hd : mfderiv 𝓘(𝕜, Fin (n + 1) → 𝕜) 𝓘(𝕜, Fin (n + 1) → 𝕜)
      (L ∘ Subtype.val : TauCeti.puncturedSpace (Fin (n + 1) → 𝕜) → _) z w = c • w :=
    (mfderiv_modelSpace_comp_subtypeVal_apply (f := L) (x := z) w).trans (by
      rw [L.fderiv]
      -- The two sides are `c • w` for the scalar actions on the tangent space and on
      -- `Fin (n + 1) → 𝕜`, which agree by definition but not syntactically.
      exact rfl)
  -- `rw [ContinuousLinearMap.comp_apply]` fails here, as the tangent spaces in `h` are not
  -- syntactically the model spaces; the composite applied to `w` unfolds to the same term.
  have h' : mfderivMk v w = mfderivMk (L v) (mfderiv 𝓘(𝕜, Fin (n + 1) → 𝕜)
      𝓘(𝕜, Fin (n + 1) → 𝕜) (L ∘ Subtype.val : TauCeti.puncturedSpace (Fin (n + 1) → 𝕜) → _)
        z w) := by
    rw [← mfderiv_mkNonzero_self_apply z w]
    exact DFunLike.congr_fun h w
  rw [h', hd]
  simp [L]

variable [NormedAlgebra ℝ 𝕜]

variable (𝕜 n) in
/-- The projection from the nonzero vectors onto projective space is `C^r` for the underlying real
manifold structures, for every `r`. -/
theorem contMDiff_mkNonzero (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, Fin (n + 1) → 𝕜) 𝓘(ℝ, Fin n → 𝕜) r (mkNonzero 𝕜 n) :=
  (contMDiff_mkNonzero_self (𝕜 := 𝕜) (n := n) r).restrictScalars' ℝ

/-- The map of projective spaces induced by an injective linear map is `C^r` for the underlying
real manifold structures. -/
theorem contMDiff_map_restrictScalars {m : ℕ} (f : (Fin (m + 1) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜)
    (hf : Injective f) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, Fin m → 𝕜) 𝓘(ℝ, Fin n → 𝕜) r (map f hf) :=
  (contMDiff_map f hf r).restrictScalars' ℝ

/-- The inverse of an affine chart is `C^r` for the underlying real manifold structures. -/
theorem contMDiff_affineChart_symm_restrictScalars (j : Fin (n + 1)) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, Fin n → 𝕜) 𝓘(ℝ, Fin n → 𝕜) r (affineChart (K := 𝕜) j).symm :=
  (contMDiff_affineChart_symm (𝕜 := 𝕜) j r).restrictScalars' ℝ

/-- For the underlying real manifold structures, the derivative of `mkNonzero` at `v` is still
Tau Ceti's derivative `Projectivization.mfderivMk v` of the projection `w ↦ [w]`. -/
theorem mfderiv_mkNonzero_apply (v : TauCeti.puncturedSpace (Fin (n + 1) → 𝕜))
    (w : Fin (n + 1) → 𝕜) :
    mfderiv 𝓘(ℝ, Fin (n + 1) → 𝕜) 𝓘(ℝ, Fin n → 𝕜) (mkNonzero 𝕜 n) v w =
      mfderivMk (v : Fin (n + 1) → 𝕜) w :=
  (((contMDiff_mkNonzero_self 1 v).mdifferentiableAt
    one_ne_zero).mfderiv_modelWithCornersSelf_restrictScalars_apply ℝ w).trans
    (mfderiv_mkNonzero_self_apply v w)

/-- For the underlying real manifold structures, the derivative of `mkNonzero` at `v` is Tau
Ceti's derivative `Projectivization.mfderivMk v` of the projection `w ↦ [w]`, with its scalars
restricted to `ℝ`. -/
theorem mfderiv_mkNonzero (v : TauCeti.puncturedSpace (Fin (n + 1) → 𝕜)) :
    mfderiv 𝓘(ℝ, Fin (n + 1) → 𝕜) 𝓘(ℝ, Fin n → 𝕜) (mkNonzero 𝕜 n) v =
      (mfderivMk (v : Fin (n + 1) → 𝕜)).restrictScalars ℝ :=
  ContinuousLinearMap.ext (mfderiv_mkNonzero_apply v)

/-- Every nonzero vector `v` is a regular point of the projection `mkNonzero` for the underlying
real manifold structures: its real derivative at `v` is surjective. -/
theorem isRegularPoint_mkNonzero (v : TauCeti.puncturedSpace (Fin (n + 1) → 𝕜)) :
    TauCeti.IsRegularPoint 𝓘(ℝ, Fin (n + 1) → 𝕜) 𝓘(ℝ, Fin n → 𝕜) (mkNonzero 𝕜 n) v := by
  rw [TauCeti.isRegularPoint_iff]
  intro w
  obtain ⟨u, hu⟩ := surjective_mfderivMk (TauCeti.mem_puncturedSpace.1 v.property) w
  exact ⟨u, (mfderiv_mkNonzero_apply v u).trans hu⟩

variable (𝕜 n) in
/-- The projection from the nonzero vectors onto projective space is a smooth submersion of the
underlying real manifolds. -/
theorem isSubmersion_mkNonzero [FiniteDimensional ℝ 𝕜] :
    IsSubmersion 𝓘(ℝ, Fin (n + 1) → 𝕜) 𝓘(ℝ, Fin n → 𝕜) ∞ (mkNonzero 𝕜 n) :=
  ((contMDiff_mkNonzero 𝕜 n ∞).isSubmersionOfComplement_of_surjective_mfderiv
    (by exact_mod_cast le_top)
    fun v ↦ TauCeti.isRegularPoint_iff.1 (isRegularPoint_mkNonzero v)).isSubmersion

/-- The kernel of the real derivative of `mkNonzero` at `v` is the line `𝕜 ∙ v`, viewed as a real
subspace. -/
theorem ker_mfderiv_mkNonzero (v : TauCeti.puncturedSpace (Fin (n + 1) → 𝕜)) :
    LinearMap.ker (mfderiv 𝓘(ℝ, Fin (n + 1) → 𝕜) 𝓘(ℝ, Fin n → 𝕜) (mkNonzero 𝕜 n) v).toLinearMap =
      (𝕜 ∙ (v : Fin (n + 1) → 𝕜)).restrictScalars ℝ := by
  rw [mfderiv_mkNonzero, ← ker_mfderivMk (TauCeti.mem_puncturedSpace.1 v.property),
    ContinuousLinearMap.coe_restrictScalars]
  -- `rw [LinearMap.ker_restrictScalars]` fails, as the tangent spaces at `v` and `[v]` are not
  -- syntactically the model spaces; the lemma still closes the goal up to that identification.
  exact LinearMap.ker_restrictScalars ℝ
    (mfderivMk (v : Fin (n + 1) → 𝕜) : (Fin (n + 1) → 𝕜) →ₗ[𝕜] Fin n → 𝕜)

/-- The real derivative of `mkNonzero` at `v` vanishes on the line `𝕜 ∙ v`, along which
`mkNonzero` is constant. -/
theorem mfderiv_mkNonzero_smul_self (v : TauCeti.puncturedSpace (Fin (n + 1) → 𝕜)) (c : 𝕜) :
    mfderiv 𝓘(ℝ, Fin (n + 1) → 𝕜) 𝓘(ℝ, Fin n → 𝕜) (mkNonzero 𝕜 n) v
      (c • (v : Fin (n + 1) → 𝕜)) = 0 := by
  have h : c • (v : Fin (n + 1) → 𝕜) ∈ (𝕜 ∙ (v : Fin (n + 1) → 𝕜)).restrictScalars ℝ :=
    Submodule.mem_span_singleton.2 ⟨c, rfl⟩
  rw [← ker_mfderiv_mkNonzero] at h
  exact LinearMap.mem_ker.1 h

end MkNonzero

section AffineLift

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {n : ℕ}

/-- The section `w ↦ Fin.insertNth j 1 w` of the projection `mkNonzero` over the affine chart of
`j`: it lifts the inverse `(affineChart j).symm` of the chart to the nonzero vectors of `𝕜ⁿ⁺¹`
(`mkNonzero_comp_affineLift`). -/
noncomputable def affineLift (j : Fin (n + 1)) (w : Fin n → 𝕜) :
    TauCeti.puncturedSpace (Fin (n + 1) → 𝕜) :=
  ⟨Fin.insertNth (α := fun _ ↦ 𝕜) j 1 w,
    TauCeti.mem_puncturedSpace.2 (Fin.insertNth_one_ne_zero j w)⟩

variable {𝕜}

/-- `affineLift 𝕜 j w` is the vector `Fin.insertNth j 1 w`. -/
@[simp]
theorem coe_affineLift (j : Fin (n + 1)) (w : Fin n → 𝕜) :
    (affineLift 𝕜 j w : Fin (n + 1) → 𝕜) = Fin.insertNth (α := fun _ ↦ 𝕜) j 1 w :=
  (rfl)

variable (𝕜) in
/-- The lift is a section of `mkNonzero` over the affine chart of `j`: its projection is the
inverse of that chart. -/
theorem mkNonzero_comp_affineLift (j : Fin (n + 1)) :
    mkNonzero 𝕜 n ∘ affineLift 𝕜 j = (affineChart (K := 𝕜) j).symm :=
  funext fun w ↦ by
    simp only [comp_apply, mkNonzero_apply, affineChart_symm_apply, coe_affineLift]

variable (𝕜) in
/-- Over `𝕜` itself, the lift is `C^r` for every `r`; over `ℂ` it is holomorphic. -/
theorem contMDiff_affineLift_self (j : Fin (n + 1)) (r : ℕ∞ω) :
    ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin (n + 1) → 𝕜) r (affineLift 𝕜 j) :=
  (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1
    (ContDiff.finInsertNth (F := fun _ ↦ 𝕜) j contDiff_const contDiff_id).contMDiff

variable [NormedAlgebra ℝ 𝕜]

variable (𝕜) in
/-- The lift is `C^r` for the underlying real manifold structures, for every `r`. -/
theorem contMDiff_affineLift (j : Fin (n + 1)) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, Fin n → 𝕜) 𝓘(ℝ, Fin (n + 1) → 𝕜) r (affineLift 𝕜 j) :=
  (contMDiff_affineLift_self 𝕜 j r).restrictScalars' ℝ

/-- The real derivative of the lift at any point sends `u` to `Fin.insertNth j 0 u`. -/
theorem mfderiv_affineLift_apply (j : Fin (n + 1)) (w : Fin n → 𝕜)
    (u : TangentSpace 𝓘(ℝ, Fin n → 𝕜) w) :
    mfderiv 𝓘(ℝ, Fin n → 𝕜) 𝓘(ℝ, Fin (n + 1) → 𝕜) (affineLift 𝕜 j) w u =
      Fin.insertNth (α := fun _ ↦ 𝕜) j 0 (u : Fin n → 𝕜) := by
  -- The linear map `u ↦ Fin.insertNth j 0 u`; the lift is its translate by `Pi.single j 1`.
  let L : (Fin n → 𝕜) →L[ℝ] Fin (n + 1) → 𝕜 :=
    ContinuousLinearMap.pi (Fin.insertNth j 0 fun k ↦ ContinuousLinearMap.proj k)
  have hL (u : Fin n → 𝕜) : L u = Fin.insertNth (α := fun _ ↦ 𝕜) j 0 u := by
    funext k
    induction k using j.succAboveCases <;> simp [L]
  have hlift : Subtype.val ∘ affineLift 𝕜 j = fun w ↦ Pi.single j 1 + L w := by
    funext w k
    induction k using j.succAboveCases <;> simp [hL]
  rw [← TauCeti.Manifold.mfderiv_subtype_val_comp_apply, mfderiv_eq_fderiv, hlift,
    fderiv_const_add, ContinuousLinearMap.fderiv]
  exact hL u

end AffineLift

end Projectivization

namespace SymplecticGeometry

open TauCeti Metric Projectivization

variable (n : ℕ)

/-- The unit sphere of `StdSpace (Fin (n + 1))`, read in `ℂⁿ⁺¹ ∖ 0` through the inverse of
`complexToRealEuclidean`. -/
noncomputable def sphereToPuncturedSpace (x : sphere (0 : StdSpace (Fin (n + 1))) 1) :
    puncturedSpace (Fin (n + 1) → ℂ) :=
  ⟨(complexToRealEuclidean (Fin (n + 1))).symm x, mem_puncturedSpace.2 <| by
    simpa using ne_zero_of_mem_unit_sphere x⟩

variable {n} in
/-- The point `sphereToPuncturedSpace n x` of `ℂⁿ⁺¹ ∖ 0` is `(complexToRealEuclidean _)⁻¹ x`. -/
@[simp]
theorem coe_sphereToPuncturedSpace (x : sphere (0 : StdSpace (Fin (n + 1))) 1) :
    (sphereToPuncturedSpace n x : Fin (n + 1) → ℂ) =
      (complexToRealEuclidean (Fin (n + 1))).symm x :=
  (rfl)

/-- The inclusion of the unit sphere into `ℂⁿ⁺¹ ∖ 0` is `C^r` for every `r`. -/
theorem contMDiff_sphereToPuncturedSpace (r : ℕ∞ω) :
    ContMDiff (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin (n + 1) → ℂ) r (sphereToPuncturedSpace n) := by
  rw [← TauCeti.ContMDiff.subtypeVal_comp_iff,
    show Subtype.val ∘ sphereToPuncturedSpace n =
      (complexToRealEuclidean (Fin (n + 1))).symm ∘ Subtype.val from
      funext coe_sphereToPuncturedSpace]
  exact ((complexToRealEuclidean (Fin (n + 1))).symm :
    StdSpace (Fin (n + 1)) →L[ℝ] (Fin (n + 1) → ℂ)).contMDiff.comp contMDiff_coe_sphere

/-- The Hopf map `S²ⁿ⁺¹ → ℂPⁿ` from the unit sphere of `StdSpace (Fin (n + 1))`, sending `x` to
the complex line through `(complexToRealEuclidean _)⁻¹ x`. -/
noncomputable def sphereHopf (x : sphere (0 : StdSpace (Fin (n + 1))) 1) :
    ℙ ℂ (Fin (n + 1) → ℂ) :=
  mkNonzero ℂ n (sphereToPuncturedSpace n x)

variable {n} in
/-- The Hopf map sends `x` to the line through `(complexToRealEuclidean _)⁻¹ x`. -/
@[simp]
theorem sphereHopf_apply (x : sphere (0 : StdSpace (Fin (n + 1))) 1) :
    sphereHopf n x = Projectivization.mk ℂ ((complexToRealEuclidean (Fin (n + 1))).symm x)
      (by simpa using ne_zero_of_mem_unit_sphere x) :=
  (rfl)

/-- The Hopf map is the projection `mkNonzero ℂ n` after the inclusion of the sphere. -/
theorem mkNonzero_comp_sphereToPuncturedSpace :
    mkNonzero ℂ n ∘ sphereToPuncturedSpace n = sphereHopf n :=
  (rfl)

/-- The Hopf map is `C^r` for every `r`. -/
theorem contMDiff_sphereHopf (r : ℕ∞ω) :
    ContMDiff (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) r (sphereHopf n) :=
  (contMDiff_mkNonzero ℂ n r).comp (contMDiff_sphereToPuncturedSpace n r)

/-- The radial projection `z ↦ ẑ / ‖ẑ‖` of `ℂⁿ⁺¹ ∖ 0` onto the unit sphere of
`StdSpace (Fin (n + 1))`, with `ẑ = complexToRealEuclidean _ z`: the sphere component of Tau Ceti's
polar coordinates `TauCeti.sphereProdRealDiffeomorph`. -/
noncomputable def radialProjection (z : puncturedSpace (Fin (n + 1) → ℂ)) :
    sphere (0 : StdSpace (Fin (n + 1))) 1 :=
  ((sphereProdRealDiffeomorph (V := StdSpace (Fin (n + 1))) (n := 2 * n + 1)).symm
    ⟨complexToRealEuclidean (Fin (n + 1)) z, mem_puncturedSpace.2 <| by
      simpa using mem_puncturedSpace.1 z.property⟩).1

variable {n} in
/-- The radial projection of `z` is `ẑ / ‖ẑ‖`, with `ẑ = complexToRealEuclidean _ z`. -/
@[simp]
theorem radialProjection_apply (z : puncturedSpace (Fin (n + 1) → ℂ)) :
    (radialProjection n z : StdSpace (Fin (n + 1))) =
      ‖complexToRealEuclidean (Fin (n + 1)) z‖⁻¹ • complexToRealEuclidean (Fin (n + 1)) z :=
  coe_sphereProdRealDiffeomorph_symm_apply_fst _

/-- The radial projection onto the unit sphere is `C^r` for every `r`. -/
theorem contMDiff_radialProjection (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, Fin (n + 1) → ℂ) (𝓡 (2 * n + 1)) r (radialProjection n) := by
  -- `contMDiff_normalize_sphere` is stated on the open set `{0}ᶜ` itself rather than on
  -- `puncturedSpace`; matching the two by unification times out, so `g` lands in `{0}ᶜ`.
  let g : puncturedSpace (Fin (n + 1) → ℂ) →
      (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens (StdSpace (Fin (n + 1)))) := fun z ↦
    ⟨complexToRealEuclidean (Fin (n + 1)) z, by simpa using mem_puncturedSpace.1 z.property⟩
  have hg : ContMDiff 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, StdSpace (Fin (n + 1))) r g :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1
      (((complexToRealEuclidean (Fin (n + 1))) :
        (Fin (n + 1) → ℂ) →L[ℝ] StdSpace (Fin (n + 1))).contMDiff.comp contMDiff_subtypeVal)
  have hr : radialProjection n = (fun x : (⟨{0}ᶜ, isOpen_compl_singleton⟩ :
      Opens (StdSpace (Fin (n + 1)))) ↦ (⟨NormedSpace.normalize (x : StdSpace (Fin (n + 1))),
        mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize_eq_one_iff.2 x.property)⟩ :
          sphere (0 : StdSpace (Fin (n + 1))) 1)) ∘ g :=
    funext fun z ↦ Subtype.ext (by simp [g, NormedSpace.normalize])
  rw [hr]
  exact contMDiff_normalize_sphere.comp hg

variable {n} in
/-- The derivative of the radial projection at `z`, read in `StdSpace (Fin (n + 1))` through the
inclusion of the sphere, sends `v` to `v̂ / ‖ẑ‖ - (⟪ẑ, v̂⟫ / ‖ẑ‖ ^ 3) ẑ`, where `ẑ` and `v̂` are the
images of `z` and `v` under `complexToRealEuclidean`. -/
theorem mvfderiv_radialProjection (z : puncturedSpace (Fin (n + 1) → ℂ))
    (v : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) z) :
    mvfderiv (𝓡 (2 * n + 1))
        ((↑) : sphere (0 : StdSpace (Fin (n + 1))) 1 → StdSpace (Fin (n + 1)))
        (radialProjection n z)
        (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) (𝓡 (2 * n + 1)) (radialProjection n) z v) =
      ‖complexToRealEuclidean (Fin (n + 1)) z‖⁻¹ • complexToRealEuclidean (Fin (n + 1)) v -
        (⟪complexToRealEuclidean (Fin (n + 1)) z, complexToRealEuclidean (Fin (n + 1)) v⟫_ℝ /
          ‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 3) •
          complexToRealEuclidean (Fin (n + 1)) z := by
  have hz : complexToRealEuclidean (Fin (n + 1)) z ≠ 0 := by
    simpa using mem_puncturedSpace.1 z.property
  have hd := (TauCeti.hasFDerivAt_radialRescale hz
    (hasDerivAt_inv (norm_ne_zero_iff.2 hz))).comp (z : Fin (n + 1) → ℂ)
    (complexToRealEuclidean (Fin (n + 1))).hasFDerivAt
  have hfun : ((↑) : sphere (0 : StdSpace (Fin (n + 1))) 1 → StdSpace (Fin (n + 1))) ∘
      radialProjection n =
        (TauCeti.radialRescale (·⁻¹) ∘ complexToRealEuclidean (Fin (n + 1))) ∘ Subtype.val :=
    funext fun y ↦ (radialProjection_apply y).trans (TauCeti.radialRescale_apply _ _).symm
  rw [← mvfderiv_comp_apply _ ((contMDiff_coe_sphere _).mdifferentiableAt one_ne_zero)
      ((contMDiff_radialProjection n 1 z).mdifferentiableAt one_ne_zero), hfun,
    TauCeti.Manifold.mvfderiv_modelSpace_comp_subtype_val_apply, hd.fderiv]
  -- Read `v` as a vector of `Fin (n + 1) → ℂ`, so that the evaluation lemmas of continuous linear
  -- maps apply to it.
  revert v
  intro (w : Fin (n + 1) → ℂ)
  simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, ContinuousLinearEquiv.coe_coe,
    smul_eq_mul, sub_eq_add_neg, ← neg_smul]
  congr 2
  field_simp

/-- The radial projection is a left inverse of the inclusion of the sphere. -/
@[simp]
theorem radialProjection_sphereToPuncturedSpace (x : sphere (0 : StdSpace (Fin (n + 1))) 1) :
    radialProjection n (sphereToPuncturedSpace n x) = x := by
  ext1
  simp [norm_eq_of_mem_sphere x]

/-- The projection of `ℂⁿ⁺¹ ∖ 0` onto `ℂPⁿ` is the Hopf map after the radial projection. -/
theorem sphereHopf_comp_radialProjection :
    sphereHopf n ∘ radialProjection n = mkNonzero ℂ n := by
  funext z
  rw [comp_apply, sphereHopf_apply, mkNonzero_apply, mk_eq_mk_iff']
  refine ⟨((‖complexToRealEuclidean (Fin (n + 1)) z‖⁻¹ : ℝ) : ℂ), ?_⟩
  rw [radialProjection_apply, map_smul, ContinuousLinearEquiv.symm_apply_apply, Complex.coe_smul]

/-- The Hopf map is surjective. -/
theorem surjective_sphereHopf : Surjective (sphereHopf n) :=
  Surjective.of_comp (g := radialProjection n)
    (by rw [sphereHopf_comp_radialProjection]; exact surjective_mkNonzero ℂ n)

/-- The Hopf map is a smooth submersion. -/
theorem isSubmersion_sphereHopf :
    IsSubmersion (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) ∞ (sphereHopf n) := by
  refine IsSubmersion.of_comp (π := radialProjection n) ?_ (contMDiff_radialProjection n ∞)
    (LeftInverse.surjective (radialProjection_sphereToPuncturedSpace n))
    (contMDiff_sphereHopf n ∞) (by exact_mod_cast le_top)
  rw [sphereHopf_comp_radialProjection]
  exact isSubmersion_mkNonzero ℂ n

/-- Two points of the unit sphere have the same image under the Hopf map exactly when they lie on
the same orbit of the circle action of the rotations `stdRotation _ t`,
`x ↦ cos t • x + sin t • J₀ x`. -/
theorem sphereHopf_eq_sphereHopf_iff (x y : sphere (0 : StdSpace (Fin (n + 1))) 1) :
    sphereHopf n x = sphereHopf n y ↔
      ∃ t : ℝ, (y : StdSpace (Fin (n + 1))) = stdRotation (Fin (n + 1)) t x := by
  set e := complexToRealEuclidean (Fin (n + 1))
  rw [sphereHopf_apply, sphereHopf_apply, eq_comm, mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩
    have hy : (y : StdSpace (Fin (n + 1))) = e (a • e.symm x) := by
      rw [ha, ContinuousLinearEquiv.apply_symm_apply]
    have ha1 : ‖a‖ = 1 := by
      have h := norm_complexToRealEuclidean_smul a (e.symm x)
      rwa [← hy, ContinuousLinearEquiv.apply_symm_apply, norm_eq_of_mem_sphere,
        norm_eq_of_mem_sphere, mul_one, eq_comm] at h
    obtain ⟨t, rfl⟩ := (Complex.norm_eq_one_iff a).1 ha1
    exact ⟨t, by
      rw [hy, complexToRealEuclidean_exp_mul_I_smul, ContinuousLinearEquiv.apply_symm_apply]⟩
  · rintro ⟨t, ht⟩
    exact ⟨Complex.exp (t * Complex.I), e.injective (by
      rw [complexToRealEuclidean_exp_mul_I_smul, ContinuousLinearEquiv.apply_symm_apply,
        ContinuousLinearEquiv.apply_symm_apply,
        ht])⟩


/-- The Hopf map is Tau Ceti's Hopf projection `TauCeti.ComplexProjectiveSpace.mk n`, after the
identification of the unit sphere of `StdSpace (Fin (n + 1))` with that of
`EuclideanSpace ℂ (Fin (n + 1))` by the inverse of the isometry `complexToRealEuclideanIsometry`,
followed by the diffeomorphism `TauCeti.ComplexProjectiveSpace.diffeomorphProjectivization n` onto
`ℙ ℂ (Fin (n + 1) → ℂ)`. -/
theorem sphereHopf_eq_diffeomorphProjectivization_mk (x : sphere (0 : StdSpace (Fin (n + 1))) 1) :
    sphereHopf n x = ComplexProjectiveSpace.diffeomorphProjectivization n
      (ComplexProjectiveSpace.mk n
        ((complexToRealEuclideanIsometry (Fin (n + 1))).symm.unitSphereEquiv x)) := by
  rw [ComplexProjectiveSpace.diffeomorphProjectivization_mk, sphereHopf_apply]
  simp only [LinearIsometryEquiv.coe_unitSphereEquiv_apply,
    complexToRealEuclideanIsometry_symm_apply, WithLp.ofLp_toLp]
end SymplecticGeometry
