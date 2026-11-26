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
public import TauCeti.Geometry.Manifold.Submersion.Split
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import TauCeti.Analysis.Calculus.ContDiff.FinInsertNth
import TauCeti.Analysis.InnerProductSpace.RadialRescale
import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars
import SymplecticGeometry.LinearAlgebra.FiniteDimensional.RestrictScalars
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.Instances.Sphere
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Opens
import TauCeti.Geometry.Manifold.MFDeriv.Slice
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import SymplecticGeometry.Analysis.Complex.Euclidean.Space

/-!
# The Hopf maps

This file makes the two quotient maps onto projective space into smooth submersions of the
underlying real manifolds, using Tau Ceti's affine charts of `ℙ 𝕜 (Fin (n + 1) → 𝕜)`.

* `Projectivization.mkNonzero 𝕜 n` is the projection `v ↦ [v]` from the punctured space
  `TauCeti.puncturedSpace (Fin (n + 1) → 𝕜)` onto `ℙ 𝕜 (Fin (n + 1) → 𝕜)`, for a nontrivially
  normed field `𝕜` that is a finite-dimensional normed `ℝ`-algebra, such as `ℝ` or `ℂ`. It is
  smooth of every order (`contMDiff_mkNonzero`), holomorphic over `𝕜` itself
  (`contMDiff_mkNonzero_self`), and a submersion (`isSubmersion_mkNonzero`), regular at every
  point (`isRegularPoint_mkNonzero`): over the affine open of a coordinate `j` with `v j ≠ 0` it
  has the local section `z ↦ v j • Fin.insertNth j 1 z` in the chart. Its fibre over `[v]` is the
  punctured line of the nonzero multiples of `v` (`preimage_mkNonzero_singleton_mk`). For `𝕜 = ℂ`
  and `n = 1` it is the pencil `[z₀ : z₁]` on `ℂ² ∖ 0`. The kernel of its derivative at `v` is the
  line `𝕜 ∙ v` (`ker_mfderiv_mkNonzero`),
  since `mkNonzero` is constant along that line and the dimensions agree.
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
  (`sphereHopf_eq_sphereHopf_iff`), and the kernel of the derivative of the Hopf map at `x`, read
  in `StdSpace (Fin (n + 1))`, is the tangent line `ℝ ∙ J₀ x` of that orbit
  (`ker_mfderiv_sphereHopf`).

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

variable (𝕜 n) in
/-- Every point of projective space is the line through a nonzero vector. -/
theorem surjective_mkNonzero : Surjective (mkNonzero 𝕜 n) := fun x ↦
  ⟨⟨x.rep, TauCeti.mem_puncturedSpace.2 x.rep_ne_zero⟩, mk_rep x⟩

/-- Over `𝕜` itself, `mkNonzero` is `C^r` for every `r`; over `ℂ` it is holomorphic. -/
theorem contMDiff_mkNonzero_self (r : ℕ∞ω) :
    ContMDiff 𝓘(𝕜, Fin (n + 1) → 𝕜) 𝓘(𝕜, Fin n → 𝕜) r (mkNonzero 𝕜 n) := fun _ ↦
  contMDiffAt_of_eventually_eq_mk (F := Subtype.val) contMDiff_subtypeVal.contMDiffAt
    (Filter.Eventually.of_forall fun w ↦ ⟨TauCeti.mem_puncturedSpace.1 w.property, rfl⟩)

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

/-- Every nonzero vector `v` is a regular point of the projection `mkNonzero` for the underlying
real manifold structures: its real derivative at `v` is surjective. Near `v` the projection has
the local section `y ↦ v j • Fin.insertNth j 1 (affineChart j y)` through `v`, for a coordinate
`j` with `v j ≠ 0`. -/
theorem isRegularPoint_mkNonzero (v : TauCeti.puncturedSpace (Fin (n + 1) → 𝕜)) :
    TauCeti.IsRegularPoint 𝓘(ℝ, Fin (n + 1) → 𝕜) 𝓘(ℝ, Fin n → 𝕜) (mkNonzero 𝕜 n) v := by
  rw [TauCeti.isRegularPoint_iff]
  have hv := TauCeti.mem_puncturedSpace.1 v.property
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
  let s : ℙ 𝕜 (Fin (n + 1) → 𝕜) → TauCeti.puncturedSpace (Fin (n + 1) → 𝕜) := fun y ↦
    ⟨(v : Fin (n + 1) → 𝕜) j • Fin.insertNth (α := fun _ ↦ 𝕜) j 1 (affineChart j y),
      TauCeti.mem_puncturedSpace.2 (smul_ne_zero hj (Fin.insertNth_one_ne_zero j _))⟩
  have hx : mkNonzero 𝕜 n v ∈ affineOpen j := by simpa using hj
  have hsx : s (mkNonzero 𝕜 n v) = v := by
    refine Subtype.ext ?_
    simp only [s, mkNonzero_apply, affineChart_mk, Fin.insertNth_one_div_eq_inv_smul j _ hj,
      smul_smul, mul_inv_cancel₀ hj, one_smul]
  have hs : MDifferentiableAt 𝓘(ℝ, Fin n → 𝕜) 𝓘(ℝ, Fin (n + 1) → 𝕜) s (mkNonzero 𝕜 n v) := by
    have h := (((contDiff_const_smul ((v : Fin (n + 1) → 𝕜) j)).contMDiff).comp_contMDiffOn
      (contMDiffOn_insertNth_affineChart j 1)).contMDiffAt ((isOpen_affineOpen j).mem_nhds hx)
    exact ((TauCeti.ContMDiffAt.subtypeVal_comp_iff (n := 1) _ s _).1
      (h.restrictScalars' ℝ)).mdifferentiableAt
        one_ne_zero
  have hid : mkNonzero 𝕜 n ∘ s =ᶠ[𝓝 (mkNonzero 𝕜 n v)] id := by
    filter_upwards [(isOpen_affineOpen j).mem_nhds hx] with y hy
    have hy' : y ∈ (affineChart j).source := by rwa [affineChart_source]
    rw [comp_apply, mkNonzero_apply, id_eq]
    conv_rhs => rw [← (affineChart j).left_inv hy',
      affineChart_symm_apply]
    exact (mk_eq_mk_iff' 𝕜 _ _ _ _).2 ⟨(v : Fin (n + 1) → 𝕜) j, rfl⟩
  have hsurj : Surjective (mfderiv 𝓘(ℝ, Fin (n + 1) → 𝕜) 𝓘(ℝ, Fin n → 𝕜) (mkNonzero 𝕜 n)
      (s (mkNonzero 𝕜 n v))) := fun w ↦
    ⟨mfderiv 𝓘(ℝ, Fin n → 𝕜) 𝓘(ℝ, Fin (n + 1) → 𝕜) s (mkNonzero 𝕜 n v) w,
      (TauCeti.mfderiv_apply_mfderiv_of_eventuallyEq_comp hid
        ((contMDiff_mkNonzero 𝕜 n 1 _).mdifferentiableAt one_ne_zero) hs w).trans
        -- `w` is read in the tangent space at `mkNonzero 𝕜 n (s _)`, the same model space.
        (by rw [mfderiv_id]; rfl)⟩
  rwa [hsx] at hsurj

variable (𝕜 n) in
/-- The projection from the nonzero vectors onto projective space is a smooth submersion of the
underlying real manifolds. -/
theorem isSubmersion_mkNonzero [FiniteDimensional ℝ 𝕜] :
    IsSubmersion 𝓘(ℝ, Fin (n + 1) → 𝕜) 𝓘(ℝ, Fin n → 𝕜) ∞ (mkNonzero 𝕜 n) :=
  ((contMDiff_mkNonzero 𝕜 n ∞).isSubmersionOfComplement_of_surjective_mfderiv
    (by exact_mod_cast le_top)
    fun v ↦ TauCeti.isRegularPoint_iff.1 (isRegularPoint_mkNonzero v)).isSubmersion

/-- The real derivative of `mkNonzero` at `v` vanishes on the line `𝕜 ∙ v`, along which
`mkNonzero` is constant. -/
theorem mfderiv_mkNonzero_smul_self (v : TauCeti.puncturedSpace (Fin (n + 1) → 𝕜)) (c : 𝕜) :
    mfderiv 𝓘(ℝ, Fin (n + 1) → 𝕜) 𝓘(ℝ, Fin n → 𝕜) (mkNonzero 𝕜 n) v
      (c • (v : Fin (n + 1) → 𝕜)) = 0 := by
  have hv := TauCeti.mem_puncturedSpace.1 v.property
  let φ : TauCeti.puncturedSpace 𝕜 → TauCeti.puncturedSpace (Fin (n + 1) → 𝕜) := fun a ↦
    ⟨(a : 𝕜) • (v : Fin (n + 1) → 𝕜),
      TauCeti.mem_puncturedSpace.2 (smul_ne_zero (TauCeti.mem_puncturedSpace.1 a.property) hv)⟩
  let one : TauCeti.puncturedSpace 𝕜 := ⟨1, TauCeti.mem_puncturedSpace.2 one_ne_zero⟩
  have hφ1 : φ one = v := Subtype.ext (one_smul _ _)
  have hconst : mkNonzero 𝕜 n ∘ φ = fun _ ↦ mkNonzero 𝕜 n v := by
    funext a
    exact (mk_eq_mk_iff' 𝕜 _ _ _ _).2 ⟨a, rfl⟩
  have hderiv : mfderiv 𝓘(ℝ, 𝕜) 𝓘(ℝ, Fin (n + 1) → 𝕜) φ one c = c • (v : Fin (n + 1) → 𝕜) := by
    -- `φ` is the restriction of `a ↦ a • v` to the punctured spaces.
    have h := TauCeti.Manifold.mfderiv_apply_of_subtype_val_comp_eq (I := 𝓘(ℝ, 𝕜))
      (I' := 𝓘(ℝ, Fin (n + 1) → 𝕜)) (A := fun a : 𝕜 ↦ a • (v : Fin (n + 1) → 𝕜))
      (f := φ) (x := one) rfl c
    rw [mfderiv_eq_fderiv] at h
    exact h.trans <| congrArg (fun L ↦ L c)
      ((hasFDerivAt_id (𝕜 := ℝ) (1 : 𝕜)).smul_const (v : Fin (n + 1) → 𝕜)).fderiv
  rw [← hderiv, ← hφ1]
  exact TauCeti.mfderiv_mfderiv_apply_eq_zero_of_comp_eventuallyEq_const (.of_eq hconst) c

/-- The kernel of the real derivative of `mkNonzero` at `v` is the line `𝕜 ∙ v`, viewed as a real
subspace. -/
theorem ker_mfderiv_mkNonzero [FiniteDimensional ℝ 𝕜]
    (v : TauCeti.puncturedSpace (Fin (n + 1) → 𝕜)) :
    LinearMap.ker (mfderiv 𝓘(ℝ, Fin (n + 1) → 𝕜) 𝓘(ℝ, Fin n → 𝕜) (mkNonzero 𝕜 n) v).toLinearMap =
      (𝕜 ∙ (v : Fin (n + 1) → 𝕜)).restrictScalars ℝ := by
  have hv := TauCeti.mem_puncturedSpace.1 v.property
  let L : (Fin (n + 1) → 𝕜) →ₗ[ℝ] (Fin n → 𝕜) :=
    (mfderiv 𝓘(ℝ, Fin (n + 1) → 𝕜) 𝓘(ℝ, Fin n → 𝕜) (mkNonzero 𝕜 n) v).toLinearMap
  -- The tangent spaces are the model spaces; reading the derivative as a linear map between
  -- these makes their finite-dimensionality instances available.
  change LinearMap.ker L = _
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    exact mfderiv_mkNonzero_smul_self v c
  · have h := LinearMap.finrank_range_add_finrank_ker L
    rw [show LinearMap.range L = ⊤ from LinearMap.range_eq_top.2
      ((isSubmersion_mkNonzero 𝕜 n).surjective_mfderiv
      (by simp) v), finrank_top] at h
    have h₁ : finrank ℝ ((𝕜 ∙ (v : Fin (n + 1) → 𝕜)).restrictScalars ℝ) = finrank ℝ 𝕜 := by
      rw [Submodule.finrank_restrictScalars, finrank_span_singleton hv, mul_one]
    simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at h
    rw [h₁]
    linarith

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
    TauCeti.Manifold.mvfderiv_comp_subtype_val]
  refine (TauCeti.mvfderiv_eq_fderiv_apply _ (z : Fin (n + 1) → ℂ) v).trans ?_
  rw [hd.fderiv]
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

/-- The kernel of the derivative of the Hopf map at `x`, read in `StdSpace (Fin (n + 1))` through
the derivative of the inclusion of the sphere, is the line `ℝ ∙ J₀ x` tangent to the circle
orbit `t ↦ stdRotation _ t x = cos t • x + sin t • J₀ x` through `x`. -/
theorem ker_mfderiv_sphereHopf (x : sphere (0 : StdSpace (Fin (n + 1))) 1) :
    (LinearMap.ker (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) (sphereHopf n) x).toLinearMap).map
        (mvfderiv (𝓡 (2 * n + 1))
          (Subtype.val : sphere (0 : StdSpace (Fin (n + 1))) 1 → StdSpace (Fin (n + 1)))
            x).toLinearMap =
      ℝ ∙ stdComplexStructure (Fin (n + 1)) (x : StdSpace (Fin (n + 1))) := by
  set e := complexToRealEuclidean (Fin (n + 1))
  let L : EuclideanSpace ℝ (Fin (2 * n + 1)) →ₗ[ℝ] (Fin n → ℂ) :=
    (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) (sphereHopf n) x).toLinearMap
  let D : EuclideanSpace ℝ (Fin (2 * n + 1)) →ₗ[ℝ] StdSpace (Fin (n + 1)) :=
    (mvfderiv (𝓡 (2 * n + 1))
      (Subtype.val : sphere (0 : StdSpace (Fin (n + 1))) 1 → StdSpace (Fin (n + 1))) x).toLinearMap
  -- The tangent spaces are the model spaces; reading both derivatives as linear maps between
  -- these makes their finite-dimensionality instances available.
  change (LinearMap.ker L).map D = _
  have hJ : stdComplexStructure (Fin (n + 1)) (x : StdSpace (Fin (n + 1))) =
      e (Complex.I • e.symm x) := by
    rw [← stdComplexStructure_complexToRealEuclidean, ContinuousLinearEquiv.apply_symm_apply]
  have hJx : stdComplexStructure (Fin (n + 1)) (x : StdSpace (Fin (n + 1))) ≠ 0 := by
    rw [hJ]
    simpa using ne_zero_of_mem_unit_sphere x
  have hmem : stdComplexStructure (Fin (n + 1)) (x : StdSpace (Fin (n + 1))) ∈
      (LinearMap.ker L).map D := by
    -- The tangent vector is read in the model space, the domain of `D`.
    obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℝ (Fin (2 * n + 1)),
        D w = stdComplexStructure (Fin (n + 1)) (x : StdSpace (Fin (n + 1))) :=
      exists_mvfderiv_coe_sphere_eq x (AlmostComplexStructure.inner_self_apply
        (inner_stdComplexStructure_stdComplexStructure (ι := Fin (n + 1))) _)
    refine ⟨w, ?_, hw⟩
    let w' : TangentSpace (𝓡 (2 * n + 1)) x := w
    have hι : mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin (n + 1) → ℂ) (sphereToPuncturedSpace n) x w' =
        Complex.I • e.symm x := by
      have h₁ := TauCeti.Manifold.mfderiv_subtype_val_comp_apply (I := 𝓘(ℝ, Fin (n + 1) → ℂ))
        (J := 𝓡 (2 * n + 1)) (f := sphereToPuncturedSpace n) (x := x) w'
      have h₂ := mfderiv_comp_apply x
        ((e.symm : StdSpace (Fin (n + 1)) →L[ℝ] (Fin (n + 1) → ℂ)).mdifferentiableAt)
        ((contMDiff_coe_sphere x).mdifferentiableAt one_ne_zero) w'
      rw [ContinuousLinearMap.mfderiv_eq] at h₂
      have h₃ : e.symm (D w) = Complex.I • e.symm x := by
        rw [hw, hJ, ContinuousLinearEquiv.symm_apply_apply]
      exact h₁.symm.trans (h₂.trans h₃)
    -- `w'` is `w` read as a tangent vector of the sphere at `x`.
    change mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) (sphereHopf n) x w' = 0
    rw [← mkNonzero_comp_sphereToPuncturedSpace, mfderiv_comp_apply x
      ((contMDiff_mkNonzero ℂ n 1 _).mdifferentiableAt one_ne_zero)
      ((contMDiff_sphereToPuncturedSpace n 1 x).mdifferentiableAt one_ne_zero), hι]
    exact mfderiv_mkNonzero_smul_self _ Complex.I
  symm
  refine Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 hmem) ?_
  rw [finrank_span_singleton hJx, ← LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective D (injective_mvfderiv_subtypeVal_sphere x) _)]
  have h := LinearMap.finrank_range_add_finrank_ker L
  rw [show LinearMap.range L = ⊤ from LinearMap.range_eq_top.2
    ((isSubmersion_sphereHopf n).surjective_mfderiv (by simp) x), finrank_top] at h
  simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, finrank_euclideanSpace] at h
  omega

end SymplecticGeometry
