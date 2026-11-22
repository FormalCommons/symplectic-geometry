/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Polynomial
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Topology.VectorBundle.Constructions
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.Basic
public import SymplecticGeometry.Geometry.Manifold.Projectivization.TwistCore
public import TauCeti.Topology.VectorBundle.Pullback

import TauCeti.Geometry.Manifold.VectorBundle.Pullback

/-!
# The section of `X.embedding^* 𝒪(1)^{⊕ι}` given by linear forms

A linear map `ℓ : 𝕜^{m+1} → 𝕜^ι` is a tuple of `ι` linear forms on `𝕜^{m+1}`, and each of them
is a section of `𝒪(1)` on `ℙ 𝕜 (Fin (m + 1) → 𝕜)`, by Tau Ceti's `homogeneousSection 1`. Together
they form a section `Projectivization.linearSection ℓ` of `𝒪(1) ⊗ 𝕜^ι`, the bundle
`Projectivization.twistPiCore 1 ι`, whose zeros are the lines on which all the forms vanish.

On a smooth projective hypersurface `X` of dimension `n`, a tuple of `ι` linear forms on
`ℂ^{n+2}` so gives a section of the pull-back `X.embedding *ᵖ (twistPiCore 1 ι).Fiber` of
`𝒪(1) ⊗ ℂ^ι` to `X`. For `ι = Fin n`, the rank of that bundle is the dimension of `X`, and the
degree of `X` can be computed by counting the zeros of a generic such section, with Tau Ceti's
`ContMDiffSection.mem_residual_setOf_regular_and_finite_zero_affineFamily`; this file provides
the section in the form that theorem takes: a smooth section of the underlying real vector bundle
over the underlying real manifold, real-linear in the forms, such that the sections of finitely
many forms span every fibre.

## Main declarations

* `Projectivization.linearSection ℓ`: the section of `𝒪(1) ⊗ 𝕜^ι` given by `ℓ`. In the frame of
  the chart `j`, at the line spanned by `v`, it is `ℓ v / v j`
  (`Projectivization.twistTransition_mul_linearSection_mk`); it vanishes at `x` exactly when
  `ℓ` vanishes on `x` (`Projectivization.linearSection_eq_zero_iff`), and it is analytic
  (`Projectivization.contMDiff_linearSection`).
* The instance `ContMDiffVectorBundle ∞ _ _ 𝓘(ℝ, _)` on the pull-back of `𝒪(k) ⊗ ℂ^ι` to `X`,
  by the library's `ContMDiffVectorBundle.restrictScalars`; its real structure is Mathlib's
  pull-back of the one that `Projectivization/TwistCore.lean` gives `𝒪(k) ⊗ ℂ^ι`.
* `SymplecticGeometry.SmoothProjectiveHypersurface.linearSection`: the `ℝ`-linear map sending
  `ℓ : ℂ^{n+2} → ℂ^ι` to the smooth real section of the pull-back of `𝒪(1) ⊗ ℂ^ι` that it gives,
  the holomorphic section with its scalars restricted (`ContMDiffSection.restrictScalars`), with
  `SymplecticGeometry.SmoothProjectiveHypersurface.linearSection_eq_zero_iff` for its zeros and
  `SymplecticGeometry.SmoothProjectiveHypersurface.span_range_linearSection_smulRight`: the
  sections of the forms `x_j e_k` and `i x_j e_k` span every fibre over `ℝ`.
* `SymplecticGeometry.SmoothProjectiveHypersurface.contMDiff_linearSection_embedding`: that
  section is holomorphic.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 1,
  §1 (sections of `𝒪(1)` given by linear forms).
-/

public section

noncomputable section

open Bundle Set Projectivization
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace Projectivization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {m : ℕ} {ι : Type*} [Fintype ι]

/-- The section of `𝒪(1) ⊗ 𝕜^ι` on `ℙ 𝕜 (Fin (m + 1) → 𝕜)` given by a linear map
`ℓ : 𝕜^{m+1} → 𝕜^ι`, that is, by the `ι` linear forms `v ↦ ℓ v k`. Its coordinate `k` is Tau
Ceti's section `homogeneousSection 1` of `𝒪(1)` given by the form `v ↦ ℓ v k`, so that in the
frame of the chart `j`, at the line spanned by a vector `v` with `v j = 1`, it is `ℓ v`
(`Projectivization.twistTransition_mul_linearSection_mk`). -/
def linearSection (ℓ : (Fin (m + 1) → 𝕜) →ₗ[𝕜] ι → 𝕜) (x : ℙ 𝕜 (Fin (m + 1) → 𝕜)) :
    (twistPiCore 1 ι).Fiber x :=
  (fun k ↦ homogeneousSection 1 ((LinearMap.toMatrix' ℓ).toMvPolynomial k) x : ι → 𝕜)

/-- The coordinate `k` of the section given by `ℓ` is the section of `𝒪(1)` given by the form
`v ↦ ℓ v k`, written as a polynomial by Mathlib's `Matrix.toMvPolynomial`. -/
theorem linearSection_def (ℓ : (Fin (m + 1) → 𝕜) →ₗ[𝕜] ι → 𝕜) (x : ℙ 𝕜 (Fin (m + 1) → 𝕜))
    (k : ι) :
    linearSection ℓ x k = homogeneousSection 1 ((LinearMap.toMatrix' ℓ).toMvPolynomial k) x :=
  (rfl)

/-- The section given by `ℓ`, in the frame of the preferred chart `i` at `x`: its coordinate `k`
is `ℓ v k / v i` for the chosen representative `v` of `x`. -/
theorem linearSection_apply (ℓ : (Fin (m + 1) → 𝕜) →ₗ[𝕜] ι → 𝕜) (x : ℙ 𝕜 (Fin (m + 1) → 𝕜))
    (k : ι) : linearSection ℓ x k = ℓ x.rep k / x.rep ((twistCore (𝕜 := 𝕜) 1).indexAt x) := by
  simp [linearSection_def, homogeneousSection_def, Matrix.toMvPolynomial_eval_eq_apply]

/-- In the frame of the chart `j`, the coordinate `k` of the section given by `ℓ` is
`ℓ v k / v j` at `x`, for the chosen representative `v` of `x`. -/
theorem twistTransition_mul_linearSection (ℓ : (Fin (m + 1) → 𝕜) →ₗ[𝕜] ι → 𝕜)
    (j : Fin (m + 1)) (x : ℙ 𝕜 (Fin (m + 1) → 𝕜)) (k : ι) :
    twistTransition 1 ((twistCore (𝕜 := 𝕜) 1).indexAt x) j x * linearSection ℓ x k =
      ℓ x.rep k / x.rep j := by
  rw [linearSection_def]
  simpa [Matrix.toMvPolynomial_eval_eq_apply] using
    twistTransition_mul_homogeneousSection (𝕜 := 𝕜) 1 ((LinearMap.toMatrix' ℓ).toMvPolynomial k)
      j x

/-- **The section given by `ℓ` in the standard charts.** In the frame of the chart `j`, at the
line spanned by a nonzero vector `v`, the coordinate `k` of the section given by `ℓ` is
`ℓ v k / v j`; it is `ℓ v k` where `v j = 1`. -/
theorem twistTransition_mul_linearSection_mk (ℓ : (Fin (m + 1) → 𝕜) →ₗ[𝕜] ι → 𝕜)
    (j : Fin (m + 1)) {v : Fin (m + 1) → 𝕜} (hv : v ≠ 0) (k : ι) :
    twistTransition 1 ((twistCore (𝕜 := 𝕜) 1).indexAt (mk 𝕜 v hv)) j (mk 𝕜 v hv) *
        linearSection ℓ (mk 𝕜 v hv) k = ℓ v k / v j := by
  rw [twistTransition_mul_linearSection]
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep 𝕜 v hv
  rw [← ha, Units.smul_def, map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    mul_div_mul_left _ _ a.ne_zero]

/-- The section given by `ℓ` vanishes at `x` exactly when all the forms `v ↦ ℓ v k` vanish on
the line `x`. -/
@[simp]
theorem linearSection_eq_zero_iff (ℓ : (Fin (m + 1) → 𝕜) →ₗ[𝕜] ι → 𝕜)
    (x : ℙ 𝕜 (Fin (m + 1) → 𝕜)) : linearSection ℓ x = 0 ↔ ℓ x.rep = 0 := by
  have hi := (mem_affineOpen_iff _ x).1 (mem_affineOpen_twistCore_indexAt (n := m) 1 x)
  constructor
  · intro h
    funext k
    have hk : linearSection ℓ x k = 0 := congrArg (fun s : (twistPiCore 1 ι).Fiber x ↦ s k) h
    rwa [linearSection_apply, div_eq_zero_iff, or_iff_left hi] at hk
  · intro h
    funext k
    -- The zero of the fibre is that of `ι → 𝕜`, by the definition of `VectorBundleCore.Fiber`.
    exact (linearSection_apply ℓ x k).trans (by rw [h, Pi.zero_apply, zero_div]; rfl)

/-- The section given by a sum of linear maps is the sum of their sections. -/
theorem linearSection_add (ℓ ℓ' : (Fin (m + 1) → 𝕜) →ₗ[𝕜] ι → 𝕜) (x : ℙ 𝕜 (Fin (m + 1) → 𝕜)) :
    linearSection (ℓ + ℓ') x = linearSection ℓ x + linearSection ℓ' x := by
  funext k
  -- The addition of the fibre is that of `ι → 𝕜`, by the definition of `VectorBundleCore.Fiber`.
  exact (linearSection_apply _ x k).trans (by
    rw [LinearMap.add_apply, Pi.add_apply, add_div, ← linearSection_apply, ← linearSection_apply]
    rfl)

/-- The section given by a scalar multiple of a linear map is the scalar multiple of its
section. -/
theorem linearSection_smul (c : 𝕜) (ℓ : (Fin (m + 1) → 𝕜) →ₗ[𝕜] ι → 𝕜)
    (x : ℙ 𝕜 (Fin (m + 1) → 𝕜)) : linearSection (c • ℓ) x = c • linearSection ℓ x := by
  funext k
  -- The scalar multiplication of the fibre is that of `ι → 𝕜`, by the definition of
  -- `VectorBundleCore.Fiber`.
  exact (linearSection_apply _ x k).trans (by
    rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, mul_div_assoc, ← linearSection_apply]
    rfl)

/-- **The section given by linear forms is analytic.** The section of `𝒪(1) ⊗ 𝕜^ι` given by
`ℓ` is `C^r` for every `r`, including the analytic order `ω`; for `𝕜 = ℂ` it is holomorphic. -/
theorem contMDiff_linearSection (ℓ : (Fin (m + 1) → 𝕜) →ₗ[𝕜] ι → 𝕜) (r : ℕ∞ω) :
    ContMDiff 𝓘(𝕜, Fin m → 𝕜) (𝓘(𝕜, Fin m → 𝕜).prod 𝓘(𝕜, ι → 𝕜)) r
      (fun x ↦ TotalSpace.mk' (ι → 𝕜) x (linearSection ℓ x)) := by
  rw [contMDiff_section_twistPiCore_iff]
  refine fun j ↦ contMDiffOn_pi_module_iff.2 fun k ↦ ?_
  simpa only [Nat.cast_one, linearSection_def] using
    (contMDiff_section_twistCore_iff _ _).1 (contMDiff_homogeneousSection
      (Matrix.toMvPolynomial_isHomogeneous (LinearMap.toMatrix' ℓ) k) r) j

end Projectivization

namespace SymplecticGeometry

namespace SmoothProjectiveHypersurface

variable {n d : ℕ} (X : SmoothProjectiveHypersurface n d)

/-- The pull-back of `𝒪(k) ⊗ ℂ^ι` to a smooth projective hypersurface is a smooth real vector
bundle over the underlying real manifold. Its real structure is Mathlib's pull-back of that of
`𝒪(k) ⊗ ℂ^ι`. -/
instance (k : ℤ) (ι : Type*) [Fintype ι] :
    ContMDiffVectorBundle ∞ (ι → ℂ) (X.embedding *ᵖ (twistPiCore (𝕜 := ℂ) (n := n + 1) k ι).Fiber)
      𝓘(ℝ, Fin (n + 1 - Fintype.card Unit) → ℂ) :=
  have : ContMDiffVectorBundle ∞ (ι → ℂ)
      (X.embedding *ᵖ (twistPiCore (𝕜 := ℂ) (n := n + 1) k ι).Fiber)
      𝓘(ℂ, Fin (n + 1 - Fintype.card Unit) → ℂ) :=
    Bundle.Pullback.contMDiffVectorBundle (X.embedding.contMDiff.of_le le_top)
  ContMDiffVectorBundle.restrictScalars (𝕜' := ℂ) ℝ _ _

variable {ι : Type*} [Fintype ι]

/-- **The pull-back to `X` of the section given by `ℓ` is holomorphic.** The section
`x ↦ Projectivization.linearSection ℓ (X.embedding x)` of the pull-back of `𝒪(1) ⊗ ℂ^ι` to `X` is
analytic. -/
theorem contMDiff_linearSection_embedding (ℓ : (Fin (n + 2) → ℂ) →ₗ[ℂ] ι → ℂ) :
    ContMDiff 𝓘(ℂ, Fin (n + 1 - Fintype.card Unit) → ℂ)
      (𝓘(ℂ, Fin (n + 1 - Fintype.card Unit) → ℂ).prod 𝓘(ℂ, ι → ℂ)) ω
      (fun x : X ↦ TotalSpace.mk' (ι → ℂ)
        (E := X.embedding *ᵖ (twistPiCore (𝕜 := ℂ) (n := n + 1) 1 ι).Fiber) x
        (Projectivization.linearSection ℓ (X.embedding x))) :=
  (Bundle.Pullback.contMDiff_iff X.embedding X.embedding.contMDiff).2
    ⟨contMDiff_id, (contMDiff_linearSection ℓ ω).comp X.embedding.contMDiff⟩

/-- **The section of `X.embedding^* 𝒪(1)^{⊕ι}` given by linear forms.** For a linear map
`ℓ : ℂ^{n+2} → ℂ^ι`, the smooth section of the pull-back of `𝒪(1) ⊗ ℂ^ι` to `X` whose value at
`x` is that of `Projectivization.linearSection ℓ` at `x`, as a section of the underlying real
vector bundle over the underlying real manifold. It is `ℝ`-linear in `ℓ`. -/
def linearSection : ((Fin (n + 2) → ℂ) →ₗ[ℂ] ι → ℂ) →ₗ[ℝ]
    ContMDiffSection 𝓘(ℝ, Fin (n + 1 - Fintype.card Unit) → ℂ) (ι → ℂ) ∞
      (X.embedding *ᵖ (twistPiCore (𝕜 := ℂ) (n := n + 1) 1 ι).Fiber) where
  toFun ℓ := ContMDiffSection.restrictScalars ℝ
    { toFun x := Projectivization.linearSection ℓ (X.embedding x)
      contMDiff_toFun := (X.contMDiff_linearSection_embedding ℓ).of_le le_top }
  -- The fibres of the pull-back are those of `𝒪(1) ⊗ ℂ^ι` by the definition of `Bundle.Pullback`,
  -- so the values of the sections are compared there; the closing `exact`s read the values of
  -- the holomorphic sections through that definition (see `linearSection_apply`).
  map_add' ℓ ℓ' := by
    ext x
    simp only [ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.restrictScalars_apply]
    exact Projectivization.linearSection_add ℓ ℓ' (X.embedding x)
  map_smul' c ℓ := by
    ext x
    simp only [RingHom.id_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
      ContMDiffSection.restrictScalars_apply]
    exact Projectivization.linearSection_smul (c : ℂ) ℓ (X.embedding x)

/-- The value at `x` of the section given by `ℓ` is the section of `𝒪(1) ⊗ ℂ^ι` given by `ℓ` at
the image of `x` in projective space. -/
theorem linearSection_apply (ℓ : (Fin (n + 2) → ℂ) →ₗ[ℂ] ι → ℂ) (x : X) :
    X.linearSection ℓ x = Projectivization.linearSection ℓ (X.embedding x) := by
  rw [linearSection, LinearMap.coe_mk, AddHom.coe_mk, ContMDiffSection.restrictScalars_apply]
  -- `ContMDiffSection.coeFn_mk` does not apply, since the section is written with values in the
  -- fibres of `𝒪(1) ⊗ ℂ^ι`, which are those of the pull-back only by the definition of
  -- `Bundle.Pullback`.
  rfl

/-- **The zeros of the section given by `ℓ`.** The section given by `ℓ` vanishes at `x` exactly
when all the forms of `ℓ` vanish on the line `x`. -/
theorem linearSection_eq_zero_iff (ℓ : (Fin (n + 2) → ℂ) →ₗ[ℂ] ι → ℂ) (x : X) :
    X.linearSection ℓ x = 0 ↔ ℓ (x : ℙ ℂ (Fin (n + 2) → ℂ)).rep = 0 := by
  rw [linearSection_apply, ← coe_embedding]
  exact Projectivization.linearSection_eq_zero_iff ℓ _

/-- **The sections given by the forms `x_j e_k` and `i x_j e_k` span every fibre.** At every
point of `X`, the values of the sections given by the linear maps `v ↦ v j • c • e_k`, for
`c` in the real basis `1, i` of `ℂ` and `e_k` the standard basis of `ℂ^ι`, span the fibre
over `ℝ`. -/
theorem span_range_linearSection_smulRight [DecidableEq ι] (x : X) :
    Submodule.span ℝ (range fun p : Fin (n + 2) × ι × Fin 2 ↦
      X.linearSection ((LinearMap.proj (R := ℂ) (φ := fun _ ↦ ℂ) p.1).smulRight
        (Pi.single p.2.1 (Complex.basisOneI p.2.2))) x) = ⊤ := by
  have hi := (mem_affineOpen_iff _ _).1
    (mem_affineOpen_twistCore_indexAt (𝕜 := ℂ) 1 (X.embedding x))
  -- The fibre is `ι → ℂ` by the definitions of `Bundle.Pullback` and
  -- `VectorBundleCore.Fiber`, so the real basis of `ι → ℂ` is one of the fibre.
  let e : Module.Basis (Σ _ : ι, Fin 2) ℝ
      ((X.embedding *ᵖ (twistPiCore (𝕜 := ℂ) (n := n + 1) 1 ι).Fiber) x) :=
    Pi.basis fun _ ↦ Complex.basisOneI
  rw [eq_top_iff, ← e.span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨⟨k, b⟩, rfl⟩
  refine ⟨((twistCore 1).indexAt (X.embedding x), k, b), ?_⟩
  funext l
  dsimp only
  rw [linearSection_apply, Projectivization.linearSection_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, Pi.smul_apply, smul_eq_mul, mul_div_cancel_left₀ _ hi]
  exact (congrFun (Pi.basis_apply (fun _ ↦ Complex.basisOneI) ⟨k, b⟩) l).symm

end SmoothProjectiveHypersurface

end SymplecticGeometry
