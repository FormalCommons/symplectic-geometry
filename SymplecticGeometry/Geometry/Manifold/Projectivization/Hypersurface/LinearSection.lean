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
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization
public import TauCeti.Topology.VectorBundle.Pullback

import SymplecticGeometry.Geometry.Manifold.VectorBundle.RestrictScalars
import SymplecticGeometry.LinearAlgebra.FiniteDimensional.KerInf
import SymplecticGeometry.LinearAlgebra.Projectivization.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.LinearAlgebra.Dimension.Submodule

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
  by Tau Ceti's `ContMDiffVectorBundle.restrictScalars_modelWithCornersSelf`; its real structure is
  Mathlib's pull-back of the one that `Projectivization/TwistCore.lean` gives `𝒪(k) ⊗ ℂ^ι`.
* `SymplecticGeometry.SmoothProjectiveHypersurface.linearSection`: the `ℝ`-linear map sending
  `ℓ : ℂ^{n+2} → ℂ^ι` to the smooth real section of the pull-back of `𝒪(1) ⊗ ℂ^ι` that it gives,
  the holomorphic section with its scalars restricted (`ContMDiffSection.restrictScalars'`), with
  `SymplecticGeometry.SmoothProjectiveHypersurface.linearSection_eq_zero_iff` for its zeros and
  `SymplecticGeometry.SmoothProjectiveHypersurface.span_range_linearSection_smulRight`: the
  sections of the forms `x_j e_k` and `i x_j e_k` span every fibre over `ℝ`.
* `SymplecticGeometry.SmoothProjectiveHypersurface.contMDiff_linearSection_embedding`: that
  section is holomorphic.

The following are in the namespace `SymplecticGeometry.SmoothProjectiveHypersurface`.

* `trivializationAt_linearSection_snd`: in the preferred trivialization of the pull-back at `z`,
  the section is `ℓ` applied to the homogeneous coordinates normalized for the chart at `z`.
* `exists_hasFDerivAt_trivializationAt_linearSection`: read in the chart of `X` and the
  trivialization of the pull-back at `z`, the section has a complex-linear derivative.
* `surjective_sectionLinearization_linearSection_iff`: for `ℓ : ℂ^{n+2} → ℂ^n` onto, the section
  is transverse to zero at a zero `z` exactly when the line `{ℓ = 0}` is transverse to `X` at
  `z`, and then `exists_continuousLinearEquiv_hasFDerivAt_trivializationAt_linearSection` makes
  the derivative a complex isomorphism. With `exists_sum_mul_eval_pderiv_ne_zero_iff`, the
  transversality of the line reads as the hypothesis of `card_inter_line` (in
  `Hypersurface/Line.lean`) for a parametrization of it.

## Transversality at a zero

In the preferred chart `j` at `z`, the section given by `ℓ` is `ℓ` applied to the homogeneous
coordinates `v` of the points of `X` normalized by `v j = 1`. Their derivative at `z` is
injective, since `X` is immersed; it is read through the bijective differential of the standard
affine chart, as in Tau Ceti's `TauCeti.surjective_mfderiv_eval_dehomogenize_affineChart_iff`.
Its range lies in the hyperplane `{w j = 0}` and in the kernel of the differential `df` of the
polynomial at the normalized `z`. These hyperplanes differ, since `z` lies in the second by
Euler's identity but not in the first, so by counting dimensions the range is their intersection:
the tangent space of `X` at `z` in homogeneous coordinates (compare Tau Ceti's
`TauCeti.tangentRange_complexProjectiveZeroLocusEmbedding`). As the derivative of the section goes
from an `n`-dimensional space to `ℂ^n`, it is onto exactly when `ker ℓ` meets that intersection
in `0`, which for `ℓ` onto says that `df` does not vanish on the plane `ker ℓ`
(`Submodule.inf_ker_inf_ker_eq_bot_iff`).

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 1,
  §1 (sections of `𝒪(1)` given by linear forms), and Chapter 0, §2 (the tangent space of a
  hypersurface).
-/

public section

noncomputable section

open Bundle Set Projectivization
open scoped Manifold ContDiff LinearAlgebra.Projectivization VectorBundle.ComplexToReal

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
  have hi := rep_indexAt_twistCore_ne_zero (n := m) 1 x
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
      𝓘(ℝ, Fin n → ℂ) :=
  have : ContMDiffVectorBundle ∞ (ι → ℂ)
      (X.embedding *ᵖ (twistPiCore (𝕜 := ℂ) (n := n + 1) k ι).Fiber)
      𝓘(ℂ, Fin n → ℂ) :=
    Bundle.Pullback.contMDiffVectorBundle (X.embedding.contMDiff.of_le le_top)
  ContMDiffVectorBundle.restrictScalars_modelWithCornersSelf ℝ this

variable {ι : Type*} [Fintype ι]

/-- **The pull-back to `X` of the section given by `ℓ` is holomorphic.** The section
`x ↦ Projectivization.linearSection ℓ (X.embedding x)` of the pull-back of `𝒪(1) ⊗ ℂ^ι` to `X` is
analytic. -/
theorem contMDiff_linearSection_embedding (ℓ : (Fin (n + 2) → ℂ) →ₗ[ℂ] ι → ℂ) :
    ContMDiff 𝓘(ℂ, Fin n → ℂ)
      (𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ, ι → ℂ)) ω
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
    ContMDiffSection 𝓘(ℝ, Fin n → ℂ) (ι → ℂ) ∞
      (X.embedding *ᵖ (twistPiCore (𝕜 := ℂ) (n := n + 1) 1 ι).Fiber) where
  toFun ℓ := ContMDiffSection.restrictScalars' ℝ
    { toFun x := Projectivization.linearSection ℓ (X.embedding x)
      contMDiff_toFun := (X.contMDiff_linearSection_embedding ℓ).of_le le_top }
  -- The fibres of the pull-back are those of `𝒪(1) ⊗ ℂ^ι` by the definition of `Bundle.Pullback`,
  -- so the values of the sections are compared there; the closing `exact`s read the values of
  -- the holomorphic sections through that definition (see `linearSection_apply`).
  map_add' ℓ ℓ' := by
    ext x
    simp only [ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.restrictScalars'_apply]
    exact Projectivization.linearSection_add ℓ ℓ' (X.embedding x)
  map_smul' c ℓ := by
    ext x
    simp only [RingHom.id_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
      ContMDiffSection.restrictScalars'_apply]
    exact Projectivization.linearSection_smul (c : ℂ) ℓ (X.embedding x)

/-- The value at `x` of the section given by `ℓ` is the section of `𝒪(1) ⊗ ℂ^ι` given by `ℓ` at
the image of `x` in projective space. -/
theorem linearSection_apply (ℓ : (Fin (n + 2) → ℂ) →ₗ[ℂ] ι → ℂ) (x : X) :
    X.linearSection ℓ x = Projectivization.linearSection ℓ (X.embedding x) := by
  rw [linearSection, LinearMap.coe_mk, AddHom.coe_mk, ContMDiffSection.restrictScalars'_apply]
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
  have hi := rep_indexAt_twistCore_ne_zero (𝕜 := ℂ) 1 (X.embedding x)
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

/-! ### The section in a chart and its transversality at a zero -/

section Transversality

open MvPolynomial
open scoped Topology

/-- **The section given by `ℓ` in the trivialization at `z`.** At a point `y` of `X` in the
standard affine open of the preferred chart `j` of `𝒪(1)` at `z`, the preferred trivialization of
the pull-back at `z` reads the section given by `ℓ` as `ℓ` applied to the homogeneous
coordinates `Fin.insertNth j 1 (affineChart j y)` of `y`, whose coordinate `j` is `1`. -/
theorem trivializationAt_linearSection_snd (ℓ : (Fin (n + 2) → ℂ) →ₗ[ℂ] ι → ℂ) {z y : X}
    (hy : (y : ℙ ℂ (Fin (n + 2) → ℂ)) ∈
      affineOpen ((twistCore (𝕜 := ℂ) 1).indexAt (z : ℙ ℂ (Fin (n + 2) → ℂ)))) :
    (trivializationAt (ι → ℂ) (X.embedding *ᵖ (twistPiCore (𝕜 := ℂ) (n := n + 1) 1 ι).Fiber) z
      ⟨y, X.linearSection ℓ y⟩).2 =
      ℓ (Fin.insertNth (α := fun _ ↦ ℂ) ((twistCore (𝕜 := ℂ) 1).indexAt (z : ℙ ℂ _)) 1
        (affineChart ((twistCore (𝕜 := ℂ) 1).indexAt (z : ℙ ℂ _)) (y : ℙ ℂ _))) := by
  rw [linearSection_apply, trivializationAt, FiberBundle.pullback_trivializationAt',
    Trivialization.pullback_apply, Pullback.lift_mk, twistPiCore_trivializationAt_apply_snd,
    coe_embedding]
  funext k
  rw [twistTransition_mul_linearSection, insertNth_one_affineChart_eq_normalizedRep _ hy,
    normalizedRep_def, LinearMap.proj_apply, map_smul, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]

/-- The normalized homogeneous coordinates of points of `X` near `z`, read in the chart of `X`
at `z`: the representative of the image in projective space whose coordinate of the preferred
chart at `z` is `1`. -/
private noncomputable def chartLift (z : X) (y : Fin n → ℂ) :
    Fin (n + 2) → ℂ :=
  Fin.insertNth (α := fun _ ↦ ℂ) ((twistCore (𝕜 := ℂ) 1).indexAt (z : ℙ ℂ (Fin (n + 2) → ℂ))) 1
    (affineChart ((twistCore (𝕜 := ℂ) 1).indexAt (z : ℙ ℂ (Fin (n + 2) → ℂ)))
      (((chartAt (Fin n → ℂ) z).symm y : X) : ℙ ℂ (Fin (n + 2) → ℂ)))

/-- Near the image of `z`, the chart inverse lands in the affine open of the preferred chart. -/
private theorem eventually_mem_affineOpen (z : X) :
    ∀ᶠ y in 𝓝 (chartAt (Fin n → ℂ) z z),
      (((chartAt (Fin n → ℂ) z).symm y : X) : ℙ ℂ (Fin (n + 2) → ℂ)) ∈
        affineOpen ((twistCore (𝕜 := ℂ) 1).indexAt (z : ℙ ℂ (Fin (n + 2) → ℂ))) := by
  have hc : ContinuousAt (fun y ↦ (((chartAt (Fin n → ℂ) z).symm y :
      X) : ℙ ℂ (Fin (n + 2) → ℂ))) (chartAt (Fin n → ℂ) z z) :=
    continuous_subtypeVal.continuousAt.comp
      ((chartAt _ z).continuousAt_symm ((chartAt _ z).map_source (mem_chart_source _ z)))
  refine hc.preimage_mem_nhds ((isOpen_affineOpen _).mem_nhds ?_)
  rw [(chartAt _ z).left_inv (mem_chart_source _ z)]
  exact mem_affineOpen_twistCore_indexAt 1 _

/-- The normalized homogeneous coordinates of the points of `X`, for the preferred chart at `z`,
are holomorphic at `z`. -/
private theorem mdifferentiableAt_insertNth_affineChart (z : X) :
    MDifferentiableAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin (n + 2) → ℂ)
      (fun y : X ↦ Fin.insertNth (α := fun _ ↦ ℂ)
        ((twistCore (𝕜 := ℂ) 1).indexAt (z : ℙ ℂ (Fin (n + 2) → ℂ))) 1
        (affineChart ((twistCore (𝕜 := ℂ) 1).indexAt (z : ℙ ℂ (Fin (n + 2) → ℂ)))
          (y : ℙ ℂ (Fin (n + 2) → ℂ)))) z := by
  have h1 := (contMDiffOn_insertNth_affineChart (𝕜 := ℂ) (n := n + 1)
    ((twistCore (𝕜 := ℂ) 1).indexAt (z : ℙ ℂ (Fin (n + 2) → ℂ))) 1).contMDiffAt
      ((isOpen_affineOpen _).mem_nhds (mem_affineOpen_twistCore_indexAt 1 _))
  have h2 := (X.embedding.contMDiff.of_le (show (1 : ℕ∞ω) ≤ ω from le_top)).contMDiffAt (x := z)
  rw [coe_embedding] at h2
  exact (h1.comp z h2).mdifferentiableAt one_ne_zero

/-- The normalized homogeneous coordinates, read in the chart of `X` at `z`, are complex
differentiable at the image of `z`. -/
private theorem differentiableAt_chartLift (z : X) : DifferentiableAt ℂ (chartLift X z)
    (chartAt (Fin n → ℂ) z z) := by
  have := (mdifferentiableWithinAt_univ.2
    (X.mdifferentiableAt_insertNth_affineChart z)).differentiableWithinAt_comp_extChartAt_symm
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, range_id, preimage_univ, inter_univ, Function.comp_def, id,
    differentiableWithinAt_univ] at this
  exact this

/-- Near the image of `z`, the section given by `ℓ`, read in the chart of `X` and the
trivialization of the pull-back at `z`, is `ℓ` applied to the normalized homogeneous
coordinates. -/
private theorem chartLift_eventuallyEq (ℓ : (Fin (n + 2) → ℂ) →ₗ[ℂ] ι → ℂ) (z : X) :
    (fun y ↦ (trivializationAt (ι → ℂ)
      (X.embedding *ᵖ (twistPiCore (𝕜 := ℂ) (n := n + 1) 1 ι).Fiber) z
      ⟨(chartAt (Fin n → ℂ) z).symm y,
        X.linearSection ℓ ((chartAt (Fin n → ℂ) z).symm y)⟩).2) =ᶠ[𝓝
      (chartAt (Fin n → ℂ) z z)] fun y ↦ ℓ (chartLift X z y) := by
  filter_upwards [X.eventually_mem_affineOpen z] with y hy
  exact X.trivializationAt_linearSection_snd ℓ hy

/-- The section given by `ℓ`, read in the chart of `X` and the trivialization of the pull-back at
`z`, has at the image of `z` the real derivative of the complex-linear map `ℓ ∘ D`, where `D` is
the derivative of the normalized homogeneous coordinates. -/
private theorem hasFDerivAt_trivializationAt_linearSection (ℓ : (Fin (n + 2) → ℂ) →ₗ[ℂ] ι → ℂ)
    (z : X) : HasFDerivAt (fun y ↦ (trivializationAt (ι → ℂ)
        (X.embedding *ᵖ (twistPiCore (𝕜 := ℂ) (n := n + 1) 1 ι).Fiber) z
        ⟨(chartAt (Fin n → ℂ) z).symm y,
          X.linearSection ℓ ((chartAt (Fin n → ℂ) z).symm y)⟩).2)
      (((LinearMap.toContinuousLinearMap ℓ).comp (fderiv ℂ (chartLift X z)
        (chartAt (Fin n → ℂ) z z))).restrictScalars ℝ)
      (chartAt (Fin n → ℂ) z z) :=
  (((LinearMap.toContinuousLinearMap ℓ).hasFDerivAt.comp _
    (X.differentiableAt_chartLift z).hasFDerivAt).restrictScalars ℝ).congr_of_eventuallyEq
    (X.chartLift_eventuallyEq ℓ z)

/-- **The derivative of the section given by `ℓ` is complex linear.** Read in the chart
`chartAt _ z` of `X` and the trivialization `trivializationAt _ _ z` of the pull-back of
`𝒪(1) ⊗ ℂ^ι`, the section given by `ℓ` has, at the image of `z`, a real derivative that is the
restriction of scalars of a `ℂ`-linear map. -/
theorem exists_hasFDerivAt_trivializationAt_linearSection (ℓ : (Fin (n + 2) → ℂ) →ₗ[ℂ] ι → ℂ)
    (z : X) : ∃ A : (Fin n → ℂ) →L[ℂ] ι → ℂ,
      HasFDerivAt (fun y ↦ (trivializationAt (ι → ℂ)
        (X.embedding *ᵖ (twistPiCore (𝕜 := ℂ) (n := n + 1) 1 ι).Fiber) z
        ⟨(chartAt (Fin n → ℂ) z).symm y,
          X.linearSection ℓ ((chartAt (Fin n → ℂ) z).symm y)⟩).2)
        (A.restrictScalars ℝ) (chartAt (Fin n → ℂ) z z) :=
  ⟨_, X.hasFDerivAt_trivializationAt_linearSection ℓ z⟩

/-- At the image of `z`, the normalized homogeneous coordinates are those of `z`. -/
private theorem chartLift_chartAt (z : X) :
    chartLift X z (chartAt (Fin n → ℂ) z z) =
      ((z : ℙ ℂ (Fin (n + 2) → ℂ)).rep ((twistCore (𝕜 := ℂ) 1).indexAt (z : ℙ ℂ _)))⁻¹ •
        (z : ℙ ℂ (Fin (n + 2) → ℂ)).rep := by
  rw [chartLift, (chartAt _ z).left_inv (mem_chart_source _ z),
    insertNth_one_affineChart_eq_normalizedRep _ (mem_affineOpen_twistCore_indexAt 1 _),
    normalizedRep_def, LinearMap.proj_apply]

/-- The derivative of the normalized homogeneous coordinates at the image of `z` is injective,
since `X` is immersed in projective space. -/
private theorem injective_fderiv_chartLift (z : X) :
    Function.Injective
      (fderiv ℂ (chartLift X z) (chartAt (Fin n → ℂ) z z)) := by
  set j := (twistCore (𝕜 := ℂ) 1).indexAt (z : ℙ ℂ (Fin (n + 2) → ℂ))
  have hz := mem_affineOpen_twistCore_indexAt (𝕜 := ℂ) 1 (z : ℙ ℂ (Fin (n + 2) → ℂ))
  have h1 : MDifferentiableAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) (affineChart j)
      (z : ℙ ℂ (Fin (n + 2) → ℂ)) :=
    ((contMDiffOn_affineChart (𝕜 := ℂ) (n := n + 1) j 1).contMDiffAt
      ((isOpen_affineOpen j).mem_nhds hz)).mdifferentiableAt one_ne_zero
  have h2 : MDifferentiableAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ)
      (Subtype.val : X → ℙ ℂ (Fin (n + 2) → ℂ)) z := by
    have := (X.embedding.contMDiff.of_le (show (1 : ℕ∞ω) ≤ ω from le_top)).mdifferentiableAt
      one_ne_zero (x := z)
    rwa [coe_embedding] at this
  -- The differential of `affineChart j` restricted to `X` is injective: that of the chart is
  -- bijective, and that of the inclusion is injective since `X` is immersed.
  have hinj : Function.Injective (mfderiv 𝓘(ℂ, Fin n → ℂ)
      𝓘(ℂ, Fin (n + 1) → ℂ) (affineChart j ∘ (Subtype.val : X → ℙ ℂ (Fin (n + 2) → ℂ))) z) := by
    rw [mfderiv_comp z h1 h2]
    have hbij := (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, Fin (n + 1) → ℂ))
      (affineOpenPartialHomeomorph_mem_atlas j)).mfderiv_bijective (by simpa using hz)
    rw [coe_affineOpenPartialHomeomorph] at hbij
    have hi := X.embedding.isImmersion.mfderiv_injective WithTop.top_ne_zero z
    rw [coe_embedding] at hi
    exact hbij.injective.comp hi
  replace hinj : Function.Injective (fderiv ℂ
      ((affineChart j ∘ (Subtype.val : X → ℙ ℂ (Fin (n + 2) → ℂ))) ∘
        (chartAt (Fin n → ℂ) z).symm)
      (chartAt (Fin n → ℂ) z z)) := by
    rw [TauCeti.fderiv_comp_chartAt_symm]
    -- `mvfderiv` is `mfderiv` followed by `NormedSpace.fromTangentSpace`; the goal reads it on
    -- the model space, which is the tangent space of `X` at `z` by definition.
    exact (NormedSpace.fromTangentSpace _).injective.comp hinj
  -- The affine chart is the chart lift with its coordinate `j` deleted.
  set R : (Fin (n + 2) → ℂ) →L[ℂ] Fin (n + 1) → ℂ :=
    ContinuousLinearMap.pi fun k ↦ ContinuousLinearMap.proj (j.succAbove k)
  have hR : (affineChart j ∘ (Subtype.val : X → ℙ ℂ (Fin (n + 2) → ℂ))) ∘
      (chartAt (Fin n → ℂ) z).symm = R ∘ chartLift X z := by
    funext y k
    simp only [Function.comp_apply, R, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply,
      chartLift]
    exact (Fin.insertNth_apply_succAbove (α := fun _ ↦ ℂ) j 1 _ k).symm
  rw [hR, fderiv_comp _ R.differentiableAt (X.differentiableAt_chartLift z)] at hinj
  rw [R.fderiv, ContinuousLinearMap.coe_comp] at hinj
  exact hinj.of_comp

/-- The differential at `v` of the polynomial of `X`, as a linear form on `ℂ^{n+2}`. -/
private noncomputable def polyDeriv (v : Fin (n + 2) → ℂ) : (Fin (n + 2) → ℂ) →L[ℂ] ℂ :=
  ∑ i, eval v (pderiv i X.poly) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ ↦ ℂ) i

/-- The differential at `v` of the polynomial of `X`, applied to `w`. -/
private theorem polyDeriv_apply (v w : Fin (n + 2) → ℂ) :
    X.polyDeriv v w = ∑ i, w i * eval v (pderiv i X.poly) := by
  simp [polyDeriv, mul_comm]

/-- The derivative of the normalized homogeneous coordinates takes values in the kernel of the
differential of the polynomial of `X`, since the polynomial vanishes on `X`. -/
private theorem polyDeriv_comp_fderiv_chartLift (z : X) :
    (X.polyDeriv (chartLift X z (chartAt (Fin n → ℂ) z z))).comp
      (fderiv ℂ (chartLift X z) (chartAt (Fin n → ℂ) z z)) = 0 := by
  have h := (X.poly.hasFDerivAt_eval _).comp _ (X.differentiableAt_chartLift z).hasFDerivAt
  refine h.unique ((hasFDerivAt_const (0 : ℂ) _).congr_of_eventuallyEq ?_)
  filter_upwards [X.eventually_mem_affineOpen z] with y hy
  simp only [Function.comp_apply, chartLift, insertNth_one_affineChart_eq_normalizedRep _ hy,
    normalizedRep_def, X.isHomogeneous.eval_smul,
    X.mem_carrier_iff.1 (((chartAt _ z).symm y : X).property), mul_zero]

/-- The derivative of the normalized homogeneous coordinates takes values in the hyperplane
where the coordinate `j` of the preferred chart vanishes, since that coordinate is `1`. -/
private theorem proj_comp_fderiv_chartLift (z : X) :
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 2) ↦ ℂ)
      ((twistCore (𝕜 := ℂ) 1).indexAt (z : ℙ ℂ (Fin (n + 2) → ℂ)))).comp
      (fderiv ℂ (chartLift X z) (chartAt (Fin n → ℂ) z z)) = 0 := by
  have h := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 2) ↦ ℂ)
      ((twistCore (𝕜 := ℂ) 1).indexAt (z : ℙ ℂ (Fin (n + 2) → ℂ)))).hasFDerivAt.comp _
    (X.differentiableAt_chartLift z).hasFDerivAt
  refine h.unique ((hasFDerivAt_const (1 : ℂ) _).congr_of_eventuallyEq (Filter.Eventually.of_forall
    fun y ↦ ?_))
  simp only [Function.comp_apply, ContinuousLinearMap.proj_apply, chartLift,
    Fin.insertNth_apply_same]

/-- The differential of the polynomial of `X` at a nonzero multiple `c • v` of `v` is
`c ^ (d - 1)` times that at `v`. -/
private theorem polyDeriv_smul (c : ℂ) (v w : Fin (n + 2) → ℂ) :
    X.polyDeriv (c • v) w = c ^ (d - 1) * X.polyDeriv v w := by
  simp only [polyDeriv_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← TauCeti.jacobiMatrixAt_apply (fun _ : Unit ↦ X.poly) _ (),
    ← TauCeti.jacobiMatrixAt_apply (fun _ : Unit ↦ X.poly) v (),
    TauCeti.jacobiMatrixAt_smul_apply (fun _ ↦ X.isHomogeneous)]
  ring

/-- **Euler's identity.** At a zero `v` of the polynomial of `X`, its differential vanishes on
`v`. -/
private theorem polyDeriv_self_eq_zero {v : Fin (n + 2) → ℂ} (hv : eval v X.poly = 0) :
    X.polyDeriv v v = 0 := by
  have h := congrFun (TauCeti.jacobiMatrixAt_mulVec_self_eq_zero (p := fun _ : Unit ↦ X.poly)
    (fun _ ↦ X.isHomogeneous) (fun _ ↦ hv)) ()
  simpa only [polyDeriv_apply, Matrix.mulVec, dotProduct, TauCeti.jacobiMatrixAt_apply, mul_comm,
    Pi.zero_apply] using h

/-- At a nonzero multiple of a representative of a point of `X`, the differential of the
polynomial of `X` is nonzero, since `X` is smooth. -/
private theorem polyDeriv_ne_zero (x : X) {c : ℂ} (hc : c ≠ 0) :
    X.polyDeriv (c • (x : ℙ ℂ (Fin (n + 2) → ℂ)).rep) ≠ 0 := by
  obtain ⟨i, hi⟩ := X.smooth _ (by rw [← carrier_def]; exact x.property)
  intro h
  have := congrArg (fun f : (Fin (n + 2) → ℂ) →L[ℂ] ℂ ↦ f (Pi.single i 1)) h
  rw [zero_apply, polyDeriv_smul, polyDeriv_apply] at this
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at this
  exact mul_ne_zero (pow_ne_zero _ hc) hi this

/-- The coordinate `j` of the normalized homogeneous coordinates is `1`. -/
private theorem chartLift_apply_indexAt (z : X) (y : Fin n → ℂ) :
    chartLift X z y ((twistCore (𝕜 := ℂ) 1).indexAt (z : ℙ ℂ (Fin (n + 2) → ℂ))) = 1 :=
  Fin.insertNth_apply_same (α := fun _ ↦ ℂ) _ _ _

/-- The differential of the polynomial of `X` at the normalized homogeneous coordinates `v` of `z`
vanishes on `v`. -/
private theorem polyDeriv_chartLift_chartAt (z : X) :
    X.polyDeriv (chartLift X z (chartAt (Fin n → ℂ) z z))
      (chartLift X z (chartAt (Fin n → ℂ) z z)) = 0 := by
  refine X.polyDeriv_self_eq_zero ?_
  rw [X.chartLift_chartAt z, X.isHomogeneous.eval_smul, X.mem_carrier_iff.1 z.property, mul_zero]

/-- **The tangent space of `X` in homogeneous coordinates.** The derivative of the normalized
homogeneous coordinates at the image of `z` has for range the vectors whose coordinate `j`
vanishes and on which the differential of the polynomial of `X` vanishes. Both are hyperplanes,
distinct since the second contains `v`, and the derivative is injective on the `n`-dimensional
model. -/
private theorem range_fderiv_chartLift (z : X) :
    LinearMap.range (fderiv ℂ (chartLift X z)
      (chartAt (Fin n → ℂ) z z)).toLinearMap =
      LinearMap.ker (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 2) ↦ ℂ)
        ((twistCore (𝕜 := ℂ) 1).indexAt (z : ℙ ℂ (Fin (n + 2) → ℂ)))).toLinearMap ⊓
      LinearMap.ker (X.polyDeriv
        (chartLift X z (chartAt (Fin n → ℂ) z z))).toLinearMap := by
  set j := (twistCore (𝕜 := ℂ) 1).indexAt (z : ℙ ℂ (Fin (n + 2) → ℂ))
  set v := chartLift X z (chartAt (Fin n → ℂ) z z)
  set f : (Fin (n + 2) → ℂ) →ₗ[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ ↦ ℂ) j).toLinearMap
  set g : (Fin (n + 2) → ℂ) →ₗ[ℂ] ℂ := (X.polyDeriv v).toLinearMap
  have hc : ((z : ℙ ℂ (Fin (n + 2) → ℂ)).rep j)⁻¹ ≠ 0 :=
    inv_ne_zero (rep_indexAt_twistCore_ne_zero 1 _)
  have hv : v = ((z : ℙ ℂ (Fin (n + 2) → ℂ)).rep j)⁻¹ • (z : ℙ ℂ (Fin (n + 2) → ℂ)).rep :=
    X.chartLift_chartAt z
  have hfv : f v = 1 := X.chartLift_apply_indexAt z _
  have hgv : g v = 0 := X.polyDeriv_chartLift_chartAt z
  have hg : g ≠ 0 := fun h ↦ X.polyDeriv_ne_zero z hc (by
    rw [← hv]
    exact ContinuousLinearMap.coe_injective h)
  -- The kernel of `g` is a hyperplane, which `ker f` cuts in codimension one since `v` lies in
  -- the first only.
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hg
  have hfg := Module.Dual.finrank_ker_inf_add_one (f := f) (U := LinearMap.ker g) fun h ↦ by
    simp [LinearMap.mem_ker.1 (h (LinearMap.mem_ker.2 hgv))] at hfv
  rw [Module.finrank_fin_fun] at hker
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨u, rfl⟩
    exact ⟨congrArg (fun L : _ →L[ℂ] ℂ ↦ L u) (X.proj_comp_fderiv_chartLift z),
      congrArg (fun L : _ →L[ℂ] ℂ ↦ L u) (X.polyDeriv_comp_fderiv_chartLift z)⟩
  · rw [LinearMap.finrank_range_of_inj (X.injective_fderiv_chartLift z), Module.finrank_fin_fun]
    omega

/-- The derivative `ℓ ∘ D` of the section given by `ℓ` at a zero `z` is surjective exactly when
`ℓ` has a zero on which the differential of the polynomial of `X` at `z` does not vanish. -/
private theorem surjective_comp_fderiv_chartLift_iff {ℓ : (Fin (n + 2) → ℂ) →ₗ[ℂ] Fin n → ℂ}
    (hℓ : Function.Surjective ℓ) {z : X} (hz : ℓ (z : ℙ ℂ (Fin (n + 2) → ℂ)).rep = 0) :
    Function.Surjective ((LinearMap.toContinuousLinearMap ℓ).comp
      (fderiv ℂ (chartLift X z) (chartAt (Fin n → ℂ) z z))) ↔
      ∃ w, ℓ w = 0 ∧ ∑ i, w i * eval (z : ℙ ℂ (Fin (n + 2) → ℂ)).rep (pderiv i X.poly) ≠ 0 := by
  set j := (twistCore (𝕜 := ℂ) 1).indexAt (z : ℙ ℂ (Fin (n + 2) → ℂ))
  set D := fderiv ℂ (chartLift X z) (chartAt (Fin n → ℂ) z z)
  set v := chartLift X z (chartAt (Fin n → ℂ) z z)
  set c := ((z : ℙ ℂ (Fin (n + 2) → ℂ)).rep j)⁻¹
  have hc : c ≠ 0 :=
    inv_ne_zero (rep_indexAt_twistCore_ne_zero 1 _)
  have hv : v = c • (z : ℙ ℂ (Fin (n + 2) → ℂ)).rep := X.chartLift_chartAt z
  have hD := X.injective_fderiv_chartLift z
  -- Surjectivity is injectivity, as source and target both have dimension `n`.
  rw [← ContinuousLinearMap.coe_coe, ← LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl]
  have hinj : Function.Injective ((LinearMap.toContinuousLinearMap ℓ).comp D).toLinearMap ↔
      LinearMap.ker ℓ ⊓ LinearMap.range D.toLinearMap = ⊥ := by
    rw [← LinearMap.ker_eq_bot, ContinuousLinearMap.toLinearMap_comp, LinearMap.ker_comp, inf_comm,
      ← Submodule.map_comap_eq, ← Submodule.map_bot D.toLinearMap,
      (Submodule.map_injective_of_injective hD).eq_iff, LinearMap.coe_toContinuousLinearMap]
  have hℓk : Module.finrank ℂ (LinearMap.ker ℓ) = 2 := by
    rw [ℓ.finrank_ker_eq_sub_of_surjective hℓ, Module.finrank_fin_fun, Module.finrank_fin_fun]
    omega
  rw [hinj, X.range_fderiv_chartLift z, ← inf_assoc,
    Submodule.inf_ker_inf_ker_eq_bot_iff hℓk
      (v := v) (by rw [LinearMap.mem_ker, hv, map_smul, hz, smul_zero])
      (by
        rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.proj_apply]
        exact (X.chartLift_apply_indexAt z _).trans_ne one_ne_zero)
      (X.polyDeriv_chartLift_chartAt z)]
  refine exists_congr fun w ↦ and_congr LinearMap.mem_ker ?_
  rw [ContinuousLinearMap.coe_coe, X.chartLift_chartAt z, polyDeriv_smul, polyDeriv_apply]
  exact mul_ne_zero_iff.trans (and_iff_right (pow_ne_zero _ hc))

/-- **Transversality of the section given by linear forms.** Let `ℓ : ℂ^{n+2} → ℂ^n` be
surjective, and `z` a zero of the section of `X.embedding^* 𝒪(1)^{⊕n}` that it gives. The
linearization of that section at `z`, over the underlying real manifold of `X`, is surjective
exactly when some `w` with `ℓ w = 0` has `∑ i, w i * ∂f/∂x_i (z.rep) ≠ 0`, where `f` is the
polynomial of `X`: the line `{ℓ = 0}` is transverse to `X` at `z`. -/
theorem surjective_sectionLinearization_linearSection_iff
    {ℓ : (Fin (n + 2) → ℂ) →ₗ[ℂ] Fin n → ℂ} (hℓ : Function.Surjective ℓ) {z : X}
    (hz : X.linearSection ℓ z = 0) :
    Function.Surjective (TauCeti.sectionLinearization 𝓘(ℝ, Fin n → ℂ)
      (F := Fin n → ℂ) id (X.linearSection ℓ) z) ↔
      ∃ w, ℓ w = 0 ∧ ∑ i, w i * eval (z : ℙ ℂ (Fin (n + 2) → ℂ)).rep (pderiv i X.poly) ≠ 0 := by
  have hc := contMDiffAt_totalSpace_iff.1 ((X.linearSection ℓ).contMDiff z)
  have hs := hc.2.mdifferentiableAt (by simp)
  rw [TauCeti.surjective_sectionLinearization_iff continuousAt_id
    (mem_baseSet_trivializationAt _ _ z) hs hz]
  rw [← TauCeti.fderiv_comp_chartAt_symm]
  simp only [Function.comp_def, id_eq]
  rw [(X.hasFDerivAt_trivializationAt_linearSection ℓ z).fderiv]
  -- The map is read on the tangent space of `X` at `z`, the model space by definition, so the
  -- restriction of scalars, which `ContinuousLinearMap.coe_restrictScalars'` cannot rewrite
  -- there, has the same underlying function.
  exact X.surjective_comp_fderiv_chartLift_iff hℓ ((X.linearSection_eq_zero_iff ℓ z).1 hz)

/-- **At a transverse zero the derivative is a complex isomorphism.** Let `ℓ : ℂ^{n+2} → ℂ^n` be
surjective, `z` a zero of the section given by `ℓ`, and suppose that some `w` with `ℓ w = 0`
has `∑ i, w i * ∂f/∂x_i (z.rep) ≠ 0`, `f` being the polynomial of `X`. Then, read in the chart
`chartAt _ z` of `X` and the trivialization `trivializationAt _ _ z` of the pull-back, the section
has at the image of `z` the real derivative of a `ℂ`-linear isomorphism. -/
theorem exists_continuousLinearEquiv_hasFDerivAt_trivializationAt_linearSection
    {ℓ : (Fin (n + 2) → ℂ) →ₗ[ℂ] Fin n → ℂ} (hℓ : Function.Surjective ℓ) {z : X}
    (hz : X.linearSection ℓ z = 0)
    (htr : ∃ w, ℓ w = 0 ∧ ∑ i, w i * eval (z : ℙ ℂ (Fin (n + 2) → ℂ)).rep (pderiv i X.poly) ≠ 0) :
    ∃ A : (Fin n → ℂ) ≃L[ℂ] Fin n → ℂ,
      HasFDerivAt (fun y ↦ (trivializationAt (Fin n → ℂ)
        (X.embedding *ᵖ (twistPiCore (𝕜 := ℂ) (n := n + 1) 1 (Fin n)).Fiber) z
        ⟨(chartAt (Fin n → ℂ) z).symm y,
          X.linearSection ℓ ((chartAt (Fin n → ℂ) z).symm y)⟩).2)
        ((A : (Fin n → ℂ) →L[ℂ] Fin n → ℂ).restrictScalars ℝ)
        (chartAt (Fin n → ℂ) z z) := by
  set B := (LinearMap.toContinuousLinearMap ℓ).comp
    (fderiv ℂ (chartLift X z) (chartAt (Fin n → ℂ) z z))
  have hsurj : Function.Surjective B :=
    (X.surjective_comp_fderiv_chartLift_iff hℓ ((X.linearSection_eq_zero_iff ℓ z).1 hz)).2 htr
  have hinj : Function.Injective B.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).2 hsurj
  refine ⟨ContinuousLinearEquiv.ofBijective B (LinearMap.ker_eq_bot.2 hinj)
    (LinearMap.range_eq_top.2 hsurj), ?_⟩
  rw [ContinuousLinearEquiv.coe_ofBijective]
  exact X.hasFDerivAt_trivializationAt_linearSection ℓ z

/-- **The transversality condition along a parametrized line.** Let `L : ℂ² → ℂ^{n+2}` be injective
with range the kernel of `ℓ`, and let the point `p` of `ℂℙ¹` go to the point `z` of `X`. Then
`ℓ` has a zero on which the differential of the polynomial of `X` at `z` does not vanish
exactly when that differential at `L p.rep` does not vanish on the range of `L`; the latter is
the hypothesis `htr` of `SmoothProjectiveHypersurface.card_inter_line` at `p`. -/
theorem exists_sum_mul_eval_pderiv_ne_zero_iff {κ : Type*} {ℓ : (Fin (n + 2) → ℂ) →ₗ[ℂ] κ → ℂ}
    {L : (Fin 2 → ℂ) →ₗ[ℂ] Fin (n + 2) → ℂ} (hL : Function.Injective L)
    (hrange : LinearMap.range L = LinearMap.ker ℓ) {p : ℙ ℂ (Fin 2 → ℂ)} {z : X}
    (hp : Projectivization.map L hL p = z) :
    (∃ w, ℓ w = 0 ∧ ∑ i, w i * eval (z : ℙ ℂ (Fin (n + 2) → ℂ)).rep (pderiv i X.poly) ≠ 0) ↔
      ∃ w, ∑ i, L w i * eval (L p.rep) (pderiv i X.poly) ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep ℂ (L p.rep) (by simpa using hL.ne p.rep_ne_zero)
  rw [← Projectivization.map_mk L hL p.rep p.rep_ne_zero, mk_rep, hp] at ha
  simp only [← polyDeriv_apply, ← ha, Units.smul_def, polyDeriv_smul, ne_eq, mul_eq_zero,
    pow_eq_zero_iff', a.ne_zero, false_and, false_or]
  constructor
  · rintro ⟨w, hw, hne⟩
    obtain ⟨u, rfl⟩ : w ∈ LinearMap.range L := hrange ▸ LinearMap.mem_ker.2 hw
    exact ⟨u, hne⟩
  · rintro ⟨u, hu⟩
    exact ⟨L u, LinearMap.mem_ker.1 (hrange ▸ LinearMap.mem_range_self L u), hu⟩

end Transversality

end SmoothProjectiveHypersurface

end SymplecticGeometry
