/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.ComplexStructure.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Riemannian.Trivial
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Hermitian
public import TauCeti.Geometry.Manifold.VectorBundle.Trivial
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
public import SymplecticGeometry.LinearAlgebra.Complex.FiniteDimensional
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic

/-!
# The symplectic form of a Hermitian bundle

A Hermitian bundle is here, as in Tau Ceti, a complex vector bundle `V` with a real bundle metric
`g` that multiplication by `Complex.I` preserves (`hI`). Its symplectic form is no new definition:
it is `(ofComplexModule I n F V).compatibleForm g`, the form `ω_{g,J}` of `g` and of the complex
structure `J` given by multiplication by `Complex.I`. Its compatibility with `J`, hence its
nondegeneracy, and its smoothness are those of `compatibleForm`. This file computes it.

## Main results

* `ContMDiffComplexStructure.compatibleForm_ofComplexModule_apply`: under `hI`, the form is
  `ω_x(v, w) = g_x(i v, w)`; and `compatibleForm_ofComplexModule_apply_smul_I`,
  `ω_x(v, i w) = g_x(v, w)`.
* `ContMDiffComplexStructure.im_inner_eq_compatibleForm_ofComplexModule`: the form is the
  imaginary part of the Hermitian product `g.complexInnerProductSpace hI x`.
* `ContMDiffComplexStructure.compatibleForm_ofComplexModule_trivial`: on the trivial bundle with
  fibre `ι → ℂ` and any metric that `TauCeti.complexToRealEuclidean ι` carries to the Euclidean
  one, that map carries the form to the constant standard form `stdForm ι`. So the sign agrees
  with the standard model, where `stdForm ι z w = ⟪J₀ z, w⟫`.
* `ContMDiffComplexStructure.compatibleForm_ofComplexModule_constComplexEuclidean`: the same for
  the constant metric `Bundle.ContMDiffRiemannianMetric.constComplexEuclidean ι`.

The smoothness of the fibrewise map `TauCeti.complexToRealEuclidean ι` on total spaces is
Tau Ceti's `TauCeti.contMDiff_bundleMap_of_constant_coordinates`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
-/

public section

noncomputable section

open _root_.Bundle
open scoped Manifold

namespace SymplecticGeometry.Bundle.ContMDiffComplexStructure

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M] {n : ℕ∞}

section Hermitian

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousConstSMul ℂ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]

open scoped VectorBundle.ComplexToReal Module.ComplexToReal

variable (g : ContMDiffRiemannianMetric I n F V)
  (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
include hI

/-- For a metric invariant under `Complex.I`, the form `ω_{g,J}` of `g` and of multiplication by
`Complex.I` is `ω_x(v, w) = g_x(i v, w)`. -/
theorem compatibleForm_ofComplexModule_apply (x : M) (v w : V x) :
    (ofComplexModule I n F V).compatibleForm g x ![v, w] = g.inner x (Complex.I • v) w := by
  simpa only [ofComplexModule_apply] using
    compatibleForm_apply_of_invariant (g := g) (J := ofComplexModule I n F V)
      (by simpa only [ofComplexModule_apply] using hI) x v w

/-- For a metric invariant under `Complex.I`, the form `ω_{g,J}` of `g` and of multiplication by
`Complex.I` is `ω_x(v, i w) = g_x(v, w)`. -/
theorem compatibleForm_ofComplexModule_apply_smul_I (x : M) (v w : V x) :
    (ofComplexModule I n F V).compatibleForm g x ![v, Complex.I • w] = g.inner x v w := by
  rw [compatibleForm_ofComplexModule_apply g hI, hI]

/-- For a metric invariant under `Complex.I`, the form `ω_{g,J}` of `g` and of multiplication by
`Complex.I` is the imaginary part of the Hermitian product `g.complexInnerProductSpace hI x`. -/
theorem im_inner_eq_compatibleForm_ofComplexModule (x : M) (v w : V x) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI := g.complexInnerProductSpace hI x
    (inner ℂ v w).im = (ofComplexModule I n F V).compatibleForm g x ![v, w] := by
  rw [ContMDiffRiemannianMetric.complexInnerProductSpace_inner,
    compatibleForm_ofComplexModule_apply g hI]
  simp

end Hermitian

section Standard

variable (ι : Type*) [Fintype ι]

/-- The standard case. On the trivial bundle `M × (ι → ℂ)`, let `g` be a metric with
`g_x(u, v) = ⟪c u, c v⟫` for `c = TauCeti.complexToRealEuclidean ι`, such as
`Bundle.ContMDiffRiemannianMetric.constComplexEuclidean ι`. Then the fibrewise map `c` carries
the form of `g` and of multiplication by `Complex.I` to the constant standard form `stdForm ι`
on `M × StdSpace ι`: the transport of the one along `c` is the other. -/
theorem compatibleForm_ofComplexModule_trivial
    (g : ContMDiffRiemannianMetric I n (ι → ℂ) (Trivial M (ι → ℂ)))
    (hg : ∀ x (u v : ι → ℂ), g.inner x u v =
      inner ℝ (TauCeti.complexToRealEuclidean ι u) (TauCeti.complexToRealEuclidean ι v)) :
    ContMDiffTwoForm.pushforward (fun _ ↦ TauCeti.complexToRealEuclidean ι)
        (TauCeti.contMDiff_bundleMap_of_constant_coordinates (E₁ := Trivial M (ι → ℂ))
          (E₂ := Trivial M (StdSpace ι)) (fun _ ↦ TauCeti.complexToRealEuclidean ι)
          (TauCeti.complexToRealEuclidean ι).toContinuousLinearMap fun _ _ _ _ ↦ by simp)
        ((ofComplexModule I n (ι → ℂ) (Trivial M (ι → ℂ))).compatibleForm g) =
      ContMDiffTwoForm.const (stdForm ι) := by
  refine (ContMDiffTwoForm.pushforward_eq_iff _ _).2 fun x v w ↦ ?_
  rw [ContMDiffTwoForm.bilinFormAt_apply, ContMDiffTwoForm.const_apply,
    ContMDiffTwoForm.bilinFormAt_apply, compatibleForm_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ofComplexModule_apply, hg,
    stdForm_apply_eq_inner_sub_inner, stdComplexStructure_complexToRealEuclidean]

/-- The standard case for the constant metric
`g₀ = Bundle.ContMDiffRiemannianMetric.constComplexEuclidean ι` on `M × (ι → ℂ)`, with
`g₀(u, v) = ⟪c u, c v⟫` for `c = TauCeti.complexToRealEuclidean ι`: the fibrewise map `c`
carries the form of `g₀` and of multiplication by `Complex.I` to the constant standard form
`stdForm ι` on `M × StdSpace ι`. -/
theorem compatibleForm_ofComplexModule_constComplexEuclidean :
    ContMDiffTwoForm.pushforward (fun _ ↦ TauCeti.complexToRealEuclidean ι)
        (TauCeti.contMDiff_bundleMap_of_constant_coordinates (E₁ := Trivial M (ι → ℂ))
          (E₂ := Trivial M (StdSpace ι)) (fun _ ↦ TauCeti.complexToRealEuclidean ι)
          (TauCeti.complexToRealEuclidean ι).toContinuousLinearMap fun _ _ _ _ ↦ by simp)
        ((ofComplexModule I n (ι → ℂ) (Trivial M (ι → ℂ))).compatibleForm
          (ContMDiffRiemannianMetric.constComplexEuclidean ι)) =
      ContMDiffTwoForm.const (stdForm ι) :=
  compatibleForm_ofComplexModule_trivial ι _
    (ContMDiffRiemannianMetric.constComplexEuclidean_inner ι)

end Standard

end SymplecticGeometry.Bundle.ContMDiffComplexStructure

end
