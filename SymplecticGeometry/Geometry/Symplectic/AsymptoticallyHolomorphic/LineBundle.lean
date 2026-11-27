/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.RealImage
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hermitian.RealChernClass
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle
public import SymplecticGeometry.Geometry.Manifold.Projectivization.TwistCore
public import TauCeti.Geometry.Manifold.SmoothSingular.SingularCohomology
public import TauCeti.Topology.VectorBundle.Orientation.Complex.EulerClass
import SymplecticGeometry.Geometry.Manifold.SmoothSingular.DeRham.MayerVietoris.Induction
import SymplecticGeometry.Topology.VectorBundle.Pullback
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hermitian.ChernWeil
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hermitian.Realization

/-!
# The prequantum line bundle

Let `M` be a compact boundaryless smooth manifold and `σ` a closed two-form on `M`, for instance
a symplectic form, and let `a ∈ H²(M; ℤ)` (with `ULift ℤ` values) be an integral lift of the de
Rham class of `σ`: its image in real singular cohomology is `TauCeti.deRhamHom` of `[σ]`. This
file builds a Hermitian line bundle `L` over `M` with a unitary connection of curvature
`-2π i σ` (`SymplecticGeometry.exists_prequantumLineBundle`). In the library's normalization of
circle connection forms (`SymplecticGeometry.IsCircleConnectionForm`), this is a connection form
`α` on the unitary frame bundle of `L` with `hα.curvature = -(2 * π) • σ`.

The bundle is the pull-back `f^* 𝒪(1)` of Tau Ceti's `Projectivization.twistCore 1` along a
smooth map `f : M → ℂPᴺ` with Euler class `-a`
(`SymplecticGeometry.exists_hermitianLineBundle_complexEulerClass_eq`), with any smooth Hermitian
metric. Under the library's signs, `deRhamHom` of the real first Chern class of such a bundle is
minus the real image of its Euler class
(`SymplecticGeometry.Bundle.deRhamHom_realFirstChernClass_eq_neg`), so it is the image of `a`,
which is `deRhamHom [σ]`. By the de Rham theorem on a compact manifold
(`TauCeti.injective_deRhamHom`), the real first Chern class of `L` is `[σ]`. So `-2π σ` is the
curvature of a connection form (`Bundle.ContMDiffRiemannianMetric.isConnectionCurvature_iff`): an
arbitrary connection form, corrected by the pull-back of a primitive of the difference of the two
curvatures (`SymplecticGeometry.exists_isCircleConnectionForm_curvature_eq_iff`).

The Euler class of `L` is `-a`, not `a`: the bundle with curvature `-2π i σ` has real first Chern
class `[σ]`, and its Euler class is minus the integral class that lifts it.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.4
  (the line bundle of Donaldson's construction) and Theorem 2.7.4.
* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
-/

public section

noncomputable section

open Bundle Module TauCeti
open Projectivization (twistCore)
open scoped LinearAlgebra.Projectivization Manifold ContDiff VectorBundle.ComplexToReal

namespace SymplecticGeometry

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]

/-- **The prequantum line bundle.** Let `M` be a compact boundaryless smooth manifold, `σ` a
closed two-form on `M`, and `a ∈ H²(M; ℤ)` (with `ULift ℤ` values) an integral lift of `[σ]`: the
image of `a` in real singular cohomology is the image of `[σ]` under the de Rham homomorphism.
Then there are a smooth map `f : M → ℂPᴺ`, for some `N`, and a smooth Hermitian metric `g` on the
pull-back `L = f^* 𝒪(1)` of Tau Ceti's `Projectivization.twistCore 1`, such that the Euler class
of `L` is `-a` and `-2π σ` is the curvature of a connection form on the circle bundle of
`g`-unitary frames of `L` (`Bundle.ContMDiffRiemannianMetric.IsConnectionCurvature`). -/
theorem exists_prequantumLineBundle (σ : SmoothForm I M ℝ 2) (hσ : σ ∈ closedForms I M 2)
    (a : (TopCat.of M).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) 2)
    (ha : (TopCat.of M).singularCohomologyRealImageAddMonoidHom 2 a =
      deRhamHom I M 2 (deRhamCohomology.mk I 2 ⟨σ, hσ⟩)) :
    ∃ (N : ℕ) (f : C(M, ℙ ℂ (Fin (N + 1) → ℂ))) (hf : ContMDiff I 𝓘(ℝ, Fin N → ℂ) ∞ f)
      (g : ContMDiffRiemannianMetric I ∞ ℂ ((⇑f) *ᵖ (twistCore (𝕜 := ℂ) (n := N) 1).Fiber))
      (hI : ∀ x v w, g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w),
      complexEulerClass (r := 0) ℂ ((⇑f) *ᵖ (twistCore (𝕜 := ℂ) (n := N) 1).Fiber)
          (finrank_self ℂ) = -a ∧
        haveI := _root_.Bundle.Pullback.contMDiffVectorBundle (F := ℂ)
          (E := (twistCore (𝕜 := ℂ) (n := N) 1).Fiber) hf
        g.IsConnectionCurvature hI (-(2 * Real.pi) • σ) := by
  obtain ⟨N, f, hf, -, he⟩ := exists_hermitianLineBundle_complexEulerClass_eq (I := I) (-a)
  have := _root_.Bundle.Pullback.contMDiffVectorBundle (F := ℂ)
    (E := (twistCore (𝕜 := ℂ) (n := N) 1).Fiber) hf
  obtain ⟨g, hI⟩ := exists_contMDiffRiemannianMetric_inner_smul_I (IB := I) (n := ⊤) (F := ℂ)
    (V := (⇑f) *ᵖ (twistCore (𝕜 := ℂ) (n := N) 1).Fiber)
  refine ⟨N, f, hf, g, hI, he, ?_⟩
  -- By Chern–Weil and the de Rham theorem, the real first Chern class of `L` is `[σ]`.
  have hc : g.realFirstChernClass hI = deRhamCohomology.mk I 2 ⟨σ, hσ⟩ := by
    refine injective_deRhamHom (I := I) 2 ?_
    rw [Bundle.deRhamHom_realFirstChernClass_eq_neg f hf g hI, he, map_neg, neg_neg, ha]
  rw [g.isConnectionCurvature_iff hI (Submodule.smul_mem _ (-(2 * Real.pi)) hσ), hc,
    ← _root_.map_smul, SetLike.mk_smul_mk]
  congr 2
  rw [smul_smul, neg_mul_neg, inv_mul_cancel₀ (by simp [Real.pi_ne_zero]), one_smul]

end SymplecticGeometry

end
