/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import TauCeti.Geometry.Manifold.SmoothApprox.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Hermitian
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
public import TauCeti.Topology.VectorBundle.Orientation.Complex.EulerClass
public import TauCeti.Topology.FiberBundle.Pullback
import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralCohomologyULift
import SymplecticGeometry.Geometry.Manifold.Projectivization.ClassifyingMap
import SymplecticGeometry.Geometry.Manifold.Projectivization.TwistCore
import SymplecticGeometry.Topology.VectorBundle.Orientation.Complex.Tensor
import SymplecticGeometry.Topology.VectorBundle.Pullback

/-!
# Hermitian line bundles with a prescribed Euler class

Let `M` be a compact boundaryless smooth manifold. This file shows that every class
`b ∈ H²(M; ℤ)` is the Euler class of a smooth Hermitian line bundle: for some `N` there is a smooth
map `f : M → ℙ ℂ (Fin (N + 1) → ℂ)` such that the pull-back `f^* 𝒪(1)` of Tau Ceti's line bundle
`Projectivization.twistCore 1` carries a smooth Hermitian metric and has Euler class `b`
(`SymplecticGeometry.exists_hermitianLineBundle_complexEulerClass_eq`). Integral classes have
`ULift ℤ` values, as for `TauCeti.complexEulerClass`.

## Proof

Read in integral cohomology through `TopCat.uliftIntegralCohomologyIso`, the class `b` is the
pull-back of the hyperplane class `h` along a continuous map `M → ℙ ℂ (Fin (N + 1) → ℂ)`, with
`N = dim M` (`Projectivization.exists_continuousMap_projectivization_pullback_eq_of_isManifold`).
Tau Ceti's Whitney approximation `ContinuousMap.exists_contMDiff_homotopic` replaces it by a
homotopic smooth map `f`. The Euler class of `f^* 𝒪(1)` is the pull-back of that of `𝒪(1)`
(`TauCeti.complexEulerClass_pullback`), which is `h`
(`Projectivization.complexEulerClass_twistCore_one`).
The bundle `f^* 𝒪(1)` is a smooth real vector bundle, so it has a smooth metric invariant under
multiplication by `i` (`TauCeti.exists_contMDiffRiemannianMetric_inner_smul_I`).

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.3 (maps into
  `ℂPᴺ`).
-/

public section

noncomputable section

open Bundle CategoryTheory Module TauCeti
open Projectivization (twistCore)
open scoped LinearAlgebra.Projectivization Manifold ContDiff VectorBundle.ComplexToReal

namespace SymplecticGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]

/-- **Every integral class of degree two is the Euler class of a Hermitian line bundle.** On a
compact boundaryless smooth manifold `M`, every class `b ∈ H²(M; ℤ)` (with `ULift ℤ` values) is
the Euler class of the pull-back `f^* 𝒪(1)` of Tau Ceti's `Projectivization.twistCore 1` along a
smooth map `f : M → ℙ ℂ (Fin (N + 1) → ℂ)`, for some `N`; this bundle carries a smooth real
metric invariant under multiplication by `Complex.I`, that is, a smooth Hermitian metric. -/
theorem exists_hermitianLineBundle_complexEulerClass_eq
    (b : (TopCat.of M).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) 2) :
    ∃ (N : ℕ) (f : C(M, ℙ ℂ (Fin (N + 1) → ℂ))), ContMDiff I 𝓘(ℝ, Fin N → ℂ) ∞ f ∧
      (∃ g : ContMDiffRiemannianMetric I ∞ ℂ ((⇑f) *ᵖ (twistCore (𝕜 := ℂ) (n := N) 1).Fiber),
        ∀ x v w, g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w) ∧
      complexEulerClass (r := 0) ℂ ((⇑f) *ᵖ (twistCore (𝕜 := ℂ) (n := N) 1).Fiber)
        (finrank_self ℂ) = b := by
  set N := finrank ℝ E
  obtain ⟨f₀, hf₀⟩ :=
    Projectivization.exists_continuousMap_projectivization_pullback_eq_of_isManifold I
      (N := N) (by omega) (((TopCat.of M).uliftIntegralCohomologyIso 2).hom b)
  obtain ⟨f, hf, hff⟩ := f₀.exists_contMDiff_homotopic (I := I) (J := 𝓘(ℝ, Fin N → ℂ)) ⊤
  refine ⟨N, f, hf, ?_, ?_⟩
  · have := Bundle.Pullback.contMDiffVectorBundle (F := ℂ)
      (E := (twistCore (𝕜 := ℂ) (n := N) 1).Fiber) hf
    exact exists_contMDiffRiemannianMetric_inner_smul_I (IB := I) (n := ⊤) (F := ℂ)
      (V := (⇑f) *ᵖ (twistCore (𝕜 := ℂ) (n := N) 1).Fiber)
  · apply (ConcreteCategory.bijective_of_isIso ((TopCat.of M).uliftIntegralCohomologyIso 2).hom).1
    rw [complexEulerClass_pullback, TopCat.uliftIntegralCohomologyIso_naturality_apply,
      Projectivization.complexEulerClass_twistCore_one, ← hf₀,
      TopCat.Homotopy.congr_singularCohomologyMap (f := TopCat.ofHom f₀) (g := TopCat.ofHom f)
        hff.some _ ℤ _ 2]

end SymplecticGeometry

end
