/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralCohomologyULift
public import SymplecticGeometry.AlgebraicTopology.Cohomology.ProjectiveSpaceClassifying
public import SymplecticGeometry.Geometry.Manifold.Projectivization.TwistCore
public import SymplecticGeometry.Topology.VectorBundle.Orientation.Complex.Tensor
public import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import TauCeti.Geometry.Manifold.Morse.CWModel
public import TauCeti.Geometry.Manifold.Morse.Generic.Basic
public import TauCeti.Geometry.Manifold.Morse.Index
public import TauCeti.Geometry.Manifold.SmoothApprox.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Hermitian

/-!
# Hermitian line bundles with a prescribed Euler class

Let `M` be a compact boundaryless smooth manifold. This file shows that every class
`b ∈ H²(M; ℤ)` is the Euler class of a smooth Hermitian line bundle: for some `N` there is a smooth
map `f : M → ℙ ℂ (Fin (N + 1) → ℂ)` such that the pull-back `f^* 𝒪(1)` of Tau Ceti's line bundle
`Projectivization.twistCore 1` carries a smooth Hermitian metric and has Euler class `b`
(`exists_hermitianLineBundle_complexEulerClass_eq`). Integral classes have `ULift ℤ` values, as
for `TauCeti.complexEulerClass`.

## Main results

* `Projectivization.exists_continuousMap_projectivization_pullback_eq_of_isManifold`: on a compact
  manifold of dimension `N`, every class of `H²(M; ℤ)` is the pull-back of the hyperplane class
  of `ℙ ℂ (Fin (N + 1) → ℂ)` along a continuous map.
* `SymplecticGeometry.exists_hermitianLineBundle_complexEulerClass_eq`: the statement above.

## Proof

A Morse function on `M` gives a finite CW complex `W` homotopy equivalent to `M` whose cells have
dimension at most `N = dim M` (`TauCeti.IsMorse.exists_finite_cwComplex_homotopyEquiv`,
`TauCeti.manifoldMorseIndex_le_finrank`), the argument of Tau Ceti's
`TauCeti.FiniteCWType.of_isManifold` with control of the dimensions of the cells.
The class `b`, carried to `W` and read in integral cohomology through
`TopCat.uliftIntegralCohomologyIso`, is the pull-back of the hyperplane class `h` along a map
`W → ℙ ℂ (Fin (N + 1) → ℂ)` (`Projectivization.exists_continuousMap_projectivization_pullback_eq`).
Composed with the homotopy equivalence `M → W`, this gives a map pulling `h` back to `b`, by
homotopy invariance (`TopCat.Homotopy.congr_singularCohomologyMap`). Tau Ceti's Whitney
approximation `ContinuousMap.exists_contMDiff_homotopic_of_isCompact_closure_range` replaces it
by a homotopic smooth map `f`. The Euler class of `f^* 𝒪(1)` is the pull-back of that of `𝒪(1)`
(`TauCeti.complexEulerClass_pullback`), which is `h`
(`Projectivization.complexEulerClass_twistCore_one`).
The bundle `f^* 𝒪(1)` is a smooth real vector bundle, so it has a smooth metric invariant under
multiplication by `i` (`TauCeti.exists_contMDiffRiemannianMetric_inner_smul_I`).

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.3 (maps into
  `ℂPᴺ` and line bundles classified by `H²`).
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 (the CW model of a manifold from a Morse function).
-/

public section

noncomputable section

open Bundle CategoryTheory Module Set TauCeti Topology.RelCWComplex
open Projectivization (twistCore)
open scoped LinearAlgebra.Projectivization Manifold ContDiff VectorBundle.ComplexToReal

namespace SymplecticGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]

variable (I) in
include I in
/-- **Classes of degree two on a compact manifold come from complex projective space.** Let `M` be
a compact boundaryless smooth manifold of dimension `N`. Every class `b ∈ H²(M; ℤ)` is the
pull-back `f^* h` of the hyperplane class `h` of `ℙ ℂ (Fin (N + 1) → ℂ)` along some continuous
map `f : M → ℙ ℂ (Fin (N + 1) → ℂ)`. -/
theorem _root_.Projectivization.exists_continuousMap_projectivization_pullback_eq_of_isManifold
    (b : (TopCat.of M).integralCohomology 2) :
    ∃ f : C(M, ℙ ℂ (Fin (finrank ℝ E + 1) → ℂ)),
      TopCat.singularCohomologyMap (TopCat.ofHom f) 2
        (Projectivization.hyperplaneClass (Fin (finrank ℝ E + 1) → ℂ)) = b := by
  obtain ⟨φ, hφ⟩ := exists_isMorse (I := I) (M := M)
  obtain ⟨W, _, _, _, -, ⟨e⟩, hcell⟩ := hφ.exists_finite_cwComplex_homotopyEquiv
  -- The `m`-cells of `W` are critical points of index `m ≤ dim M`.
  have hW : ∀ m, 2 * finrank ℝ E < m → IsEmpty (cell (univ : Set W) m) := fun m hm ↦ by
    obtain ⟨σ⟩ := hcell m
    refine ⟨fun c ↦ ?_⟩
    have h := (σ c).property.2
    have := manifoldMorseIndex_le_finrank (I := I) (f := φ) (x := (σ c : M))
    omega
  -- Carry `b` to the CW complex `univ ⊆ W`, homotopy equivalent to `M`.
  let e' : ContinuousMap.HomotopyEquiv (univ : Set W) M :=
    (Homeomorph.Set.univ W).toHomotopyEquiv.trans e
  obtain ⟨F, hF⟩ := Projectivization.exists_continuousMap_projectivization_pullback_eq
    (C := (univ : Set W)) (N := finrank ℝ E) hW
    (TopCat.singularCohomologyMap (TopCat.ofHom e'.toFun) 2 b)
  refine ⟨F.comp e'.invFun, ?_⟩
  rw [TopCat.ofHom_comp, TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply, hF,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    TopCat.Homotopy.congr_singularCohomologyMap
      (f := TopCat.ofHom e'.invFun ≫ TopCat.ofHom e'.toFun) (g := 𝟙 _) e'.right_inv.some _ ℤ _ 2,
    TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]

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
    (((TopCat.of M).uliftIntegralCohomologyIso 2).hom b)
  obtain ⟨f, hf, hff⟩ := f₀.exists_contMDiff_homotopic_of_isCompact_closure_range
    (I := I) (J := 𝓘(ℝ, Fin N → ℂ)) ⊤ (isCompact_range f₀.continuous).closure
  refine ⟨N, f, hf, ?_, ?_⟩
  · have : ContMDiffVectorBundle ∞ ℂ (twistCore (𝕜 := ℂ) (n := N) 1).Fiber
        𝓘(ℝ, Fin N → ℂ) :=
      have : ContMDiffVectorBundle ∞ ℂ (twistCore (𝕜 := ℂ) (n := N) 1).Fiber
          𝓘(ℂ, Fin N → ℂ) :=
        ContMDiffVectorBundle.of_le le_top
      ContMDiffVectorBundle.restrictScalars_modelWithCornersSelf ℝ this
    have := Bundle.Pullback.contMDiffVectorBundle (F := ℂ)
      (E := (twistCore (𝕜 := ℂ) (n := N) 1).Fiber) hf
    have : ∀ x, ContinuousSMul ℝ ((twistCore (𝕜 := ℂ) (n := N) 1).Fiber x) :=
      fun _ ↦ IsScalarTower.continuousSMul ℂ
    -- The metric lemma asks for continuity of the scalar action that comes from the module
    -- structure of the pull-back fibres, which instance search does not identify with the scalar
    -- action `Bundle.Pullback` declares; so the instance is stated with that action.
    have : ∀ x, @ContinuousConstSMul ℂ
        (((⇑f) *ᵖ (twistCore (𝕜 := ℂ) (n := N) 1).Fiber) x) _
        (Module.toDistribMulAction (R := ℂ)).toDistribSMul.toSMul :=
      fun x ↦ inferInstanceAs
        (ContinuousConstSMul ℂ ((twistCore (𝕜 := ℂ) (n := N) 1).Fiber (f x)))
    obtain ⟨g, hg⟩ := exists_contMDiffRiemannianMetric_inner_smul_I (IB := I) (n := ⊤) (F := ℂ)
      (V := (⇑f) *ᵖ (twistCore (𝕜 := ℂ) (n := N) 1).Fiber)
    exact ⟨g, hg⟩
  · apply (ConcreteCategory.bijective_of_isIso ((TopCat.of M).uliftIntegralCohomologyIso 2).hom).1
    rw [complexEulerClass_pullback, TopCat.uliftIntegralCohomologyIso_naturality_apply,
      Projectivization.complexEulerClass_twistCore_one, ← hf₀,
      TopCat.Homotopy.congr_singularCohomologyMap (f := TopCat.ofHom f₀) (g := TopCat.ofHom f)
        hff.some _ ℤ _ 2]

end SymplecticGeometry

end
