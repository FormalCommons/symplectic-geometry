/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.SurfaceGenus
public import SymplecticGeometry.Geometry.Manifold.Orientation.EulerCharacteristic
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.Basic
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.Gluing
public import SymplecticGeometry.Geometry.Symplectic.Manifold.ComplexOrientation
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Genus
public import TauCeti.Geometry.Manifold.Morse.CWModel
public import TauCeti.Geometry.Symplectic.Manifold.Volume
import SymplecticGeometry.Geometry.Manifold.Degree.Collapse
import SymplecticGeometry.Geometry.Symplectic.Manifold.Volume
import TauCeti.Geometry.Symplectic.Manifold.Sphere

/-!
# The axioms of the first Chern number of symplectic bundles over surfaces

This file states the axioms that characterize the first Chern number
`SymplecticGeometry.Bundle.symplecticChernNumber` of symplectic vector bundles over closed
connected oriented surfaces, proves that the number satisfies them, and that it is the only
assignment that does.

## Main definitions

* `SymplecticGeometry.ClosedConnectedOrientedSurface`: a closed connected surface with an
  orientation, as bundled data.
* `SymplecticGeometry.Bundle.SymplecticSurfaceBundle S`: a smooth vector bundle over `S` with a
  smooth nondegenerate two-form, as bundled data, with its symplectic isomorphisms
  `SymplecticSurfaceBundle.Iso`, and the pull-back `SymplecticSurfaceBundle.pullback`, the direct
  sum `SymplecticSurfaceBundle.whitneySum`, the trivial bundle `SymplecticSurfaceBundle.trivial`
  and the tangent bundle with an area form `SymplecticSurfaceBundle.tangent`, each the
  construction of the unbundled files packaged.
* `SymplecticGeometry.Bundle.SymplecticSurfaceBundle.symplecticChernNumber`: the first Chern
  number of such a bundle.
* `SymplecticGeometry.Bundle.ChernNumberAxioms c`: naturality, functoriality, additivity and
  normalization for an assignment `c` of an integer to every such bundle.

## Main results

* `symplecticChernNumber_tangent`: on a closed connected surface `M` with an area form `σ`
  inducing the orientation `o`, the tangent bundle with the form `σ` has first Chern number
  `2 - 2 g`, for `g = TauCeti.surfaceGenus M`.
* `SymplecticSurfaceBundle.symplecticChernNumber_nonempty_iso_iff`: bundles of equal rank are
  isomorphic exactly when their numbers agree;
  `SymplecticSurfaceBundle.symplecticChernNumber_eq_zero_iff` is the case of the trivial bundle,
  which has number `0` (`SymplecticSurfaceBundle.symplecticChernNumber_trivial`), and an
  isomorphism with the trivial bundle is a global symplectic frame
  (`SymplecticSurfaceBundle.Iso.isSymplecticFrameOn_trans_symm_toFun`).
* `chernNumberAxioms_symplecticChernNumber`: the first Chern number satisfies the axioms.
* `eq_symplecticChernNumber_of_chernNumberAxioms`: every assignment satisfying the axioms is the
  first Chern number.
* `existsUnique_chernNumberAxioms`: there is exactly one assignment satisfying the axioms.

## Proof

*Normalization.* Take a complex structure `J` on `TM` compatible with `σ`, so that the number is
that of the complex line bundle `(TM, J)` (`symplecticChernNumber_eq_chernNumber`): the Euler
class of `(TM, J)`, oriented as a complex line, evaluated on the fundamental class
(`firstChernClass_eq_complexEulerClass`). Since `σ` tames `J` and induces `o`, this Euler class
is that of `TM` oriented by `o`
(`TauCeti.SmoothTwoForm.IsNondegenerate.complexEulerClass_eq_eulerClass`). By Poincaré–Hopf its
evaluation is the Euler characteristic
(`TauCeti.Manifold.Orientation.evalFundamentalClass_eulerClass_eq_eulerChar_of_finiteCWType`).
The first Betti
number of `M` is even (`TauCeti.HomologicalOrientation.even_finrank_singularHomology_one`), so
the Euler characteristic is `2 - 2 g`
(`TauCeti.HomologicalOrientation.eulerChar_eq_two_sub_two_mul_genus_iff_even_finrank` and
`TauCeti.HomologicalOrientation.genus_eq_surfaceGenus`). The same route, for the complex
orientation of a complex manifold, gives
`SymplecticGeometry.evalFundamentalClass_chernClass_eq_eulerChar`.

*The other axioms* are the unbundled results `symplecticChernNumber_congr` and
`exists_pushforward_eq_of_symplecticChernNumber_eq` (naturality),
`symplecticChernNumber_pullback` with
`TauCeti.Manifold.Orientation.degree_toHomologicalOrientation_eq_degree` (functoriality) and
`symplecticChernNumber_whitneySum` (additivity).

*Uniqueness.* Let `c` satisfy the axioms, and fix `S`. By naturality `c` is constant on
isomorphism classes. A trivial bundle is isomorphic to its pull-back along a constant map, which
has degree `0` (`TauCeti.degree_const`), so `c` vanishes on it; a bundle of rank `0` is trivial.
Over a coordinate disc of `S` the clutching line bundles `L_k` (`clutchingLineBundle`) have
number `k` (`symplecticChernNumber_clutchingLineBundle`). By naturality for the first Chern
number, a bundle of rank `n ≥ 1` and number `k` is isomorphic to `L_k ⊕ ℝ^(2n-2)`, and
`L_a ⊕ L_b` to `L_(a+b) ⊕ ℝ²`. So `c` is determined by `h k = c L_k`, and `h` is additive.
Finally `TS²`, with the volume form `o.sphereVolumeForm` and the outward orientation
(`Orientation.volumeOrientation_sphereVolumeForm`), pulls back
along a map `S → S²` of degree one (`SymplecticGeometry.exists_contMDiff_degree_eq_one`) to a
line bundle on which both `c` and the first Chern number take the value `2`
(`TauCeti.surfaceGenus_sphere`), so it is isomorphic to `L_2`, and `h 2 = 2`. Normalization on
`S` alone would not suffice: on the torus it gives `c (TS) = 0`, which fixes no scale.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7
  (Theorem 2.7.1).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 (the Euler class of the tangent bundle evaluated on the fundamental class
  is the Euler characteristic) and §14 (the top Chern class of a complex bundle is the Euler class
  of its realification).
-/

public section

open Bundle Module TauCeti TauCeti.Bundle
open scoped Manifold ContDiff

namespace SymplecticGeometry

namespace Bundle

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  {EM : Type} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  [ChartedSpace EM M] [IsManifold 𝓘(ℝ, EM) ∞ M] (hn : finrank ℝ EM = 2)
  (o : Manifold.Orientation 𝓘(ℝ, EM) M (Fin 2))
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ EM = 2 * finrank ℂ G)]

/-- **The first Chern number of the tangent bundle of a closed surface.** Let `M` be a compact
connected Hausdorff smooth surface with an orientation `o`, and `σ` an area form on `M` (a
nondegenerate smooth two-form) whose symplectic orientation is `o`. Then the tangent bundle of
`M` with the form `σ` has first Chern number `2 - 2 g`, computed with any complex model `G`, for
`g = TauCeti.surfaceGenus M` the genus of `M`. -/
theorem symplecticChernNumber_tangent {σ : SmoothTwoForm 𝓘(ℝ, EM) M} (hσ : σ.IsNondegenerate)
    (ho : hσ.volumeOrientation (n := 1) hn = o) :
    symplecticChernNumber (o.toHomologicalOrientation hn) hn G
      (ContMDiffTwoForm.tangentEquiv.symm σ) = 2 - 2 * surfaceGenus M := by
  have : Fact (finrank ℝ EM = 2 * finrank ℂ ℂ) := ⟨by rw [hn, finrank_self]⟩
  let := FiniteCWType.of_isManifold (I := 𝓘(ℝ, EM)) M
  obtain ⟨J, hJ⟩ :=
    (ContMDiffTwoForm.isNondegenerate_tangentEquiv_symm_iff.2 hσ).exists_compatible
  rw [symplecticChernNumber_congr_model _ hn ℂ G,
    symplecticChernNumber_eq_chernNumber _ hn ℂ hJ.tames, chernNumber_def,
    firstChernClass_eq_complexEulerClass _ (finrank_self ℂ),
    hσ.complexEulerClass_eq_eulerClass hn hJ.tames, ho,
    Manifold.Orientation.evalFundamentalClass_eulerClass_eq_eulerChar_of_finiteCWType,
    ((o.toHomologicalOrientation hn).eulerChar_eq_two_sub_two_mul_genus_iff_even_finrank hn).2
      ((o.toHomologicalOrientation hn).even_finrank_singularHomology_one hn),
    (o.toHomologicalOrientation hn).genus_eq_surfaceGenus hn]

end Bundle

/-! ### Closed connected oriented surfaces and symplectic bundles over them -/

/-- A **closed connected oriented surface**: a compact connected Hausdorff smooth manifold
modelled on `ℝ²`, with an orientation. Bundling the surface lets the axioms of the first Chern
number quantify over all surfaces. -/
structure ClosedConnectedOrientedSurface where
  /-- The underlying space. -/
  carrier : Type
  [topologicalSpace : TopologicalSpace carrier]
  [chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 2)) carrier]
  [isManifold : IsManifold (𝓡 2) ∞ carrier]
  [t2Space : T2Space carrier]
  [compactSpace : CompactSpace carrier]
  [connectedSpace : ConnectedSpace carrier]
  /-- The orientation. -/
  o : Manifold.Orientation (𝓡 2) carrier (Fin 2)

namespace ClosedConnectedOrientedSurface

instance : CoeSort ClosedConnectedOrientedSurface Type := ⟨carrier⟩

attribute [instance] topologicalSpace chartedSpace isManifold t2Space compactSpace connectedSpace

end ClosedConnectedOrientedSurface

namespace Bundle

/-- A **symplectic vector bundle over a closed connected oriented surface** `S`: a smooth real
vector bundle `V` over `S` of rank `2 n`, with model fibre `F`, and a smooth nondegenerate
two-form `form` on it. -/
structure SymplecticSurfaceBundle (S : ClosedConnectedOrientedSurface) where
  /-- The complex rank: half the real rank. -/
  n : ℕ
  /-- The model fibre. -/
  F : Type
  [normedAddCommGroup : NormedAddCommGroup F]
  [normedSpace : NormedSpace ℝ F]
  [finiteDimensional : FiniteDimensional ℝ F]
  finrank_eq : finrank ℝ F = 2 * n
  /-- The fibres. -/
  V : S → Type
  [addCommGroup : ∀ x, AddCommGroup (V x)]
  [module : ∀ x, Module ℝ (V x)]
  [topologicalSpaceFiber : ∀ x, TopologicalSpace (V x)]
  [isTopologicalAddGroup : ∀ x, IsTopologicalAddGroup (V x)]
  [continuousSMul : ∀ x, ContinuousSMul ℝ (V x)]
  [topologicalSpaceTotalSpace : TopologicalSpace (TotalSpace F V)]
  [fiberBundle : FiberBundle F V]
  [vectorBundle : VectorBundle ℝ F V]
  [contMDiffVectorBundle : ContMDiffVectorBundle ∞ F V (𝓡 2)]
  /-- The symplectic form. -/
  form : ContMDiffTwoForm (𝓡 2) ⊤ F V
  isNondegenerate : form.IsNondegenerate

namespace SymplecticSurfaceBundle

attribute [instance] normedAddCommGroup normedSpace finiteDimensional addCommGroup module
  topologicalSpaceFiber isTopologicalAddGroup continuousSMul topologicalSpaceTotalSpace fiberBundle
  vectorBundle contMDiffVectorBundle

variable {S S' : ClosedConnectedOrientedSurface}

instance fact_finrank_eq (E : SymplecticSurfaceBundle S) :
    Fact (finrank ℝ E.F = 2 * finrank ℂ (Fin E.n → ℂ)) :=
  ⟨by rw [E.finrank_eq, finrank_fin_fun]⟩

/-- The **first Chern number** of a symplectic bundle over a closed connected oriented surface:
`SymplecticGeometry.Bundle.symplecticChernNumber` for the orientation of the surface. -/
noncomputable def symplecticChernNumber (E : SymplecticSurfaceBundle S) : ℤ :=
  Bundle.symplecticChernNumber
    (S.o.toHomologicalOrientation (finrank_euclideanSpace_fin (n := 2)))
    (finrank_euclideanSpace_fin (n := 2)) (Fin E.n → ℂ) E.form

theorem symplecticChernNumber_def (E : SymplecticSurfaceBundle S) :
    E.symplecticChernNumber =
      Bundle.symplecticChernNumber
        (S.o.toHomologicalOrientation (finrank_euclideanSpace_fin (n := 2)))
        (finrank_euclideanSpace_fin (n := 2)) (Fin E.n → ℂ) E.form := (rfl)

/-! #### Isomorphisms -/

/-- A **symplectic isomorphism** of symplectic bundles over the same surface: fibrewise linear
isomorphisms whose map of total spaces is smooth and that carry the form of `E` to that
of `E'`. -/
@[ext]
structure Iso (E E' : SymplecticSurfaceBundle S) where
  /-- The isomorphism of each fibre. -/
  toFun : ∀ x, E.V x ≃L[ℝ] E'.V x
  contMDiff : ContMDiff ((𝓡 2).prod 𝓘(ℝ, E.F)) ((𝓡 2).prod 𝓘(ℝ, E'.F)) ∞
    (fun p : TotalSpace E.F E.V ↦ TotalSpace.mk' E'.F p.proj (toFun p.proj p.snd))
  pushforward_eq : ContMDiffTwoForm.pushforward toFun contMDiff E.form = E'.form

namespace Iso

variable {E E' E'' : SymplecticSurfaceBundle S}

/-- An isomorphism preserves the forms: `ω'(Φ v, Φ w) = ω(v, w)`. -/
theorem bilinFormAt_apply (Φ : E.Iso E') (x : S) (v w : E.V x) :
    E'.form.bilinFormAt x (Φ.toFun x v) (Φ.toFun x w) = E.form.bilinFormAt x v w :=
  (ContMDiffTwoForm.pushforward_eq_iff _ _).1 Φ.pushforward_eq x v w

/-- An isomorphism preserves the forms, evaluated on pairs of vectors: `ω'(Φ v, Φ w) = ω(v, w)`.
This is `bilinFormAt_apply` in the form that `simp` normalizes to. -/
@[simp]
theorem form_apply_toFun (Φ : E.Iso E') (x : S) (v w : E.V x) :
    E'.form x ![Φ.toFun x v, Φ.toFun x w] = E.form x ![v, w] := by
  simpa using Φ.bilinFormAt_apply x v w

/-- The identity isomorphism. -/
def refl (E : SymplecticSurfaceBundle S) : E.Iso E where
  toFun x := ContinuousLinearEquiv.refl ℝ (E.V x)
  contMDiff := contMDiff_id
  pushforward_eq := (ContMDiffTwoForm.pushforward_eq_iff _ _).2 fun _ _ _ ↦ rfl

/-- The inverse of an isomorphism. -/
def symm (Φ : E.Iso E') : E'.Iso E where
  toFun x := (Φ.toFun x).symm
  contMDiff := (TauCeti.contMDiff_hom_bundle_iff
    fun x ↦ ((Φ.toFun x).symm : E'.V x →L[ℝ] E.V x)).1 (contMDiff_hom_bundle_symm _ Φ.contMDiff)
  pushforward_eq := (ContMDiffTwoForm.pushforward_eq_iff _ _).2 fun x v w ↦ by
    rw [← Φ.bilinFormAt_apply, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply]

/-- The composite of two isomorphisms. -/
def trans (Φ : E.Iso E') (Ψ : E'.Iso E'') : E.Iso E'' where
  toFun x := (Φ.toFun x).trans (Ψ.toFun x)
  contMDiff := Ψ.contMDiff.comp Φ.contMDiff
  pushforward_eq := (ContMDiffTwoForm.pushforward_eq_iff _ _).2 fun x v w ↦ by
    simp only [ContinuousLinearEquiv.trans_apply, Ψ.bilinFormAt_apply, Φ.bilinFormAt_apply]

@[simp]
theorem refl_toFun (E : SymplecticSurfaceBundle S) (x : S) :
    (refl E).toFun x = ContinuousLinearEquiv.refl ℝ (E.V x) :=
  (rfl)

@[simp]
theorem symm_toFun (Φ : E.Iso E') (x : S) : Φ.symm.toFun x = (Φ.toFun x).symm :=
  (rfl)

@[simp]
theorem trans_toFun (Φ : E.Iso E') (Ψ : E'.Iso E'') (x : S) :
    (Φ.trans Ψ).toFun x = (Φ.toFun x).trans (Ψ.toFun x) :=
  (rfl)

end Iso

/-! #### Constructions -/

/-- The **pull-back** `φ* E` of a symplectic bundle along a smooth map `φ : S' → S`, with the
pulled-back form. -/
@[reducible, expose] noncomputable def pullback (φ : S' → S) (hφ : ContMDiff (𝓡 2) (𝓡 2) ∞ φ)
    (E : SymplecticSurfaceBundle S) : SymplecticSurfaceBundle S' where
  n := E.n
  F := E.F
  finrank_eq := E.finrank_eq
  V := ((⟨φ, hφ.continuous⟩ : C(S', S)) : S' → S) *ᵖ E.V
  contMDiffVectorBundle :=
    Bundle.Pullback.contMDiffVectorBundle (f := (⟨φ, hφ.continuous⟩ : C(S', S))) hφ
  form := E.form.pullback (⟨φ, hφ.continuous⟩ : C(S', S)) hφ
  isNondegenerate := E.isNondegenerate.pullback _ hφ

/-- The **direct sum** `E ⊕ E'` of two symplectic bundles, with the sum of the forms. -/
@[reducible, expose] noncomputable def whitneySum (E E' : SymplecticSurfaceBundle S) :
    SymplecticSurfaceBundle S where
  n := E.n + E'.n
  F := E.F × E'.F
  finrank_eq := by rw [Module.finrank_prod, E.finrank_eq, E'.finrank_eq, mul_add]
  V := E.V ×ᵇ E'.V
  form := E.form.prod E'.form
  isNondegenerate := E.isNondegenerate.prod E'.isNondegenerate

/-- The **trivial symplectic bundle** `S × ℝ²ⁿ` of rank `2 n`, with the constant standard form
`stdForm (Fin n)`. -/
@[reducible, expose] noncomputable def trivial (S : ClosedConnectedOrientedSurface) (n : ℕ) :
    SymplecticSurfaceBundle S where
  n := n
  F := StdSpace (Fin n)
  finrank_eq := by rw [finrank_stdSpace, Fintype.card_fin]
  V := Trivial S (StdSpace (Fin n))
  form := ContMDiffTwoForm.const (stdForm (Fin n))
  isNondegenerate := ContMDiffTwoForm.isNondegenerate_const _

/-- The **tangent bundle** of `S` with an area form `σ`, a nondegenerate smooth two-form. -/
@[reducible, expose] noncomputable def tangent (S : ClosedConnectedOrientedSurface)
    (σ : SmoothTwoForm (𝓡 2) S) (hσ : σ.IsNondegenerate) : SymplecticSurfaceBundle S where
  n := 1
  F := EuclideanSpace ℝ (Fin 2)
  finrank_eq := finrank_euclideanSpace_fin
  V := TangentSpace (𝓡 2)
  form := ContMDiffTwoForm.tangentEquiv.symm σ
  isNondegenerate := ContMDiffTwoForm.isNondegenerate_tangentEquiv_symm_iff.2 hσ

/-! #### The rank and the first Chern number -/

variable {E E' : SymplecticSurfaceBundle S}

/-- Every fibre of `E` has real dimension `2 n`. -/
theorem finrank_fiber (E : SymplecticSurfaceBundle S) (x : S) : finrank ℝ (E.V x) = 2 * E.n := by
  rw [← E.finrank_eq]
  exact (VectorBundle.continuousLinearEquivAt ℝ E.F E.V x).toLinearEquiv.finrank_eq

/-- Isomorphic bundles have the same rank. -/
theorem Iso.n_eq (Φ : E.Iso E') : E.n = E'.n := by
  obtain ⟨x⟩ := (inferInstance : Nonempty S)
  have h := (Φ.toFun x).toLinearEquiv.finrank_eq
  rw [finrank_fiber, finrank_fiber] at h
  omega

/-- Isomorphic bundles have the same first Chern number. -/
theorem Iso.symplecticChernNumber_eq (Φ : E.Iso E') :
    E.symplecticChernNumber = E'.symplecticChernNumber :=
  (symplecticChernNumber_congr _ _ _ _ E.isNondegenerate Φ.toFun Φ.contMDiff
    Φ.bilinFormAt_apply).symm

/-- **The isomorphism property of the first Chern number.** Over a closed connected oriented
surface, a symplectic isomorphism `E ≅ E'` exists exactly when `E` and `E'` have equal ranks and
equal first Chern numbers. -/
theorem symplecticChernNumber_nonempty_iso_iff :
    Nonempty (E.Iso E') ↔ E.n = E'.n ∧ E.symplecticChernNumber = E'.symplecticChernNumber := by
  refine ⟨fun ⟨Φ⟩ ↦ ⟨Φ.n_eq, Φ.symplecticChernNumber_eq⟩, fun ⟨hn, hc⟩ ↦ ?_⟩
  obtain ⟨Ψ, hΨ, h⟩ := exists_pushforward_eq_of_symplecticChernNumber_eq (κ := Fin E.n)
    E.isNondegenerate E'.isNondegenerate (by rw [E.finrank_eq, Fintype.card_fin])
    (by rw [E'.finrank_eq, Fintype.card_fin, hn]) (Fin E.n → ℂ) (Fin E'.n → ℂ) hc
  exact ⟨⟨Ψ, hΨ, h⟩⟩

/-- **The first Chern number of a pull-back** along a smooth map `φ : S' → S` is the degree of
`φ` times the number. -/
theorem symplecticChernNumber_pullback (φ : S' → S) (hφ : ContMDiff (𝓡 2) (𝓡 2) ∞ φ)
    (E : SymplecticSurfaceBundle S) :
    (E.pullback φ hφ).symplecticChernNumber = degree S'.o S.o φ * E.symplecticChernNumber := by
  rw [symplecticChernNumber_def, symplecticChernNumber_def,
    Bundle.symplecticChernNumber_pullback _ (finrank_euclideanSpace_fin (n := 2)) _ _
      (finrank_euclideanSpace_fin (n := 2)) E.isNondegenerate _ hφ]
  congr 1
  exact Manifold.Orientation.degree_toHomologicalOrientation_eq_degree
    (finrank_euclideanSpace_fin (n := 2)) _ _
    (hφ.of_le (by norm_cast)) (map_continuous (⟨φ, hφ.continuous⟩ : C(S', S))).isProperMap

/-- **The first Chern number is additive on direct sums.** -/
@[simp]
theorem symplecticChernNumber_whitneySum (E E' : SymplecticSurfaceBundle S) :
    (E.whitneySum E').symplecticChernNumber =
      E.symplecticChernNumber + E'.symplecticChernNumber :=
  have : Fact (finrank ℝ (E.F × E'.F) = 2 * finrank ℂ (Fin (E.whitneySum E').n → ℂ)) :=
    fact_finrank_eq (E.whitneySum E')
  Bundle.symplecticChernNumber_whitneySum _ _ _ _ _ E.isNondegenerate E'.isNondegenerate

/-- **Normalization**: the tangent bundle of `S` with an area form inducing the orientation of
`S` has first Chern number `2 - 2 g`, for `g` the genus of `S`. -/
theorem symplecticChernNumber_tangent (S : ClosedConnectedOrientedSurface)
    {σ : SmoothTwoForm (𝓡 2) S} (hσ : σ.IsNondegenerate)
    (ho : hσ.volumeOrientation (n := 1) finrank_euclideanSpace_fin = S.o) :
    (tangent S σ hσ).symplecticChernNumber = 2 - 2 * surfaceGenus S :=
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 * finrank ℂ (Fin (tangent S σ hσ).n → ℂ)) :=
    fact_finrank_eq (tangent S σ hσ)
  Bundle.symplecticChernNumber_tangent _ _ _ hσ ho

/-- The canonical isomorphism `φ* (S × ℝ²ⁿ) ≅ S' × ℝ²ⁿ`: the pull-back of a trivial bundle is
trivial, by the identity of each fibre. -/
noncomputable def Iso.pullbackTrivial (φ : S' → S) (hφ : ContMDiff (𝓡 2) (𝓡 2) ∞ φ) (n : ℕ) :
    ((trivial S n).pullback φ hφ).Iso (trivial S' n) where
  toFun _ := ContinuousLinearEquiv.refl ℝ (StdSpace (Fin n))
  contMDiff := Trivial.contMDiff_mk_iff.2 ⟨contMDiff_proj _,
    (Trivial.contMDiff_mk_iff.1 (contMDiff_id (I := (𝓡 2).prod 𝓘(ℝ, StdSpace (Fin n)))
      (M := TotalSpace (StdSpace (Fin n)) (Trivial S (StdSpace (Fin n)))))).2.comp
      (Pullback.contMDiff_lift (⟨φ, hφ.continuous⟩ : C(S', S)) hφ)⟩
  pushforward_eq := (ContMDiffTwoForm.pushforward_eq_iff _ _).2 fun x v w ↦ by
    rw [ContMDiffTwoForm.bilinFormAt_pullback, ContMDiffTwoForm.bilinFormAt_const,
      ContMDiffTwoForm.bilinFormAt_const]
    -- The fibres of both bundles are `StdSpace (Fin n)`, but only up to unfolding the pull-back,
    -- so `ContinuousLinearEquiv.refl_apply` does not apply syntactically.
    rfl

/-- `Iso.pullbackTrivial` is the identity on each fibre. -/
@[simp]
theorem Iso.pullbackTrivial_toFun (φ : S' → S) (hφ : ContMDiff (𝓡 2) (𝓡 2) ∞ φ) (n : ℕ)
    (x : S') :
    (Iso.pullbackTrivial φ hφ n).toFun x = ContinuousLinearEquiv.refl ℝ (StdSpace (Fin n)) :=
  (rfl)

/-- A bundle of rank zero is isomorphic to the trivial bundle of rank zero. -/
private noncomputable def isoTrivialOfNEqZero (E : SymplecticSurfaceBundle S) (hE : E.n = 0) :
    E.Iso (trivial S 0) :=
  have hF : finrank ℝ E.F = finrank ℝ (StdSpace (Fin 0)) := by
    rw [E.finrank_eq, hE, finrank_euclideanSpace]; rfl
  have : Subsingleton (StdSpace (Fin 0)) := Module.finrank_zero_iff.1 (by
    rw [finrank_euclideanSpace]; rfl)
  { toFun x := (VectorBundle.continuousLinearEquivAt ℝ E.F E.V x).trans
      (ContinuousLinearEquiv.ofFinrankEq hF)
    contMDiff := Trivial.contMDiff_mk_iff.2 ⟨contMDiff_proj _,
      (contMDiff_const (c := (0 : StdSpace (Fin 0)))).congr fun _ ↦ Subsingleton.elim _ _⟩
    pushforward_eq := (ContMDiffTwoForm.pushforward_eq_iff _ _).2 fun x v w ↦ by
      have h (u : E.V x) : u = 0 := (((VectorBundle.continuousLinearEquivAt ℝ E.F E.V x).trans
        (ContinuousLinearEquiv.ofFinrankEq hF))).injective (Subsingleton.elim _ _)
      simp [h v] }

end SymplecticSurfaceBundle

open SymplecticSurfaceBundle

/-! ### The axioms -/

/-- **The axioms of the first Chern number** for an assignment `c` of an integer to every
symplectic bundle over every closed connected oriented surface:
* *naturality*: `E ≅ E'` exactly when `E` and `E'` have equal ranks and equal values of `c`;
* *functoriality*: `c (φ* E) = deg φ * c E` for every smooth map `φ : S' → S`;
* *additivity*: `c (E ⊕ E') = c E + c E'`;
* *normalization*: for an area form inducing the orientation of `S`, the tangent bundle has
  value `2 - 2 g`, `g` being the genus of `S`. -/
structure ChernNumberAxioms
    (c : ∀ S : ClosedConnectedOrientedSurface, SymplecticSurfaceBundle S → ℤ) : Prop where
  nonempty_iso_iff {S : ClosedConnectedOrientedSurface} (E E' : SymplecticSurfaceBundle S) :
    Nonempty (E.Iso E') ↔ E.n = E'.n ∧ c S E = c S E'
  apply_pullback {S S' : ClosedConnectedOrientedSurface} (φ : S' → S)
    (hφ : ContMDiff (𝓡 2) (𝓡 2) ∞ φ) (E : SymplecticSurfaceBundle S) :
    c S' (E.pullback φ hφ) = degree S'.o S.o φ * c S E
  apply_whitneySum {S : ClosedConnectedOrientedSurface} (E E' : SymplecticSurfaceBundle S) :
    c S (E.whitneySum E') = c S E + c S E'
  apply_tangent (S : ClosedConnectedOrientedSurface) {σ : SmoothTwoForm (𝓡 2) S}
    (hσ : σ.IsNondegenerate)
    (ho : hσ.volumeOrientation (n := 1) finrank_euclideanSpace_fin = S.o) :
    c S (tangent S σ hσ) = 2 - 2 * surfaceGenus S

/-- The first Chern number satisfies the axioms. -/
theorem chernNumberAxioms_symplecticChernNumber :
    ChernNumberAxioms fun _ E ↦ E.symplecticChernNumber where
  nonempty_iso_iff _ _ := symplecticChernNumber_nonempty_iso_iff
  apply_pullback := SymplecticSurfaceBundle.symplecticChernNumber_pullback
  apply_whitneySum := SymplecticSurfaceBundle.symplecticChernNumber_whitneySum
  apply_tangent := SymplecticSurfaceBundle.symplecticChernNumber_tangent

namespace ChernNumberAxioms

variable {c : ∀ S : ClosedConnectedOrientedSurface, SymplecticSurfaceBundle S → ℤ}
  (h : ChernNumberAxioms c) {S : ClosedConnectedOrientedSurface}
include h

/-- An assignment satisfying the axioms takes the same value on isomorphic bundles. -/
theorem apply_eq_of_iso {E E' : SymplecticSurfaceBundle S} (Φ : E.Iso E') : c S E = c S E' :=
  ((h.nonempty_iso_iff E E').1 ⟨Φ⟩).2

/-- An assignment satisfying the axioms vanishes on trivial bundles: the trivial bundle is its
own pull-back along a constant map, which has degree `0`. -/
theorem apply_trivial (S : ClosedConnectedOrientedSurface) (n : ℕ) : c S (trivial S n) = 0 := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty S)
  have hd := h.apply_pullback (fun _ : S ↦ x₀) contMDiff_const (trivial S n)
  rw [degree_const (by rw [finrank_euclideanSpace_fin]; norm_num), zero_mul] at hd
  rw [← h.apply_eq_of_iso (Iso.pullbackTrivial _ contMDiff_const n), hd]

/-- An assignment satisfying the axioms vanishes on bundles of rank zero. -/
theorem apply_of_n_eq_zero {E : SymplecticSurfaceBundle S} (hE : E.n = 0) : c S E = 0 :=
  (h.apply_eq_of_iso (isoTrivialOfNEqZero E hE)).trans (h.apply_trivial S 0)

end ChernNumberAxioms

namespace SymplecticSurfaceBundle

variable {S : ClosedConnectedOrientedSurface}

/-- A trivial bundle has first Chern number `0`. -/
@[simp]
theorem symplecticChernNumber_trivial (S : ClosedConnectedOrientedSurface) (n : ℕ) :
    (trivial S n).symplecticChernNumber = 0 :=
  chernNumberAxioms_symplecticChernNumber.apply_trivial S n

/-- **Triviality**: a symplectic bundle over a closed connected oriented surface is trivial if
and only if its first Chern number is `0`. -/
theorem symplecticChernNumber_eq_zero_iff {E : SymplecticSurfaceBundle S} :
    E.symplecticChernNumber = 0 ↔ Nonempty (E.Iso (trivial S E.n)) := by
  rw [symplecticChernNumber_nonempty_iso_iff, symplecticChernNumber_trivial]
  exact (and_iff_right rfl).symm

/-- **Global frames of a trivial bundle.** An isomorphism `Φ` of `E` with the trivial bundle of
rank `2 n`, read backwards on each fibre after a linear symplectomorphism `e` from `(W, σ)` to
the standard model `StdSpace (Fin n)`, is a symplectic frame of `E` for `σ` over all of `S`. -/
theorem Iso.isSymplecticFrameOn_trans_symm_toFun {E : SymplecticSurfaceBundle S} {n : ℕ}
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {σ : TauCeti.SymplecticForm W}
    (Φ : E.Iso (trivial S n)) {e : W ≃L[ℝ] StdSpace (Fin n)}
    (he : σ.IsSymplectomorphism (stdForm (Fin n)) e.toLinearEquiv) :
    E.form.IsSymplecticFrameOn σ Set.univ fun x ↦ e.trans (Φ.symm.toFun x) :=
  (ContMDiffTwoForm.isSymplecticFrameOn_const he).trans _ Φ.symm.contMDiff Φ.symm.pushforward_eq

end SymplecticSurfaceBundle

/-! ### Uniqueness -/

section Uniqueness

variable {S : ClosedConnectedOrientedSurface}
  {φ : CoordinateDisc (S.o.toHomologicalOrientation (finrank_euclideanSpace_fin (n := 2)))}

/-- The clutching line bundle `clutchingLineBundle φ k`, with the symplectic form of its
Hermitian metric, as a bundle of rank one over `S`. -/
private noncomputable def lineBundle
    (hφ : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ φ.coord (Set.range φ)) (k : ℤ) :
    SymplecticSurfaceBundle S :=
  have := isContMDiff_clutchingLineBundle k hφ
  { n := 1
    F := ℂ
    finrank_eq := Complex.finrank_real_complex
    V := (clutchingLineBundle φ k).Fiber
    form := (ContMDiffComplexStructure.ofComplexModule (𝓡 2) ⊤ ℂ
      (clutchingLineBundle φ k).Fiber).compatibleForm (clutchingMetric φ k ((⊤ : ℕ∞) : WithTop ℕ∞))
    isNondegenerate := (ContMDiffComplexStructure.compatible_compatibleForm _ _).isNondegenerate }

private theorem symplecticChernNumber_lineBundle
    (hφ : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ φ.coord (Set.range φ)) (k : ℤ) :
    (lineBundle hφ k).symplecticChernNumber = k :=
  have : Fact (finrank ℝ ℂ = 2 * finrank ℂ (Fin 1 → ℂ)) := fact_finrank_eq (lineBundle hφ k)
  symplecticChernNumber_clutchingLineBundle k (finrank_euclideanSpace_fin (n := 2)) hφ (Fin 1 → ℂ)

variable {c : ∀ S : ClosedConnectedOrientedSurface, SymplecticSurfaceBundle S → ℤ}

/-- An assignment satisfying the axioms agrees with the first Chern number on the line bundles
`lineBundle hφ k`. -/
private theorem ChernNumberAxioms.apply_lineBundle (h : ChernNumberAxioms c)
    (hφ : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ φ.coord (Set.range φ)) (k : ℤ) :
    c S (lineBundle hφ k) = k := by
  have hχ := chernNumberAxioms_symplecticChernNumber
  -- Additivity: `L_a ⊕ L_b` is isomorphic to `L_(a + b) ⊕ ℝ²`.
  have hadd (a b : ℤ) :
      c S (lineBundle hφ (a + b)) = c S (lineBundle hφ a) + c S (lineBundle hφ b) := by
    obtain ⟨Φ⟩ := (hχ.nonempty_iso_iff ((lineBundle hφ a).whitneySum (lineBundle hφ b))
      ((lineBundle hφ (a + b)).whitneySum (trivial S 1))).2 ⟨rfl, by
        simp [symplecticChernNumber_lineBundle]⟩
    have := h.apply_eq_of_iso Φ
    rw [h.apply_whitneySum, h.apply_whitneySum, h.apply_trivial, add_zero] at this
    exact this.symm
  let f : ℤ →+ ℤ := AddMonoidHom.mk' (fun k ↦ c S (lineBundle hφ k)) hadd
  -- Normalization: the pull-back of `TS²` along a map of degree one has number `2` for both.
  have h2 : c S (lineBundle hφ 2) = 2 := by
    have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩
    let o₃ := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation
    let S₂ : ClosedConnectedOrientedSurface :=
      { carrier := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
        connectedSpace := TauCeti.connectedSpace_sphere 2
        o := o₃.sphereOrientation }
    obtain ⟨g, hg, hdeg⟩ := exists_contMDiff_degree_eq_one (n := 2) S.o o₃
    have hσ : SmoothTwoForm.IsNondegenerate o₃.sphereVolumeForm :=
      o₃.isSymplectic_sphereVolumeForm.isNondegenerate
    have ho : hσ.volumeOrientation (n := 1) finrank_euclideanSpace_fin = S₂.o :=
      o₃.volumeOrientation_sphereVolumeForm hσ
    have key (c' : ∀ S : ClosedConnectedOrientedSurface, SymplecticSurfaceBundle S → ℤ)
        (h' : ChernNumberAxioms c') :
        c' S ((tangent S₂ o₃.sphereVolumeForm hσ).pullback (S' := S) g hg) = 2 := by
      have hg0 : surfaceGenus S₂ = 0 := surfaceGenus_sphere
      rw [h'.apply_pullback, h'.apply_tangent S₂ hσ ho, hg0, hdeg]
      norm_num
    obtain ⟨Φ⟩ := (hχ.nonempty_iso_iff
      ((tangent S₂ o₃.sphereVolumeForm hσ).pullback (S' := S) g hg)
      (lineBundle hφ 2)).2 ⟨rfl, (key _ hχ).trans (symplecticChernNumber_lineBundle hφ 2).symm⟩
    rw [← h.apply_eq_of_iso Φ, key c h]
  have h1 : f 1 = 1 := by
    have : f 1 + f 1 = 2 := by rw [← map_add]; exact h2
    omega
  exact congr($(AddMonoidHom.ext_int (f := f) (g := AddMonoidHom.id ℤ) h1) k)

/-- **Uniqueness of the first Chern number.** An assignment of an integer to every symplectic
bundle over every closed connected oriented surface that satisfies the axioms
`ChernNumberAxioms` is the first Chern number. -/
theorem eq_symplecticChernNumber_of_chernNumberAxioms (h : ChernNumberAxioms c)
    (S : ClosedConnectedOrientedSurface) (E : SymplecticSurfaceBundle S) :
    c S E = E.symplecticChernNumber := by
  have hχ := chernNumberAxioms_symplecticChernNumber
  rcases Nat.eq_zero_or_pos E.n with hE | hE
  · rw [h.apply_of_n_eq_zero hE, hχ.apply_of_n_eq_zero hE]
  -- A coordinate disc of `S`, whose coordinate is smooth.
  obtain ⟨x₀⟩ := (inferInstance : Nonempty S)
  obtain ⟨e, r, hr, hc, he, hea, -⟩ := CoordinateDisc.exists_ofChart_pairwise_disjoint S.o
    (x := fun _ : Unit ↦ x₀) (Function.injective_of_subsingleton _) (U := fun _ ↦ Set.univ)
    fun _ ↦ Filter.univ_mem
  have hφ := CoordinateDisc.contMDiffOn_coord_ofChart (e ()) (hr ()) (hc ()) (he ()) (hea ())
  -- `E` is isomorphic to `L_k ⊕ ℝ^(2 n - 2)`, for `k` its number.
  obtain ⟨Φ⟩ := (hχ.nonempty_iso_iff E ((lineBundle hφ E.symplecticChernNumber).whitneySum
    (trivial S (E.n - 1)))).2 ⟨(Nat.add_sub_cancel' hE).symm, by
      simp [symplecticChernNumber_lineBundle]⟩
  rw [h.apply_eq_of_iso Φ, h.apply_whitneySum, h.apply_trivial, h.apply_lineBundle, add_zero]

end Uniqueness

/-- **Existence and uniqueness of the first Chern number.** There is exactly one assignment of an
integer to every symplectic vector bundle over every closed connected oriented surface that
satisfies the axioms `ChernNumberAxioms`: naturality, functoriality, additivity and
normalization. It is `SymplecticSurfaceBundle.symplecticChernNumber`.

Milestone: *First Chern number of symplectic vector bundles over surfaces*. -/
theorem existsUnique_chernNumberAxioms :
    ∃! c : ∀ S : ClosedConnectedOrientedSurface, SymplecticSurfaceBundle S → ℤ,
      ChernNumberAxioms c :=
  ⟨_, chernNumberAxioms_symplecticChernNumber, fun _ h ↦
    funext fun S ↦ funext (eq_symplecticChernNumber_of_chernNumberAxioms h S)⟩

end Bundle

end SymplecticGeometry

end
