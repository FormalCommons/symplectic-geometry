/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.DualClass.FundamentalClass
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.ThomClass
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.DualClass.Cap

/-!
# The dual class of a submanifold capped with the fundamental class

Let `f : Z → X` be a smooth embedding with closed range of an oriented manifold `Z` into a
compact oriented manifold `X`, and give its normal bundle `ν` the orientation
`TauCeti.SmoothEmbedding.normalOrientation f hn hdim oX oZ` induced by those of `X` and `Z`.
As a linear orientation, `normalOrientation` puts the tangent directions first: on each fibre it
is Tau Ceti's cokernel orientation `Orientation.cokerOfExact`, so a positive basis of `T_z Z`
followed by lifts of a positive basis of `ν_z` is a positive basis of `T_{f z} X`. In local
homology this is the order with the normal directions first: by
`TauCeti.LocalOrientation.coe_cross_localOrientation_eq_neg_one_pow_smul`, the cross product of
the local orientations of the normal fibre and of `Z`, in this order, is read in a chart as the
local orientation of `X`, since the sign of that lemma is the sign of exchanging the two blocks of
a basis. This file proves that the dual class
`d_Z = TauCeti.SmoothEmbedding.dualClass f hn hdim hf o rfl ∈ Hʳ(X; ℤ)` satisfies

`d_Z ⌢ [X] = f_* [Z]` in `H_{dim Z}(X; ℤ)`,

for the fundamental classes of Tau Ceti's homological orientations of `X` and `Z`. By Tau Ceti's
`HomologicalOrientation.bijective_singularCapAddHom_fundamentalClass`, this cap identity
determines `d_Z`: it is the statement that `d_Z` is the Poincaré dual of `f_* [Z]`.

The proof composes two earlier steps. The cap product `d_Z ⌢ [X]` is the push-forward along
`f ∘ π` of the cap product `u ⌢ μ_Φ` of the canonical Thom class `u` of the normal orientation
with the class of a normalized tube `Φ`
(`TauCeti.SmoothEmbedding.exists_isNormalizedTube_singularCap_dualClassOf_fundamentalClass`,
`DualClass/Cap.lean`), and the projection `π` carries `u ⌢ μ_Φ` to `[Z]`
(`TauCeti.SmoothEmbedding.map_proj_singularCap_tubeFundamentalClass` and its variants,
`DualClass/FundamentalClass.lean`); the push-forward along `f ∘ π` is that along `π` followed by
that along `f`, which
`TauCeti.SmoothEmbedding.dualClass_cap_fundamentalClass_of_forall_isNormalizedTube`
(`DualClass/Cap.lean`) records for the three cases at once. The order of the factors in local
homology, normal directions first, enters only in the second step: the local orientation of `X`
read through the tube is the exchanged product of those of `Z` and of the normal fibre, and
`TauCeti.LocalOrientation.cross_localOrientation_eq_map_prodComm` turns it into the cross
product, normal factor first, that the local cap computation takes
(`TubularNeighborhood/LocalOrientation.lean`).

Throughout, `Z` has dimension `m + 1` (or `0`) and the normal orientation is applied to an
orientation `oZ` indexed by `Fin (m + 1)` (or `Fin 0`), so that `m` has the same meaning in the
three cap theorems as in `DualClass/FundamentalClass.lean`. Tau Ceti's homological orientations
come in two forms, `toHomologicalOrientation` in positive dimension and
`toHomologicalOrientationOfZeroDim` in dimension zero, so the cap identity is stated in three
cases: `Z` of positive dimension (any codimension, zero included), `Z` of dimension zero and `X`
of positive dimension, and both of dimension zero.

## Main results

* `TauCeti.SmoothEmbedding.dualClass_cap_fundamentalClass`: `d_Z ⌢ [X] = f_* [Z]` for `Z` of
  positive dimension.
* `TauCeti.SmoothEmbedding.dualClass_cap_fundamentalClass_of_finrank_eq_zero`: the same for `Z`
  of dimension zero and `X` of positive dimension.
* `TauCeti.SmoothEmbedding.…` named
  `dualClass_cap_fundamentalClass_of_finrank_eq_zero_of_finrank_fiber_eq_zero`: the same for `Z`
  and `X` of dimension zero.
* `TauCeti.SmoothEmbedding.bijective_thomMap_and_dualClass_cap_fundamentalClass`: the Thom
  isomorphism of the normal bundle, the fibre restrictions of its Thom class, the vanishing of
  `d_Z` off `Z`, its restriction to `Z`, and the cap identity, together.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6
  (Propositions 6.18, 6.24 and 6.41: the Thom class of the normal bundle and the Poincaré dual of
  a closed submanifold).
* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §3.2 (Thom classes and Euler classes
  over the integers).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (cap products and fundamental classes).
-/

public section

noncomputable section

open Bundle CategoryTheory MonoidalCategory Module Set AlgebraicTopology
open scoped Manifold ContDiff

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace TauCeti.SmoothEmbedding

variable {H G : Type*} {E V P Z X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G] {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ V G} [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z]
  [TopologicalSpace X] [ChartedSpace G X] [IsManifold J ∞ X] [T2Space X]
  [SecondCountableTopology X]

/-- **Reindexing the normal orientation in a cap product.** Capping with the dual class of a
normal orientation `o`, indexed by `Fin (finrank ℝ P)`, is capping with the dual class of `o`
reindexed along `Fin (finrank ℝ P) ≃ Fin r`, in degree `r`. -/
theorem singularCap_dualClass_reindex_finCongr (f : SmoothEmbedding I J ∞ Z X)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (hf : IsClosed (range f)) {r q n : ℕ}
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.isImmersion.NormalSpace x hn) (Fin (finrank ℝ P)))
    (hr : finrank ℝ P = r) (h : r + q = n) (h' : finrank ℝ P + q = n) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    (TopCat.of X).singularCap ℤ (ρ_ _).inv (ρ_ _).hom r q n h
        (f.dualClass hn hdim hf (VectorBundleOrientation.reindex (finCongr hr) o) hr) =
      (TopCat.of X).singularCap ℤ (ρ_ _).inv (ρ_ _).hom (finrank ℝ P) q n h'
        (f.dualClass hn hdim hf o rfl) := by
  subst hr
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  rw [finCongr_refl, VectorBundleOrientation.reindex_refl, Equiv.refl_apply]

section Cap

variable [CompactSpace X] [ChartedSpace V X]

/-- **The dual class of a submanifold capped with the fundamental class.** Let `f : Z → X` be a
smooth embedding with closed range of a manifold `Z` of dimension `m + 1` into a compact manifold
`X` of dimension `d + 1`, with orientations `oX` of `X` and `oZ` of `Z`. For the induced normal
orientation `normalOrientation f hn hdim oX oZ`, the cap product of the dual class
`dualClass f hn hdim hf _ rfl ∈ Hʳ(X; ℤ)`, `r = finrank ℝ P`, with the fundamental class of `X`
(for the homological orientation of `oX`) is the push-forward along `f` of the fundamental class
of `Z` (for the homological orientation of `oZ`). The codimension `r` may be zero.

As a linear orientation, `normalOrientation` puts the tangent directions of `Z` first and the
normal directions after them (`Orientation.cokerOfExact`), with no sign. In local homology this is
the order with the normal directions first, by
`TauCeti.LocalOrientation.coe_cross_localOrientation_eq_neg_one_pow_smul`. -/
theorem dualClass_cap_fundamentalClass [ChartedSpace E Z] (f : SmoothEmbedding I J ∞ Z X)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (hf : IsClosed (range f)) {m d : ℕ}
    (hE : finrank ℝ E = m + 1) (hV : finrank ℝ V = d + 1)
    (oX : Manifold.Orientation J X (Fin (m + 1 + finrank ℝ P)))
    (oZ : Manifold.Orientation I Z (Fin (m + 1))) :
    haveI : T2Space Z := f.isEmbedding.t2Space
    haveI : CompactSpace Z := (⟨f.isEmbedding, hf⟩ : Topology.IsClosedEmbedding f).compactSpace
    ((TopCat.of X).singularCap ℤ (ρ_ _).inv (ρ_ _).hom (finrank ℝ P) (m + 1) (d + 1)
        (by have := oX.card_eq; simp only [Fintype.card_fin] at this; omega)
        (f.dualClass hn hdim hf (normalOrientation f hn hdim oX oZ) rfl)).hom
      (((oX.reindex (finCongr (by have := oX.card_eq; simp only [Fintype.card_fin] at this; omega))
        ).toHomologicalOrientation hV).fundamentalClass hV) =
      (oZ.toHomologicalOrientation hE).mapFundamentalClass hE ⟨f, f.isEmbedding.continuous⟩ := by
  have : T2Space Z := f.isEmbedding.t2Space
  have : CompactSpace Z := (⟨f.isEmbedding, hf⟩ : Topology.IsClosedEmbedding f).compactSpace
  rw [HomologicalOrientation.mapFundamentalClass_def]
  have hX := oX.card_eq
  simp only [Fintype.card_fin] at hX
  refine dualClass_cap_fundamentalClass_of_forall_isNormalizedTube f hn hdim hf _ hV _ rfl _ _
    fun W Φ hΦ hK ↦ ?_
  rcases Nat.eq_zero_or_eq_succ_pred (finrank ℝ P) with hP | hP
  · obtain rfl : d = m := by omega
    exact map_proj_singularCap_tubeFundamentalClass_of_finrank_fiber_eq_zero Φ hK hΦ hE hP hV oX
      oZ
  · exact map_proj_singularCap_tubeFundamentalClass Φ hK hΦ hE hP hV oX oZ

/-- **The dual class of a set of points capped with the fundamental class.** Let `f : Z → X` be a
smooth embedding with closed range of a manifold `Z` of dimension zero into a compact manifold `X`
of dimension `d + 1`, with orientations `oX` of `X` and `oZ` of `Z` (a sign at each point).
For the induced normal orientation, the cap product of the dual class with the fundamental class
of `X` is the push-forward along `f` of the fundamental class of the zero-dimensional
homological orientation `toHomologicalOrientationOfZeroDim` of `oZ`. -/
theorem dualClass_cap_fundamentalClass_of_finrank_eq_zero [ChartedSpace E Z]
    (f : SmoothEmbedding I J ∞ Z X)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (hf : IsClosed (range f)) {d : ℕ} (hE : finrank ℝ E = 0) (hV : finrank ℝ V = d + 1)
    (oX : Manifold.Orientation J X (Fin (0 + finrank ℝ P)))
    (oZ : Manifold.Orientation I Z (Fin 0)) :
    haveI : T2Space Z := f.isEmbedding.t2Space
    haveI : CompactSpace Z := (⟨f.isEmbedding, hf⟩ : Topology.IsClosedEmbedding f).compactSpace
    ((TopCat.of X).singularCap ℤ (ρ_ _).inv (ρ_ _).hom (finrank ℝ P) 0 (d + 1) (by omega)
        (f.dualClass hn hdim hf (normalOrientation f hn hdim oX oZ) rfl)).hom
      (((oX.reindex (finCongr (by omega))).toHomologicalOrientation hV).fundamentalClass hV) =
      oZ.toHomologicalOrientationOfZeroDim.mapFundamentalClass hE
        ⟨f, f.isEmbedding.continuous⟩ := by
  have : T2Space Z := f.isEmbedding.t2Space
  have : CompactSpace Z := (⟨f.isEmbedding, hf⟩ : Topology.IsClosedEmbedding f).compactSpace
  rw [HomologicalOrientation.mapFundamentalClass_def]
  exact dualClass_cap_fundamentalClass_of_forall_isNormalizedTube f hn hdim hf _ hV _ rfl _ _
    fun W Φ hΦ hK ↦ map_proj_singularCap_tubeFundamentalClass_of_finrank_eq_zero Φ hK hΦ hE
      (by omega) hV oX oZ

/-- **The dual class capped with the fundamental class, in dimension zero.** Let `f : Z → X` be a
smooth embedding with closed range of a manifold `Z` of dimension zero into a compact manifold `X`,
with normal fibre `P` of dimension zero (so that `X` has dimension zero too), and orientations
`oX` of `X` and `oZ` of `Z`. For the induced normal orientation, the cap product of the dual
class with the fundamental class of the zero-dimensional homological orientation of `oX` is the
push-forward along `f` of the fundamental class of the zero-dimensional homological orientation
of `oZ`. -/
theorem dualClass_cap_fundamentalClass_of_finrank_eq_zero_of_finrank_fiber_eq_zero
    [ChartedSpace E Z] (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (hE : finrank ℝ E = 0) (hP : finrank ℝ P = 0)
    (oX : Manifold.Orientation J X (Fin (0 + finrank ℝ P)))
    (oZ : Manifold.Orientation I Z (Fin 0)) :
    haveI : T2Space Z := f.isEmbedding.t2Space
    haveI : CompactSpace Z := (⟨f.isEmbedding, hf⟩ : Topology.IsClosedEmbedding f).compactSpace
    ((TopCat.of X).singularCap ℤ (ρ_ _).inv (ρ_ _).hom (finrank ℝ P) 0 0 (by omega)
        (f.dualClass hn hdim hf (normalOrientation f hn hdim oX oZ) rfl)).hom
      ((oX.reindex (finCongr ((zero_add _).trans hP))).toHomologicalOrientationOfZeroDim
        |>.fundamentalClass (by omega)) =
      oZ.toHomologicalOrientationOfZeroDim.mapFundamentalClass hE
        ⟨f, f.isEmbedding.continuous⟩ := by
  have : T2Space Z := f.isEmbedding.t2Space
  have : CompactSpace Z := (⟨f.isEmbedding, hf⟩ : Topology.IsClosedEmbedding f).compactSpace
  rw [HomologicalOrientation.mapFundamentalClass_def]
  exact dualClass_cap_fundamentalClass_of_forall_isNormalizedTube f hn hdim hf _ _ _ rfl _ _
    fun W Φ hΦ hK ↦
      map_proj_singularCap_tubeFundamentalClass_of_finrank_eq_zero_of_finrank_fiber_eq_zero Φ hK
        hΦ hE hP oX oZ

end Cap

/-- **Thom class and Poincaré dual of a submanifold.** Let `f : Z → X` be a smooth embedding with
closed range, of codimension `r = finrank ℝ P`, and let `o` be an orientation of its normal
bundle `ν`. Then:

1. the Thom map `a ↦ π^* a ⌣ u` of the integral canonical Thom class `u` of `o`
   (`intCanonicalThomClass`) is bijective, `Hᵖ(Z; M) ≅ H^{p + r}(ν, ν ∖ 0; M)`, for every
   coefficient group `M` (`bijective_thomMap_intCanonicalThomClass`);
2. on each fibre, the canonical Thom class restricts to the generator selected by the orientation
   of that fibre, read in any linear trivialization
   (`VectorBundleOrientation.singularCohomologyMap_fiberThomPairMap_canonicalThomClass`);
3. the dual class `d_Z = dualClass f hn hdim hf o hr` vanishes on `X ∖ f(Z)`
   (`dualClass_restrict_compl`);
4. its pull-back along `f` is the Euler class of the canonical Thom class, its pull-back along the
   zero section (`dualClass_restrict`);
5. if `X` is compact and `X`, `Z` are oriented by `oX`, `oZ`, then the dual class of the induced
   normal orientation `normalOrientation f hn hdim oX oZ` (in place of `o`) satisfies
   `d_Z ⌢ [X] = f_* [Z]` for the fundamental classes of Tau Ceti's homological orientations, in
   each case of the dimensions:
   `dualClass_cap_fundamentalClass` (`dim Z > 0`),
   `dualClass_cap_fundamentalClass_of_finrank_eq_zero` (`dim Z = 0 < dim X`) and
   `dualClass_cap_fundamentalClass_of_finrank_eq_zero_of_finrank_fiber_eq_zero`
   (`dim Z = dim X = 0`).
   As a linear orientation, the induced normal orientation puts the tangent directions first
   (`Orientation.cokerOfExact`), with no sign; in local homology this is the order with the
   normal directions first
   (`TauCeti.LocalOrientation.coe_cross_localOrientation_eq_neg_one_pow_smul`).

The cap identity determines `d_Z`
(`HomologicalOrientation.bijective_singularCapAddHom_fundamentalClass`): it says that `d_Z` is
the Poincaré dual of `f_* [Z]`.

Milestone: *Thom class and Poincaré dual of a submanifold*. -/
theorem bijective_thomMap_and_dualClass_cap_fundamentalClass (f : SmoothEmbedding I J ∞ Z X)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (hf : IsClosed (range f)) {r : ℕ}
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.isImmersion.NormalSpace x hn) (Fin r))
    (hr : finrank ℝ P = r) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    (∀ (M : ModuleCat.{0} ℤ) (p k : ℕ) (h : p + finrank ℝ P = k),
      Function.Bijective (thomMap P (f.isImmersion.NormalSpace · hn) M (finrank ℝ P) p k h
        (o.intCanonicalThomClass hr))) ∧
    (∀ (e : Trivialization P (π P (f.isImmersion.NormalSpace · hn))) [e.IsLinear ℝ] {z : Z}
      (hz : z ∈ e.baseSet),
      TopPair.singularCohomologyMap (fiberThomPairMap P _ z) _ (o.canonicalThomClass hr) =
        TopPair.singularCohomologyMap (e.continuousLinearEquivAt ℝ z hz).complZeroPairIso.hom r
          ((e.mapOrientation (Fin r) hz (o z)).modelThomGenerator hr)) ∧
    TopCat.singularCohomologyMap (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).map r
      (f.dualClass hn hdim hf o hr) = 0 ∧
    TopCat.singularCohomologyMap (TopCat.ofHom ⟨f, f.isEmbedding.continuous⟩) r
        (f.dualClass hn hdim hf o hr) =
      eulerClass _ _ _ P (fun x ↦ f.isImmersion.NormalSpace x hn) r (o.canonicalThomClass hr) ∧
    ∀ [CompactSpace X] [ChartedSpace V X] [ChartedSpace E Z],
      haveI : T2Space Z := f.isEmbedding.t2Space
      haveI : CompactSpace Z := (⟨f.isEmbedding, hf⟩ : Topology.IsClosedEmbedding f).compactSpace
      (∀ {m d : ℕ} (hE : finrank ℝ E = m + 1) (hV : finrank ℝ V = d + 1)
        (oX : Manifold.Orientation J X (Fin (m + 1 + finrank ℝ P)))
        (oZ : Manifold.Orientation I Z (Fin (m + 1))),
        ((TopCat.of X).singularCap ℤ (ρ_ _).inv (ρ_ _).hom (finrank ℝ P) (m + 1) (d + 1)
            (by have := oX.card_eq; simp only [Fintype.card_fin] at this; omega)
            (f.dualClass hn hdim hf (normalOrientation f hn hdim oX oZ) rfl)).hom
          (((oX.reindex
            (finCongr (by have := oX.card_eq; simp only [Fintype.card_fin] at this; omega))
            ).toHomologicalOrientation hV).fundamentalClass hV) =
          (oZ.toHomologicalOrientation hE).mapFundamentalClass hE
            ⟨f, f.isEmbedding.continuous⟩) ∧
      (∀ {d : ℕ} (hE : finrank ℝ E = 0) (hV : finrank ℝ V = d + 1)
        (oX : Manifold.Orientation J X (Fin (0 + finrank ℝ P)))
        (oZ : Manifold.Orientation I Z (Fin 0)),
        ((TopCat.of X).singularCap ℤ (ρ_ _).inv (ρ_ _).hom (finrank ℝ P) 0 (d + 1) (by omega)
            (f.dualClass hn hdim hf (normalOrientation f hn hdim oX oZ) rfl)).hom
          (((oX.reindex (finCongr (by omega))).toHomologicalOrientation hV).fundamentalClass
            hV) =
          oZ.toHomologicalOrientationOfZeroDim.mapFundamentalClass hE
            ⟨f, f.isEmbedding.continuous⟩) ∧
      (∀ (hE : finrank ℝ E = 0) (hP : finrank ℝ P = 0)
        (oX : Manifold.Orientation J X (Fin (0 + finrank ℝ P)))
        (oZ : Manifold.Orientation I Z (Fin 0)),
        ((TopCat.of X).singularCap ℤ (ρ_ _).inv (ρ_ _).hom (finrank ℝ P) 0 0 (by omega)
            (f.dualClass hn hdim hf (normalOrientation f hn hdim oX oZ) rfl)).hom
          ((oX.reindex (finCongr ((zero_add _).trans hP))).toHomologicalOrientationOfZeroDim
            |>.fundamentalClass (by omega)) =
          oZ.toHomologicalOrientationOfZeroDim.mapFundamentalClass hE
            ⟨f, f.isEmbedding.continuous⟩) :=
  letI := f.normalSpaceFiberBundle hn hdim
  letI := f.normalSpaceVectorBundle hn hdim
  ⟨bijective_thomMap_intCanonicalThomClass f hn hdim o hr,
    fun e _ _ hz ↦ o.singularCohomologyMap_fiberThomPairMap_canonicalThomClass hr e hz,
    dualClass_restrict_compl f hn hdim hf o hr, dualClass_restrict f hn hdim hf o hr,
    ⟨dualClass_cap_fundamentalClass f hn hdim hf,
      dualClass_cap_fundamentalClass_of_finrank_eq_zero f hn hdim hf,
      dualClass_cap_fundamentalClass_of_finrank_eq_zero_of_finrank_fiber_eq_zero f hn hdim hf⟩⟩

end TauCeti.SmoothEmbedding

end
