/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.ThomPairMap
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ComplexStructure
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.NormalBundle

/-!
# The complex structure on the normal bundle of a `J`-invariant submanifold

Let `J` be a smooth almost complex structure on a manifold `X` and `f : M → X` an embedding
whose tangent images `df_x (T_x M)` are `J`-invariant. Tau Ceti's
`TauCeti.SmoothEmbedding.normalComplexStructureAt` is the endomorphism `[v] ↦ [J v]` of each
normal space `ν_x = T_{f x} X ⧸ df_x (T_x M)`, and `TauCeti.SmoothEmbedding.normalComplexStructure`
bundles these endomorphisms as a continuous complex structure on the normal bundle, using that
they form a smooth section of its endomorphism bundle
(`TauCeti.SmoothEmbedding.contMDiff_normalComplexStructureAt_hom_bundle`).

This file adds the two bundled forms of the same structure that the library uses: at each point,
an almost complex structure on the normal space, which is Tau Ceti's quotient structure
`TauCeti.AlmostComplexStructure.quotient`, so that the normal class map is complex linear for
it; and on the normal bundle of a smooth embedding, a smooth complex structure
(`SymplecticGeometry.Bundle.ContMDiffComplexStructure`), whose underlying continuous complex
structure is Tau Ceti's.

## Main definitions

* `TauCeti.SmoothEmbedding.normalAlmostComplexStructureAt`: the almost complex structure that
  `J` induces on the normal space at a point.
* `TauCeti.SmoothEmbedding.contMDiffNormalComplexStructure`: these structures, as a smooth complex
  structure on the normal bundle of a smooth embedding.

## Main results

* `TauCeti.SmoothEmbedding.normalAlmostComplexStructureAt_apply`: the induced structure acts as
  Tau Ceti's `normalComplexStructureAt`.
* `TauCeti.SmoothEmbedding.isComplexLinearMap_normalClass`: the normal class map is complex
  linear.
* `TauCeti.SmoothEmbedding.normalAlmostComplexStructureAt_eq_iff`: the induced structure is the
  only one for which the normal class map is complex linear.
* `TauCeti.SmoothEmbedding.normalSpaceEquivOfComp_normalComplexStructureAt`: for `v ∘ f' = f`
  with `v` pseudoholomorphic at `f' x`, the isomorphism of normal spaces given by the derivative
  of `v` (`TauCeti.SmoothEmbedding.normalSpaceEquivOfComp`) intertwines the two normal complex
  structures.
* `TauCeti.SmoothEmbedding.toContinuousComplexStructure_contMDiffNormalComplexStructure`: the
  underlying continuous complex structure is Tau Ceti's `normalComplexStructure`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Example 4.4.5.
-/

public section

noncomputable section

open _root_.Bundle Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

open SymplecticGeometry.Bundle

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
  [IsManifold I ∞ X]
  {E' H' M : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H' M]

section Pointwise

variable {n : ℕ∞ω} {hn : n ≠ 0}

/-- The almost complex structure on the normal space `f.isImmersion.NormalSpace x hn` induced by an
almost complex structure `J` on `X` for which the tangent images of the embedding `f` are invariant:
the class of `v` is sent to the class of `J v`. -/
def normalAlmostComplexStructureAt (f : SmoothEmbedding I' I n M X)
    (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn)) (x : M) :
    AlmostComplexStructure (f.isImmersion.NormalSpace x hn) :=
  (J.almostComplexStructureAt (f x)).quotient (f.isImmersion.tangentRange x hn) fun v hv ↦ by
    rw [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
    exact hJ x hv

theorem normalAlmostComplexStructureAt_def (f : SmoothEmbedding I' I n M X)
    (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn)) (x : M) :
    f.normalAlmostComplexStructureAt J hJ x =
      (J.almostComplexStructureAt (f x)).quotient (f.isImmersion.tangentRange x hn) fun v hv ↦ by
        rw [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
        exact hJ x hv :=
  (rfl)

/-- The induced almost complex structure acts as Tau Ceti's normal complex structure
`normalComplexStructureAt`. -/
@[simp]
theorem normalAlmostComplexStructureAt_apply (f : SmoothEmbedding I' I n M X)
    (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn)) (x : M)
    (ν : f.isImmersion.NormalSpace x hn) :
    f.normalAlmostComplexStructureAt J hJ x ν =
      f.normalComplexStructureAt hn J x (hJ x) ν := by
  rw [normalAlmostComplexStructureAt_def]
  exact (LinearMap.congr_fun (normalComplexStructureAt_toLinearMap (hJ x)) ν).symm

/-- The normal class map `T_{f x} X → f.isImmersion.NormalSpace x hn` is complex linear for `J` and
the induced structure. -/
@[simp]
theorem isComplexLinearMap_normalClass (f : SmoothEmbedding I' I n M X)
    (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn)) (x : M) :
    IsComplexLinearMap (J.almostComplexStructureAt (f x))
      (f.normalAlmostComplexStructureAt J hJ x) (f.isImmersion.normalClass x hn) := by
  rw [normalAlmostComplexStructureAt_def, Manifold.IsImmersion.normalClass_def]
  -- `f.isImmersion.NormalSpace x hn` is by definition the quotient by
  -- `f.isImmersion.tangentRange x hn`.
  exact AlmostComplexStructure.isComplexLinearMap_mkQ _ _ _

/-- The induced structure is the unique almost complex structure on the normal space for which
the normal class map is complex linear. -/
theorem normalAlmostComplexStructureAt_eq_iff (f : SmoothEmbedding I' I n M X)
    (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn)) (x : M)
    (K : AlmostComplexStructure (f.isImmersion.NormalSpace x hn)) :
    f.normalAlmostComplexStructureAt J hJ x = K ↔
      IsComplexLinearMap (J.almostComplexStructureAt (f x)) K (f.isImmersion.normalClass x hn) := by
  rw [normalAlmostComplexStructureAt_def, Manifold.IsImmersion.normalClass_def]
  -- `f.isImmersion.NormalSpace x hn` is by definition the quotient by
  -- `f.isImmersion.tangentRange x hn`.
  exact AlmostComplexStructure.quotient_eq_iff _ _ _ K

end Pointwise

section Comp

variable {V G X' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace G]
  {I'' : ModelWithCorners ℝ V G} [TopologicalSpace X'] [ChartedSpace G X'] [IsManifold I'' ∞ X']
  {n m : ℕ∞ω} {v : X' → X}

/-- **The derivative of a pseudoholomorphic map is complex linear on normal spaces.** Let
`f' : M → X'` and `f : M → X` be embeddings with `v ∘ f' = f`, where `v` has invertible
derivative at each `f' x`, and let `J'`, `J` be almost complex structures on `X'`, `X` for which
the tangent images of `f'` and `f` at `x` are invariant. If `v` is `(J', J)`-holomorphic at
`f' x`, the isomorphism `f'.normalSpaceEquivOfComp f` of the normal spaces at `x` intertwines the
normal complex structures induced by `J'` and `J`. -/
theorem normalSpaceEquivOfComp_normalComplexStructureAt (f' : SmoothEmbedding I' I'' n M X')
    (f : SmoothEmbedding I' I m M X) (hn : n ≠ 0) (hm : m ≠ 0)
    (hv : ∀ x, (mfderiv I'' I v (f' x)).IsInvertible) (h : v ∘ f' = f)
    {J' : SmoothAlmostComplexStructure I'' X'} {J : SmoothAlmostComplexStructure I X} (x : M)
    (hJ' : Set.MapsTo (J' (f' x)) (f'.isImmersion.tangentRange x hn)
      (f'.isImmersion.tangentRange x hn))
    (hJ : Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hm) (f.isImmersion.tangentRange x hm))
    (hvJ : IsPseudoholomorphicAt J' J v (f' x)) (w : f'.isImmersion.NormalSpace x hn) :
    f'.normalSpaceEquivOfComp f hn hm hv h x (f'.normalComplexStructureAt hn J' x hJ' w) =
      f.normalComplexStructureAt hm J x hJ (f'.normalSpaceEquivOfComp f hn hm hv h x w) := by
  -- Transport of `J` between the equal points `v (f' x)` and `f x`.
  have hcast : ∀ y : X, y = f x → ∀ u : TangentSpace I y,
      tangentSpaceCast I y (f x) (J y u) = J (f x) (tangentSpaceCast I y (f x) u) := by
    rintro _ rfl u
    simp only [tangentSpaceCast_self]
  obtain ⟨u, rfl⟩ := f'.isImmersion.normalClass_surjective x hn w
  rw [normalComplexStructureAt_normalClass, normalSpaceEquivOfComp_normalClass,
    normalSpaceEquivOfComp_normalClass, normalComplexStructureAt_normalClass,
    hvJ.mfderiv_apply_commute, hcast (v (f' x)) (congrFun h x)]

end Comp

section Smooth

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I' ∞ M]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] {hn : (∞ : ℕ∞ω) ≠ 0}

/-- The complex structure on the normal bundle of a smooth embedding `f` induced by a smooth
almost complex structure `J` for which the tangent images of `f` are invariant: at each point it
is Tau Ceti's `f.normalComplexStructureAt`. The normal bundle carries Tau Ceti's bundle structure
with model fibre `P`, of dimension `hdim`. -/
def contMDiffNormalComplexStructure (f : SmoothEmbedding I' I ∞ M X)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn)) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    ContMDiffComplexStructure I' ⊤ P (fun x ↦ f.isImmersion.NormalSpace x hn) :=
  letI := f.normalSpaceFiberBundle hn hdim
  letI := f.normalSpaceVectorBundle hn hdim
  haveI : IsManifold I' (∞ + 1) M := .of_le (n := ∞) (by simp)
  { toEndomorphism :=
      ⟨fun x ↦ f.normalComplexStructureAt hn J x (hJ x),
        f.contMDiff_normalComplexStructureAt_hom_bundle (m := ∞) hn J (by simp) hdim
          hJ⟩
    square_neg := fun x ↦ normalComplexStructureAt_comp_self _ }

/-- The complex structure on the normal bundle acts at `x` as Tau Ceti's
`f.normalComplexStructureAt`. -/
@[simp]
theorem contMDiffNormalComplexStructure_apply (f : SmoothEmbedding I' I ∞ M X)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn)) (x : M)
    (v : f.isImmersion.NormalSpace x hn) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    f.contMDiffNormalComplexStructure hdim J hJ x v =
      f.normalComplexStructureAt hn J x (hJ x) v :=
  (rfl)

/-- The underlying continuous complex structure of the complex structure on the normal bundle is
Tau Ceti's `f.normalComplexStructure`. -/
@[simp]
theorem toContinuousComplexStructure_contMDiffNormalComplexStructure
    (f : SmoothEmbedding I' I ∞ M X)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn)) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    (f.contMDiffNormalComplexStructure hdim J hJ).toContinuousComplexStructure =
      f.normalComplexStructure hn J hdim hJ := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  ext x v
  rw [ContMDiffComplexStructure.toContinuousComplexStructure_apply,
    contMDiffNormalComplexStructure_apply]
  exact (normalComplexStructure_apply f hn J hdim hJ x v).symm

/-- The value of the complex structure on the normal bundle at `x` is
`f.normalAlmostComplexStructureAt J hJ x`. -/
@[simp]
theorem almostComplexStructureAt_contMDiffNormalComplexStructure (f : SmoothEmbedding I' I ∞ M X)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn)) (x : M) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    (f.contMDiffNormalComplexStructure hdim J hJ).almostComplexStructureAt x =
      f.normalAlmostComplexStructureAt J hJ x := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  ext v
  rw [ContMDiffComplexStructure.almostComplexStructureAt_apply,
    contMDiffNormalComplexStructure_apply, normalAlmostComplexStructureAt_apply]

end Smooth

end TauCeti.SmoothEmbedding

end
