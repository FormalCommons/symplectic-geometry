/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ComplexStructure
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
public import TauCeti.Geometry.Symplectic.AlmostComplex.Quotient

/-!
# The complex structure on the normal bundle of a `J`-invariant submanifold

Let `J` be a smooth almost complex structure on a manifold `X` and `f : M → X` an embedding
whose tangent images `df_x (T_x M)` are `J`-invariant. Then `J` descends to each normal space
`ν_x = T_{f x} X ⧸ df_x (T_x M)` (Tau Ceti's `TauCeti.SmoothEmbedding.NormalSpace`), as Tau
Ceti's quotient structure `TauCeti.AlmostComplexStructure.quotient`, and the normal class map
`T_{f x} X → ν_x` is complex linear. For a smooth embedding these structures form a smooth
complex structure on the normal bundle: the descended map of total spaces, composed with the
normal quotient map, is the normal quotient map composed with `J`, so it is smooth by Tau Ceti's
`TauCeti.SmoothEmbedding.contMDiff_normalBundle_iff`.

No metric and no choice of complement enters. Tau Ceti's `TauCeti.normalStructure`
(`TauCeti/Geometry/Symplectic/JHolomorphic/Normal/ComplexStructure.lean`) is the same quotient
construction at one point of a pseudoholomorphic map between vector spaces.

## Main definitions

* `TauCeti.SmoothEmbedding.normalAlmostComplexStructureAt`: the almost complex structure that
  `J` induces on the normal space at a point.
* `TauCeti.SmoothEmbedding.normalComplexStructure`: these structures, as a smooth complex
  structure on the normal bundle of a smooth embedding.

## Main results

* `TauCeti.SmoothEmbedding.normalAlmostComplexStructureAt_normalClass`: the induced structure
  sends the normal class of `v` to the normal class of `J v`.
* `TauCeti.SmoothEmbedding.isComplexLinearMap_normalClass`: the normal class map is complex
  linear.
* `TauCeti.SmoothEmbedding.normalAlmostComplexStructureAt_eq_iff`: the induced structure is the
  only one for which the normal class map is complex linear.

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

/-- The almost complex structure on the normal space `f.NormalSpace x hn` induced by an almost
complex structure `J` on `X` for which the tangent images of the embedding `f` are invariant:
the class of `v` is sent to the class of `J v`. -/
def normalAlmostComplexStructureAt (f : SmoothEmbedding I' I n M X)
    (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, ∀ v ∈ f.tangentRange x hn, J (f x) v ∈ f.tangentRange x hn) (x : M) :
    AlmostComplexStructure (f.NormalSpace x hn) :=
  (J.almostComplexStructureAt (f x)).quotient (f.tangentRange x hn) fun v hv ↦ by
    rw [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
    exact hJ x v hv

theorem normalAlmostComplexStructureAt_def (f : SmoothEmbedding I' I n M X)
    (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, ∀ v ∈ f.tangentRange x hn, J (f x) v ∈ f.tangentRange x hn) (x : M) :
    f.normalAlmostComplexStructureAt J hJ x =
      (J.almostComplexStructureAt (f x)).quotient (f.tangentRange x hn) fun v hv ↦ by
        rw [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
        exact hJ x v hv :=
  (rfl)

/-- The induced structure sends the normal class of `v` to the normal class of `J v`. -/
@[simp]
theorem normalAlmostComplexStructureAt_normalClass (f : SmoothEmbedding I' I n M X)
    (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, ∀ v ∈ f.tangentRange x hn, J (f x) v ∈ f.tangentRange x hn) (x : M)
    (v : TangentSpace I (f x)) :
    f.normalAlmostComplexStructureAt J hJ x (f.normalClass x hn v) =
      f.normalClass x hn (J (f x) v) := by
  rw [normalAlmostComplexStructureAt_def, normalClass_def,
    ← SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  -- `f.NormalSpace x hn` is by definition the quotient by `f.tangentRange x hn`.
  exact (J.almostComplexStructureAt (f x)).quotient_mk _ _ v

/-- The normal class map `T_{f x} X → f.NormalSpace x hn` is complex linear for `J` and the
induced structure. -/
@[simp]
theorem isComplexLinearMap_normalClass (f : SmoothEmbedding I' I n M X)
    (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, ∀ v ∈ f.tangentRange x hn, J (f x) v ∈ f.tangentRange x hn) (x : M) :
    IsComplexLinearMap (J.almostComplexStructureAt (f x))
      (f.normalAlmostComplexStructureAt J hJ x) (f.normalClass x hn) := by
  rw [normalAlmostComplexStructureAt_def, normalClass_def]
  -- `f.NormalSpace x hn` is by definition the quotient by `f.tangentRange x hn`.
  exact AlmostComplexStructure.isComplexLinearMap_mkQ _ _ _

/-- The induced structure is the unique almost complex structure on the normal space for which
the normal class map is complex linear. -/
theorem normalAlmostComplexStructureAt_eq_iff (f : SmoothEmbedding I' I n M X)
    (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, ∀ v ∈ f.tangentRange x hn, J (f x) v ∈ f.tangentRange x hn) (x : M)
    (K : AlmostComplexStructure (f.NormalSpace x hn)) :
    f.normalAlmostComplexStructureAt J hJ x = K ↔
      IsComplexLinearMap (J.almostComplexStructureAt (f x)) K (f.normalClass x hn) := by
  rw [normalAlmostComplexStructureAt_def, normalClass_def]
  -- `f.NormalSpace x hn` is by definition the quotient by `f.tangentRange x hn`.
  exact AlmostComplexStructure.quotient_eq_iff _ _ _ K

end Pointwise

section Smooth

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I' ∞ M]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] {hn : (∞ : ℕ∞ω) ≠ 0}

/-- The map of total spaces of the induced structures on the normal spaces of a smooth embedding
is smooth. -/
private theorem contMDiff_normalAlmostComplexStructureAt (f : SmoothEmbedding I' I ∞ M X)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, ∀ v ∈ f.tangentRange x hn, J (f x) v ∈ f.tangentRange x hn) :
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I'.prod 𝓘(ℝ, P)) (I'.prod 𝓘(ℝ, P)) ∞
      (fun p : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦
        TotalSpace.mk' P (E := fun x ↦ f.NormalSpace x hn) p.proj
          (f.normalAlmostComplexStructureAt J hJ p.proj p.snd)) := by
  let := f.normalSpaceFiberBundle hn hdim
  have : IsManifold I' ((∞ : ℕ∞ω) + 1) M := .of_le (n := ∞) (by simp)
  have : IsManifold I ((∞ : ℕ∞ω) + 1) X := .of_le (n := ∞) (by simp)
  -- `J` along `f`, on the pulled-back tangent bundle, is smooth on total spaces.
  have hJf : ContMDiff (I'.prod 𝓘(ℝ, E)) (I'.prod 𝓘(ℝ, E)) ∞
      (fun p : TotalSpace E ((f : M → X) *ᵖ (TangentSpace I)) ↦
        TotalSpace.mk' E (E := (f : M → X) *ᵖ (TangentSpace I)) p.proj (J (f p.proj) p.snd)) := by
    have h := (TauCeti.contMDiff_hom_bundle_iff _).1
      (J.pullbackComplexStructure f f.contMDiff).toEndomorphism.contMDiff
    simp only [SmoothAlmostComplexStructure.pullbackComplexStructure_toEndomorphism] at h
    exact h
  refine (f.contMDiff_normalBundle_iff hn (by simp) hdim _).2 ?_
  refine ((f.contMDiff_normalQuotientMap hn (m := ∞) (by simp) hdim).comp hJf).congr fun ⟨x, v⟩ ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, normalQuotientMap_apply, normalQuotientMap_apply]
  exact congrArg (TotalSpace.mk' P (E := fun y ↦ f.NormalSpace y hn) x)
    (f.normalAlmostComplexStructureAt_normalClass J hJ x v)

/-- The complex structure on the normal bundle of a smooth embedding `f` induced by a smooth
almost complex structure `J` for which the tangent images of `f` are invariant: at each point it
is `f.normalAlmostComplexStructureAt J hJ`. The normal bundle carries Tau Ceti's bundle structure
with model fibre `P`, of dimension `hdim`. -/
def normalComplexStructure (f : SmoothEmbedding I' I ∞ M X)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, ∀ v ∈ f.tangentRange x hn, J (f x) v ∈ f.tangentRange x hn) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    ContMDiffComplexStructure I' ⊤ P (fun x ↦ f.NormalSpace x hn) :=
  letI := f.normalSpaceFiberBundle hn hdim
  letI := f.normalSpaceVectorBundle hn hdim
  { toEndomorphism :=
      ⟨fun x ↦ LinearMap.toContinuousLinearMap
          (f.normalAlmostComplexStructureAt J hJ x).toLinearMap,
        (TauCeti.contMDiff_hom_bundle_iff _).2
          (f.contMDiff_normalAlmostComplexStructureAt hdim J hJ)⟩
    square_neg := fun x ↦ ContinuousLinearMap.ext fun v ↦ by simp }

/-- The complex structure on the normal bundle acts at `x` as
`f.normalAlmostComplexStructureAt J hJ x`. -/
@[simp]
theorem normalComplexStructure_apply (f : SmoothEmbedding I' I ∞ M X)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, ∀ v ∈ f.tangentRange x hn, J (f x) v ∈ f.tangentRange x hn) (x : M)
    (v : f.NormalSpace x hn) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    f.normalComplexStructure hdim J hJ x v = f.normalAlmostComplexStructureAt J hJ x v :=
  (rfl)

/-- The value of the complex structure on the normal bundle at `x` is
`f.normalAlmostComplexStructureAt J hJ x`. -/
@[simp]
theorem almostComplexStructureAt_normalComplexStructure (f : SmoothEmbedding I' I ∞ M X)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') (J : SmoothAlmostComplexStructure I X)
    (hJ : ∀ x, ∀ v ∈ f.tangentRange x hn, J (f x) v ∈ f.tangentRange x hn) (x : M) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    (f.normalComplexStructure hdim J hJ).almostComplexStructureAt x =
      f.normalAlmostComplexStructureAt J hJ x := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  ext v
  rw [ContMDiffComplexStructure.almostComplexStructureAt_apply, normalComplexStructure_apply]

end Smooth

end TauCeti.SmoothEmbedding

end
