/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Sets.OpenCover
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Restriction
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Tangent.Opens

/-!
# Gluing smooth almost complex structures

Let `U : ι → Opens M` cover a manifold `M`, and let `J i` be a smooth almost complex structure on
each open submanifold `U i`, such that `J i` and `J j` take the same value at every point of
`U i ⊓ U j`. Then there is one smooth almost complex structure on `M`,
`TauCeti.SmoothAlmostComplexStructure.glue hU hJ`, which is `J i` at every point of `U i`
(`glue_apply`). Its restriction to `U i`, in the sense of Tau Ceti's
`TauCeti.SmoothAlmostComplexStructure.restrictOpen`, is `J i` (`restrictOpen_glue`), and it is the
only structure on `M` with these restrictions (`eq_glue_iff`). In particular every structure is
glued from its restrictions (`glue_restrictOpen`). Together with `restrictOpen`, this is the
gluing property of smooth almost complex structures over the open sets of `M`.

Smoothness is local: at a point of `U i`, the glued field of endomorphisms is smooth because the
field it induces on `U i` is `J i`, by `TauCeti.Manifold.contMDiffAt_restrictOpen_tangentEnd_iff`
in `SymplecticGeometry/Geometry/Manifold/VectorBundle/Tangent/Opens.lean`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

noncomputable section

open Bundle TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothAlmostComplexStructure

variable {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (U : ι → Opens M) (J : ∀ i, SmoothAlmostComplexStructure I (U i))

/-- Smooth almost complex structures `J i` on the open sets `U i` agree on the overlaps: at a
point `x` of `U i ⊓ U j`, read on the tangent space of `M` at `x` through the canonical
identifications, `J i` and `J j` take the same value. -/
def AgreeOnOverlaps : Prop :=
  ∀ i j (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v : TangentSpace I x),
    Manifold.tangentSpaceOpenEquiv (I := I) (⟨x, hi⟩ : U i)
        (J i ⟨x, hi⟩ ((Manifold.tangentSpaceOpenEquiv (I := I) (⟨x, hi⟩ : U i)).symm v)) =
      Manifold.tangentSpaceOpenEquiv (I := I) (⟨x, hj⟩ : U j)
        (J j ⟨x, hj⟩ ((Manifold.tangentSpaceOpenEquiv (I := I) (⟨x, hj⟩ : U j)).symm v))

/-- Unfolds `AgreeOnOverlaps`: the structures take the same value at every point of every
overlap. -/
theorem agreeOnOverlaps_iff :
    AgreeOnOverlaps U J ↔ ∀ i j (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v : TangentSpace I x),
      Manifold.tangentSpaceOpenEquiv (I := I) (⟨x, hi⟩ : U i)
          (J i ⟨x, hi⟩ ((Manifold.tangentSpaceOpenEquiv (I := I) (⟨x, hi⟩ : U i)).symm v)) =
        Manifold.tangentSpaceOpenEquiv (I := I) (⟨x, hj⟩ : U j)
          (J j ⟨x, hj⟩ ((Manifold.tangentSpaceOpenEquiv (I := I) (⟨x, hj⟩ : U j)).symm v)) :=
  Iff.rfl

variable {U}

/-- The tangent endomorphism field of the glued structure: at `x`, the value of `J i` for the
chosen index `i` of a set of the cover containing `x`. -/
private def glueEnd (hU : IsOpenCover U) (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x :=
  let y : U (hU.exists_mem x).choose := ⟨x, (hU.exists_mem x).choose_spec⟩
  (Manifold.tangentSpaceOpenEquiv (I := I) y).toContinuousLinearMap.comp
    (((J _).toEndomorphism y).comp
      (Manifold.tangentSpaceOpenEquiv (I := I) y).symm.toContinuousLinearMap)

variable {J}

private theorem glueEnd_apply (hU : IsOpenCover U) (hJ : AgreeOnOverlaps U J) (i : ι) (x : M)
    (hi : x ∈ U i) (v : TangentSpace I x) :
    glueEnd J hU x v = Manifold.tangentSpaceOpenEquiv (I := I) (⟨x, hi⟩ : U i)
      (J i ⟨x, hi⟩ ((Manifold.tangentSpaceOpenEquiv (I := I) (⟨x, hi⟩ : U i)).symm v)) := by
  rw [glueEnd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  exact hJ _ _ x _ hi v

/-- The glued field read on `U i`, through the tangent-space identifications, is `J i`. -/
private theorem restrictOpenTangentSpaceEnd_glueEnd (hU : IsOpenCover U)
    (hJ : AgreeOnOverlaps U J) (i : ι) (y : U i) :
    (Manifold.tangentSpaceOpenEquiv (I := I) y).symm.toContinuousLinearMap.comp
      ((glueEnd J hU y).comp (Manifold.tangentSpaceOpenEquiv (I := I) y).toContinuousLinearMap) =
      (J i).toEndomorphism y := by
  ext v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe,
    glueEnd_apply hU hJ i y y.property]
  simp only [ContinuousLinearEquiv.symm_apply_apply]

private theorem contMDiff_glueEnd (hU : IsOpenCover U) (hJ : AgreeOnOverlaps U J) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞ fun x : M ↦
      TotalSpace.mk' (E →L[ℝ] E) (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        x (glueEnd J hU x) := by
  intro x
  refine (Manifold.contMDiffAt_restrictOpen_tangentEnd_iff (U := U (hU.exists_mem x).choose)
    (x := ⟨x, (hU.exists_mem x).choose_spec⟩)).1 ?_
  simpa only [restrictOpenTangentSpaceEnd_glueEnd hU hJ] using (J _).toEndomorphism.contMDiff _

/-- The smooth almost complex structure on `M` glued from smooth almost complex structures `J i`
on the sets `U i` of an open cover of `M` that agree on the overlaps `U i ⊓ U j`. -/
def glue (hU : IsOpenCover U) (hJ : AgreeOnOverlaps U J) : SmoothAlmostComplexStructure I M where
  toEndomorphism := ⟨glueEnd J hU, contMDiff_glueEnd hU hJ⟩
  square_neg x := by
    ext v
    simp only [ContMDiffSection.coeFn_mk, ContinuousLinearMap.comp_apply,
      glueEnd_apply hU hJ _ x (hU.exists_mem x).choose_spec]
    simp

/-- At a point `x` of `U i`, the glued structure is `J i`, read on the tangent space of `M` at
`x` through the canonical identification. -/
theorem glue_apply (hU : IsOpenCover U) (hJ : AgreeOnOverlaps U J) (i : ι) (x : M) (hi : x ∈ U i)
    (v : TangentSpace I x) :
    glue hU hJ x v = Manifold.tangentSpaceOpenEquiv (I := I) (⟨x, hi⟩ : U i)
      (J i ⟨x, hi⟩ ((Manifold.tangentSpaceOpenEquiv (I := I) (⟨x, hi⟩ : U i)).symm v)) :=
  glueEnd_apply hU hJ i x hi v

/-- The restriction of the glued structure to `U i` is `J i`. -/
@[simp]
theorem restrictOpen_glue (hU : IsOpenCover U) (hJ : AgreeOnOverlaps U J) (i : ι) :
    (glue hU hJ).restrictOpen (U i) = J i := by
  ext x v
  rw [restrictOpen_apply, glue_apply hU hJ i x x.property]
  simp only [ContinuousLinearEquiv.symm_apply_apply]

/-- A smooth almost complex structure on `M` is the glued one exactly when its restriction to
each `U i` is `J i`. -/
theorem eq_glue_iff (hU : IsOpenCover U) (hJ : AgreeOnOverlaps U J)
    (K : SmoothAlmostComplexStructure I M) :
    K = glue hU hJ ↔ ∀ i, K.restrictOpen (U i) = J i := by
  refine ⟨fun h i ↦ h ▸ restrictOpen_glue hU hJ i, fun h ↦ ?_⟩
  ext x v
  rw [glue_apply hU hJ _ x (hU.exists_mem x).choose_spec, ← h, restrictOpen_apply]
  simp

/-- The restrictions of one smooth almost complex structure to a family of open sets agree on
the overlaps. -/
theorem agreeOnOverlaps_restrictOpen (K : SmoothAlmostComplexStructure I M) :
    AgreeOnOverlaps U fun i ↦ K.restrictOpen (U i) := by
  intro i j x hi hj v
  simp

/-- A smooth almost complex structure is glued from its restrictions to the sets of an open
cover. -/
@[simp]
theorem glue_restrictOpen (hU : IsOpenCover U) (K : SmoothAlmostComplexStructure I M) :
    glue hU (agreeOnOverlaps_restrictOpen (U := U) K) = K :=
  ((eq_glue_iff hU _ K).2 fun _ ↦ rfl).symm

end SmoothAlmostComplexStructure

end TauCeti

end
