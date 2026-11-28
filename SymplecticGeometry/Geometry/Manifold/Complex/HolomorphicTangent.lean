/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ComplexTangentBundle
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FirstChernClass
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.RestrictScalars
import SymplecticGeometry.Topology.VectorBundle.Complex.FirstChernClass
import SymplecticGeometry.Topology.VectorBundle.Complex.Structure

/-!
# The tangent bundle of a complex manifold with multiplication by `i`

On a complex manifold `M` modelled on a complex normed space `E`, Tau Ceti's almost complex
structure `TauCeti.SmoothAlmostComplexStructure.ofComplexManifold E M` is multiplication by `i` on
the tangent spaces. It makes the real tangent bundle a complex vector bundle, and this file
identifies that bundle with the holomorphic tangent bundle `TangentSpace 𝓘(ℂ, E)`: on each fibre
the identification is the identity of `E`, it is complex linear because the structure is
multiplication by `i`, and on total spaces it is the identity of the real tangent bundle followed
by `TangentBundle.restrictScalarsHomeomorph`. So the two bundles have the same first Chern class.

## Main definitions and results

* `TauCeti.SmoothAlmostComplexStructure.ofComplexManifoldTangentEquiv`: the complex-linear
  equivalence of the fibre of `(TM, i)` at `x` with the holomorphic tangent space at `x`.
* `TauCeti.SmoothAlmostComplexStructure.continuous_ofComplexManifoldTangentEquiv`: it is
  continuous on total spaces.
* `TauCeti.SmoothAlmostComplexStructure.firstChernClass_ofComplexManifold`: the first Chern class
  of `(TM, i)`, for any complex model fibre, is that of the holomorphic tangent bundle.

The equivalence is `TauCeti.Bundle.ContinuousComplexStructure.fiberEquivOfCommuteI` applied to
the identity of `E`, and its continuity comes from
`TauCeti.Bundle.ContinuousComplexStructure.continuous_fiberEquivOfCommuteI`. They follow the
private `holomorphicTangentEquiv` of Tau Ceti's
`TauCeti/Geometry/Symplectic/Manifold/AlmostComplex/Chern.lean` and the continuity step in the
proof of `TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_eq_clutchingNumberHom_tangentSpace`
there; this file states them publicly.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14.
-/

public section

noncomputable section

open Bundle Module
open scoped ContDiff Manifold TauCeti.ComplexManifold

namespace TauCeti.SmoothAlmostComplexStructure

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

/-- On a complex manifold `M` modelled on `E`, the fibre at `x` of the real tangent bundle made
complex by multiplication by `i` is the holomorphic tangent space at `x`; the equivalence is the
identity of `E`. -/
def ofComplexManifoldTangentEquiv (n : ℕ∞) (x : M) :
    ((ofComplexManifold E M).toContMDiff n).toContinuousComplexStructure.Fiber x ≃L[ℂ]
      TangentSpace 𝓘(ℂ, E) x :=
  -- The real equivalence onto the holomorphic tangent space is the identity of `E`; it carries
  -- the structure, multiplication by `i`, to multiplication by `I`.
  ((ofComplexManifold E M).toContMDiff n).toContinuousComplexStructure.fiberEquivOfCommuteI
    (W := TangentSpace 𝓘(ℂ, E)) (fun _ ↦ ContinuousLinearEquiv.refl ℝ E)
    (fun x v ↦ by
      rw [ContMDiffAlmostComplexStructure.toContinuousComplexStructure_apply, toContMDiff_apply]
      exact ofComplexManifold_apply (E := E) x v)
    x

@[simp]
theorem ofComplexManifoldTangentEquiv_apply (n : ℕ∞) (x : M)
    (v : ((ofComplexManifold E M).toContMDiff n).toContinuousComplexStructure.Fiber x) :
    ofComplexManifoldTangentEquiv n x v =
      (((ofComplexManifold E M).toContMDiff n).toContinuousComplexStructure.fiberEquiv x v : E) :=
  Bundle.ContinuousComplexStructure.fiberEquivOfCommuteI_apply _ _ _ x v

@[simp]
theorem ofComplexManifoldTangentEquiv_symm_apply (n : ℕ∞) (x : M) (v : TangentSpace 𝓘(ℂ, E) x) :
    (ofComplexManifoldTangentEquiv n x).symm v =
      (((ofComplexManifold E M).toContMDiff n).toContinuousComplexStructure.fiberEquiv x).symm
        (v : E) :=
  Bundle.ContinuousComplexStructure.fiberEquivOfCommuteI_symm_apply _ _ _ x v

variable [FiniteDimensional ℂ E]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ E = 2 * finrank ℂ G)]

/-- The fibrewise equivalence `ofComplexManifoldTangentEquiv` of `(TM, i)` with the holomorphic
tangent bundle is continuous on total spaces, for any complex model fibre `G` of `(TM, i)`. -/
theorem continuous_ofComplexManifoldTangentEquiv (n : ℕ∞) :
    Continuous fun p : TotalSpace G
        ((ofComplexManifold E M).toContMDiff n).toContinuousComplexStructure.Fiber ↦
      TotalSpace.mk' E (E := TangentSpace 𝓘(ℂ, E)) p.proj
        (ofComplexManifoldTangentEquiv n p.proj p.snd) := by
  -- On total spaces the identity from the real onto the holomorphic tangent bundle is the inverse
  -- of `TangentBundle.restrictScalarsHomeomorph`.
  unfold ofComplexManifoldTangentEquiv
  refine Bundle.ContinuousComplexStructure.continuous_fiberEquivOfCommuteI _ _ _ G
    ((TangentBundle.restrictScalarsHomeomorph ℝ (𝕜' := ℂ) M).symm.continuous.congr fun p ↦ ?_)
  rw [TangentBundle.restrictScalarsHomeomorph_symm_apply]
  -- The identifications `tangentSpaceCastModel` of tangent spaces with `E` are the identity by
  -- definition, and Mathlib states no evaluation lemma for them.
  rfl

end TauCeti.SmoothAlmostComplexStructure

namespace TauCeti.SmoothAlmostComplexStructure

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

/-- **The first Chern class of a complex manifold.** On a complex manifold `M` modelled on a
finite-dimensional complex space `E`, the real tangent bundle made complex by multiplication by `i`
(`ofComplexManifold E M`, at any smoothness level `n`) has, for any complex model fibre `G`, the
first Chern class of the holomorphic tangent bundle `TangentSpace 𝓘(ℂ, E)`. -/
theorem firstChernClass_ofComplexManifold (n : ℕ∞)
    (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
    [Fact (finrank ℝ E = 2 * finrank ℂ G)] :
    firstChernClass G ((ofComplexManifold E M).toContMDiff n).toContinuousComplexStructure.Fiber =
      firstChernClass E (TangentSpace 𝓘(ℂ, E) : M → Type) :=
  TauCeti.firstChernClass_eq_of_fiberwise (φ := ofComplexManifoldTangentEquiv n)
    (continuous_ofComplexManifoldTangentEquiv G n)

end TauCeti.SmoothAlmostComplexStructure
