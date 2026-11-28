/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Morse.GradientLike
public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Analysis.ODE.Linear
public import TauCeti.Geometry.Manifold.Morse.Index
public import TauCeti.Geometry.Manifold.Morse.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization
public import TauCeti.Geometry.Symplectic.Liouville.VectorField
public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import SymplecticGeometry.Geometry.Manifold.Morse.Linearization
import TauCeti.Analysis.Normed.Module.Alternating.Curry
import SymplecticGeometry.Analysis.ODE.Linear
import SymplecticGeometry.Geometry.Symplectic.Liouville.VectorField
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import SymplecticGeometry.Analysis.ODE.LyapunovBilinForm
import SymplecticGeometry.Analysis.InnerProductSpace.Ellipsoid
import TauCeti.Analysis.ODE.ExponentialDichotomy

/-!
# The linearization of a gradient-like field at a nondegenerate critical point

Let `X` be gradient-like for `f` (`TauCeti.IsGradientLike`) on a manifold modelled on a
finite-dimensional real space `E`, and let `p` be a nondegenerate critical point of `f`, with `X`
differentiable at `p`. In the chart at `p`, write `H` for the Hessian of `f` and `A` for the
linearization of `X` at its zero `p` (Tau Ceti's `TauCeti.sectionLinearization`). By
`TauCeti.IsGradientLike.exists_pos_mul_norm_sq_le_hessian`, from
`Geometry/Manifold/Morse/Linearization.lean`, the form `v ↦ H v (A v)` is positive definite.
This is the first step of the analysis of the stable discs of a Weinstein structure at a
nondegenerate critical point: it makes `A` hyperbolic and relates its stable dimension to the
Morse index.

At a zero `p` of a Liouville vector field `Z` of a two-form `σ`, the linearization `A` of `Z`
satisfies `σ_p (A u, v) + σ_p (u, A v) = σ_p (u, v)`
(`TauCeti.IsLiouvilleVectorField.apply_sectionLinearization_add`). Along the flow of `A` the
form `σ_p` then grows like `e ^ t`, so it vanishes on the stable subspace of `A`. For a Weinstein
structure, whose form is symplectic, the stable subspace at a nondegenerate critical point is
thus isotropic, and its dimension, the Morse index, is at most half the dimension of the
manifold.

## Main results

* `TauCeti.IsGradientLike.exists_projection_exponential_bounds`: the flow of `A` has an
  exponential dichotomy.
* `TauCeti.IsGradientLike.finrank_stableSubspace_eq_manifoldMorseIndex` and
  `TauCeti.IsGradientLike.finrank_range_eq_manifoldMorseIndex`: the stable subspace of `A`, which
  is the range of the projection of any such dichotomy, has dimension the Morse index of `f` at
  `p`.
* `TauCeti.IsGradientLike.exists_continuousLinearEquiv_stableSubspace`: at a critical point of
  index `m`, a continuous linear equivalence `L` from `EuclideanSpace ℝ (Fin m)` onto the stable
  subspace of `A` with `-H (L u) (L u) = ‖u‖ ^ 2`.
* `TauCeti.IsLiouvilleVectorField.apply_eq_zero_of_mem_stableSubspace`: at a zero of a Liouville
  field, the form vanishes on the stable subspace of the linearization.
* `SymplecticGeometry.IsWeinsteinStructure.two_mul_manifoldMorseIndex_le`: at a nondegenerate
  critical point of a Weinstein structure, twice the Morse index is at most the dimension.

In the dichotomy and index statements `A : E →L[ℝ] E` comes with a hypothesis
`A = sectionLinearization …`, since the linearization itself is a map between tangent spaces,
which carry no norm.

## Implementation notes

The Hessian `H` is a symmetric bilinear Lyapunov form for `A`, and the dichotomy and the
index come from `ContinuousLinearMap.exists_projection_exponential_bounds_of_le_apply` and
`ContinuousLinearMap.sigNeg_toQuadraticMap_eq_finrank_stableSubspace`, which transfer Tau Ceti's
inertia theorem to bilinear forms on a normed space.

The Euclidean coordinate on the stable subspace is
`QuadraticMap.PosDef.exists_continuousLinearEquiv_euclideanSpace` applied to `-H`, which is
positive definite there by `ContinuousLinearMap.apply_self_neg_of_mem_stableSubspace`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Lemma 9.9, for the splitting of the linearization and the sign of the Hessian on its parts;
  Proposition 11.9 (a), for the isotropy of the stable subspace, and the dimension bound stated
  after its parts
-/

public section

open Bundle Filter Module NormedSpace Set VectorField TauCeti.Manifold
open scoped ContDiff Manifold NNReal Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- **Exponential dichotomy at a nondegenerate critical point.** Let `X` be gradient-like for `f`,
let `p` be a nondegenerate critical point of `f`, let `X` be differentiable at `p`, and let `A` be
the linearization of `X` at `p`. Then the flow of `A` has an exponential dichotomy: a projection
`P` commuting with `A`, and `K, α > 0`, such that `exp (t • A)` contracts the range of `P` at rate
`α` forward in time, and the kernel of `P` at rate `α` backward in time. -/
theorem IsGradientLike.exists_projection_exponential_bounds (hX : IsGradientLike f X) {p : M}
    (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
    (hXp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent
      (fun x ↦ (X x : TangentBundle 𝓘(ℝ, E) M)) p)
    {A : E →L[ℝ] E} (hA : A = sectionLinearization (F := E) 𝓘(ℝ, E) id X p) :
    ∃ P : E →L[ℝ] E, IsIdempotentElem P ∧ Commute A P ∧ ∃ K α : ℝ≥0, 0 < K ∧ 0 < α ∧
      (∀ t : ℝ, 0 ≤ t → ∀ v : E, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖) ∧
      (∀ t : ℝ, t ≤ 0 → ∀ v : E, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖) := by
  obtain ⟨c, hc, hcB⟩ := hX.exists_pos_mul_norm_sq_le_fderiv_fderiv hp hXp hA
  have hB := ((isManifoldNondegenerateCriticalPoint_iff _).1 hp).contDiffAt.isSymmSndFDerivAt
    (by simp)
  exact ContinuousLinearMap.exists_projection_exponential_bounds_of_le_apply hB hc hcB

/-- **The stable dimension of the linearization is the Morse index.** Let `X` be gradient-like
for `f`, let `p` be a nondegenerate critical point of `f`, let `X` be differentiable at `p`, and
let `A` be the linearization of `X` at `p`. Then the stable subspace of `A` has dimension the Morse
index of `f` at `p`. -/
theorem IsGradientLike.finrank_stableSubspace_eq_manifoldMorseIndex (hX : IsGradientLike f X)
    {p : M} (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
    (hXp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent
      (fun x ↦ (X x : TangentBundle 𝓘(ℝ, E) M)) p)
    {A : E →L[ℝ] E} (hA : A = sectionLinearization (F := E) 𝓘(ℝ, E) id X p) :
    finrank ℝ A.stableSubspace = manifoldMorseIndex 𝓘(ℝ, E) f p := by
  obtain ⟨c, hc, hcB⟩ := hX.exists_pos_mul_norm_sq_le_fderiv_fderiv hp hXp hA
  have hB := ((isManifoldNondegenerateCriticalPoint_iff _).1 hp).contDiffAt.isSymmSndFDerivAt
    (by simp)
  rw [manifoldMorseIndex_def, morseIndex_def, hessianQuadraticForm_def,
    ContinuousLinearMap.sigNeg_toQuadraticMap_eq_finrank_stableSubspace hB hc hcB]

/-- **The Morse index from an exponential dichotomy.** Let `X` be gradient-like for `f`, let `p` be
a nondegenerate critical point of `f`, let `X` be differentiable at `p`, and let `A` be the
linearization of `X` at `p`. For every exponential dichotomy `P` of `A`, as in
`TauCeti.IsGradientLike.exists_projection_exponential_bounds`, the range of `P` has dimension the
Morse index of `f` at `p`. -/
theorem IsGradientLike.finrank_range_eq_manifoldMorseIndex (hX : IsGradientLike f X) {p : M}
    (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
    (hXp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent
      (fun x ↦ (X x : TangentBundle 𝓘(ℝ, E) M)) p)
    {A : E →L[ℝ] E} (hA : A = sectionLinearization (F := E) 𝓘(ℝ, E) id X p)
    {P : E →L[ℝ] E} (hP : IsIdempotentElem P) (hAP : Commute A P) {K α : ℝ} (hα : 0 < α)
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : E, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : E, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖) :
    finrank ℝ P.range = manifoldMorseIndex 𝓘(ℝ, E) f p := by
  rw [ContinuousLinearMap.range_eq_stableSubspace_of_exponential_bounds hα hP hAP hs hu,
    hX.finrank_stableSubspace_eq_manifoldMorseIndex hp hXp hA]

/-- **Euclidean coordinates on the stable subspace.** Let `X` be gradient-like for `f`, let `p`
be a nondegenerate critical point of `f` of Morse index `m`, let `X` be differentiable at `p`,
and let `A` be the linearization of `X` at `p`. Write `H` for the second derivative of `f` read
in the chart at `p`, which is negative definite on the stable subspace of `A`. Then some
continuous linear equivalence `L` from `EuclideanSpace ℝ (Fin m)` onto the stable subspace
satisfies `-H (L u) (L u) = ‖u‖ ^ 2` for every `u`. -/
theorem IsGradientLike.exists_continuousLinearEquiv_stableSubspace
    (hX : IsGradientLike f X) {p : M} (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
    (hXp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent
      (fun x ↦ (X x : TangentBundle 𝓘(ℝ, E) M)) p)
    {A : E →L[ℝ] E} (hA : A = sectionLinearization (F := E) 𝓘(ℝ, E) id X p) {m : ℕ}
    (hm : manifoldMorseIndex 𝓘(ℝ, E) f p = m) :
    ∃ L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] A.stableSubspace, ∀ u,
      -fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm)) (extChartAt 𝓘(ℝ, E) p p)
        (L u) (L u) = ‖u‖ ^ 2 := by
  obtain ⟨c, hc, hcB⟩ := hX.exists_pos_mul_norm_sq_le_fderiv_fderiv hp hXp hA
  have hB := ((isManifoldNondegenerateCriticalPoint_iff _).1 hp).contDiffAt.isSymmSndFDerivAt
    (by simp)
  set H := fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm)) (extChartAt 𝓘(ℝ, E) p p)
  set Q : QuadraticForm ℝ A.stableSubspace :=
    -(H.toBilinForm.toQuadraticMap.comp A.stableSubspace.subtype)
  have hQ (v : A.stableSubspace) : Q v = -H v v := by
    simp [Q, LinearMap.BilinMap.toQuadraticMap_apply]
  have hQpos : Q.PosDef := fun v hv ↦ by
    rw [hQ, neg_pos]
    exact ContinuousLinearMap.apply_self_neg_of_mem_stableSubspace hB hc hcB v.property
      (by simpa using hv)
  obtain ⟨L, hL⟩ := hQpos.exists_continuousLinearEquiv_euclideanSpace
    ((hX.finrank_stableSubspace_eq_manifoldMorseIndex hp hXp hA).trans hm)
  exact ⟨L, fun u ↦ (hQ _).symm.trans (hL u)⟩

/-! ### Isotropy of the stable subspace at a zero of a Liouville field -/

section Liouville

variable {H N : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I 1 N]

omit [FiniteDimensional ℝ E] in
/-- **The stable subspace at a zero of a Liouville field is isotropic.** Let `Z` be a Liouville
vector field of a two-form `σ` on a boundaryless manifold, let `p` be a zero of `Z`, and let `A`
be the linearization of `Z` at `p`. Then `σ_p (u, v) = 0` for all `u`, `v` in the stable
subspace of `A`. -/
theorem IsLiouvilleVectorField.apply_eq_zero_of_mem_stableSubspace [CompleteSpace E]
    {σ : RoughForm I N ℝ 2} {Z : (x : N) → TangentSpace I x} (hZ : IsLiouvilleVectorField σ Z)
    {p : N} (hp : Z p = 0) {A : E →L[ℝ] E} (hA : A = sectionLinearization (F := E) I id Z p)
    {u v : E} (hu : u ∈ A.stableSubspace) (hv : v ∈ A.stableSubspace) : σ p ![u, v] = 0 := by
  subst hA
  -- The value of `σ` at `p`, an alternating map on the tangent space `E` at `p`.
  let σ₀ : E [⋀^Fin 2]→L[ℝ] ℝ := σ p
  have hB (u v : E) : ContinuousAlternatingMap.flatL ℝ E ℝ σ₀ u v = σ p ![u, v] :=
    ContinuousAlternatingMap.flatL_apply_apply σ₀ u v
  rw [← hB]
  refine ContinuousLinearMap.apply_eq_zero_of_mem_stableSubspace (fun u v ↦ ?_) hu hv
  simp only [hB]
  exact hZ.apply_sectionLinearization_add hp u v

end Liouville

end TauCeti

/-! ### The index bound for a Weinstein structure -/

namespace SymplecticGeometry

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {σ : SmoothTwoForm 𝓘(ℝ, E) M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}

/-- **The index bound for a Weinstein structure.** At a nondegenerate critical point `p` of the
function of a Weinstein structure on a manifold modelled on `E`, twice the Morse index is at most
`dim E`: the stable subspace of the linearization of the field at `p` is isotropic for the
symplectic form, and has dimension the Morse index. -/
theorem IsWeinsteinStructure.two_mul_manifoldMorseIndex_le (hW : IsWeinsteinStructure σ X f)
    {p : M} (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p) :
    2 * manifoldMorseIndex 𝓘(ℝ, E) f p ≤ finrank ℝ E := by
  have hXp := hW.mdifferentiableAt_field p
  have hp0 : X p = 0 := hW.isGradientLike.eq_zero_iff.2 hp.mem_criticalPoints
  rw [← hW.isGradientLike.finrank_stableSubspace_eq_manifoldMorseIndex hp hXp rfl]
  refine LinearMap.BilinForm.two_mul_finrank_le_finrank_of_le_orthogonal
    (hW.isSymplectic.isNondegenerate.nondegenerate_bilinFormAt p) fun w hw ↦
      LinearMap.BilinForm.mem_orthogonal_iff.2 fun v hv ↦ ?_
  rw [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply]
  exact hW.isLiouvilleVectorField.apply_eq_zero_of_mem_stableSubspace hp0 rfl hv hw

end SymplecticGeometry
