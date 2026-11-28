/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Sublevel.Basic
public import SymplecticGeometry.Geometry.Symplectic.Liouville.Filling
import TauCeti.Geometry.Manifold.RegularValue.Scalar.Outward
import TauCeti.Geometry.Symplectic.Lagrangian.SymplecticTangent
import SymplecticGeometry.Geometry.Manifold.VectorField.Pullback
import SymplecticGeometry.Geometry.Symplectic.Liouville.VectorField

/-!
# Regular sublevels of Liouville fields are strong fillings

Let `σ` be a symplectic form on a boundaryless manifold `M`, `X` a smooth Liouville vector field
of `σ`, and `c` a regular value of a smooth function `f : M → ℝ` such that `df(X) > 0` along the
level `f⁻¹(c)`. Then the sublevel `W = {f ≤ c}`, a manifold with boundary for Tau Ceti's atlas
`TauCeti.scalarRegularSublevelChartedSpace`, with the pull-back of `σ` along the inclusion
`ι : W → M` and the pull-back of `X`, is a strong filling, Liouville on all of `W`.

The differential of `ι` is invertible at every point, also on the boundary
(`TauCeti.isInvertible_mfderiv_subtypeVal_scalarRegularSublevel`). So `ι^*σ` is symplectic
(`TauCeti.SmoothTwoForm.IsNondegenerate.HasSymplecticTangentImages.isSymplectic_mpullback`), the
pulled-back field is smooth (`ContMDiff.mpullback_vectorField`) and `ι`-related to `X`, hence
Liouville for `ι^*σ` (`TauCeti.IsLiouvilleVectorField.mpullback`). Along the boundary, which is
the level (`TauCeti.boundary_scalarRegularSublevel`), a tangent vector of `W` points outward
exactly when `df` is positive on its image under `dι`
(`TauCeti.isOutwardPointing_scalarRegularSublevel_iff_mfderiv`), and `dι` sends the pulled-back
field to `X` (`VectorField.mfderiv_apply_mpullback`), so `df(X) > 0` gives the condition.

## Main results

* `SymplecticGeometry.isStrongFilling_scalarRegularSublevel`: the regular sublevel is a strong
  filling, with `U = univ`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Definition 3.5.38 (strong fillings)
* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §11.1, for Liouville cobordisms and domains, whose field points outward along the (positive)
  boundary, and for the exhaustions of a Liouville manifold by compact domains with this property
-/

public section

open Module Set TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {n : ℕ}

/-- **A regular sublevel of a Liouville field is a strong filling.** Let `σ` be a symplectic form
on a boundaryless manifold `M` of dimension `n + 1`, `X` a smooth Liouville vector field of `σ`,
and `c` a regular value of a smooth function `f : M → ℝ` with `df_x (X x) > 0` at every point `x`
of the level `f⁻¹(c)`. Then the sublevel `{f ≤ c}`, with its atlas
`TauCeti.scalarRegularSublevelChartedSpace`, the pull-back of `σ` along the inclusion and the
pull-back of `X` along the inclusion, is a strong filling whose field is Liouville everywhere. -/
theorem isStrongFilling_scalarRegularSublevel (hn : finrank ℝ E = n + 1)
    {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic) {X : (x : M) → TangentSpace I x}
    (hX : ContMDiff I I.tangent ∞ (T% X)) (hXσ : IsLiouvilleVectorField σ.val X)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hc : IsRegularValue I 𝓘(ℝ) f c)
    (hXf : ∀ x, f x = c → 0 < mvfderiv I f x (X x)) :
    letI := scalarRegularSublevelChartedSpace (hf.of_le (by simp)) hc hn
    haveI := isManifold_scalarRegularSublevel hc hn (by simp) hf
    IsStrongFilling
      (SmoothForm.mpullback Subtype.val
        (contMDiff_subtypeVal_scalarRegularSublevel hc hn (by simp) hf) σ)
      univ (VectorField.mpullback (𝓡∂ (n + 1)) I Subtype.val X) := by
  let := scalarRegularSublevelChartedSpace (hf.of_le (by simp)) hc hn
  have := isManifold_scalarRegularSublevel hc hn (by simp) hf
  have hι := contMDiff_subtypeVal_scalarRegularSublevel hc hn (by simp) hf
  have hinv := isInvertible_mfderiv_subtypeVal_scalarRegularSublevel (hf.of_le (by simp)) hc hn
  -- The pulled-back field is smooth, and it is `ι`-related to `X` since `dι` is invertible.
  have hY : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (T% (VectorField.mpullback (𝓡∂ (n + 1)) I Subtype.val X)) :=
    hX.mpullback_vectorField hι hinv (by simp)
  refine ⟨(hσ.isNondegenerate.hasSymplecticTangentImages_of_surjective
      fun x ↦ (hinv x).surjective).isSymplectic_mpullback hσ hι fun x ↦ (hinv x).injective,
    isOpen_univ, subset_univ _, .intro hY fun x hx ↦ ?_, fun x _ ↦ ?_⟩
  · rw [boundary_scalarRegularSublevel hc hn (by simp) hf] at hx
    rw [isOutwardPointing_scalarRegularSublevel_iff_mfderiv (hf.of_le (by simp)) hn hc hx,
      VectorField.mfderiv_apply_mpullback (hinv x)]
    exact hXf x hx
  · exact congrFun (isLiouvilleVectorField_iff.1 <| IsLiouvilleVectorField.mpullback hι
      (hX.of_le (by simp)) hXσ (hY.mdifferentiable (by simp))
      fun x ↦ VectorField.mfderiv_apply_mpullback (hinv x) X) x

end SymplecticGeometry

end
