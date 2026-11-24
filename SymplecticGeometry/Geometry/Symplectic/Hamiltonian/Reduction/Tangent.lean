/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.LinearReduction
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# The tangent spaces of a reduced space, for general reduction data

Fix a fiberwise nondegenerate two-form `σ` on `M`, and reduction data given as maps: a smooth
map `i : Z → M` and a map `p : Z → Q` of manifolds. At a point `z` of `Z`, suppose that

* the image of `di_z` is a subspace `W` of `T_{i z} M`;
* the kernel of `dp_z` is the kernel of the pulled-back form `(i^* σ)_z`;
* `dp_z` is onto.

These are the hypotheses that Tau Ceti's reduction data satisfy pointwise
(`TauCeti.SmoothTwoForm.IsMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback`), with `W`
the kernel `ker dμ_{i z}` of the differential of a moment map at any level `c`, `i` the inclusion
of the level and `p` its projection to the reduced space. Write `W_red = W ⧸ (W ∩ W^σ)` for the
linear symplectic reduction of `W` (`TauCeti.SymplecticForm.ReducedSpace`), with its symplectic
form `TauCeti.SymplecticForm.reduction`.

* `reducedSpaceEquivTangentSpace`: the linear equivalence `W_red ≃ T_{p z} Q`. The map
  `v ↦ [di_z v]` sends `T_z Z` onto `W_red`, with kernel the kernel of `(i^* σ)_z`, which is the
  kernel of `dp_z`; since `dp_z` is onto, it descends to the equivalence.
* `reducedSpaceEquivTangentSpace_mk` and `reducedSpaceEquivTangentSpace_symm_mfderiv`: the class
  of `di_z v` goes to `dp_z v`, and back.
* `eval₂_reducedSpaceEquivTangentSpace` and `isSymplectomorphism_reducedSpaceEquivTangentSpace`:
  if `η` is a two-form on `Q` with `p^* η = i^* σ`, then the equivalence carries the reduced form
  of `σ_{i z}` on `W_red` to `η` at `p z`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Proposition 5.4.13 and Remark 5.4.14.
* [A. Cannas da Silva, *Lectures on Symplectic Geometry*][CannasdaSilva2001Lectures],
  Lecture 23.
* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130.
-/

public section

noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

namespace IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {EZ HZ Z : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
  {J : ModelWithCorners ℝ EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z] [IsManifold J ∞ Z]
  {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
  {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
  {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate) {i : Z → M} {p : Z → Q}

/-- The differential of `i` at `z`, with values in `W`, followed by the projection to the reduced
space of `W`. -/
private def tangentToReducedSpace {z : Z} {W : Submodule ℝ (TangentSpace I (i z))}
    (hrange : LinearMap.range (mfderiv J I i z).toLinearMap = W) :
    TangentSpace J z →ₗ[ℝ] (hσ.symplecticFormAt (i z)).ReducedSpace W :=
  Submodule.mkQ _ ∘ₗ (mfderiv J I i z).toLinearMap.codRestrict _
    fun v ↦ hrange.le (LinearMap.mem_range_self _ v)

omit [IsManifold J ∞ Z] in
private theorem tangentToReducedSpace_apply {z : Z} {W : Submodule ℝ (TangentSpace I (i z))}
    (hrange : LinearMap.range (mfderiv J I i z).toLinearMap = W) (v : TangentSpace J z) :
    hσ.tangentToReducedSpace hrange v =
      Submodule.Quotient.mk ⟨mfderiv J I i z v, hrange.le (LinearMap.mem_range_self _ v)⟩ :=
  (rfl)

omit [IsManifold J ∞ Z] in
private theorem surjective_tangentToReducedSpace {z : Z}
    {W : Submodule ℝ (TangentSpace I (i z))}
    (hrange : LinearMap.range (mfderiv J I i z).toLinearMap = W) :
    Surjective (hσ.tangentToReducedSpace hrange) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H u =>
  obtain ⟨v, hv⟩ : (u : TangentSpace I (i z)) ∈ LinearMap.range (mfderiv J I i z).toLinearMap :=
    hrange ▸ u.property
  exact ⟨v, by rw [tangentToReducedSpace_apply]; congr 1; exact Subtype.ext hv⟩

private theorem ker_tangentToReducedSpace (hi : ContMDiff J I ∞ i) {z : Z}
    {W : Submodule ℝ (TangentSpace I (i z))}
    (hrange : LinearMap.range (mfderiv J I i z).toLinearMap = W)
    (hker : LinearMap.ker ((SmoothForm.mpullback i hi σ).bilinFormAt z) =
      (mfderiv J JQ p z).ker) :
    LinearMap.ker (hσ.tangentToReducedSpace hrange) = (mfderiv J JQ p z).ker := by
  rw [← hker]
  ext v
  rw [LinearMap.mem_ker, tangentToReducedSpace_apply, SymplecticForm.ReducedSpace.mk_eq_zero_iff,
    SymplecticForm.mem_orthogonal_iff', LinearMap.mem_ker, LinearMap.ext_iff]
  simp only [LinearMap.zero_apply, SmoothForm.bilinFormAt_apply, SmoothForm.eval₂_mpullback]
  refine ⟨fun hv w ↦ ?_, fun hv y hy ↦ ?_⟩
  · rw [← IsNondegenerate.symplecticFormAt_apply hσ]
    exact hv _ (hrange ▸ LinearMap.mem_range_self _ w)
  · obtain ⟨w, rfl⟩ := hrange ▸ hy
    simpa [hσ.toBilinForm_symplecticFormAt, SmoothForm.bilinFormAt_apply] using hv w

/-- **The tangent space of a reduced space.** Let `σ` be nondegenerate, `i : Z → M` smooth and
`p : Z → Q`, and let `z` be a point of `Z` at which the image of `di_z` is `W`, the kernel of
`dp_z` is the kernel of the pulled-back form `(i^* σ)_z`, and `dp_z` is onto. Then the linear
symplectic reduction of `W` for `σ_{i z}`, the quotient of `W` by its intersection with its
`σ_{i z}`-orthogonal, is linearly equivalent to the tangent space of `Q` at `p z`: the class of
`di_z v` goes to `dp_z v`. -/
def reducedSpaceEquivTangentSpace (hi : ContMDiff J I ∞ i) (z : Z)
    {W : Submodule ℝ (TangentSpace I (i z))}
    (hrange : LinearMap.range (mfderiv J I i z).toLinearMap = W)
    (hker : LinearMap.ker ((SmoothForm.mpullback i hi σ).bilinFormAt z) =
      (mfderiv J JQ p z).ker)
    (hdp : Surjective (mfderiv J JQ p z)) :
    (hσ.symplecticFormAt (i z)).ReducedSpace W ≃ₗ[ℝ] TangentSpace JQ (p z) :=
  ((hσ.tangentToReducedSpace hrange).quotKerEquivOfSurjective
      (hσ.surjective_tangentToReducedSpace hrange)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (hσ.ker_tangentToReducedSpace hi hrange hker) ≪≫ₗ
    (mfderiv J JQ p z).toLinearMap.quotKerEquivOfSurjective hdp

/-- `reducedSpaceEquivTangentSpace` sends the class of `di_z v` to `dp_z v`, for a tangent vector
`v` of `Z` at `z`. -/
@[simp]
theorem reducedSpaceEquivTangentSpace_mk (hi : ContMDiff J I ∞ i) (z : Z)
    {W : Submodule ℝ (TangentSpace I (i z))}
    (hrange : LinearMap.range (mfderiv J I i z).toLinearMap = W)
    (hker : LinearMap.ker ((SmoothForm.mpullback i hi σ).bilinFormAt z) =
      (mfderiv J JQ p z).ker)
    (hdp : Surjective (mfderiv J JQ p z)) (v : TangentSpace J z) :
    hσ.reducedSpaceEquivTangentSpace hi z hrange hker hdp
        (Submodule.Quotient.mk ⟨mfderiv J I i z v, hrange.le (LinearMap.mem_range_self _ v)⟩) =
      mfderiv J JQ p z v := by
  rw [reducedSpaceEquivTangentSpace, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    ← tangentToReducedSpace_apply hσ hrange, (LinearEquiv.symm_apply_eq _).2
      (LinearMap.quotKerEquivOfSurjective_apply_mk _ _ v).symm,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk,
    ContinuousLinearMap.coe_coe]

/-- The inverse of `reducedSpaceEquivTangentSpace` sends `dp_z v` to the class of `di_z v`, for a
tangent vector `v` of `Z` at `z`. -/
theorem reducedSpaceEquivTangentSpace_symm_mfderiv (hi : ContMDiff J I ∞ i) (z : Z)
    {W : Submodule ℝ (TangentSpace I (i z))}
    (hrange : LinearMap.range (mfderiv J I i z).toLinearMap = W)
    (hker : LinearMap.ker ((SmoothForm.mpullback i hi σ).bilinFormAt z) =
      (mfderiv J JQ p z).ker)
    (hdp : Surjective (mfderiv J JQ p z)) (v : TangentSpace J z) :
    (hσ.reducedSpaceEquivTangentSpace hi z hrange hker hdp).symm (mfderiv J JQ p z v) =
      Submodule.Quotient.mk ⟨mfderiv J I i z v, hrange.le (LinearMap.mem_range_self _ v)⟩ := by
  rw [LinearEquiv.symm_apply_eq, reducedSpaceEquivTangentSpace_mk]

/-- **The reduced form on tangent spaces.** In the setting of `reducedSpaceEquivTangentSpace`,
let `p` be smooth and let `η` be a two-form on `Q` with `p^* η = i^* σ`. Then for `v, w ∈ W`, the
value of `η` at `p z` on the images of the classes of `v` and `w` is `σ_{i z}(v, w)`. -/
theorem eval₂_reducedSpaceEquivTangentSpace [IsManifold JQ ∞ Q] (hi : ContMDiff J I ∞ i)
    (hp : ContMDiff J JQ ∞ p) (z : Z) {W : Submodule ℝ (TangentSpace I (i z))}
    (hrange : LinearMap.range (mfderiv J I i z).toLinearMap = W)
    (hker : LinearMap.ker ((SmoothForm.mpullback i hi σ).bilinFormAt z) =
      (mfderiv J JQ p z).ker)
    (hdp : Surjective (mfderiv J JQ p z)) {η : SmoothTwoForm JQ Q}
    (hη : SmoothForm.mpullback p hp η = SmoothForm.mpullback i hi σ) (v w : W) :
    SmoothBundleForm.eval₂ η (p z)
        (hσ.reducedSpaceEquivTangentSpace hi z hrange hker hdp (Submodule.Quotient.mk v))
        (hσ.reducedSpaceEquivTangentSpace hi z hrange hker hdp (Submodule.Quotient.mk w)) =
      SmoothBundleForm.eval₂ σ (i z) v w := by
  obtain ⟨v, hv⟩ := v
  obtain ⟨w, hw⟩ := w
  obtain ⟨v', hv'⟩ := hrange ▸ hv
  obtain rfl : mfderiv J I i z v' = v := hv'
  obtain ⟨w', hw'⟩ := hrange ▸ hw
  obtain rfl : mfderiv J I i z w' = w := hw'
  rw [reducedSpaceEquivTangentSpace_mk, reducedSpaceEquivTangentSpace_mk,
    ← SmoothForm.eval₂_mpullback _ hp, hη]
  exact SmoothForm.eval₂_mpullback _ _ _ _ _ _

/-- **The tangent spaces of a reduced space, symplectically.** In the setting of
`reducedSpaceEquivTangentSpace`, let `p` be smooth and let `η` be a nondegenerate two-form on `Q`
with `p^* η = i^* σ`. Then `reducedSpaceEquivTangentSpace` is a symplectomorphism from the linear
symplectic reduction of `(W, σ_{i z})` to the tangent space of `Q` at `p z` with the form `η`. -/
theorem isSymplectomorphism_reducedSpaceEquivTangentSpace [IsManifold JQ ∞ Q]
    (hi : ContMDiff J I ∞ i)
    (hp : ContMDiff J JQ ∞ p) (z : Z) {W : Submodule ℝ (TangentSpace I (i z))}
    (hrange : LinearMap.range (mfderiv J I i z).toLinearMap = W)
    (hker : LinearMap.ker ((SmoothForm.mpullback i hi σ).bilinFormAt z) =
      (mfderiv J JQ p z).ker)
    (hdp : Surjective (mfderiv J JQ p z)) {η : SmoothTwoForm JQ Q} (hη : η.IsNondegenerate)
    (hpull : SmoothForm.mpullback p hp η = SmoothForm.mpullback i hi σ) :
    SymplecticForm.IsSymplectomorphism ((hσ.symplecticFormAt (i z)).reduction W)
      (hη.symplecticFormAt (p z)) (hσ.reducedSpaceEquivTangentSpace hi z hrange hker hdp) := by
  rw [SymplecticForm.isSymplectomorphism_iff]
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | H v =>
  induction y using Submodule.Quotient.induction_on with
  | H w =>
  rw [IsNondegenerate.symplecticFormAt_apply, SymplecticForm.reduction_mk,
    IsNondegenerate.symplecticFormAt_apply]
  exact hσ.eval₂_reducedSpaceEquivTangentSpace hi hp z hrange hker hdp hpull v w

end IsNondegenerate

end SmoothTwoForm

end TauCeti

end
