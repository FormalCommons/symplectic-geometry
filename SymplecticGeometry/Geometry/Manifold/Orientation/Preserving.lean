/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Topology.Algebra.Module.Determinant
import TauCeti.Geometry.Manifold.Orientation.Pullback

/-!
# Orientation-preserving maps between a manifold and its model space

A map of a finite-dimensional real normed space `E` whose derivative at `v` has positive
determinant preserves every orientation of `E` at `v`
(`TauCeti.Manifold.Orientation.isOrientationPreservingAt_of_det_fderiv_pos`). This is the
counterpart of Tau Ceti's `TauCeti.Manifold.Orientation.isOrientationReversingAt_of_det_fderiv_neg`,
and its proof is that of Tau Ceti's lemma with the sign changed. In particular, for `0 < c`, the
affine map `y ↦ q + c • (y - p)` of `E`, whose derivative `c • id` has determinant
`c ^ finrank ℝ E`, preserves every orientation of `E` at every point
(`TauCeti.Manifold.Orientation.isOrientationPreservingAt_add_smul_sub`).

The inverse of a chart of the maximal `C¹` atlas of a manifold modelled on `E` preserves
orientation at a point of its target when the chart preserves it at the corresponding point of its
source (`TauCeti.Manifold.Orientation.IsOrientationPreservingAt.symm_of_mem_maximalAtlas`). It
reads the chart as a partial diffeomorphism and applies Tau Ceti's
`TauCeti.Manifold.Orientation.IsOrientationPreservingAt.partialDiffeomorph_symm`.

A local diffeomorphism of a preconnected manifold preserves orientations at one point exactly when
it does at any other (`IsLocalDiffeomorph.isOrientationPreservingAt_iff`), by Tau Ceti's
`IsPreconnected.isOrientationPreservingAt_iff` on the whole manifold. So it preserves
orientations at every point or reverses them at every point
(`IsLocalDiffeomorph.forall_isOrientationPreservingAt_or_forall_isOrientationReversingAt`), and
negating the target orientation where needed makes it preserve, or reverse, orientations at every
point (`IsLocalDiffeomorph.exists_orientation_forall_isOrientationPreservingAt`,
`IsLocalDiffeomorph.exists_orientation_forall_isOrientationReversingAt`).

Orientation preservation of `g : M → N` at `x` can be read in the preferred tangent
trivializations at any two points whose base sets contain `x` and `g x`
(`TauCeti.Manifold.Orientation.isOrientationPreservingAt_iff_map_eq_of_mem`). This generalizes
Tau Ceti's `TauCeti.Manifold.Orientation.isOrientationPreservingAt_iff_map_eq`, whose source
trivialization is the one at `x` itself, and its proof follows Tau Ceti's.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 15.
-/

public section

open scoped Manifold

namespace TauCeti.Manifold.Orientation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

/-- **A positive Jacobian determinant preserves orientation.** A map of a finite-dimensional real
normed space whose derivative at `v` has positive determinant preserves every orientation there. -/
theorem isOrientationPreservingAt_of_det_fderiv_pos (o : Manifold.Orientation 𝓘(ℝ, E) E ι)
    {f : E → E} {v : E} (hdet : 0 < (fderiv ℝ f v).det) : IsOrientationPreservingAt o o f v := by
  let D : E ≃L[ℝ] E := (fderiv ℝ f v).toContinuousLinearEquivOfDetNeZero hdet.ne'
  refine (isOrientationPreservingAt_iff_of_coe_eq o o _ v D ?_).mpr ?_
  · rw [mfderiv_eq_fderiv]
    exact (fderiv ℝ f v).coe_toContinuousLinearEquivOfDetNeZero hdet.ne'
  · rw [orientationAt_eq_orientationAt o (f v) v]
    exact (_root_.Orientation.map_eq_iff_det_pos _ _ o.card_eq).mpr hdet

/-- **Positive homotheties preserve orientation.** For `0 < c`, the affine map
`y ↦ q + c • (y - p)` of a finite-dimensional real normed space `E` preserves every orientation of
`E` at every point. -/
theorem isOrientationPreservingAt_add_smul_sub (o : Manifold.Orientation 𝓘(ℝ, E) E ι) {c : ℝ}
    (hc : 0 < c) (q p v : E) : IsOrientationPreservingAt o o (fun y ↦ q + c • (y - p)) v := by
  refine isOrientationPreservingAt_of_det_fderiv_pos o ?_
  have hd : HasFDerivAt (fun y ↦ q + c • (y - p)) (c • ContinuousLinearMap.id ℝ E) v :=
    (((hasFDerivAt_id v).sub_const p).const_smul c).const_add q
  rw [hd.fderiv, ContinuousLinearMap.det_smul, ContinuousLinearMap.det_id, mul_one]
  positivity

/-- **The inverse of an oriented smooth chart preserves orientation.** If a chart `e` of the
maximal `C¹` atlas of a manifold `M` modelled on `E` preserves orientations at `e.symm y`, from
`o` to an orientation `o'` of `E`, then its inverse preserves them at `y`, from `o'` to `o`. -/
theorem IsOrientationPreservingAt.symm_of_mem_maximalAtlas {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] {o : Manifold.Orientation 𝓘(ℝ, E) M ι}
    {o' : Manifold.Orientation 𝓘(ℝ, E) E ι} {e : OpenPartialHomeomorph M E} {y : E}
    (h : IsOrientationPreservingAt o o' e (e.symm y))
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M) (hy : y ∈ e.target) :
    IsOrientationPreservingAt o' o e.symm y := by
  -- Read `e` as a partial diffeomorphism, whose inverse is `e.symm`.
  let Φ := e.toPartialDiffeomorphOfMemMaximalAtlas he
  have hΦ : ⇑Φ = ⇑e := funext fun x ↦ by simp [Φ]
  have hΦs : ⇑Φ.symm = ⇑e.symm := funext fun v ↦ by simp [Φ]
  have h' := IsOrientationPreservingAt.partialDiffeomorph_symm (Φ := Φ) (o := o) (o' := o')
    (by simpa [Φ] using hy) (by rwa [hΦ, hΦs]) one_ne_zero
  rwa [hΦs] at h'

/-- **Orientation preservation of a local diffeomorphism is global.** A `Cⁿ` local
diffeomorphism `f : M → M'`, for `n ≠ 0`, of a preconnected manifold `M` preserves the orientations
`o` and `o'` at one point exactly when it preserves them at any other. -/
theorem _root_.IsLocalDiffeomorph.isOrientationPreservingAt_iff {H E' H' M M' : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [PreconnectedSpace M] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 1 M'] {n : WithTop ℕ∞}
    {f : M → M'} (hf : IsLocalDiffeomorph I I' n f) (hn : n ≠ 0)
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι) (x y : M) :
    IsOrientationPreservingAt o o' f x ↔ IsOrientationPreservingAt o o' f y :=
  isPreconnected_univ.isOrientationPreservingAt_iff
    (fun z _ ↦ (hf z).contMDiffAt.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn))
    (fun z _ ↦ (hf z).isInvertible_mfderiv hn) o o' (Set.mem_univ x) (Set.mem_univ y)

/-- **A local diffeomorphism of a connected manifold preserves or reverses orientation.** A `Cⁿ`
local diffeomorphism `f : M → M'`, for `n ≠ 0`, out of a preconnected manifold `M` either
preserves the orientations `o` and `o'` at every point or reverses them at every point. -/
theorem
    _root_.IsLocalDiffeomorph.forall_isOrientationPreservingAt_or_forall_isOrientationReversingAt
    {H E' H' M M' : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [PreconnectedSpace M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
    [IsManifold I' 1 M'] {n : WithTop ℕ∞} {f : M → M'} (hf : IsLocalDiffeomorph I I' n f)
    (hn : n ≠ 0) (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι) :
    (∀ x, IsOrientationPreservingAt o o' f x) ∨ ∀ x, IsOrientationReversingAt o o' f x := by
  by_cases h : ∀ x, IsOrientationPreservingAt o o' f x
  · exact .inl h
  · obtain ⟨x, hx⟩ := not_forall.1 h
    exact .inr fun y ↦ ((hf y).isOrientationPreservingAt_or_isOrientationReversingAt hn o o'
      ).resolve_left fun hy ↦ hx ((hf.isOrientationPreservingAt_iff hn o o' x y).2 hy)

/-- For a `Cⁿ` local diffeomorphism `f : M → M'`, `n ≠ 0`, out of a preconnected manifold `M`,
and orientations `o` of `M` and `o'` of `M'`, either `o'` or `-o'` is an orientation of `M'` such
that `f` preserves orientation from `o` at every point. -/
theorem _root_.IsLocalDiffeomorph.exists_orientation_forall_isOrientationPreservingAt
    {H E' H' M M' : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [PreconnectedSpace M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
    [IsManifold I' 1 M'] {n : WithTop ℕ∞} {f : M → M'} (hf : IsLocalDiffeomorph I I' n f)
    (hn : n ≠ 0) (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι) :
    ∃ o'' ∈ ({o', -o'} : Set (Manifold.Orientation I' M' ι)),
      ∀ x, IsOrientationPreservingAt o o'' f x := by
  rcases hf.forall_isOrientationPreservingAt_or_forall_isOrientationReversingAt hn o o' with h | h
  · exact ⟨o', .inl rfl, h⟩
  · exact ⟨-o', .inr rfl, fun x ↦ (isOrientationPreservingAt_neg_right _ _ _ _).2 (h x)⟩

/-- For a `Cⁿ` local diffeomorphism `f : M → M'`, `n ≠ 0`, out of a preconnected manifold `M`,
and orientations `o` of `M` and `o'` of `M'`, either `o'` or `-o'` is an orientation of `M'` such
that `f` reverses orientation from `o` at every point. -/
theorem _root_.IsLocalDiffeomorph.exists_orientation_forall_isOrientationReversingAt
    {H E' H' M M' : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [PreconnectedSpace M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
    [IsManifold I' 1 M'] {n : WithTop ℕ∞} {f : M → M'} (hf : IsLocalDiffeomorph I I' n f)
    (hn : n ≠ 0) (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι) :
    ∃ o'' ∈ ({o', -o'} : Set (Manifold.Orientation I' M' ι)),
      ∀ x, IsOrientationReversingAt o o'' f x := by
  rcases hf.forall_isOrientationPreservingAt_or_forall_isOrientationReversingAt hn o o' with h | h
  · exact ⟨-o', .inr rfl, fun x ↦ (isOrientationReversingAt_neg_right _ _ _ _).2 (h x)⟩
  · exact ⟨o', .inl rfl, h⟩


section Trivialization

variable {E' H H' M N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H] [TopologicalSpace H'] {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]

/-- A map `g` preserves the orientations `o` and `o'` at `x` exactly when its derivative `D` at
`x`, read in the preferred trivializations of the tangent bundles at any points `a` and `b` whose
base sets contain `x` and `g x`, carries the orientation of `o` at `x` to that of `o'` at
`g x`, both read in the same trivializations. -/
theorem isOrientationPreservingAt_iff_map_eq_of_mem (o : Manifold.Orientation I M ι)
    (o' : Manifold.Orientation J N ι) (g : M → N) {x : M} (a : M) (b : N)
    (D : TangentSpace I x ≃L[ℝ] TangentSpace J (g x))
    (hDc : (D : TangentSpace I x →L[ℝ] TangentSpace J (g x)) = mfderiv I J g x)
    (hx : x ∈ (trivializationAt E (TangentSpace I) a).baseSet)
    (hp : g x ∈ (trivializationAt E' (TangentSpace J) b).baseSet) :
    IsOrientationPreservingAt o o' g x ↔
      _root_.Orientation.map ι
          (((((trivializationAt E (TangentSpace I) a).continuousLinearEquivAt ℝ x hx).symm.trans
            D).trans ((trivializationAt E' (TangentSpace J) b).continuousLinearEquivAt ℝ (g x)
              hp)).toLinearEquiv)
          ((trivializationAt E (TangentSpace I) a).mapOrientation ι hx (o.orientationAt x)) =
        (trivializationAt E' (TangentSpace J) b).mapOrientation ι hp (o'.orientationAt (g x)) := by
  rw [isOrientationPreservingAt_iff_of_coe_eq o o' _ x D hDc]
  have he : ((trivializationAt E (TangentSpace I) a).continuousLinearEquivAt ℝ x hx
      ).toLinearEquiv = (trivializationAt E (TangentSpace I) a).linearEquivAt ℝ x hx := by
    ext v
    simp [Bundle.Trivialization.continuousLinearEquivAt_apply]
  have he' : ((trivializationAt E' (TangentSpace J) b).continuousLinearEquivAt ℝ (g x) hp
      ).toLinearEquiv = (trivializationAt E' (TangentSpace J) b).linearEquivAt ℝ (g x) hp := by
    ext v
    simp [Bundle.Trivialization.continuousLinearEquivAt_apply]
  simp only [ContinuousLinearEquiv.trans_toLinearEquiv, _root_.Orientation.map_trans,
    Bundle.Trivialization.mapOrientation_apply, ContinuousLinearEquiv.toLinearEquiv_symm, he, he',
    ← _root_.Orientation.map_symm, Equiv.symm_apply_apply]
  exact (_root_.Orientation.map ι _).injective.eq_iff.symm

end Trivialization
end TauCeti.Manifold.Orientation

end
