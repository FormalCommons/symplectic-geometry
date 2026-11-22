/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Contact.Gray
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import SymplecticGeometry.Geometry.Contact.Family
public import SymplecticGeometry.Geometry.Contact.Hamiltonian
public import SymplecticGeometry.Geometry.Contact.Moser
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Tangent.Opens
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Flow.Family

/-!
# The Gray vector field: naturality, and the Gray field of a family of contact structures

Let `α` be a one-form on `ℝ × N`, representing the family of its slices `α_t = ι_t^* α`, and let
`f : M → N` be smooth with bijective differentials. The slices of the pullback `(id × f)^* α` are
the pullbacks `f^* α_t`, and the slices of its time derivative are the pullbacks of the slices of
`∂_t α`. So if `α_t` is a contact form, the differential of `f` carries the Gray vector of the
pulled-back family at time `t` and point `x` to the Gray vector of `α` at time `t` and point
`f x` (`TauCeti.SmoothForm.mfderiv_grayVectorField_mpullback_prodMap`). The case of an open subset
`U ⊆ N`, `f = Subtype.val`, says that the Gray vector field of a family restricted to `ℝ × U`
is the restriction of the Gray vector field
(`TauCeti.SmoothForm.tangentSpaceOpenEquiv_grayVectorField_mpullback_prodMap_subtype_val`).
This lets one compare Gray vector fields of local defining families of a contact family that
live on different open sets.

The Gray vector at `(t, x)` only depends on the kernels of the slices near `(t, x)`, at the times
of a set such as `[0, 1]`
(`TauCeti.SmoothForm.grayVectorField_eq_of_eventually_kerDistribution_eq`):
two families with the same kernels differ by a nowhere vanishing factor, the value of one on the
Reeb field of the other, and `TauCeti.SmoothForm.grayVectorField_eq_of_eventuallyEq_smul` applies.
So two local defining families of a smooth family `ξ` of contact structures over `[0, 1]`, as
given by `SymplecticGeometry.IsContactFamily.exists_local_extension`, have the same Gray vector
at every time of `[0, 1]` and point where both are defined, once both are restricted to the
intersection of their open sets (`SymplecticGeometry.tangentSpaceOpenEquiv_grayVectorField_eq`).

On a σ-compact Hausdorff manifold, these local Gray fields glue to a smooth time-dependent vector
field on `ℝ × M`, the Gray field of `ξ` (`SymplecticGeometry.IsContactFamily.exists_grayField`).
The conditions on its value at a point, to lie in `ξ` and to be the Gray vector of every local
defining family, are convex, so Mathlib's `exists_contMDiffSection_forall_mem_convex_of_local`
glues local solutions with a smooth partition of unity. It is applied to the tangent bundle of
`ℝ × M`, the field being the `M` component of a section with vanishing `ℝ` component; away from
`[0, 1] × M` the local solution is `0`.

The comparison of two local defining families,
`SymplecticGeometry.tangentSpaceOpenEquiv_grayVectorField_eq`, follows the proofs of
`TauCeti.IsLocalContactFormFamily.mfderiv_grayVectorField_eq` and
`TauCeti.IsLocalContactFormFamily.mpullback_inclusion`, in Tau Ceti's file
`TauCeti/Geometry/Contact/Gray/Distribution.lean` at commit
034344347f0ca1144bf5ae35c82e3edaf848fca5 (Tau Ceti pull request #773), which the pinned version
of Tau Ceti does not have: both families are restricted to the intersection of their open sets,
the restrictions are contact forms with the same kernels, and naturality of the Gray vector field
under the inclusions concludes. The factor between two families with the same kernels in
`TauCeti.SmoothForm.grayVectorField_eq_of_eventually_kerDistribution_eq` is the one of
`TauCeti.SmoothForm.grayVectorField_eq_of_kerDistribution_eq`, in Tau Ceti's
`TauCeti/Geometry/Contact/Gray.lean` at the same commit.

## Main results

* `TauCeti.SmoothForm.mfderiv_grayVectorField_mpullback_prodMap`: naturality of the Gray vector
  field under `id × f` for maps `f` with bijective differentials.
* `TauCeti.SmoothForm.tangentSpaceOpenEquiv_grayVectorField_mpullback_prodMap_subtype_val`:
  its restriction to an open subset.
* `TauCeti.SmoothForm.grayVectorField_eq_of_eventually_kerDistribution_eq`: the Gray vector
  depends only on the kernels of the slices.
* `SymplecticGeometry.tangentSpaceOpenEquiv_grayVectorField_eq`: local defining families of a
  family of contact structures have the same Gray vectors.
* `SymplecticGeometry.IsContactFamily.exists_grayField`: the Gray field of a smooth family of
  contact structures.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.5,
  the discussion of Gray stability on pp. 135–136.
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.2.2 (Gray stability) and its proof.
-/

public section

open Filter TopologicalSpace
open scoped ContDiff Manifold Topology

namespace TauCeti.SmoothForm

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I ∞ M] [IsManifold J ∞ N] [I.Boundaryless] [J.Boundaryless]
  {α : SmoothForm (𝓘(ℝ, ℝ).prod J) (ℝ × N) ℝ 1}

/-- **Naturality of the Gray vector field.** Let `α` be a one-form on `ℝ × N` whose slice `α_t`
at time `t` is a contact form, and let `f : M → N` be smooth with bijective differentials. Then
the differential of `f` at `x` sends the Gray vector at time `t` and point `x` of the
pulled-back family `(id × f)^* α` to the Gray vector of `α` at time `t` and point `f x`. -/
theorem mfderiv_grayVectorField_mpullback_prodMap [FiniteDimensional ℝ E] {t : ℝ}
    (hc : (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
    (f : M → N) (hf : ContMDiff I J ∞ f)
    (hdf : ∀ x, Function.Bijective (mfderiv I J f x)) (x : M) :
    mfderiv I J f x
        ((mpullback (Prod.map id f) (contMDiff_id.prodMap hf) α).grayVectorField t x) =
      α.grayVectorField t (f x) := by
  rw [grayVectorField_def, grayVectorField_def, mpullback_prodMk_mpullback_prodMap,
    mpullback_prodMk_timeDeriv_mpullback_prodMap]
  exact hc.mfderiv_contactMoserVectorField_mpullback f hf hdf _ x

/-- **The Gray vector field restricts to open subsets.** Let `α` be a one-form on `ℝ × N` whose
slice `α_t` at time `t` is a contact form, and let `U ⊆ N` be open. Under the canonical
identification of tangent spaces, the Gray vector at time `t` and point `x ∈ U` of the
restriction of `α` to `ℝ × U` is the Gray vector of `α` at time `t` and point `x`. -/
theorem tangentSpaceOpenEquiv_grayVectorField_mpullback_prodMap_subtype_val
    [FiniteDimensional ℝ F] {t : ℝ}
    (hc : (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
    (U : Opens N) (x : U) :
    Manifold.tangentSpaceOpenEquiv x
        ((mpullback (Prod.map id Subtype.val) (contMDiff_id.prodMap contMDiff_subtypeVal)
          α).grayVectorField t x) =
      α.grayVectorField t x := by
  simpa only [Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe] using
    mfderiv_grayVectorField_mpullback_prodMap hc Subtype.val contMDiff_subtypeVal
      (fun y ↦ Manifold.mfderiv_subtype_val (I := J) y ▸
        (Manifold.tangentSpaceOpenEquiv (I := J) y).bijective) x

end TauCeti.SmoothForm

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]

/-- **The Gray vector depends only on the hyperplanes.** Let `α` and `α'` be one-forms on `ℝ × M`
such that every slice `α_u` and the slice `α'_t` are contact forms, and let `s ∋ t` be a set of
times on which derivatives at `t` are unique, such as `[0, 1]`. If the slices of `α` and `α'`
have the same kernels at the points `(u, y)` of `s × M` near `(t, x)`, then the Gray vector fields
of `α` and `α'` agree at time `t` and the point `x`. -/
theorem grayVectorField_eq_of_eventually_kerDistribution_eq
    {α α' : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1} {s : Set ℝ} {t : ℝ} {x : M}
    (hs : UniqueDiffWithinAt ℝ s t) (ht : t ∈ s)
    (hc : ∀ u, (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
    (hc' : (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α').IsContactForm)
    (h : ∀ᶠ q in 𝓝[s ×ˢ Set.univ] (t, x),
      (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α').kerDistribution q.2 =
        (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution q.2) :
    α'.grayVectorField t x = α.grayVectorField t x := by
  -- The multiplier is the value of `α'_u` on the Reeb field of `α_u`, smooth in `(u, y)`.
  have hf := contMDiff_apply_reebVectorField_mpullback_prodMk α α' hc
  have hmul : ∀ᶠ q in 𝓝[s ×ˢ Set.univ] (t, x),
      (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α').val q.2 =
        (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α').val q.2
          ![(mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField
            q.2] • (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α).val q.2 :=
    h.mono fun q hq ↦ (hc q.1).apply_eq_apply_reebVectorField_smul_of_kerDistribution_le
      (by rw [← hq, kerDistribution_eq_ker])
  refine grayVectorField_eq_of_eventuallyEq_smul hs ht (hc t) hc' ?_
    ((hf.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt (by simp)) ?_ hmul
  · exact ((contMDiff_iff_contDiff.1 (hf.comp (contMDiff_id.prodMk contMDiff_const))).differentiable
      (by simp) t).differentiableWithinAt
  · intro h₀
    refine hc'.apply_ne_zero x ?_
    rw [hmul.self_of_nhdsWithin ⟨ht, Set.mem_univ x⟩]
    exact (congrArg (· • _) h₀).trans (zero_smul ℝ _)

/-- **The Gray vector field restricts to smaller open subsets.** Let `α` be a one-form on `ℝ × U`,
for an open subset `U` of `M`, whose slice `α_t` is a contact form, and let `V ⊆ U` be open. Read
in the tangent space of `M`, the Gray vector at time `t` and point `x ∈ V` of the restriction of
`α` to `ℝ × V` is the Gray vector of `α` at time `t` and point `x`. -/
theorem tangentSpaceOpenEquiv_grayVectorField_mpullback_prodMap_inclusion {U V : Opens M}
    (hVU : V ≤ U) {α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1} {t : ℝ}
    (hc : (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
    (x : V) :
    Manifold.tangentSpaceOpenEquiv x ((mpullback (Prod.map id (Opens.inclusion hVU))
        (contMDiff_id.prodMap (contMDiff_inclusion hVU)) α).grayVectorField t x) =
      Manifold.tangentSpaceOpenEquiv (Opens.inclusion hVU x)
        (α.grayVectorField t (Opens.inclusion hVU x)) := by
  rw [← mfderiv_grayVectorField_mpullback_prodMap hc (Opens.inclusion hVU)
    (contMDiff_inclusion hVU)
    (fun y ↦ ((isLocalDiffeomorph_inclusion (n := ∞) hVU y).isInvertible_mfderiv
      (by simp)).bijective) x,
    Manifold.tangentSpaceOpenEquiv_mfderiv_apply (f := Opens.inclusion hVU) (A := id) rfl,
    mfderiv_id,
    ContinuousLinearMap.id_apply]

end TauCeti.SmoothForm

namespace SymplecticGeometry

open Set TauCeti TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  {ξ : unitInterval → Π x : M, Submodule ℝ (TangentSpace I x)}

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- Let `α` be a one-form on `ℝ × U`, for an open subset `U` of `M`, whose slices have kernels `ξ`
at the times of `(a, b) ∩ [0, 1]`. At such a time `t`, a tangent vector of `U` at `x` lies in the
kernel of `α_t` exactly when, read in the tangent space of `M`, it lies in `ξ t x`. -/
theorem mem_kerDistribution_iff_tangentSpaceOpenEquiv_mem {a b : ℝ} {U : Opens M}
    {α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1}
    (hα : ∀ (t : ℝ) (ht : t ∈ Ioo a b ∩ unitInterval) (x : U),
      ξ ⟨t, ht.2⟩ x = ((mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        α).kerDistribution x).map
          (Manifold.tangentSpaceOpenEquiv (I := I) x).toLinearEquiv.toLinearMap)
    {t : ℝ} (ht : t ∈ Ioo a b ∩ unitInterval) (x : U) (v : TangentSpace I x) :
    v ∈ (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x ↔
      Manifold.tangentSpaceOpenEquiv x v ∈ ξ ⟨t, ht.2⟩ x := by
  rw [hα t ht x, Submodule.mem_map_equiv, ContinuousLinearEquiv.coe_symm_toLinearEquiv,
    ContinuousLinearEquiv.symm_apply_apply]

/-- **Local Gray fields agree on overlaps.** Let `α` on `ℝ × U` and `α'` on `ℝ × U'` be local
defining families of a family `ξ` of distributions over `[0, 1]`, as given by
`SymplecticGeometry.IsContactFamily.exists_local_extension`: all their slices are contact forms,
and their kernels are `ξ` at the times of `(a, b) ∩ [0, 1]`, respectively `(a', b') ∩ [0, 1]`.
At a time `t ∈ [0, 1]` of both intervals and a point `x ∈ U ∩ U'`, their Gray vectors agree,
read in the tangent space of `M`. -/
theorem tangentSpaceOpenEquiv_grayVectorField_eq {a b a' b' : ℝ} {U U' : Opens M}
    {α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1} {α' : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U') ℝ 1}
    (hc : ∀ t, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
    (hc' : ∀ t, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α').IsContactForm)
    (hα : ∀ (t : ℝ) (ht : t ∈ Ioo a b ∩ unitInterval) (x : U),
      ξ ⟨t, ht.2⟩ x = ((mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        α).kerDistribution x).map
          (Manifold.tangentSpaceOpenEquiv (I := I) x).toLinearEquiv.toLinearMap)
    (hα' : ∀ (t : ℝ) (ht : t ∈ Ioo a' b' ∩ unitInterval) (x : U'),
      ξ ⟨t, ht.2⟩ x = ((mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        α').kerDistribution x).map
          (Manifold.tangentSpaceOpenEquiv (I := I) x).toLinearEquiv.toLinearMap)
    {t : ℝ} (ht : t ∈ unitInterval) (htab : t ∈ Ioo a b) (htab' : t ∈ Ioo a' b') {x : M}
    (hx : x ∈ U) (hx' : x ∈ U') :
    Manifold.tangentSpaceOpenEquiv ⟨x, hx⟩ (α.grayVectorField t ⟨x, hx⟩) =
      Manifold.tangentSpaceOpenEquiv ⟨x, hx'⟩ (α'.grayVectorField t ⟨x, hx'⟩) := by
  -- Compare the restrictions of both families to `ℝ × (U ∩ U')`.
  have hV : U ⊓ U' ≤ U := inf_le_left
  have hV' : U ⊓ U' ≤ U' := inf_le_right
  set β := mpullback (Prod.map id (Opens.inclusion hV)) (contMDiff_id.prodMap
    (contMDiff_inclusion hV)) α
  set β' := mpullback (Prod.map id (Opens.inclusion hV')) (contMDiff_id.prodMap
    (contMDiff_inclusion hV')) α'
  have hβ (u : ℝ) :
      (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) β).IsContactForm := by
    rw [mpullback_prodMk_mpullback_prodMap]
    exact (hc u).mpullback _ (contMDiff_inclusion hV) fun y ↦
      ((isLocalDiffeomorph_inclusion (n := ∞) hV y).isInvertible_mfderiv (by simp)).bijective
  have hβ' (u : ℝ) :
      (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) β').IsContactForm := by
    rw [mpullback_prodMk_mpullback_prodMap]
    exact (hc' u).mpullback _ (contMDiff_inclusion hV') fun y ↦
      ((isLocalDiffeomorph_inclusion (n := ∞) hV' y).isInvertible_mfderiv (by simp)).bijective
  -- At the times of both intervals in `[0, 1]`, both restrictions have kernels `ξ`.
  have hker : ∀ᶠ q in 𝓝[unitInterval ×ˢ univ] (t, (⟨x, hx, hx'⟩ : (U ⊓ U' : Opens M))),
      (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) β').kerDistribution q.2 =
        (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) β).kerDistribution q.2 := by
    have hJ : (Ioo a b ∩ Ioo a' b') ×ˢ (univ : Set (U ⊓ U' : Opens M)) ∈
        𝓝 (t, (⟨x, hx, hx'⟩ : (U ⊓ U' : Opens M))) :=
      prod_mem_nhds ((isOpen_Ioo.inter isOpen_Ioo).mem_nhds ⟨htab, htab'⟩) univ_mem
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hJ] with q hq hq'
    ext v
    rw [mpullback_prodMk_mpullback_prodMap _ (contMDiff_inclusion hV'),
      mpullback_prodMk_mpullback_prodMap _ (contMDiff_inclusion hV),
      kerDistribution_mpullback (Opens.inclusion hV') (contMDiff_inclusion hV'),
      kerDistribution_mpullback (Opens.inclusion hV) (contMDiff_inclusion hV), Submodule.mem_comap,
      Submodule.mem_comap, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe,
      mem_kerDistribution_iff_tangentSpaceOpenEquiv_mem hα' ⟨hq'.1.2, hq.1⟩,
      mem_kerDistribution_iff_tangentSpaceOpenEquiv_mem hα ⟨hq'.1.1, hq.1⟩,
      Manifold.tangentSpaceOpenEquiv_mfderiv_apply (f := Opens.inclusion hV') (A := id) rfl,
      Manifold.tangentSpaceOpenEquiv_mfderiv_apply (f := Opens.inclusion hV) (A := id) rfl,
      mfderiv_id,
      ContinuousLinearMap.id_apply]
  have h := congrArg (Manifold.tangentSpaceOpenEquiv _)
    (grayVectorField_eq_of_eventually_kerDistribution_eq (uniqueDiffOn_Icc zero_lt_one t ht)
      ht hβ (hβ' t) hker)
  rw [tangentSpaceOpenEquiv_grayVectorField_mpullback_prodMap_inclusion hV' (hc' t),
    tangentSpaceOpenEquiv_grayVectorField_mpullback_prodMap_inclusion hV (hc t)] at h
  -- `Opens.inclusion hV ⟨x, hx, hx'⟩` is `⟨x, hx⟩` by definition; `Set.inclusion_mk` cannot rewrite
  -- it in `h`, where the tangent spaces depend on the point.
  exact h.symm

namespace IsContactFamily

/-- **The Gray field of a smooth family of contact structures.** On a σ-compact Hausdorff
manifold without boundary, a smooth family `ξ` of contact structures over `[0, 1]` has a
time-dependent vector field `Y`, jointly smooth in `(t, x) ∈ ℝ × M`, such that for every time
`t ∈ [0, 1]` and point `x`:
* `Y t x` lies in `ξ t x`;
* `Y t x` is the Gray vector at `(t, x)` of every local defining family of `ξ` near `(t, x)`: for
  every open interval `(a, b) ∋ t`, open set `U ∋ x` and one-form `α` on `ℝ × U` all of whose
  slices are contact forms and whose kernels are `ξ` at the times of `(a, b) ∩ [0, 1]`, as given
  by `SymplecticGeometry.IsContactFamily.exists_local_extension`, the Gray vector of `α` at
  `(t, x)` is `Y t x`, the tangent spaces of `U` and `M` being identified.

At times outside `[0, 1]` nothing is said of `Y`. -/
theorem exists_grayField [T2Space M] [SigmaCompactSpace M] (hξ : IsContactFamily ξ) :
    ∃ Y : ℝ → Π x : M, TangentSpace I x,
      ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
        (fun p : ℝ × M ↦ (⟨p.2, Y p.1 p.2⟩ : TangentBundle I M)) ∧
      (∀ (t : ℝ) (ht : t ∈ unitInterval) (x : M), Y t x ∈ ξ ⟨t, ht⟩ x) ∧
      ∀ (t : ℝ), t ∈ unitInterval → ∀ (a b : ℝ), t ∈ Ioo a b → ∀ (U : Opens M) (x : M)
        (hx : x ∈ U) (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1),
        (∀ s, (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm) →
        (∀ (s : ℝ) (hs : s ∈ Ioo a b ∩ unitInterval) (y : U),
          ξ ⟨s, hs.2⟩ y = ((mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id)
            α).kerDistribution y).map
            (Manifold.tangentSpaceOpenEquiv (I := I) y).toLinearEquiv.toLinearMap) →
        Manifold.tangentSpaceOpenEquiv ⟨x, hx⟩ (α.grayVectorField t ⟨x, hx⟩) = Y t x := by
  classical
  -- The vector `w ∈ T_x M` is the Gray vector at `(t, x)` of every local defining family.
  let G (t : ℝ) (x : M) (w : TangentSpace I x) : Prop :=
    ∀ (a b : ℝ), t ∈ Ioo a b → ∀ (U : Opens M) (hx : x ∈ U)
      (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1),
      (∀ s, (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm) →
      (∀ (s : ℝ) (hs : s ∈ Ioo a b ∩ unitInterval) (y : U),
        ξ ⟨s, hs.2⟩ y = ((mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id)
          α).kerDistribution y).map
          (Manifold.tangentSpaceOpenEquiv (I := I) y).toLinearEquiv.toLinearMap) →
      Manifold.tangentSpaceOpenEquiv ⟨x, hx⟩ (α.grayVectorField t ⟨x, hx⟩) = w
  -- The field is glued as a section of the tangent bundle of `ℝ × M` with vanishing `ℝ`
  -- component, subject at times of `[0, 1]` to the conditions of the statement on its `M`
  -- component.
  let D (p : ℝ × M) : Set (TangentSpace I p.2) :=
    {w | ∀ ht : p.1 ∈ unitInterval, w ∈ ξ ⟨p.1, ht⟩ p.2 ∧ G p.1 p.2 w}
  have hD (p : ℝ × M) : Convex ℝ (D p) := by
    intro v hv w hw c d _ _ hcd ht
    refine ⟨add_mem (Submodule.smul_mem _ c (hv ht).1) (Submodule.smul_mem _ d (hw ht).1),
      fun a b hab U hx α hα hker ↦ ?_⟩
    rw [← (hv ht).2 a b hab U hx α hα hker, ← (hw ht).2 a b hab U hx α hα hker]
    exact (Convex.combo_self hcd _).symm
  let C (p : ℝ × M) : Set (TangentSpace (𝓘(ℝ, ℝ).prod I) p) :=
    Manifold.tangentSpaceProdEquiv p ⁻¹' ({0} ×ˢ D p)
  have hC (p : ℝ × M) : Convex ℝ (C p) :=
    ((convex_singleton _).prod (hD p)).linear_preimage _
  have hloc (p₀ : ℝ × M) : ∃ W ∈ 𝓝 p₀, ∃ s : (p : ℝ × M) → TangentSpace (𝓘(ℝ, ℝ).prod I) p,
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p ↦ (⟨p, s p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) W ∧
      ∀ p ∈ W, s p ∈ C p := by
    by_cases ht₀ : p₀.1 ∈ unitInterval
    · -- Near a point of `[0, 1] × M`, take the Gray field of a local defining family.
      obtain ⟨a, b, hab, U, hxU, α, hc, hα⟩ := hξ.exists_local_extension (⟨p₀.1, ht₀⟩, p₀.2)
      let w (p : ℝ × M) : TangentSpace I p.2 := if hx : p.2 ∈ U then
        Manifold.tangentSpaceOpenEquiv ⟨p.2, hx⟩ (α.grayVectorField p.1 ⟨p.2, hx⟩) else 0
      have hw := Manifold.contMDiffOn_tangentSpaceOpenEquiv_dite (J := 𝓘(ℝ, ℝ))
        (contMDiff_grayVectorField hc)
      refine ⟨Ioo a b ×ˢ U, prod_mem_nhds (isOpen_Ioo.mem_nhds hab) (U.isOpen.mem_nhds hxU),
        fun p ↦ (Manifold.tangentSpaceProdEquiv p).symm (0, w p), ?_, fun p hp ↦ ?_⟩
      · -- The section is `(0, w)` under the identification `T (ℝ × M) ≃ T ℝ × T M`.
        -- After `tangentSpaceProdEquiv_symm_apply`, both sides are `⟨p, (0, w p)⟩`, since
        -- `equivTangentBundleProd` leaves the components of a tangent vector unchanged.
        refine ContMDiffOn.congr (f := fun p ↦ (equivTangentBundleProd 𝓘(ℝ, ℝ) ℝ I M).symm
          (Bundle.zeroSection ℝ (TangentSpace 𝓘(ℝ, ℝ)) p.1, ⟨p.2, w p⟩)) ?_
          fun _ _ ↦ by simp only [Manifold.tangentSpaceProdEquiv_symm_apply]; rfl
        exact contMDiff_equivTangentBundleProd_symm.comp_contMDiffOn
          (((Bundle.contMDiff_zeroSection ℝ _).comp contMDiff_fst).contMDiffOn.prodMk
            (hw.mono fun p hp ↦ (mem_prod.1 hp).2))
      · obtain ⟨hp₁, hp₂⟩ := mem_prod.1 hp
        have hw' : w p = Manifold.tangentSpaceOpenEquiv ⟨p.2, hp₂⟩
            (α.grayVectorField p.1 ⟨p.2, hp₂⟩) := dite_eq_left hp₂
        rw [mem_preimage, ContinuousLinearEquiv.apply_symm_apply]
        refine ⟨mem_singleton _, fun ht ↦ ⟨?_, fun a' b' hab' U' hx' α' hc' hα' ↦ ?_⟩⟩
        · rw [hw']
          exact (mem_kerDistribution_iff_tangentSpaceOpenEquiv_mem hα ⟨hp₁, ht⟩ ⟨p.2, hp₂⟩ _).1
            (mem_kerDistribution.2 (apply_grayVectorField (hc p.1) _))
        · rw [hw']
          exact tangentSpaceOpenEquiv_grayVectorField_eq hc' hc hα' hα ht hab' hp₁ hx' hp₂
    · -- Away from `[0, 1] × M` the conditions are only on the `ℝ` component; take `0`.
      refine ⟨unitIntervalᶜ ×ˢ univ, prod_mem_nhds (isClosed_Icc.isOpen_compl.mem_nhds ht₀)
        univ_mem, fun _ ↦ 0, (Bundle.contMDiff_zeroSection ℝ _).contMDiffOn, fun p hp ↦ ?_⟩
      rw [mem_preimage, map_zero]
      exact ⟨mem_singleton _, fun ht ↦ absurd ht (mem_prod.1 hp).1⟩
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local (𝓘(ℝ, ℝ).prod I)
    (TangentSpace (𝓘(ℝ, ℝ).prod I)) C hC hloc
  refine ⟨fun t x ↦ (Manifold.tangentSpaceProdEquiv (t, x) (s (t, x))).2, ?_,
    fun t ht x ↦ ((hs (t, x)).2 ht).1,
    fun t ht a b hab U x hx α hα hker ↦ ((hs (t, x)).2 ht).2 a b hab U hx α hα hker⟩
  -- The field is the `M` component of `s` under `T (ℝ × M) ≃ T ℝ × T M`.
  simp only [Manifold.tangentSpaceProdEquiv_apply]
  exact contMDiff_snd.comp (contMDiff_equivTangentBundleProd.comp s.contMDiff)

end IsContactFamily

end SymplecticGeometry

end
