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
public import SymplecticGeometry.Geometry.Manifold.Flow.TimeDependent
public import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Transports
public import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Velocity
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Basic
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Real

/-!
# The Gray vector field, the Gray isotopy and Gray stability

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
So two local defining families over `ℝ` (`SymplecticGeometry.IsLocalDefiningFamily`) of a smooth
family `ξ` of contact structures over `[0, 1]`, as given by
`SymplecticGeometry.IsContactFamily.exists_local_extension`, have the same Gray vector at every
time of `[0, 1]` and point where both are defined, once both are restricted to the intersection
of their open sets
(`SymplecticGeometry.IsLocalDefiningFamily.tangentSpaceOpenEquiv_grayVectorField_eq`).

On a σ-compact Hausdorff manifold, these local Gray fields glue to a smooth time-dependent vector
field on `ℝ × M`, the Gray field of `ξ` (`SymplecticGeometry.IsContactFamily.exists_grayField`).
The conditions on its value at a point, to lie in `ξ` and to be the Gray vector of every local
defining family, are convex, so Mathlib's `exists_contMDiffSection_forall_mem_convex_of_local`
glues local solutions with a smooth partition of unity. It is applied to the tangent bundle of
`ℝ × M`, the field being the `M` component of a section with vanishing `ℝ` component; away from
`[0, 1] × M` the local solution is `0`.

On a compact manifold the suspension of this field is complete, and its time-dependent flow from
time `0` is a diffeotopy, the Gray isotopy `ψ_t` of `ξ`
(`SymplecticGeometry.IsContactFamily.grayDiffeotopy`). Its velocity is the Gray field, which lies
in `ξ` (`SymplecticGeometry.IsContactFamily.velocity_grayDiffeotopy_mem`). It transports `ξ`,
`ψ_t^* ξ_t = ξ_0` (`SymplecticGeometry.IsContactFamily.transports_grayDiffeotopy`), by an
open-and-closed argument in `t`. Near a time `t₀` and the point `ψ_{t₀} x`, a local defining
family `α` on `ℝ × U` has, at the times of `[0, 1]` near `t₀`, the restriction of the Gray field
to `U` as its Gray vector field. By Gray's equation and the rescaling theorem along one trajectory
of `Flow/Family.lean`, the flow of that restriction, which is the flow of the Gray field, rescales
`α` along the trajectory of `ψ_{t₀} x`, so its differential carries `ξ_{t₀}` onto `ξ_t` there. With
the cocycle property of the flow, the pullback of `ξ_t` by `ψ_t` at `x` is a locally constant
function of `t`, equal to `ξ_0 x` at `t = 0`, and `[0, 1]` is connected.

The Gray isotopy is the only diffeotopy that transports `ξ` and whose velocity lies in `ξ`
(`SymplecticGeometry.IsContactFamily.eq_grayDiffeotopy_of_transports`). Such a diffeotopy `Φ` is
read over `ℝ` as `u ↦ φ_{s(u)}`, `s = Real.smoothTransition`, the time-dependent flow of its
Eulerian field `Z_u = s'(u) X_{s(u)}`. Near a point, take a local defining family `β` and its
reparametrization `β'_u = β_{s(u)}`. Since `Φ` transports `ξ`, the pullback of `β'_v` along the
flow from time `u` vanishes on `ker β'_u` for `v` near `u`, and so does its derivative at `v = u`,
`ι_u^* L_{∂_t} β' + L_{Z_u} β'_u`. As `β'_u(Z_u) = 0` on an open set, Cartan's formula leaves
`dβ_{s(u)}(Z_u, ·) + s'(u) ∂_t β_{s(u)}`, so `Z_u = s'(u) Y_{s(u)}` by
`TauCeti.SmoothForm.eq_grayVectorField_iff`. Two such diffeotopies are therefore both flows of the
same field, and agree, since `s` maps `ℝ` onto `[0, 1]`.

When `ξ` is the family of kernels of contact forms `α_t`, every diffeotopy `φ_t` that transports
`ξ` rescales them, `φ_t^* α_t = f_t α_0` with `f` smooth and positive and `f_0 = 1`
(`TauCeti.Diffeotopy.Transports.exists_mpullback_eq_smul`): `f_t` is the value of `φ_t^* α_t` on
the Reeb field of `α_0`, and it does not vanish on the connected interval. Together with the
existence and uniqueness this is Gray stability
(`SymplecticGeometry.IsContactFamily.existsUnique_transports`).

The comparison of two local defining families,
`SymplecticGeometry.IsLocalDefiningFamily.tangentSpaceOpenEquiv_grayVectorField_eq`, follows the
proofs of
`TauCeti.IsLocalContactFormFamily.mfderiv_grayVectorField_eq` and
`TauCeti.IsLocalContactFormFamily.mpullback_inclusion`, in Tau Ceti's file
`TauCeti/Geometry/Contact/Gray/Distribution.lean` at commit
034344347f0ca1144bf5ae35c82e3edaf848fca5 (Tau Ceti pull request #773), which the pinned version
of Tau Ceti does not have: both families are restricted to the intersection of their open sets,
the restrictions are contact forms with the same kernels, and naturality of the Gray vector field
under the inclusions concludes. The factor between two families with the same kernels in
`TauCeti.SmoothForm.grayVectorField_eq_of_eventually_kerDistribution_eq` is the one of
`TauCeti.SmoothForm.grayVectorField_eq_of_kerDistribution_eq`, in Tau Ceti's
`TauCeti/Geometry/Contact/Gray.lean` at the same commit. Gray's equation as a rate,
`TauCeti.SmoothForm.mpullback_prodMk_mlieDerivForm_add_mlieDerivForm_grayVectorField_apply`, is
the pointwise form of the private lemma
`TauCeti.SmoothForm.mpullback_prodMk_mlieDerivForm_add_mlieDerivForm_grayVectorField` of the
pinned Tau Ceti's `TauCeti/Geometry/Contact/Gray.lean`, with its proof.

## Main results

* `TauCeti.SmoothForm.mfderiv_grayVectorField_mpullback_prodMap`: naturality of the Gray vector
  field under `id × f` for maps `f` with bijective differentials.
* `TauCeti.SmoothForm.tangentSpaceOpenEquiv_grayVectorField_mpullback_prodMap_subtype_val`:
  its restriction to an open subset.
* `TauCeti.SmoothForm.grayVectorField_eq_of_eventually_kerDistribution_eq`: the Gray vector
  depends only on the kernels of the slices.
* `SymplecticGeometry.IsLocalDefiningFamily.tangentSpaceOpenEquiv_grayVectorField_eq`: local
  defining families of a family of contact structures have the same Gray vectors.
* `TauCeti.SmoothForm.mpullback_prodMk_mlieDerivForm_add_mlieDerivForm_grayVectorField_apply`:
  Gray's equation, in the form of the hypothesis of the rescaling theorems along flows.
* `SymplecticGeometry.IsContactFamily.exists_grayField`: the Gray field of a smooth family of
  contact structures.
* `SymplecticGeometry.IsContactFamily.grayDiffeotopy`: the Gray isotopy, with
  `SymplecticGeometry.IsContactFamily.exists_grayField_grayDiffeotopy_apply`, which gives it as a
  flow.
* `SymplecticGeometry.IsContactFamily.transports_grayDiffeotopy`: the Gray isotopy transports the
  family.
* `SymplecticGeometry.IsContactFamily.velocity_grayDiffeotopy_mem`: its velocity lies in the
  family.
* `SymplecticGeometry.IsContactFamily.eq_grayDiffeotopy_of_transports`: it is the only
  diffeotopy that transports the family with velocity in the family.
* `TauCeti.Diffeotopy.Transports.exists_mpullback_eq_smul`: a diffeotopy that transports the
  kernels of a family of contact forms rescales the forms by a smooth positive function.
* `SymplecticGeometry.IsContactFamily.existsUnique_transports`: Gray stability.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.5,
  the discussion of Gray stability on pp. 135–136, and Exercise 3.5.21.
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

omit [I.Boundaryless] in
/-- **Gray's equation, as a rate.** If the slice `α_t` of a family of one-forms on `ℝ × M` is a
contact form, then at each point `y` the rate `ι_t^* L_{∂_t} α + L_{Y_t} α_t` of the family along
its Gray vector field `Y` is `μ_t(y) • α_t(y)`, where `μ` is the Gray rate. This is the hypothesis
of the rescaling theorems along one trajectory of a time-dependent flow, in `Flow/Family.lean`. -/
theorem mpullback_prodMk_mlieDerivForm_add_mlieDerivForm_grayVectorField_apply
    {α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1} {t : ℝ}
    (hc : (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
    (y : M) :
    (TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
        (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α.val) +
      mlieDerivForm (α.grayVectorField t)
        (TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α.val)) y =
      α.grayRate (t, y) • TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α.val y := by
  ext v
  -- A one-form is determined by its value on the single vector `v 0`.
  have hv : v = ![v 0] := funext fun i ↦ by fin_cases i; rfl
  have h := mlieDerivForm_grayVectorField_add hc y (v 0)
  rw [hv]
  simp only [coe_mpullback, coe_timeDeriv, Pi.add_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h ⊢
  rw [add_comm, h]

end TauCeti.SmoothForm

namespace TauCeti.Diffeotopy

open Set TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- **Transporting diffeotopies rescale the forms.** Let `α` be a one-form on `[0, 1] × M` all of
whose slices `α_t` are contact forms, and let `Φ` be a diffeotopy that transports their kernels.
Then `φ_t^* α_t = f(t, ·) • α_0` for a smooth function `f` on `[0, 1] × M`, positive everywhere
and equal to `1` at time `0`. -/
theorem Transports.exists_mpullback_eq_smul {Φ : Diffeotopy I ∞ M}
    (α : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) ℝ 1)
    (hc : ∀ t, (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
      α).IsContactForm)
    (hΦ : Φ.Transports fun t ↦
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution) :
    ∃ f : unitInterval × M → ℝ, ContMDiff ((𝓡∂ 1).prod I) 𝓘(ℝ) ∞ f ∧ (∀ p, 0 < f p) ∧
      (∀ x, f (0, x) = 1) ∧ ∀ t x,
        (SmoothForm.mpullback (Φ.timeSlice t) (Φ.timeSlice t).contMDiff
          (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α)).val x =
          f (t, x) •
            (SmoothForm.mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) α).val x := by
  set α₀ := SmoothForm.mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) α
  -- The constant family of `α₀`, and the pullback of `α` by the total diffeomorphism.
  set κ := SmoothForm.mpullback (Prod.snd : unitInterval × M → M)
    (contMDiff_snd : ContMDiff ((𝓡∂ 1).prod I) I ∞ (Prod.snd : unitInterval × M → M)) α₀
  set β := SmoothForm.mpullback Φ.toDiffeomorph Φ.toDiffeomorph.contMDiff α
  have hκ (t : unitInterval) :
      SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) κ = α₀ := by
    rw [SmoothForm.mpullback_mpullback]
    exact LinearMap.congr_fun SmoothForm.mpullback_id α₀
  have hβ (t : unitInterval) :
      SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β =
        SmoothForm.mpullback (Φ.timeSlice t) (Φ.timeSlice t).contMDiff
          (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α) :=
    SmoothForm.mpullback_mpullback_of_comp_eq (f := Prod.mk t) (g := Φ.toDiffeomorph)
      (f' := Φ.timeSlice t) (g' := Prod.mk t) _ _ _ _
      (funext fun x ↦ by
        rw [Function.comp_apply, Function.comp_apply, Φ.toDiffeomorph_apply, timeSlice_apply]) α
  have hf := contMDiff_apply_reebVectorField_mpullback_prodMk κ β fun t ↦ (hκ t).symm ▸ hc 0
  simp only [hκ, hβ] at hf
  set f : unitInterval × M → ℝ := fun p ↦
    (SmoothForm.mpullback (Φ.timeSlice p.1) (Φ.timeSlice p.1).contMDiff
      (SmoothForm.mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α)).val p.2
        ![α₀.reebVectorField p.2] with hfdef
  -- By the transport, `φ_t^* α_t` and `α₀` have the same kernel, so the first is `f • α₀`.
  have heq (t : unitInterval) (x : M) :
      (SmoothForm.mpullback (Φ.timeSlice t) (Φ.timeSlice t).contMDiff
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α)).val x =
        f (t, x) • α₀.val x := by
    refine (hc 0).apply_eq_apply_reebVectorField_smul_of_kerDistribution_le ?_
    have h := transports_iff.1 hΦ t x
    rw [← timeSlice_apply] at h
    rw [← kerDistribution_eq_ker, kerDistribution_mpullback (Φ.timeSlice t)]
    exact h.le
  have hne (t : unitInterval) (x : M) : f (t, x) ≠ 0 := by
    intro h
    refine ((hc t).mpullback _ (Φ.timeSlice t).contMDiff fun y ↦
      ((Φ.timeSlice t).isInvertible_mfderiv (x := y) (by simp)).bijective).apply_ne_zero x ?_
    rw [heq, h, zero_smul]
  have h0 (x : M) : f (0, x) = 1 := by
    rw [hfdef]
    dsimp only
    rw [coe_mpullback, timeSlice_zero, Diffeomorph.coe_refl, TauCeti.mpullback_id]
    exact (hc 0).apply_reebVectorField x
  refine ⟨f, hf, fun p ↦ ?_, h0, heq⟩
  -- On the connected interval, the nowhere vanishing `t ↦ f (t, x)` keeps the sign of `f (0, x)`.
  by_contra hneg
  obtain ⟨s, -, hs⟩ := isPreconnected_univ.intermediate_value (mem_univ p.1) (mem_univ 0)
    (hf.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    ⟨not_lt.1 hneg, (h0 p.2).ge.trans' zero_le_one⟩
  exact hne s p.2 hs

end TauCeti.Diffeotopy

namespace SymplecticGeometry

open Set TauCeti TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  {ξ : unitInterval → Π x : M, Submodule ℝ (TangentSpace I x)}

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [I.Boundaryless] in
/-- A tangent vector at `p` lies in `D p` exactly when, read at a point `q` equal to `p`, it lies in
`D q`. -/
private theorem mem_iff_mem_of_eq (D : Π x : M, Submodule ℝ (TangentSpace I x)) {p q : M}
    (h : p = q) (v : TangentSpace I p) : v ∈ D p ↔ (v : TangentSpace I q) ∈ D q := by
  subst h
  exact Iff.rfl

/-- **Local Gray fields agree on overlaps.** Let `α` on `ℝ × U` and `α'` on `ℝ × U'` be local
defining families over `ℝ` of a family `ξ` of distributions over `[0, 1]`, on the time intervals
`(a, b)` and `(a', b')`, as given by `SymplecticGeometry.IsContactFamily.exists_local_extension`.
At a time `t ∈ [0, 1]` of both intervals and a point `x ∈ U ∩ U'`, their Gray vectors agree,
read in the tangent space of `M`. -/
theorem IsLocalDefiningFamily.tangentSpaceOpenEquiv_grayVectorField_eq {a b a' b' : ℝ}
    {U U' : Opens M} {α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1}
    {α' : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U') ℝ 1} (hα : IsLocalDefiningFamily ξ U α a b)
    (hα' : IsLocalDefiningFamily ξ U' α' a' b') {t : ℝ} (ht : t ∈ unitInterval) (htab : t ∈ Ioo a b)
    (htab' : t ∈ Ioo a' b') {x : M} (hx : x ∈ U) (hx' : x ∈ U') :
    Manifold.tangentSpaceOpenEquiv ⟨x, hx⟩ (α.grayVectorField t ⟨x, hx⟩) =
      Manifold.tangentSpaceOpenEquiv ⟨x, hx'⟩ (α'.grayVectorField t ⟨x, hx'⟩) := by
  have hc := hα.isContactForm
  have hc' := hα'.isContactForm
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
      hα'.mem_kerDistribution_iff ⟨hq'.1.2, hq.1⟩, hα.mem_kerDistribution_iff ⟨hq'.1.1, hq.1⟩,
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
  every open interval `(a, b) ∋ t`, open set `U ∋ x` and local defining family `α` over `ℝ` of
  `ξ` on `U` and `(a, b)` (`SymplecticGeometry.IsLocalDefiningFamily`), as given by
  `SymplecticGeometry.IsContactFamily.exists_local_extension`, the Gray vector of `α` at `(t, x)`
  is `Y t x`, the tangent spaces of `U` and `M` being identified.

At times outside `[0, 1]` nothing is said of `Y`. -/
theorem exists_grayField [T2Space M] [SigmaCompactSpace M] (hξ : IsContactFamily ξ) :
    ∃ Y : ℝ → Π x : M, TangentSpace I x,
      ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
        (fun p : ℝ × M ↦ (⟨p.2, Y p.1 p.2⟩ : TangentBundle I M)) ∧
      (∀ (t : ℝ) (ht : t ∈ unitInterval) (x : M), Y t x ∈ ξ ⟨t, ht⟩ x) ∧
      ∀ (t : ℝ), t ∈ unitInterval → ∀ (a b : ℝ), t ∈ Ioo a b → ∀ (U : Opens M) (x : M)
        (hx : x ∈ U) (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1),
        IsLocalDefiningFamily ξ U α a b →
        Manifold.tangentSpaceOpenEquiv ⟨x, hx⟩ (α.grayVectorField t ⟨x, hx⟩) = Y t x := by
  classical
  -- The vector `w ∈ T_x M` is the Gray vector at `(t, x)` of every local defining family.
  let G (t : ℝ) (x : M) (w : TangentSpace I x) : Prop :=
    ∀ (a b : ℝ), t ∈ Ioo a b → ∀ (U : Opens M) (hx : x ∈ U)
      (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1), IsLocalDefiningFamily ξ U α a b →
      Manifold.tangentSpaceOpenEquiv ⟨x, hx⟩ (α.grayVectorField t ⟨x, hx⟩) = w
  -- The field is glued as a section of the tangent bundle of `ℝ × M` with vanishing `ℝ`
  -- component, subject at times of `[0, 1]` to the conditions of the statement on its `M`
  -- component.
  let D (p : ℝ × M) : Set (TangentSpace I p.2) :=
    {w | ∀ ht : p.1 ∈ unitInterval, w ∈ ξ ⟨p.1, ht⟩ p.2 ∧ G p.1 p.2 w}
  have hD (p : ℝ × M) : Convex ℝ (D p) := by
    intro v hv w hw c d _ _ hcd ht
    refine ⟨add_mem (Submodule.smul_mem _ c (hv ht).1) (Submodule.smul_mem _ d (hw ht).1),
      fun a b hab U hx α hα ↦ ?_⟩
    rw [← (hv ht).2 a b hab U hx α hα, ← (hw ht).2 a b hab U hx α hα]
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
      obtain ⟨a, b, hab, U, hxU, α, hα⟩ := hξ.exists_local_extension (⟨p₀.1, ht₀⟩, p₀.2)
      let w (p : ℝ × M) : TangentSpace I p.2 := if hx : p.2 ∈ U then
        Manifold.tangentSpaceOpenEquiv ⟨p.2, hx⟩ (α.grayVectorField p.1 ⟨p.2, hx⟩) else 0
      have hw := Manifold.contMDiffOn_tangentSpaceOpenEquiv_dite (J := 𝓘(ℝ, ℝ))
        (contMDiff_grayVectorField hα.isContactForm)
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
        refine ⟨mem_singleton _, fun ht ↦ ⟨?_, fun a' b' hab' U' hx' α' hα' ↦ ?_⟩⟩
        · rw [hw']
          exact (hα.mem_kerDistribution_iff ⟨hp₁, ht⟩ ⟨p.2, hp₂⟩ _).1
            (mem_kerDistribution.2 (apply_grayVectorField (hα.isContactForm p.1) _))
        · rw [hw']
          exact hα'.tangentSpaceOpenEquiv_grayVectorField_eq hα ht hab' hp₁ hx' hp₂
    · -- Away from `[0, 1] × M` the conditions are only on the `ℝ` component; take `0`.
      refine ⟨unitIntervalᶜ ×ˢ univ, prod_mem_nhds (isClosed_Icc.isOpen_compl.mem_nhds ht₀)
        univ_mem, fun _ ↦ 0, (Bundle.contMDiff_zeroSection ℝ _).contMDiffOn, fun p hp ↦ ?_⟩
      rw [mem_preimage, map_zero]
      exact ⟨mem_singleton _, fun ht ↦ absurd ht (mem_prod.1 hp).1⟩
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local (𝓘(ℝ, ℝ).prod I)
    (TangentSpace (𝓘(ℝ, ℝ).prod I)) C hC hloc
  refine ⟨fun t x ↦ (Manifold.tangentSpaceProdEquiv (t, x) (s (t, x))).2, ?_,
    fun t ht x ↦ ((hs (t, x)).2 ht).1,
    fun t ht a b hab U x hx α hα ↦ ((hs (t, x)).2 ht).2 a b hab U hx α hα⟩
  -- The field is the `M` component of `s` under `T (ℝ × M) ≃ T ℝ × T M`.
  simp only [Manifold.tangentSpaceProdEquiv_apply]
  exact contMDiff_snd.comp (contMDiff_equivTangentBundleProd.comp s.contMDiff)


section GrayDiffeotopy

variable [T2Space M]

/-- Transport along the flow of a Gray field, near one time. Let `Y` be a smooth field with the
properties of `SymplecticGeometry.IsContactFamily.exists_grayField`. For `t` in `[0, 1]` near
`t₀`, the flow of `Y` from `t₀` to `t` is defined at `y₀`, and its differential pulls `ξ_t` back
to `ξ_{t₀}` at `y₀`. A local defining family `α` on `ℝ × U` near `(t₀, y₀)` has the restriction of
`Y` to `U` as Gray field at the times between `t₀` and `t`, so along the trajectory of `y₀` the
flow rescales `α`. -/
private theorem eventually_comap_mfderiv_timeDependentFlowOf (hξ : IsContactFamily ξ)
    {Y : ℝ → Π x : M, TangentSpace I x}
    (hY : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
        (fun p : ℝ × M ↦ (⟨p.2, Y p.1 p.2⟩ : TangentBundle I M)))
    (hgray : ∀ (t : ℝ), t ∈ unitInterval → ∀ (a b : ℝ), t ∈ Ioo a b → ∀ (U : Opens M) (x : M)
        (hx : x ∈ U) (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1),
        IsLocalDefiningFamily ξ U α a b →
        Manifold.tangentSpaceOpenEquiv ⟨x, hx⟩ (α.grayVectorField t ⟨x, hx⟩) = Y t x)
    (t₀ : unitInterval) (y₀ : M) :
    ∀ᶠ t : ℝ in 𝓝 (t₀ : ℝ), ∀ ht : t ∈ unitInterval,
      (((t₀ : ℝ), t), y₀) ∈ timeDependentFlowDomain Y ∧
      (ξ ⟨t, ht⟩ (timeDependentFlowOf Y t₀ t y₀)).comap
        (mfderiv I I (timeDependentFlowOf Y t₀ t) y₀).toLinearMap = ξ t₀ y₀ := by
  obtain ⟨a, b, hab, U, hy₀, α, hα⟩ := hξ.exists_local_extension (t₀, y₀)
  have hc := hα.isContactForm
  -- The restriction of `Y` to `U`.
  set XU : ℝ → (y : U) → TangentSpace I y :=
    fun u y ↦ (Manifold.tangentSpaceOpenEquiv y).symm (Y u y)
  have hXU : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × U ↦ (⟨p.2, XU p.1 p.2⟩ : TangentBundle I U)) :=
    Manifold.contMDiff_tangentSpaceOpenEquiv_symm (f := Prod.snd)
      (hY.comp (contMDiff_fst.prodMk (contMDiff_subtypeVal.comp contMDiff_snd)))
  have hXU₁ := hXU.of_le (m := 1) (by simp)
  have hY₁ := hY.of_le (m := 1) (by simp)
  set y₀' : U := ⟨y₀, hy₀⟩
  have hdom : ∀ᶠ t : ℝ in 𝓝 (t₀ : ℝ), (((t₀ : ℝ), t), y₀') ∈ timeDependentFlowDomain XU :=
    ((isOpen_timeDependentFlowDomain hXU₁).preimage (by fun_prop)).mem_nhds
      (mem_timeDependentFlowDomain_self hXU₁ _ _)
  filter_upwards [hdom, isOpen_Ioo.mem_nhds hab] with t hdom htab ht
  obtain ⟨hdomM, hpt⟩ := timeDependentFlowOf_restrict_eq hY₁ hdom
  refine ⟨hdomM, ?_⟩
  -- The times between `t₀` and `t` lie in `(a, b) ∩ [0, 1]`, where `XU` is the Gray field of `α`.
  have huIcc : uIcc (t₀ : ℝ) t ⊆ Ioo a b ∩ unitInterval :=
    (ordConnected_Ioo.inter ordConnected_Icc).uIcc_subset ⟨hab, t₀.property⟩ ⟨htab, ht⟩
  have hXUα (u : ℝ) (hu : u ∈ uIcc (t₀ : ℝ) t) : XU u = α.grayVectorField u := by
    funext y
    simp only [XU]
    rw [← hgray u (huIcc hu).2 a b (huIcc hu).1 U y y.property α hα]
    exact ContinuousLinearEquiv.symm_apply_apply _ _
  have hdomU (u : ℝ) (hu : u ∈ uIcc (t₀ : ℝ) t) :
      (((t₀ : ℝ), u), y₀') ∈ timeDependentFlowDomain XU :=
    (ordConnected_setOf_mem_timeDependentFlowDomain _ _).uIcc_subset
      (mem_timeDependentFlowDomain_self hXU₁ _ _) hdom hu
  -- Along the trajectory of `y₀'`, the flow of `XU` rescales `α` (the name of the theorem does not
  -- fit in an indented line).
  have key :=
mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_forall_mem_uIcc_of_mem
      (X := XU) (α := α.val) (hXU.of_le (by simp)) hdom
      (fun u _ ↦ (α.contMDiff.of_le (by simp)).contMDiffAt)
      (c := fun u ↦ α.grayRate (u, timeDependentFlowOf XU t₀ u y₀'))
      ((contMDiff_grayRate hc).continuous.comp_continuousOn (continuousOn_id.prodMk
        fun u hu ↦ (hasMFDerivAt_timeDependentFlowOf hXU₁ (hdomU u hu)).continuousAt
          |>.continuousWithinAt))
      (fun u hu ↦ by
        rw [hXUα u hu]
        exact mpullback_prodMk_mlieDerivForm_add_mlieDerivForm_grayVectorField_apply (hc u) _)
  -- The rescaling identity, evaluated on a vector at `y₀'`, compares the kernels.
  have hker (v : TangentSpace I y₀') :
      mfderiv I I (timeDependentFlowOf XU t₀ t) y₀' v ∈
          (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution
            (timeDependentFlowOf XU t₀ t y₀') ↔
        v ∈ (mpullback (Prod.mk (t₀ : ℝ)) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution
          y₀' := by
    have hk := congrArg (fun A ↦ A ![v]) key
    have hv : (fun i ↦ mfderiv I I (timeDependentFlowOf XU t₀ t) y₀' (![v] i)) =
        ![mfderiv I I (timeDependentFlowOf XU t₀ t) y₀' v] :=
      funext fun i ↦ by fin_cases i; rfl
    simp only [TauCeti.mpullback_apply (f := timeDependentFlowOf XU t₀ t), hv,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul] at hk
    rw [mem_kerDistribution, mem_kerDistribution, coe_mpullback, coe_mpullback, hk,
      mul_eq_zero_iff_left (Real.exp_pos _).ne']
  -- Read in `M`, through the flow of `Y`.
  ext w
  have hw := tangentSpaceOpenEquiv_mfderiv_timeDependentFlowOf_restrict hY₁ hdom
    ((Manifold.tangentSpaceOpenEquiv y₀').symm w)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hw
  rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, ← hw]
  refine (mem_iff_mem_of_eq (ξ ⟨t, ht⟩) hpt _).symm.trans ?_
  exact ((hα.mem_kerDistribution_iff ⟨htab, ht⟩ _ _).symm.trans
    (hker _)).trans ((hα.mem_kerDistribution_iff ⟨hab, t₀.property⟩ y₀' _).trans
      (by rw [ContinuousLinearEquiv.apply_symm_apply]))

/-- The Eulerian field of a normalized transporting diffeotopy, read over `ℝ`. Let `Φ` transport
`ξ` with velocity in `ξ`, and let `Y` be a field with the properties of
`SymplecticGeometry.IsContactFamily.exists_grayField`. The family `u ↦ φ_{s(u)}`,
`s = Real.smoothTransition`, has Eulerian field `s'(u) • Y_{s(u)}`. Where `s'(u) ≠ 0`, take a local
defining family `β` near `(s(u), y)` and reparametrize it to `β'_v = β_{s(v)}`. The pullback of
`β'_v` along the flow from time `u` vanishes on `ker β'_u` for `v` near `u`, because `Φ`
transports `ξ`. So does its derivative at `v = u`, which by Cartan's formula and `β'_u(Z_u) = 0` is
`dβ_{s(u)}(Z_u, ·) + s'(u) ∂_t β_{s(u)}`; then `s'(u)⁻¹ Z_u` is the Gray vector of `β`. -/
private theorem eulerianField_smoothTransitionFamily_eq (hξ : IsContactFamily ξ)
    {Y : ℝ → Π x : M, TangentSpace I x}
    (hgray : ∀ (t : ℝ), t ∈ unitInterval → ∀ (a b : ℝ), t ∈ Ioo a b → ∀ (U : Opens M) (x : M)
        (hx : x ∈ U) (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1),
        IsLocalDefiningFamily ξ U α a b →
        Manifold.tangentSpaceOpenEquiv ⟨x, hx⟩ (α.grayVectorField t ⟨x, hx⟩) = Y t x)
    {Φ : Diffeotopy I ∞ M} (hΦ : Φ.Transports ξ) (hv : ∀ t y, Φ.velocity t y ∈ ξ t y)
    (u : ℝ) (y : M) :
    eulerianField I (fun v ↦ (Φ.smoothTransitionFamily v).toEquiv) u y =
      deriv Real.smoothTransition u • Y (Real.smoothTransition u) y := by
  obtain ⟨Z, hZdef⟩ : ∃ Z, Z = eulerianField I (fun v ↦ (Φ.smoothTransitionFamily v).toEquiv) :=
    ⟨_, rfl⟩
  rw [← hZdef]
  have hZeq (u' : ℝ) (y' : M) :
      Z u' y' = deriv Real.smoothTransition u' • Φ.velocity (Real.smoothTransitionUnit u') y' := by
    rw [hZdef, Φ.eulerianField_smoothTransitionFamily u', ContMDiffSection.coe_smul, Pi.smul_apply]
  by_cases hd : deriv Real.smoothTransition u = 0
  · rw [hZeq, hd, zero_smul, zero_smul]
  have hs : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ Real.smoothTransition :=
    Real.smoothTransition.contDiff.contMDiff
  have hsI (u' : ℝ) : Real.smoothTransition u' ∈ unitInterval :=
    ⟨Real.smoothTransition.nonneg u', Real.smoothTransition.le_one u'⟩
  have hunit (u' : ℝ) :
      (⟨Real.smoothTransition u', hsI u'⟩ : unitInterval) = Real.smoothTransitionUnit u' :=
    Subtype.ext (Real.coe_smoothTransitionUnit u').symm
  -- The velocities of `Φ` lie in `ξ`, so the Eulerian field does.
  have hZmem (u' : ℝ) (y' : M) : Z u' y' ∈ ξ (Real.smoothTransitionUnit u') y' := by
    rw [hZeq]
    exact Submodule.smul_mem _ _ (hv _ _)
  have hZ : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, Z p.1 p.2⟩ : TangentBundle I M)) :=
    hZdef ▸ Φ.contMDiff_eulerianField_smoothTransitionFamily
  have hZ₁ := hZ.of_le (m := 1) (by simp)
  have hflow (u' : ℝ) : timeDependentFlowOf Z u u' =
      fun y' ↦ Φ.timeSlice (Real.smoothTransitionUnit u')
        ((Φ.timeSlice (Real.smoothTransitionUnit u)).symm y') := by
    funext y'
    rw [hZdef, Φ.timeDependentFlowOf_eulerianField_smoothTransitionFamily,
      Diffeotopy.smoothTransitionFamily_def, Diffeotopy.smoothTransitionFamily_def]
  -- A local defining family `β` near `(s u, y)`, with `y = φ_{s u} x`, read over `ℝ` as `β'`.
  obtain ⟨x, rfl⟩ : ∃ x, Φ.timeSlice (Real.smoothTransitionUnit u) x = y :=
    (Φ.timeSlice (Real.smoothTransitionUnit u)).surjective y
  obtain ⟨a, b, hab, U, hxU, β, hβ⟩ :=
    hξ.exists_local_extension
      (Real.smoothTransitionUnit u, Φ.timeSlice (Real.smoothTransitionUnit u) x)
  rw [Real.coe_smoothTransitionUnit] at hab
  set β' := mpullback (Prod.map Real.smoothTransition id) (hs.prodMap contMDiff_id) β
  have hslice (u' : ℝ) : mpullback (Prod.mk u') (contMDiff_const.prodMk contMDiff_id) β' =
      mpullback (Prod.mk (Real.smoothTransition u')) (contMDiff_const.prodMk contMDiff_id) β := by
    rw [mpullback_prodMk_mpullback_prodMap' hs id contMDiff_id]
    exact LinearMap.congr_fun SmoothForm.mpullback_id _
  have hdslice : mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) β'.timeDeriv =
      deriv Real.smoothTransition u • mpullback (Prod.mk (Real.smoothTransition u))
        (contMDiff_const.prodMk contMDiff_id) β.timeDeriv := by
    rw [mpullback_prodMk_timeDeriv_mpullback_prodMap' hs id contMDiff_id, SmoothForm.mpullback_id,
      LinearMap.id_apply]
  have hker (u' : ℝ) (hu' : Real.smoothTransition u' ∈ Ioo a b) (z : U) (v : TangentSpace I z) :
      v ∈ (mpullback (Prod.mk (Real.smoothTransition u')) (contMDiff_const.prodMk contMDiff_id)
        β).kerDistribution z ↔
        Manifold.tangentSpaceOpenEquiv z v ∈ ξ (Real.smoothTransitionUnit u') z := by
    rw [hβ.mem_kerDistribution_iff ⟨hu', hsI u'⟩, hunit]
  -- The restriction `ZU` of `Z` to `U`, which lies in the kernels of `β`.
  set ZU : ℝ → (z : U) → TangentSpace I z :=
    fun u' z ↦ (Manifold.tangentSpaceOpenEquiv z).symm (Z u' z)
  have hZU : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × U ↦ (⟨p.2, ZU p.1 p.2⟩ : TangentBundle I U)) :=
    Manifold.contMDiff_tangentSpaceOpenEquiv_symm (f := Prod.snd)
      (hZ.comp (contMDiff_fst.prodMk (contMDiff_subtypeVal.comp contMDiff_snd)))
  have hZU₁ := hZU.of_le (m := 1) (by simp)
  have hZker (z : U) : (mpullback (Prod.mk (Real.smoothTransition u))
      (contMDiff_const.prodMk contMDiff_id) β).val z ![ZU u z] = 0 := by
    rw [← mem_kerDistribution, hker u hab, ContinuousLinearEquiv.apply_symm_apply]
    exact hZmem u z
  set y' : U := ⟨Φ.timeSlice (Real.smoothTransitionUnit u) x, hxU⟩
  have hdom : ∀ᶠ u' : ℝ in 𝓝 u, ((u, u'), y') ∈ timeDependentFlowDomain ZU :=
    ((isOpen_timeDependentFlowDomain hZU₁).preimage (by fun_prop)).mem_nhds
      (mem_timeDependentFlowDomain_self hZU₁ _ _)
  -- Along the flow of `ZU` from time `u`, the pullback of `β'_{u'}` vanishes on the kernel of
  -- `β'_u` at `y'`, for `u'` near `u`, since `Φ` transports `ξ`.
  have hA (w : TangentSpace I y') (hw : w ∈ (mpullback (Prod.mk (Real.smoothTransition u))
      (contMDiff_const.prodMk contMDiff_id) β).kerDistribution y') :
      (fun u' ↦ TauCeti.mpullback I I (timeDependentFlowOf ZU u u')
        (TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u') β'.val) y' ![w]) =ᶠ[𝓝 u]
        fun _ ↦ 0 := by
    filter_upwards [hdom, (isOpen_Ioo.preimage Real.smoothTransition.continuous).mem_nhds hab]
      with u' hdom' hu'
    obtain ⟨-, hpt⟩ := timeDependentFlowOf_restrict_eq hZ₁ hdom'
    have hw' := tangentSpaceOpenEquiv_mfderiv_timeDependentFlowOf_restrict hZ₁ hdom' w
    have hvec : (fun i ↦ mfderiv I I (timeDependentFlowOf ZU u u') y' (![w] i)) =
        ![mfderiv I I (timeDependentFlowOf ZU u u') y' w] :=
      funext fun i ↦ by fin_cases i; rfl
    rw [TauCeti.mpullback_apply, hvec,
      ← coe_mpullback (Prod.mk u') (contMDiff_const.prodMk contMDiff_id), hslice,
      ← mem_kerDistribution,
      hker u' hu', hw']
    have hpt' : timeDependentFlowOf Z u u' (Φ.timeSlice (Real.smoothTransitionUnit u) x) =
        Φ.timeSlice (Real.smoothTransitionUnit u') x := by
      simp only [hflow, Diffeomorph.symm_apply_apply]
    refine (mem_iff_mem_of_eq _ (hpt.trans hpt') _).2 ?_
    rw [hflow]
    have hw₀ : Manifold.tangentSpaceOpenEquiv y' w ∈ ξ (Real.smoothTransitionUnit u)
        (Φ.timeSlice (Real.smoothTransitionUnit u) x) := (hker u hab y' w).1 hw
    have h := hΦ.mfderiv_timeSlice_comp_symm_mem (by simp) (Real.smoothTransitionUnit u)
      (Real.smoothTransitionUnit u') x hw₀
    exact h
  -- So the derivative at `u`, the rate `ι_u^* L_{∂_t} β' + L_{ZU_u} β'_u`, vanishes there.
  have hD := hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk (hZU.of_le (by simp))
    (mem_timeDependentFlowDomain_self hZU₁ u y') ((β'.contMDiff.of_le (by simp)).contMDiffAt)
  rw [show timeDependentFlowOf ZU u u = id from funext (timeDependentFlowOf_self ZU u),
    TauCeti.mpullback_id] at hD
  have hB (w : TangentSpace I y') (hw : w ∈ (mpullback (Prod.mk (Real.smoothTransition u))
      (contMDiff_const.prodMk contMDiff_id) β).kerDistribution y') :
      mextDeriv (mpullback (Prod.mk (Real.smoothTransition u))
          (contMDiff_const.prodMk contMDiff_id) β).val y' ![ZU u y', w] +
        deriv Real.smoothTransition u * (mpullback (Prod.mk (Real.smoothTransition u))
          (contMDiff_const.prodMk contMDiff_id) β.timeDeriv).val y' ![w] = 0 := by
    -- Evaluation on `w`, read in the model space `E`.
    have h₁ := (ContinuousAlternatingMap.apply ℝ E ℝ (Matrix.vecCons (α := E) w ![])).hasFDerivAt
      |>.comp_hasDerivAt u hD
    have h₂ := (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq (hA w hw)
    have h := h₁.unique h₂
    rw [← coe_timeDeriv, ← coe_mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id), hdslice,
      ← coe_mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id), hslice] at h
    -- Evaluation on `![w]` of a sum of forms at `y'`; the evaluation map is read in the model
    -- fibre, so `ContinuousAlternatingMap.apply_apply` does not rewrite it.
    replace h : (deriv Real.smoothTransition u • mpullback (Prod.mk (Real.smoothTransition u))
        (contMDiff_const.prodMk contMDiff_id) β.timeDeriv).val y' ![w] +
        mlieDerivForm (ZU u) (mpullback (Prod.mk (Real.smoothTransition u))
          (contMDiff_const.prodMk contMDiff_id) β).val y' ![w] = 0 := h
    simp only [Submodule.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul] at h
    rw [      mlieDerivForm_apply_eq_mextDeriv_add (f := fun _ ↦ (0 : ℝ)) hZker
        ((SmoothForm.mpullback (Prod.mk (Real.smoothTransition u))
          (contMDiff_const.prodMk contMDiff_id) β).contMDiff.mdifferentiableAt (by simp))
        ((hZU.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt (by simp))] at h
    have h0 : mvfderiv I (fun _ : U ↦ (0 : ℝ)) y' w = 0 := by simp [mvfderiv]
    rw [h0] at h
    linarith
  -- Hence `s'(u)⁻¹ • ZU u y'` solves the equation of the Gray vector of `β` at time `s u`.
  have hsmul₁ (f : TangentSpace I y' [⋀^Fin 1]→L[ℝ] ℝ) (r : ℝ) (v : TangentSpace I y') :
      f ![r • v] = r * f ![v] := by
    simpa using f.toAlternatingMap.map_vecCons_smul ![] r v
  have hsmul₂ (f : TangentSpace I y' [⋀^Fin 2]→L[ℝ] ℝ) (r : ℝ) (v w : TangentSpace I y') :
      f ![r • v, w] = r * f ![v, w] := by
    simpa using f.toAlternatingMap.map_vecCons_smul ![w] r v
  have hgv : (deriv Real.smoothTransition u)⁻¹ • ZU u y' =
      β.grayVectorField (Real.smoothTransition u) y' := by
    refine (eq_grayVectorField_iff (hβ.isContactForm _)).2 ⟨?_, fun w hw ↦ ?_⟩
    · rw [hsmul₁, hZker, mul_zero]
    · have h := hB w hw
      rw [← smul_inv_smul₀ hd (ZU u y'), hsmul₂, ← mul_add] at h
      exact (mul_eq_zero.1 h).resolve_left hd
  rw [← hgray (Real.smoothTransition u) (hsI u) a b hab U
    (Φ.timeSlice (Real.smoothTransitionUnit u) x) hxU β hβ, ← hgv, map_smul,
    smul_inv_smul₀ hd]
  exact (ContinuousLinearEquiv.apply_symm_apply _ _).symm

/-- A normalized transporting diffeotopy `Φ`, read over `ℝ` as `u ↦ φ_{s(u)}`, is the
time-dependent flow from time `0` of the field `s'(u) • Y_{s(u)}`, which depends only on `Y`. -/
private theorem apply_smoothTransitionUnit_eq_timeDependentFlowOf (hξ : IsContactFamily ξ)
    {Y : ℝ → Π x : M, TangentSpace I x}
    (hgray : ∀ (t : ℝ), t ∈ unitInterval → ∀ (a b : ℝ), t ∈ Ioo a b → ∀ (U : Opens M) (x : M)
        (hx : x ∈ U) (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1),
        IsLocalDefiningFamily ξ U α a b →
        Manifold.tangentSpaceOpenEquiv ⟨x, hx⟩ (α.grayVectorField t ⟨x, hx⟩) = Y t x)
    {Φ : Diffeotopy I ∞ M} (hΦ : Φ.Transports ξ) (hv : ∀ t y, Φ.velocity t y ∈ ξ t y)
    (u : ℝ) (x : M) :
    Φ (Real.smoothTransitionUnit u, x) = timeDependentFlowOf
      (fun u y ↦ deriv Real.smoothTransition u • Y (Real.smoothTransition u) y) 0 u x := by
  have hZ : eulerianField I (fun v ↦ (Φ.smoothTransitionFamily v).toEquiv) =
      fun u y ↦ deriv Real.smoothTransition u • Y (Real.smoothTransition u) y :=
    funext fun u ↦ funext (eulerianField_smoothTransitionFamily_eq hξ hgray hΦ hv u)
  rw [← hZ, Φ.timeDependentFlowOf_eulerianField_smoothTransitionFamily,
    Φ.smoothTransitionFamily_of_nonpos le_rfl, Φ.smoothTransitionFamily_apply]
  simp

variable [CompactSpace M]

/-- **The Gray isotopy** of a smooth family `ξ` of contact structures over `[0, 1]` on a compact
manifold without boundary: the diffeotopy `ψ_t` that runs, from time `0`, the Gray field `Y` of
`ξ` chosen by `SymplecticGeometry.IsContactFamily.exists_grayField`. Its suspension is complete
since `M` is compact. It transports `ξ`
(`SymplecticGeometry.IsContactFamily.transports_grayDiffeotopy`) and its velocity lies in `ξ`
(`SymplecticGeometry.IsContactFamily.velocity_grayDiffeotopy_mem`).

The field `Y` is a choice, determined only on `[0, 1] × M`. -/
noncomputable def grayDiffeotopy (hξ : IsContactFamily ξ) : Diffeotopy I ∞ M :=
  timeDependentFlowDiffeotopy le_top hξ.exists_grayField.choose_spec.1
    (isCompleteVectorField_timeDependentSuspensionField
      (hξ.exists_grayField.choose_spec.1.of_le (by simp)) isCompact_univ
      fun _ _ h ↦ absurd (mem_univ _) h)

/-- The Gray isotopy at time `t` is the time-dependent flow from time `0` to time `t` of a smooth
field `Y` with the properties of `SymplecticGeometry.IsContactFamily.exists_grayField`: in `ξ` at
the times of `[0, 1]`, where it is the Gray vector field of every local defining family. -/
theorem exists_grayField_grayDiffeotopy_apply (hξ : IsContactFamily ξ) :
    ∃ Y : ℝ → Π x : M, TangentSpace I x,
      ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
        (fun p : ℝ × M ↦ (⟨p.2, Y p.1 p.2⟩ : TangentBundle I M)) ∧
      (∀ (t : ℝ) (ht : t ∈ unitInterval) (x : M), Y t x ∈ ξ ⟨t, ht⟩ x) ∧
      (∀ (t : ℝ), t ∈ unitInterval → ∀ (a b : ℝ), t ∈ Ioo a b → ∀ (U : Opens M) (x : M)
        (hx : x ∈ U) (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1),
        IsLocalDefiningFamily ξ U α a b →
        Manifold.tangentSpaceOpenEquiv ⟨x, hx⟩ (α.grayVectorField t ⟨x, hx⟩) = Y t x) ∧
      ∀ p : unitInterval × M, hξ.grayDiffeotopy p = timeDependentFlowOf Y 0 p.1 p.2 :=
  ⟨_, hξ.exists_grayField.choose_spec.1, hξ.exists_grayField.choose_spec.2.1,
    hξ.exists_grayField.choose_spec.2.2, timeDependentFlowDiffeotopy_apply _ _ _⟩

/-- **The Gray isotopy transports the family**: `ψ_t^* ξ_t = ξ_0` for every `t ∈ [0, 1]`. -/
theorem transports_grayDiffeotopy (hξ : IsContactFamily ξ) :
    hξ.grayDiffeotopy.Transports ξ := by
  obtain ⟨Y, hY, -, hgray, happly⟩ := hξ.exists_grayField_grayDiffeotopy_apply
  have hY₁ := hY.of_le (m := 1) (by simp)
  have hc : IsCompleteVectorField (timeDependentSuspensionField Y) :=
    isCompleteVectorField_timeDependentSuspensionField hY₁ isCompact_univ
      fun _ _ h ↦ absurd (mem_univ _) h
  have hdom (s t : ℝ) (x : M) : ((s, t), x) ∈ timeDependentFlowDomain Y :=
    (timeDependentFlowDomain_eq_univ hc).symm ▸ mem_univ _
  refine Diffeotopy.transports_iff.2 fun t x ↦ ?_
  -- The pullback of `ξ_s` by the flow from `0` to `s`, at `x`, as a function of `s`. It is locally
  -- constant, by the cocycle property of the flow and the transport near each time.
  let g : unitInterval → Submodule ℝ (TangentSpace I x) := fun s ↦
    (ξ s (timeDependentFlowOf Y 0 s x)).comap
      (mfderiv I I (timeDependentFlowOf Y 0 s) x).toLinearMap
  have hg : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro s₀
    filter_upwards [(continuous_subtypeVal.tendsto s₀).eventually
      (eventually_comap_mfderiv_timeDependentFlowOf hξ hY hgray s₀
        (timeDependentFlowOf Y 0 s₀ x))] with s hs
    ext v
    have hd := congrArg (· v)
      (mfderiv_timeDependentFlowOf_trans_of_mem hY₁ (hdom 0 s₀ x) (hdom s₀ s _))
    simp only [g, Submodule.mem_comap, ContinuousLinearMap.coe_coe] at hd ⊢
    rw [hd, mem_iff_mem_of_eq (ξ s) (timeDependentFlowOf_trans hc hY₁ 0 s₀ s x).symm,
      ← (hs s.property).2]
    -- `⟨(s : ℝ), s.2⟩` is `s`.
    exact Iff.rfl
  have h0 : g 0 = ξ 0 x := by
    ext v
    simp only [g, Set.Icc.coe_zero, mfderiv_timeDependentFlowOf_self, ContinuousLinearMap.coe_id]
    exact mem_iff_mem_of_eq (ξ 0) (timeDependentFlowOf_self Y 0 x) v
  have hslice : ⇑(hξ.grayDiffeotopy.timeSlice t) = timeDependentFlowOf Y 0 t :=
    funext fun y ↦ (Diffeotopy.timeSlice_apply _ t y).trans (happly (t, y))
  ext v
  rw [← h0, hg.apply_eq_of_preconnectedSpace 0 t]
  simp only [g]
  refine (mem_iff_mem_of_eq (ξ t) (happly (t, x)).symm _).trans ?_
  rw [← hslice]
  -- Membership in a `comap` is membership of the image.
  exact Iff.rfl

/-- **The velocity of the Gray isotopy lies in the family**: the time derivative of `ψ_t` at `x`
lies in `ξ_t` at `ψ_t x`, for every `t ∈ [0, 1]`, the ends included. -/
theorem velocity_grayDiffeotopy_mem (hξ : IsContactFamily ξ) (t : unitInterval) (x : M) :
    mfderiv (I.prod (𝓡∂ 1)) I hξ.grayDiffeotopy.cylinderMap (x, t)
      ((0 : E), (1 : TangentSpace (𝓡∂ 1) t)) ∈ ξ t (hξ.grayDiffeotopy (t, x)) := by
  rw [← Diffeotopy.velocity_apply_apply, grayDiffeotopy,
    Diffeotopy.velocity_timeDependentFlowDiffeotopy]
  exact hξ.exists_grayField.choose_spec.2.1 t t.property _

/-- **Uniqueness of the normalized Gray isotopy.** On a compact Hausdorff manifold without
boundary, a diffeotopy `Φ` that transports a smooth family `ξ` of contact structures over
`[0, 1]` and whose velocity lies in `ξ` at every time and point is the Gray isotopy of `ξ`. -/
theorem eq_grayDiffeotopy_of_transports (hξ : IsContactFamily ξ) {Φ : Diffeotopy I ∞ M}
    (hΦ : Φ.Transports ξ)
    (hv : ∀ (t : unitInterval) (x : M), mfderiv (I.prod (𝓡∂ 1)) I Φ.cylinderMap (x, t)
      ((0 : E), (1 : TangentSpace (𝓡∂ 1) t)) ∈ ξ t (Φ (t, x))) :
    Φ = hξ.grayDiffeotopy := by
  obtain ⟨Y, -, -, hgray⟩ := hξ.exists_grayField
  -- Read along the motion, the normalization says that the velocity lies in `ξ`.
  have hvel {Ψ : Diffeotopy I ∞ M} (h : ∀ (t : unitInterval) (x : M),
      mfderiv (I.prod (𝓡∂ 1)) I Ψ.cylinderMap (x, t)
        ((0 : E), (1 : TangentSpace (𝓡∂ 1) t)) ∈ ξ t (Ψ (t, x))) (t : unitInterval) (y : M) :
      Ψ.velocity t y ∈ ξ t y := by
    obtain ⟨x, rfl⟩ : ∃ x, Ψ (t, x) = y := ⟨_, Ψ.apply_mk_symm_apply t y⟩
    rw [Diffeotopy.velocity_apply_apply]
    exact h t x
  refine Diffeotopy.ext fun p ↦ ?_
  obtain ⟨u, hu⟩ := Real.smoothTransitionUnit_surjective p.1
  rw [← Prod.mk.eta (p := p), ← hu,
    apply_smoothTransitionUnit_eq_timeDependentFlowOf hξ hgray hΦ (hvel hv),
    apply_smoothTransitionUnit_eq_timeDependentFlowOf hξ hgray hξ.transports_grayDiffeotopy
      (hvel hξ.velocity_grayDiffeotopy_mem)]

/-- **Gray stability.** Let `M` be a compact Hausdorff manifold without boundary and `ξ` a
smooth family of contact structures over `[0, 1]`, not necessarily coorientable. There is a unique
diffeotopy `ψ_t` that transports `ξ`, `ψ_t^* ξ_t = ξ_0`, and whose velocity `∂_t ψ_t`, read along
the motion, lies in `ξ_t` at every time and point. If moreover `ξ_t = ker α_t` for a smooth
family of contact forms `α` over `[0, 1]`, then every diffeotopy that transports `ξ` rescales the
forms: `ψ_t^* α_t = f_t α_0` with `f` smooth and positive on `[0, 1] × M` and `f_0 = 1`.

Milestone: *Gray stability*. -/
theorem existsUnique_transports (hξ : IsContactFamily ξ) :
    (∃! Φ : Diffeotopy I ∞ M, Φ.Transports ξ ∧ ∀ (t : unitInterval) (x : M),
      mfderiv (I.prod (𝓡∂ 1)) I Φ.cylinderMap (x, t)
        ((0 : E), (1 : TangentSpace (𝓡∂ 1) t)) ∈ ξ t (Φ (t, x))) ∧
    ∀ α : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) ℝ 1,
      (∀ t, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm) →
      (∀ t, ξ t = (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution) →
      ∀ Φ : Diffeotopy I ∞ M, Φ.Transports ξ →
        ∃ f : unitInterval × M → ℝ, ContMDiff ((𝓡∂ 1).prod I) 𝓘(ℝ) ∞ f ∧ (∀ p, 0 < f p) ∧
          (∀ x, f (0, x) = 1) ∧ ∀ t x,
            (mpullback (Φ.timeSlice t) (Φ.timeSlice t).contMDiff
              (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α)).val x =
              f (t, x) •
                (mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) α).val x :=
  ⟨⟨hξ.grayDiffeotopy, ⟨hξ.transports_grayDiffeotopy, hξ.velocity_grayDiffeotopy_mem⟩,
      fun _ hΦ ↦ hξ.eq_grayDiffeotopy_of_transports hΦ.1 hΦ.2⟩,
    fun α hc hker _ hΦ ↦ Diffeotopy.Transports.exists_mpullback_eq_smul α hc
      ((funext hker : ξ = _) ▸ hΦ)⟩


end GrayDiffeotopy
end IsContactFamily

end SymplecticGeometry

end
