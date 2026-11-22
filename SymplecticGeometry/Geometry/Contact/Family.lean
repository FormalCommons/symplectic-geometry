/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition
public import SymplecticGeometry.Geometry.Contact.Levi
public import SymplecticGeometry.Geometry.Contact.Moser
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Flow.Family
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.TimeExtension
public import SymplecticGeometry.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Geometry.Contact.Distribution
public import TauCeti.Geometry.Contact.Flat
public import TauCeti.Geometry.Contact.Gray
public import TauCeti.Topology.VectorBundle.Hom

/-!
# Smooth families of contact structures

A family `ξ : unitInterval → Π x : M, Submodule ℝ (TangentSpace I x)` of distributions on `M` is a
smooth family of contact structures, `SymplecticGeometry.IsContactFamily ξ`, when near every point
`(t, x)` of the cylinder `[0, 1] × M` there is a smooth one-form `α` on the cylinder whose slices
`α_s = ι_s^* α`, `ι_s = Prod.mk s`, are contact at the nearby points `(s, y)` and have kernel
`ξ s y` there. No global defining form is asked for, so the family need not be coorientable, and
the neighbourhoods are taken in the cylinder, since a non-coorientable family need not be defined
by one form on `[0, 1] × U` for an open `U ⊆ M`.

Each member `ξ t` of such a family is a smooth contact structure in Tau Ceti's sense,
`TauCeti.IsContactDistribution I ∞ (ξ t)`, and a one-form on the cylinder all of whose slices are
contact forms defines one.

A local defining family over `ℝ` of `ξ` (`SymplecticGeometry.IsLocalDefiningFamily ξ U α a b`)
is a one-form `α` on `ℝ × U`, for an open `U ⊆ M`, all of whose slices are contact forms and
whose kernels are those of `ξ` at the times of `(a, b) ∩ [0, 1]`. It plays the part of Tau Ceti's
`TauCeti.IsLocalContactFormFamily` (in `TauCeti/Geometry/Contact/Gray/Distribution.lean`, which
the pinned version of Tau Ceti does not have) for a family indexed by `[0, 1]` rather than by
`ℝ`: Tau Ceti's predicate asks the kernels to be those of the family at all real times near a
given time, which a family over `[0, 1]` does not prescribe near `0` and `1`.

A local defining family restricts to smaller open sets
(`SymplecticGeometry.IsLocalDefiningFamily.mpullback_inclusion`). The proof is that of Tau Ceti's
`TauCeti.IsLocalContactFormFamily.mpullback_inclusion`, in the same Tau Ceti file at commit
034344347f0ca1144bf5ae35c82e3edaf848fca5.

On a manifold without boundary, a family over `[0, 1]` has local defining families over `ℝ` near
every point (`SymplecticGeometry.IsContactFamily.exists_local_extension`). Near a point
`(t₀, x₀)`, a local defining form on the cylinder is extended in time by Seeley's operator
(`TauCeti.SmoothForm.timeExtend`). Its slices are contact on an open subset of `ℝ × M`
(`TauCeti.SmoothForm.isOpen_setOf_isContactFormAt_mpullback_prodMk`, read off the invertibility
of the contact flat map, as in the proof of Tau Ceti's
`TauCeti.SmoothForm.exists_isOpen_forall_isContactFormAt_add_smul_sub`), hence on a product of
an interval around `t₀` and an open `U ∋ x₀`.
Composing in time with a smooth map into that interval which is the identity near `t₀` in
`[0, 1]` (`SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_Ioo`) and restricting to `U` gives
a form on `ℝ × U` all of whose slices are contact, and whose kernels are those of `ξ` at the
times near `t₀` in `[0, 1]`. No compactness of `M` is needed.

Let `α` and `α'` be one-forms on `ℝ × M` whose slices at `t` are contact forms. If their slices
satisfy `α'_u = f(u, ·) α_u` near `(t, x)`, for times `u` in a set `s ∋ t` such as `[0, 1]` and a
function `f` differentiable and nonzero at `(t, x)`, then their Gray vector fields
(`TauCeti.SmoothForm.grayVectorField`) agree at `(t, x)`. The `dt` components of the forms play no
role, and no relation is asked at times outside `s`, so two local defining forms of a family over
`[0, 1]` can be compared at `t = 0` and `t = 1` too. This makes the Gray field of
a non-coorientable family well defined through local defining forms. It rests on the pointwise form
of the same fact for Tau Ceti's contact-Moser vector field, in
`SymplecticGeometry.Geometry.Contact.Moser`.

## Main definitions

* `SymplecticGeometry.IsContactFamily ξ`: `ξ` is a smooth family of contact structures over
  `[0, 1]`.
* `SymplecticGeometry.IsLocalDefiningFamily ξ U α a b`: `α` is a local defining family over `ℝ`
  of `ξ` on `U` and `(a, b)`.

## Main results

* `SymplecticGeometry.IsContactFamily.of_isContactForm`: a one-form on the cylinder whose slices are
  contact forms defines a smooth family of contact structures by its kernels.
* `SymplecticGeometry.IsContactFamily.isContactDistribution`: each member of a smooth family of
  contact structures is a smooth contact structure.
* `SymplecticGeometry.IsContactFamily.exists_local_extension`: near each point of the cylinder, a
  smooth family of contact structures has a local defining family over `ℝ`.
* `SymplecticGeometry.IsLocalDefiningFamily.mpullback_inclusion`: a local defining family
  restricts to smaller open sets.
* `TauCeti.SmoothForm.isOpen_setOf_isContactFormAt_mpullback_prodMk`: the points of `N × M` at
  which the slices of a one-form are contact form an open set.
* `TauCeti.SmoothForm.isContactFormAt_mpullback_subtype_val_iff`,
  `TauCeti.SmoothForm.map_kerDistribution_mpullback_subtype_val`: restricting a one-form to an open
  subset keeps its contact points and its kernels.
* `TauCeti.SmoothForm.grayVectorField_eq_of_eventuallyEq_smul`: the Gray vector at `(t, x)` of a
  family whose slice at `t` is a contact form is unchanged when the slices at times of `s` are
  multiplied, near `(t, x)`, by a function nonzero at `(t, x)`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.5,
  the discussion of Gray stability on pp. 135–136 and Exercise 3.5.21.
* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Theorem 2.2.2 (Gray stability) and its proof, which Tau Ceti's contact-Moser and Gray
  files follow.
-/

public section

noncomputable section

open Set Filter Function Module Bundle
open scoped Manifold Topology ContDiff

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A family `ξ` of distributions on `M`, indexed by `t ∈ [0, 1]`, is a **smooth family of contact
structures** when near every point of the cylinder `[0, 1] × M` it is given by a smooth one-form
`α` on the cylinder: at every nearby point `(s, y)` the slice `α_s = ι_s^* α` is a contact form at
`y` and its kernel there is `ξ s y`. -/
def IsContactFamily (ξ : unitInterval → Π x : M, Submodule ℝ (TangentSpace I x)) : Prop :=
  ∀ p : unitInterval × M, ∃ α : TauCeti.SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) ℝ 1,
    ∀ᶠ q in 𝓝 p,
      TauCeti.IsContactFormAt (TauCeti.SmoothForm.mpullback (Prod.mk q.1)
        (contMDiff_const.prodMk contMDiff_id) α).val q.2 ∧
      ξ q.1 q.2 = (TauCeti.SmoothForm.mpullback (Prod.mk q.1)
        (contMDiff_const.prodMk contMDiff_id) α).kerDistribution q.2

variable {ξ : unitInterval → Π x : M, Submodule ℝ (TangentSpace I x)}

/-- The definition of a smooth family of contact structures. -/
theorem isContactFamily_def : IsContactFamily ξ ↔
    ∀ p : unitInterval × M, ∃ α : TauCeti.SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) ℝ 1,
      ∀ᶠ q in 𝓝 p,
        TauCeti.IsContactFormAt (TauCeti.SmoothForm.mpullback (Prod.mk q.1)
          (contMDiff_const.prodMk contMDiff_id) α).val q.2 ∧
        ξ q.1 q.2 = (TauCeti.SmoothForm.mpullback (Prod.mk q.1)
          (contMDiff_const.prodMk contMDiff_id) α).kerDistribution q.2 :=
  Iff.rfl

/-- A smooth family of contact structures, with the kernels of the slices of the local defining
forms written as the vectors `v` for which `α` vanishes on the vertical vector `(0, v)`. -/
theorem isContactFamily_iff : IsContactFamily ξ ↔
    ∀ p : unitInterval × M, ∃ α : TauCeti.SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) ℝ 1,
      ∀ᶠ q in 𝓝 p,
        TauCeti.IsContactFormAt (TauCeti.SmoothForm.mpullback (Prod.mk q.1)
          (contMDiff_const.prodMk contMDiff_id) α).val q.2 ∧
        ∀ v : TangentSpace I q.2,
          v ∈ ξ q.1 q.2 ↔ α.val q ![((0 : EuclideanSpace ℝ (Fin 1)), v)] = 0 := by
  refine forall_congr' fun p ↦ exists_congr fun α ↦
    eventually_congr (.of_forall fun q ↦ and_congr_right' ?_)
  rw [SetLike.ext_iff]
  refine forall_congr' fun v ↦ ?_
  rw [TauCeti.SmoothForm.mem_kerDistribution, TauCeti.SmoothForm.mpullback_apply,
    mfderiv_prod_right]
  -- The slice inclusion `Prod.mk t` sends `v` to the vertical vector `(0, v)`.
  congr! 3
  ext i : 1
  fin_cases i
  exact ContinuousLinearMap.inr_apply v

namespace IsContactFamily

/-- **A family of contact forms defines a smooth family of contact structures**: if every slice
`α_t` of a one-form `α` on the cylinder `[0, 1] × M` is a contact form, then the kernels of the
slices form a smooth family of contact structures. -/
theorem of_isContactForm (α : TauCeti.SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) ℝ 1)
    (hc : ∀ t, (TauCeti.SmoothForm.mpullback (Prod.mk t)
      (contMDiff_const.prodMk contMDiff_id) α).IsContactForm) :
    IsContactFamily fun t ↦ (TauCeti.SmoothForm.mpullback (Prod.mk t)
      (contMDiff_const.prodMk contMDiff_id) α).kerDistribution :=
  fun _ ↦ ⟨α, .of_forall fun q ↦
    ⟨TauCeti.SmoothForm.isContactForm_iff_forall_isContactFormAt.1 (hc q.1) q.2, rfl⟩⟩

variable [FiniteDimensional ℝ E]

/-- **Each member of a smooth family of contact structures is a contact structure**: for every
`t ∈ [0, 1]`, the distribution `ξ t` is a smooth contact structure on `M`. -/
theorem isContactDistribution (hξ : IsContactFamily ξ) (t : unitInterval) :
    TauCeti.IsContactDistribution I ∞ (ξ t) := by
  -- Near each `x`, the slice at `t` of a local defining form defines `ξ t` and is contact.
  have hloc (x : M) : ∃ β : TauCeti.SmoothForm I M ℝ 1, ∀ᶠ y in 𝓝 x,
      TauCeti.IsContactFormAt β.val y ∧ ξ t y = β.kerDistribution y := by
    obtain ⟨α, hα⟩ := hξ (t, x)
    exact ⟨TauCeti.SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α,
      ((continuous_const.prodMk continuous_id).continuousAt.eventually hα).mono
      fun _ h ↦ h⟩
  have hD : TauCeti.IsContMDiffDistribution I ∞ (finrank ℝ E - 1) (ξ t) :=
    .of_forall_eventuallyEq_kerDistribution fun x ↦
      have ⟨β, hβ⟩ := hloc x
      ⟨β, hβ.self_of_nhds.1.ne_zero, hβ.mono fun _ h ↦ h.2⟩
  refine (TauCeti.isContactDistribution_iff_forall_exists_isContactFormAt hD (by simp)).2
    fun x ↦ ?_
  obtain ⟨β, hβ⟩ := hloc x
  refine ⟨β.val, β.mdifferentiableAt x, hβ.mono fun y h ↦ ?_, hβ.self_of_nhds.1⟩
  rw [h.2, TauCeti.SmoothForm.kerDistribution_eq_ker]

end IsContactFamily

end SymplecticGeometry

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- **The Gray vector at a point does not depend on the defining family.** Let `α` and `α'` be
one-forms on `ℝ × M` whose slices at time `t` are contact forms, and let `s ∋ t` be a set of times
on which derivatives at `t` are unique, such as `[0, 1]`. Suppose that the slices satisfy
`α'_u = f(u, ·) α_u` at the points `(u, y)` of `s × M` near `(t, x)`, for a function `f` with
`f (t, x) ≠ 0` that is differentiable within `s` in time at `t` and differentiable in space at
`x`. Then the Gray vector fields of `α` and `α'` agree at time `t` and the point `x`. -/
theorem grayVectorField_eq_of_eventuallyEq_smul [I.Boundaryless]
    {α α' : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1} {f : ℝ × M → ℝ} {s : Set ℝ} {t : ℝ}
    {x : M} (hs : UniqueDiffWithinAt ℝ s t) (ht : t ∈ s)
    (hc : (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
    (hc' : (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α').IsContactForm)
    (hft : DifferentiableWithinAt ℝ (fun u ↦ f (u, x)) s t)
    (hfy : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ f (t, y)) x) (hf₀ : f (t, x) ≠ 0)
    (h : ∀ᶠ q in 𝓝[s ×ˢ univ] (t, x),
      (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α').val q.2 =
        f q • (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α).val q.2) :
    α'.grayVectorField t x = α.grayVectorField t x := by
  -- The relation holds near `x` at time `t`, and near `t` within `s` at the point `x`.
  have hy := (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (fun y : M ↦ (t, y))
    ((continuous_const.prodMk continuous_id).tendsto x)
    (.of_forall fun y ↦ mk_mem_prod ht (mem_univ y))).eventually h
  have hu := (((continuous_id.prodMk continuous_const).continuousWithinAt
    (x := t)).tendsto_nhdsWithin (t := s ×ˢ univ) fun _ hu ↦ ⟨hu, mem_univ x⟩).eventually h
  -- The velocities of the slices are related by the product rule.
  have hβ := hs.eq_deriv _ (hasDerivAt_mpullback_prodMk_timeDeriv α' t x).hasDerivWithinAt
    ((hft.hasDerivWithinAt.smul (hasDerivAt_mpullback_prodMk_timeDeriv α t x).hasDerivWithinAt
      ).congr_of_eventuallyEq hu (h.self_of_nhdsWithin ⟨ht, mem_univ x⟩))
  rw [grayVectorField_def, grayVectorField_def]
  exact hc.contactMoserVectorField_apply_of_eventuallyEq_smul hc' hfy hf₀ hy hβ

/-- **The contact condition is open in families.** For a one-form `α` on a product `N × M`, the
points `(t, y)` at which the slice `α_t = ι_t^* α` is a contact form form an open set. Near a
contact point the model space is odd-dimensional, and there contactness of `α_t` at `y` is the
invertibility of its contact flat map, which depends continuously on `(t, y)`. -/
theorem isOpen_setOf_isContactFormAt_mpullback_prodMk {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] [IsManifold J ∞ N] (α : SmoothForm (J.prod I) (N × M) ℝ 1) :
    IsOpen {q : N × M | IsContactFormAt
      (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α).val q.2} := by
  refine isOpen_iff_mem_nhds.2 fun q₀ hq₀ ↦ ?_
  have hodd : Odd (finrank ℝ E) :=
    (isContactFormAt_iff_isContact.1 hq₀).odd_finrank (isAlt_bilinFormAt _ q₀.2)
  -- The contact flat maps of the slices are invertible on an open set. The bundles and the base
  -- map are given explicitly: unification would otherwise read the section along the identity.
  have hO : IsOpen {q : N × M | ((mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id)
      α).contactFlat q.2).IsInvertible} :=
    Continuous.isOpen_setOf_clm_bundle_isInvertible (𝕜 := ℝ) (F₁ := E)
      (F₂ := E →L[ℝ] ℝ) (E₁ := TangentSpace I) (E₂ := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
      (b := Prod.snd) (ϕ := fun q : N × M ↦ (mpullback (Prod.mk q.1)
        (contMDiff_const.prodMk contMDiff_id) α).contactFlat q.2)
      (ContMDiff.continuous (n := ∞) fun q ↦ contMDiffAt_sectionAlong_contactFlat (b := Prod.snd)
        (α := fun q : N × M ↦ mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α)
        (contMDiff_mpullback_prodMk α q) (contMDiff_mextDeriv_mpullback_prodMk α q))
  filter_upwards [hO.mem_nhds (isInvertible_contactFlat_of_isContactFormAt hq₀)] with q hq
  exact isContactFormAt_of_isInvertible_contactFlat hodd hq

omit [FiniteDimensional ℝ E] in
/-- **Contactness restricts to open subsets.** The restriction of a one-form `α` to an open subset
`U ⊆ M` is contact at `x ∈ U` if and only if `α` is contact at `x`. -/
theorem isContactFormAt_mpullback_subtype_val_iff {U : TopologicalSpace.Opens M}
    (α : SmoothForm I M ℝ 1) (x : U) :
    IsContactFormAt (mpullback (Subtype.val : U → M) contMDiff_subtypeVal α).val x ↔
      IsContactFormAt α.val x := by
  rw [coe_mpullback, isContactFormAt_mpullback_iff contMDiff_subtypeVal.contMDiffAt
    (((SmoothForm.contMDiff _) _).of_le (mod_cast le_top))
    (Manifold.mfderiv_subtype_val (I := I) x ▸ (Manifold.tangentSpaceOpenEquiv x).bijective)]

omit [FiniteDimensional ℝ E] in
/-- **Kernels restrict to open subsets.** Under the canonical identification of tangent spaces,
the kernel at `x ∈ U` of the restriction of a one-form `α` to an open subset `U ⊆ M` is the kernel
of `α` at `x`. -/
theorem map_kerDistribution_mpullback_subtype_val {U : TopologicalSpace.Opens M}
    (α : SmoothForm I M ℝ 1) (x : U) :
    ((mpullback (Subtype.val : U → M) contMDiff_subtypeVal α).kerDistribution x).map
      (Manifold.tangentSpaceOpenEquiv (I := I) x).toLinearEquiv.toLinearMap =
      α.kerDistribution x := by
  rw [kerDistribution_mpullback, Manifold.mfderiv_subtype_val]
  exact Submodule.map_comap_eq_of_surjective (Manifold.tangentSpaceOpenEquiv x).surjective _

end TauCeti.SmoothForm

namespace SymplecticGeometry

open TauCeti TauCeti.SmoothForm TopologicalSpace

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ξ : unitInterval → Π x : M, Submodule ℝ (TangentSpace I x)}

/-- A **local defining family** over `ℝ` of a family `ξ` of distributions over `[0, 1]`, on an
open set `U` and a time interval `(a, b)`: a one-form `α` on `ℝ × U` all of whose slices
`α_t = ι_t^* α`, for all real `t`, are contact forms on `U`, and whose slice at each
`t ∈ (a, b) ∩ [0, 1]` has kernel `ξ t x` at every `x ∈ U`, the tangent spaces of `U` being
identified with those of `M`. -/
def IsLocalDefiningFamily (ξ : unitInterval → Π x : M, Submodule ℝ (TangentSpace I x))
    (U : Opens M) (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1) (a b : ℝ) : Prop :=
  (∀ t : ℝ, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm) ∧
    ∀ (t : ℝ) (ht : t ∈ Ioo a b ∩ unitInterval) (x : U),
      ξ ⟨t, ht.2⟩ x = ((mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        α).kerDistribution x).map
          (Manifold.tangentSpaceOpenEquiv (I := I) x).toLinearEquiv.toLinearMap

/-- The definition of a local defining family. -/
theorem isLocalDefiningFamily_def {U : Opens M} {α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1}
    {a b : ℝ} : IsLocalDefiningFamily ξ U α a b ↔
      (∀ t : ℝ, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm) ∧
        ∀ (t : ℝ) (ht : t ∈ Ioo a b ∩ unitInterval) (x : U),
          ξ ⟨t, ht.2⟩ x = ((mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
            α).kerDistribution x).map
              (Manifold.tangentSpaceOpenEquiv (I := I) x).toLinearEquiv.toLinearMap :=
  Iff.rfl

namespace IsLocalDefiningFamily

variable {U : Opens M} {α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1} {a b : ℝ}

/-- Every slice of a local defining family is a contact form. -/
theorem isContactForm (hα : IsLocalDefiningFamily ξ U α a b) (t : ℝ) :
    (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm :=
  hα.1 t

/-- At a time `t ∈ (a, b) ∩ [0, 1]`, a tangent vector of `U` at `x` lies in the kernel of the slice
`α_t` of a local defining family exactly when, read in the tangent space of `M`, it lies in
`ξ t x`. -/
theorem mem_kerDistribution_iff (hα : IsLocalDefiningFamily ξ U α a b) {t : ℝ}
    (ht : t ∈ Ioo a b ∩ unitInterval) (x : U) (v : TangentSpace I x) :
    v ∈ (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x ↔
      Manifold.tangentSpaceOpenEquiv x v ∈ ξ ⟨t, ht.2⟩ x := by
  rw [hα.2 t ht x, Submodule.mem_map_equiv, ContinuousLinearEquiv.coe_symm_toLinearEquiv,
    ContinuousLinearEquiv.symm_apply_apply]

/-- **Local defining families restrict to smaller open sets.** The restriction of a local defining
family `α` of `ξ` on `U` and `(a, b)` to `ℝ × V`, for an open `V ⊆ U`, is a local defining family
of `ξ` on `V` and `(a, b)`. -/
theorem mpullback_inclusion (hα : IsLocalDefiningFamily ξ U α a b) {V : Opens M} (hV : V ≤ U) :
    IsLocalDefiningFamily ξ V (mpullback (Prod.map id (Opens.inclusion hV))
      (contMDiff_id.prodMap (contMDiff_inclusion hV)) α) a b := by
  refine ⟨fun t ↦ ?_, fun t ht x ↦ ?_⟩
  · rw [mpullback_prodMk_mpullback_prodMap]
    exact (hα.isContactForm t).mpullback _ (contMDiff_inclusion hV) fun y ↦
      ((isLocalDiffeomorph_inclusion (n := ∞) hV y).isInvertible_mfderiv (by simp)).bijective
  · ext v
    rw [Submodule.mem_map_equiv, ContinuousLinearEquiv.coe_symm_toLinearEquiv,
      mpullback_prodMk_mpullback_prodMap _ (contMDiff_inclusion hV), kerDistribution_mpullback,
      Submodule.mem_comap, ContinuousLinearMap.coe_coe, hα.mem_kerDistribution_iff ht,
      Manifold.tangentSpaceOpenEquiv_mfderiv_apply (f := Opens.inclusion hV) (A := id) rfl,
      mfderiv_id, ContinuousLinearMap.id_apply, ContinuousLinearEquiv.apply_symm_apply]

end IsLocalDefiningFamily

namespace IsContactFamily

variable [FiniteDimensional ℝ E] [BoundarylessManifold I M]

/-- **Local defining families over `ℝ`.** Let `ξ` be a smooth family of contact structures over
`[0, 1]` on a manifold without boundary. Near every point `(t₀, x₀)` of the cylinder there are an
open interval `(a, b) ∋ t₀`, an open set `U ∋ x₀` and a local defining family `α` of `ξ` on `U`
and `(a, b)`: a one-form on `ℝ × U` such that every slice `α_t`, for all real `t`, is a contact
form on `U`, and for `t ∈ (a, b) ∩ [0, 1]` its kernel at each `x ∈ U` is `ξ t x`, under the
identification of the tangent spaces of `U` with those of `M`. -/
theorem exists_local_extension (hξ : IsContactFamily ξ) (p : unitInterval × M) :
    ∃ a b : ℝ, (p.1 : ℝ) ∈ Ioo a b ∧ ∃ U : Opens M, p.2 ∈ U ∧
      ∃ α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1, IsLocalDefiningFamily ξ U α a b := by
  obtain ⟨α, hα⟩ := hξ p
  -- Extend `α` past the ends of `[0, 1]`; its slices are contact on an open set `C ∋ p`.
  set β := SmoothForm.timeExtend α
  have hC := isOpen_setOf_isContactFormAt_mpullback_prodMk β
  have hp : ((p.1 : ℝ), p.2) ∈ {q : ℝ × M | IsContactFormAt
      (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) β).val q.2} := by
    simpa only [mem_ofPred_eq, β, SmoothForm.mpullback_prodMk_timeExtend] using
      hα.self_of_nhds.1
  -- Read the neighbourhood of `p` in the cylinder as one in `ℝ × M`.
  rw [(Topology.IsInducing.subtypeVal.prodMap Topology.IsInducing.id).nhds_eq_comap,
    eventually_comap] at hα
  have hW := hα.and (hC.mem_nhds hp)
  rw [Prod.map_apply, id, nhds_prod_eq] at hW
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := eventually_prod_iff.1 hW
  obtain ⟨δ, hδ, hδa⟩ := Metric.eventually_nhds_iff.1 hpa
  obtain ⟨U, hUb, hU, hxU⟩ := eventually_nhds_iff.1 hpb
  -- Reparametrize time by a map into `(t₀ - δ, t₀ + δ)`, equal to the identity near `t₀` in
  -- `[0, 1]`.
  have ht₀ := p.1.property
  obtain ⟨c, hc, hcid, hcmem, -⟩ := exists_contDiff_eqOn_id_Icc_mem_Ioo
    (a := max 0 ((p.1 : ℝ) - δ / 2)) (b := min 1 ((p.1 : ℝ) + δ / 2))
    (le_min (max_le zero_le_one (by linarith [ht₀.2]))
      (max_le (by linarith [ht₀.1]) (by linarith)))
    (half_pos hδ)
  refine ⟨p.1 - δ / 2, p.1 + δ / 2, ⟨by linarith, by linarith⟩, ⟨U, hU⟩, hxU,
    mpullback (Prod.map c Subtype.val) (hc.contMDiff.prodMap contMDiff_subtypeVal) β,
    ⟨fun t ↦ ?_, fun t ht x ↦ ?_⟩⟩
  · rw [mpullback_prodMk_mpullback_prodMap' hc.contMDiff Subtype.val contMDiff_subtypeVal,
      isContactForm_iff_forall_isContactFormAt]
    intro x
    have hct : dist (c t) p.1 < δ := by
      have h₁ := hcmem t
      have h₂ := le_max_right 0 ((p.1 : ℝ) - δ / 2)
      have h₃ := min_le_right 1 ((p.1 : ℝ) + δ / 2)
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [h₁.1, h₁.2]
    exact (isContactFormAt_mpullback_subtype_val_iff _ x).2 (hab (hδa hct) (hUb x x.property)).2
  · have hct : c t = t := hcid ⟨max_le ht.2.1 (by linarith [ht.1.1]),
      le_min ht.2.2 (by linarith [ht.1.2])⟩
    have htδ : dist t p.1 < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [ht.1.1, ht.1.2]
    have hx := ((hab (hδa htδ) (hUb x x.property)).1 (⟨t, ht.2⟩, x) rfl).2
    rw [mpullback_prodMk_mpullback_prodMap' hc.contMDiff Subtype.val contMDiff_subtypeVal, hct,
      map_kerDistribution_mpullback_subtype_val, hx]
    have hβ : mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β =
        mpullback (Prod.mk (⟨t, ht.2⟩ : unitInterval)) (contMDiff_const.prodMk contMDiff_id) α :=
      SmoothForm.mpullback_prodMk_timeExtend α ⟨t, ht.2⟩
    rw [hβ]

end IsContactFamily

end SymplecticGeometry

end
