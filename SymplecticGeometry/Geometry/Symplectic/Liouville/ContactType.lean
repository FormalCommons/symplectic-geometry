/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Liouville.ContactType
public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.DifferentialForm.Interior
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Contact.Flat
import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.RelativePoincare
import SymplecticGeometry.Geometry.Manifold.VectorField.Pullback
import SymplecticGeometry.Geometry.Symplectic.Manifold.Flat

/-!
# Contact type through local Liouville fields

Tau Ceti's `TauCeti.IsContactType J σ α ι` asks for a primitive `α` of `σ` near the image of
`ι : S → M` together with a field `Z`, smooth near the image, with `ι_Z σ = α` there and
transverse along `ι`. This file relates it to McDuff–Salamon's definition, which asks only for
a vector field defined near the hypersurface that is Liouville there, `L_Z σ = σ`, and transverse
to it. It derives the contact form of the hypersurface in the signs of the book and, conversely,
builds such a field from a prescribed contact form.

* `TauCeti.isContactType_interior`: for a closed `C¹` two-form `σ`, a field `Z`, smooth and
  Liouville on an open neighbourhood `U` of the image of `ι` and transverse along `ι`, makes `ι`
  of contact type with primitive `ι_Z σ`.
* `TauCeti.exists_isContactType_iff`: for a closed `C¹` two-form `σ`, `ι` is of contact type for
  some primitive exactly when such a field exists. This is the local version of Tau Ceti's
  `TauCeti.exists_isRestrictedContactType_iff`, whose proof it adapts: Cartan's formula
  `L_Z σ = d(ι_Z σ)` is applied at each point of `U` (`mlieDerivForm_eq_mextDeriv_interior_apply`)
  instead of on all of `M`, and the exterior derivative of the primitive at a point of `U` is
  that of `ι_Z σ` because the two forms agree near the point.
* `TauCeti.IsContactType.isContactFormAt_mpullback`: for a nondegenerate two-form, the pullback
  of a primitive `α` along a map `ι` of contact type and codimension one is contact at each
  point where `ι` is `C²` with injective differential. Here `α` is only a rough form; it is
  smooth near the image of `ι` because it equals `ι_Z σ` there. The proof is that of Tau Ceti's
  `TauCeti.IsContactType.isContactForm_mpullback`, adapted to such a primitive.
* `TauCeti.SmoothEmbedding.exists_isContactForm_eq_neg_mpullback_interior`: for `σ`
  symplectic, a smooth embedding `i : S → M` of codimension one and such a field `Z`, the one-form
  `α = -i^*(ι_Z σ)` on `S` is a contact form with `dα = -i^*σ`. These are McDuff–Salamon's
  signs: the Liouville primitive is `λ = -ι_Z σ`, with `dλ = -σ`. The vector field is smooth
  only on `U`, so the form is built from the rough interior product `RoughForm.interior Z σ`;
  its pullback is nevertheless a smooth form on `S`, and the conclusion is stated for the bundled
  form with that value. The contact condition follows from
  `TauCeti.IsContactType.isContactFormAt_mpullback`.
* `TauCeti.SmoothEmbedding.exists_liouville_of_isContactForm`: the converse for a prescribed
  form. For `σ` symplectic, a smooth embedding `i : S → M` and a contact form `α` on `S` with
  `dα = -i^*σ`, some field `Z`, smooth and Liouville on an open neighbourhood `U` of the image of
  `i` and transverse along `i`, has `-i^*(ι_Z σ) = α`. Following McDuff–Salamon, a primitive `β`
  of `-σ` near the image with `i^*β = α` comes from a tubular retraction and the relative Poincaré
  lemma (`TauCeti.SmoothEmbedding.exists_mextDeriv_eq_and_mpullback_eq`), and `Z` is the field
  with `ι_Z σ = -β`, obtained pointwise from the inverse flat map of `σ`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.interior_flat_inverse_ofSubsingleton`,
  `TauCeti.SmoothTwoForm.contMDiffAt_flat_inverse_apply`). It is Liouville by Cartan's formula. It
  is transverse because a vector `v` with `di(v) = Z` would satisfy `α(v) = 0` and `ι_v dα = α`,
  so that `ι_v dα + α(v) α = α`, which forces `α(v) = 1`
  (`TauCeti.SmoothForm.IsContactForm.contactFlat_apply_eq_iff`). This pointwise step is
  `TauCeti.SmoothForm.IsContactForm.notMem_range_mfderiv_of_interior_eq_neg`.
* Restriction to the open set `U` of a field `Z` that is smooth and Liouville on `U`: for the
  restriction `β = TauCeti.SmoothForm.restrictInterior σ Z hZ` of `ι_Z σ`, a smooth one-form on
  `U`, `TauCeti.SmoothTwoForm.mextDeriv_restrictInterior` and
  `TauCeti.SmoothTwoForm.interior_mextDeriv_restrictInterior` say that `dβ` is the restriction
  of `σ`, and that the restricted field `VectorField.mpullback I I Subtype.val Z` is Liouville
  for `β` in Tau Ceti's sense. The last is Tau Ceti's naturality of the interior product,
  `TauCeti.mpullback_interior`, after Cartan's formula on `U`, with the restricted field related
  to `Z` by `VectorField.mfderiv_subtypeVal_mpullback_subtypeVal`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.5.
-/

public section

open Bundle Module Set TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {U : Set M} {Z : (x : M) → TangentSpace I x}

section Rough

variable [IsManifold I 1 M] {σ : RoughForm I M ℝ 2} {ι : S → M}

/-- **A local Liouville field gives contact type.** Let `σ` be a closed `C¹` two-form and let `Z`
be a vector field, smooth on an open neighbourhood `U` of the image of `ι`, with `L_Z σ = σ` on
`U` and transverse along `ι`. Then `ι` is of contact type for `σ` with primitive `ι_Z σ`. -/
theorem isContactType_interior (hσ : IsSmoothForm I 1 σ) (hdσ : mextDeriv σ = 0) (hU : IsOpen U)
    (hιU : range ι ⊆ U) (hZ : ContMDiffOn I I.tangent (⊤ : ℕ∞) (T% Z) U)
    (hZσ : ∀ x ∈ U, mlieDerivForm Z σ x = σ x) (hZι : IsTransverseAlong J Z ι) :
    IsContactType J σ (σ.interior Z) ι := by
  refine isContactType_iff.2 ⟨U, hU, hιU, fun x hx ↦ ?_, Z, hZ, fun _ _ ↦ rfl, hZι⟩
  rw [← mlieDerivForm_eq_mextDeriv_interior_apply
    (hσ.contMDiff.mdifferentiable one_ne_zero x)
    ((hZ.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)) (congrFun hdσ x), hZσ x hx]

/-- **Contact type through local Liouville vector fields.** For a closed `C¹` two-form `σ`, a map
`ι` is of contact type for some primitive of `σ` exactly when some vector field `Z`, smooth on an
open neighbourhood `U` of the image of `ι`, satisfies `L_Z σ = σ` on `U` and is transverse along
`ι`. The primitive may then be taken to be `ι_Z σ` (`TauCeti.isContactType_interior`). -/
theorem exists_isContactType_iff (hσ : IsSmoothForm I 1 σ) (hdσ : mextDeriv σ = 0) :
    (∃ α, IsContactType J σ α ι) ↔
      ∃ U : Set M, IsOpen U ∧ range ι ⊆ U ∧ ∃ Z : (x : M) → TangentSpace I x,
        ContMDiffOn I I.tangent (⊤ : ℕ∞) (T% Z) U ∧ (∀ x ∈ U, mlieDerivForm Z σ x = σ x) ∧
          IsTransverseAlong J Z ι := by
  constructor
  · rintro ⟨α, hα⟩
    obtain ⟨U, hU, hιU, hdα, Z, hZ, hZα, hZι⟩ := isContactType_iff.1 hα
    refine ⟨U, hU, hιU, Z, hZ, fun x hx ↦ ?_, hZι⟩
    rw [mlieDerivForm_eq_mextDeriv_interior_apply (hσ.contMDiff.mdifferentiable one_ne_zero x)
      ((hZ.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)) (congrFun hdσ x),
      mextDeriv_congr_of_eventuallyEq (Filter.eventually_of_mem (hU.mem_nhds hx) hZα), hdα x hx]
  · rintro ⟨U, hU, hιU, Z, hZ, hZσ, hZι⟩
    exact ⟨_, isContactType_interior hσ hdσ hU hιU hZ hZσ hZι⟩

end Rough

/-- **Contact type for a rough primitive gives contact forms pointwise.** Let `ι : S → M`, from a
manifold of one dimension less, be of contact type for a nondegenerate two-form `σ`, with a
primitive `α` that need only be a rough form. If `ι` is `C²` at a point `s` and its differential
at `s` is injective, then the pullback `ι^* α` is a contact form at `s`. -/
theorem IsContactType.isContactFormAt_mpullback [IsManifold I ∞ M] [IsManifold J 2 S]
    {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate) {α : RoughForm I M ℝ 1} {ι : S → M}
    (h : IsContactType J σ.val α ι) {s : S} (hι : ContMDiffAt J I 2 ι s)
    (hιs : Function.Injective (mfderiv J I ι s)) (hdim : finrank ℝ E' + 1 = finrank ℝ E) :
    IsContactFormAt (mpullback J I ι α) s := by
  obtain ⟨U, hU, hιU, hdα, Z, hZ, hZα, hZι⟩ := isContactType_iff.1 h
  have hs : ι s ∈ U := hιU (mem_range_self s)
  -- Near `ι s` the primitive agrees with `ι_Z σ`, which is smooth there.
  have hα : ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) (ι s) :=
    (RoughForm.contMDiffAt_interior (hZ.contMDiffAt (hU.mem_nhds hs))
      (σ.contMDiff (ι s))).congr_of_eventuallyEq
      (Filter.eventually_of_mem (hU.mem_nhds hs) fun x hx ↦ by simp only [hZα x hx])
  refine TauCeti.isContactFormAt_mpullback hdim hι hιs (fun v hv ↦ ?_) (hα.of_le (by simp))
    (hdα _ hs) (isTransverseAlong_iff.1 hZι s) fun v ↦ ?_
  · exact (SmoothTwoForm.isNondegenerate_iff_separatingLeft.1 hσ) _ v fun w ↦ by
      simpa [SmoothBundleForm.eval₂_apply] using hv w
  · rw [← hZα _ hs, RoughForm.interior_apply]

/-- **The contact form induced by a local Liouville field**, in McDuff–Salamon's signs. Let `σ` be
a symplectic form on `M`, `i : S → M` a smooth embedding of codimension one, and `Z` a vector
field, smooth on an open neighbourhood `U` of the image of `i`, with `L_Z σ = σ` on `U` and
transverse along `i`. Then the one-form `α = -i^*(ι_Z σ)` on `S` is smooth, is a contact form,
and satisfies `dα = -i^*σ`. -/
theorem SmoothEmbedding.exists_isContactForm_eq_neg_mpullback_interior [IsManifold I ∞ M]
    [IsManifold J 2 S] {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
    (i : SmoothEmbedding J I ∞ S M) (hdim : finrank ℝ E' + 1 = finrank ℝ E) (hU : IsOpen U)
    (hiU : range i ⊆ U) (hZ : ContMDiffOn I I.tangent (⊤ : ℕ∞) (T% Z) U)
    (hZσ : ∀ x ∈ U, mlieDerivForm Z σ.val x = σ.val x) (hZi : IsTransverseAlong J Z i) :
    ∃ α : SmoothForm J S ℝ 1, α.val = -mpullback J I i (RoughForm.interior Z σ.val) ∧
      α.IsContactForm ∧
        mextDerivₗ J 1 α = -SmoothForm.mpullback i i.contMDiff σ := by
  have hdσ : mextDeriv σ.val = 0 :=
    (SmoothForm.isClosed_def σ).1 hσ.isClosed
  have hct := isContactType_interior (J := J) (σ.isSmoothForm.of_le (by simp)) hdσ hU hiU hZ
    hZσ hZi
  obtain ⟨V, -, hiV, hdα, -⟩ := isContactType_iff.1 hct
  -- The interior product `ι_Z σ` is smooth at each point of `U`.
  have hβ (s : S) := RoughForm.contMDiffAt_interior
    (hZ.contMDiffAt (hU.mem_nhds (hiU (mem_range_self s)))) (σ.contMDiff (i s))
  have hpb : IsSmoothForm J ∞ (mpullback J I i (RoughForm.interior Z σ.val)) :=
    (isSmoothForm_def ∞ _).mpr fun s ↦ (hβ s).mpullback_form (i.contMDiff s) (by simp)
  let α' : SmoothForm J S ℝ 1 := ⟨_, hpb.mem_smoothBundleForms⟩
  have hα'd : mextDerivₗ J 1 α' = SmoothForm.mpullback i i.contMDiff σ := by
    refine Subtype.ext (funext fun s ↦ ?_)
    rw [mextDerivₗ_apply, SmoothForm.coe_mpullback, ← mpullback_mextDeriv_at
      ((i.contMDiff s).of_le (by simp)) ((hβ s).of_le (by simp))]
    exact mpullback_apply_congr (hdα _ (hiV (mem_range_self s)))
  refine ⟨-α', rfl, SmoothForm.isContactForm_neg_iff.2 ?_, by rw [map_neg, hα'd]⟩
  exact SmoothForm.isContactForm_iff_forall_isContactFormAt.2
    fun s ↦ hct.isContactFormAt_mpullback hσ.isNondegenerate ((i.contMDiff s).of_le (by simp))
      (i.isImmersion.mfderiv_injective (by simp) s) hdim

/-- **A field dual to a primitive is transverse to a contact form.** Let `σ` be a two-form on `M`,
`i : S → M` a smooth map, `α` a contact form on `S` with `dα = -i^*σ`, and `β` a one-form on `M`
with `i^*β = α`. If `ι_Z σ = -β` at `i s`, then `Z (i s)` is not in the image of the differential
of `i` at `s`. -/
theorem SmoothForm.IsContactForm.notMem_range_mfderiv_of_interior_eq_neg [IsManifold I ∞ M]
    [IsManifold J ∞ S] {σ : SmoothTwoForm I M} {i : S → M} (hi : ContMDiff J I ∞ i)
    {α : SmoothForm J S ℝ 1} (hα : α.IsContactForm)
    (hdα : mextDerivₗ J 1 α = -SmoothForm.mpullback i hi σ) {β : RoughForm I M ℝ 1}
    (hiβ : TauCeti.mpullback J I i β = α.val) {s : S}
    (hZσ : RoughForm.interior Z σ.val (i s) = -β (i s)) :
    Z (i s) ∉ (mfderiv J I i s).range := by
  -- If `Z (i s) = di(v)`, then `α(v) = 0` and `ι_v dα = α`, against the contact condition.
  intro hs
  obtain ⟨v, hv⟩ := LinearMap.mem_range.1 hs
  replace hv : mfderiv J I i s v = Z (i s) := hv
  have hβZ (u : TangentSpace I (i s)) : β (i s) ![u] = -σ.val (i s) ![Z (i s), u] := by
    rw [← RoughForm.interior_apply, hZσ, ContinuousAlternatingMap.neg_apply, neg_neg]
  have hαβ (w : TangentSpace J s) : α.val s ![w] = β (i s) ![mfderiv J I i s w] := by
    rw [← hiβ, TauCeti.mpullback_apply]
    congr 1
    ext k
    fin_cases k
    simp
  have hdαv (w : TangentSpace J s) :
      mextDeriv α.val s ![v, w] = -σ.val (i s) ![mfderiv J I i s v, mfderiv J I i s w] := by
    rw [← mextDerivₗ_apply, hdα, SmoothForm.neg_toRoughForm, Pi.neg_apply,
      ContinuousAlternatingMap.neg_apply, SmoothForm.coe_mpullback, TauCeti.mpullback_apply]
    congr 2
    ext k
    fin_cases k <;> simp
  have hαv : α.val s ![v] = 0 := by
    rw [hαβ, hv, hβZ, (σ.val (i s)).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by simp),
      neg_zero]
  have hflat : α.contactFlat s v = SmoothForm.degreeOneEquiv α s := by
    ext w
    rw [SmoothForm.contactFlat_apply, hαv, zero_mul, add_zero, hdαv, hv, ← hβZ, ← hαβ,
      SmoothForm.degreeOneEquiv_apply_apply_vec]
  have h1 := ((hα.contactFlat_apply_eq_iff).1 hflat).1
  rw [hαv] at h1
  exact zero_ne_one h1

/-- **The Liouville field of a prescribed contact form**, in McDuff–Salamon's signs. Let `σ` be a
symplectic form on `M`, `i : S → M` a smooth embedding and `α` a contact form on `S` with
`dα = -i^*σ`. Then there are an open neighbourhood `U` of the image of `i` and a vector field `Z`,
smooth on `U`, with `L_Z σ = σ` on `U`, transverse along `i`, and with `-i^*(ι_Z σ) = α`. No
codimension is assumed: transversality follows from the contact condition alone. -/
theorem SmoothEmbedding.exists_liouville_of_isContactForm [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ E'] [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ M]
    [IsManifold J ∞ S] [T2Space M] [SecondCountableTopology M] {σ : SmoothTwoForm I M}
    (hσ : σ.IsSymplectic) (i : SmoothEmbedding J I ∞ S M) {α : SmoothForm J S ℝ 1}
    (hα : α.IsContactForm) (hdα : mextDerivₗ J 1 α = -SmoothForm.mpullback i i.contMDiff σ) :
    ∃ U : Set M, IsOpen U ∧ range i ⊆ U ∧ ∃ Z : (x : M) → TangentSpace I x,
      ContMDiffOn I I.tangent (⊤ : ℕ∞) (T% Z) U ∧ (∀ x ∈ U, mlieDerivForm Z σ.val x = σ.val x) ∧
        IsTransverseAlong J Z i ∧ -mpullback J I i (RoughForm.interior Z σ.val) = α.val := by
  have hσn := hσ.isNondegenerate
  -- A primitive `β` of `-σ` near the image of `i`, with `i^* β = α`.
  obtain ⟨U, hU, hiU, β, hβ, hdβ, hiβ⟩ := i.exists_mextDeriv_eq_and_mpullback_eq hσ.isClosed.neg
    (by rw [hdα, map_neg])
  -- The field `Z` with `ι_Z σ = -β`.
  let c : (x : M) → TangentSpace I x →L[ℝ] ℝ := fun x ↦
    (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ 0).symm (-β x)
  let Z : (x : M) → TangentSpace I x := fun x ↦ (σ.flat x).inverse (c x)
  have hZσ : RoughForm.interior Z σ.val = -β := hσn.interior_flat_inverse_ofSubsingleton (-β)
  have hZ : ContMDiffOn I I.tangent (⊤ : ℕ∞) (T% Z) U := fun x hx ↦ by
    have hc : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) y (c y))
        x := by
      refine contMDiffAt_ofSubsingleton_iff.1 ?_
      convert (hβ x hx).neg_section using 3 with y
      exact (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I y) ℝ 0).apply_symm_apply _
    exact (SmoothTwoForm.contMDiffAt_flat_inverse_apply le_rfl (hσn.isInvertible_flat x)
      hc).contMDiffWithinAt
  have hdσ : mextDeriv σ.val = 0 := (SmoothForm.isClosed_def σ).1 hσ.isClosed
  refine ⟨U, hU, hiU, Z, hZ, fun x hx ↦ ?_, isTransverseAlong_iff.2 fun s ↦ ?_, ?_⟩
  · -- Liouville by Cartan's formula: `L_Z σ = d(ι_Z σ) = -dβ = σ`.
    rw [mlieDerivForm_eq_mextDeriv_interior_apply
      (σ.isSmoothForm.contMDiff.mdifferentiable (by simp) x)
      ((hZ.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)) (congrFun hdσ x), hZσ,
      mextDeriv_neg, Pi.neg_apply, hdβ x hx, SmoothForm.neg_toRoughForm, Pi.neg_apply, neg_neg]
  · exact hα.notMem_range_mfderiv_of_interior_eq_neg i.contMDiff hdα hiβ
      ((congrFun hZσ (i s)).trans (Pi.neg_apply β (i s)))
  · rw [hZσ, ← hiβ, neg_eq_iff_eq_neg]
    funext s
    ext v
    simp [mpullback_apply]

section Restrict

/-! ### Restricting a local Liouville field to its open set -/

variable [IsManifold I ∞ M]

/-- Cartan's formula on an open set `U`: if `σ` is closed and the field `Z`, smooth on `U`, has
`L_Z σ = σ` on `U`, then the restriction of `ι_Z σ` to `U` is a primitive of the restriction of
`σ`. -/
theorem SmoothTwoForm.mextDeriv_restrictInterior {U : Opens M} {σ : SmoothTwoForm I M}
    (hσ : σ.IsClosed) (hZ : ContMDiffOn I I.tangent ∞ (T% Z) U)
    (hZσ : ∀ x ∈ U, mlieDerivForm Z σ.val x = σ.val x) :
    mextDeriv (σ.restrictInterior Z hZ).val = mpullback I I Subtype.val σ.val := by
  funext x
  have hZx := hZ.contMDiffAt (U.isOpen.mem_nhds x.property)
  rw [SmoothForm.coe_restrictInterior, ← mpullback_subtype_val_mextDeriv,
    mpullback_subtype_val_apply,
    ← mlieDerivForm_eq_mextDeriv_interior_apply
      (σ.isSmoothForm.contMDiff.mdifferentiable (by simp) x)
      (hZx.mdifferentiableAt (by simp))
      (congrFun ((SmoothForm.isClosed_def σ).1 hσ) x), hZσ x x.property,
    mpullback_subtype_val_apply]

/-- **The restriction of a local Liouville field.** If `σ` is closed and the field `Z`, smooth on
an open set `U`, has `L_Z σ = σ` on `U`, then its restriction `Z'` to `U` is a Liouville field of
the restriction `β` of `ι_Z σ` in Tau Ceti's sense: `ι_{Z'} dβ = β`. -/
theorem SmoothTwoForm.interior_mextDeriv_restrictInterior {U : Opens M} {σ : SmoothTwoForm I M}
    (hσ : σ.IsClosed) (hZ : ContMDiffOn I I.tangent ∞ (T% Z) U)
    (hZσ : ∀ x ∈ U, mlieDerivForm Z σ.val x = σ.val x) :
    (mextDeriv (σ.restrictInterior Z hZ).val).interior (VectorField.mpullback I I Subtype.val Z) =
      (σ.restrictInterior Z hZ).val := by
  rw [mextDeriv_restrictInterior hσ hZ hZσ, SmoothForm.coe_restrictInterior,
    ← mpullback_interior _ _ Z σ.val (VectorField.mfderiv_subtypeVal_mpullback_subtypeVal Z)]

end Restrict

end TauCeti

end
