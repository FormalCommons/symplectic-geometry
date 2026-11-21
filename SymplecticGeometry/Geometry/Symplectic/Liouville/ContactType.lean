/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Liouville.ContactType
public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Interior
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Contact type through local Liouville fields

Tau Ceti's `TauCeti.IsContactType J σ α ι` asks for a primitive `α` of `σ` near the image of
`ι : S → M` together with a field `Z`, smooth near the image, with `ι_Z σ = α` there and
transverse along `ι`. This file relates it to McDuff–Salamon's definition, which asks only for
a vector field defined near the hypersurface that is Liouville there, `L_Z σ = σ`, and transverse
to it, and derives the contact form of the hypersurface in the signs of the book.

* `TauCeti.isContactType_interior`: for a closed `C¹` two-form `σ`, a field `Z`, smooth and
  Liouville on an open neighbourhood `U` of the image of `ι` and transverse along `ι`, makes `ι`
  of contact type with primitive `ι_Z σ`.
* `TauCeti.exists_isContactType_iff`: for a closed `C¹` two-form `σ`, `ι` is of contact type for
  some primitive exactly when such a field exists. This is the local version of Tau Ceti's
  `TauCeti.exists_isRestrictedContactType_iff`, whose proof it adapts: Cartan's formula
  `L_Z σ = d(ι_Z σ)` is applied at each point of `U` (`mlieDerivForm_eq_mextDeriv_interior_apply`)
  instead of on all of `M`, and the exterior derivative of the primitive at a point of `U` is
  that of `ι_Z σ` because the two forms agree near the point.
* `TauCeti.SmoothEmbedding.isContactForm_neg_mpullback_interior`: for `σ` symplectic, a smooth
  embedding `i : S → M` of codimension one and such a field `Z`, the one-form
  `α = -i^*(ι_Z σ)` on `S` is a contact form with `dα = -i^*σ`. These are McDuff–Salamon's
  signs: the Liouville primitive is `λ = -ι_Z σ`, with `dλ = -σ`. The vector field is smooth
  only on `U`, so the form is built from the rough interior product `RoughForm.interior Z σ`;
  its pullback is nevertheless a smooth form on `S`, and the conclusion is stated for the bundled
  form with that value. The contact condition is checked point by point with
  `TauCeti.isContactFormAt_mpullback`, as in the proof of Tau Ceti's
  `TauCeti.IsContactType.isContactForm_mpullback`, which this proof adapts to a primitive that is
  smooth only near the image of `i`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.5.
-/

public section

open Bundle Module Set
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

/-- **The contact form induced by a local Liouville field**, in McDuff–Salamon's signs. Let `σ` be
a symplectic form on `M`, `i : S → M` a smooth embedding of codimension one, and `Z` a vector
field, smooth on an open neighbourhood `U` of the image of `i`, with `L_Z σ = σ` on `U` and
transverse along `i`. Then the one-form `α = -i^*(ι_Z σ)` on `S` is smooth, is a contact form,
and satisfies `dα = -i^*σ`. -/
theorem SmoothEmbedding.isContactForm_neg_mpullback_interior [IsManifold I ∞ M]
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
  have hα' : α'.val = mpullback J I i (RoughForm.interior Z σ.val) := rfl
  have hα'd : mextDerivₗ J 1 α' = SmoothForm.mpullback i i.contMDiff σ := by
    refine Subtype.ext (funext fun s ↦ ?_)
    rw [mextDerivₗ_apply, SmoothForm.coe_mpullback, ← mpullback_mextDeriv_at
      ((i.contMDiff s).of_le (by simp)) ((hβ s).of_le (by simp))]
    ext v
    rw [mpullback_apply, mpullback_apply, hdα _ (hiV (mem_range_self s))]
  refine ⟨-α', rfl, SmoothForm.isContactForm_neg_iff.2 ?_, by rw [map_neg, hα'd]⟩
  refine SmoothForm.isContactForm_iff_forall_isContactFormAt.2 fun s ↦ ?_
  rw [hα']
  refine isContactFormAt_mpullback hdim ((i.contMDiff s).of_le (by simp))
    (i.isImmersion.mfderiv_injective (by simp) s) (fun v hv ↦ ?_) ((hβ s).of_le (by simp))
    (hdα _ (hiV (mem_range_self s))) (isTransverseAlong_iff.1 hZi s) fun v ↦ ?_
  · exact (SmoothTwoForm.isNondegenerate_iff_separatingLeft.1 hσ.isNondegenerate) _ v fun w ↦ by
      simpa [SmoothBundleForm.eval₂_apply] using hv w
  · rw [RoughForm.interior_apply]

end TauCeti

end
