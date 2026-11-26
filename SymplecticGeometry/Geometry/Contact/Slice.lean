/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Contact.Slice
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Contact forms on a slice transverse to the Reeb field

Two facts about a contact form `α` on `M` and a map into `M` that is transverse to the Reeb field,
beside Tau Ceti's `TauCeti/Geometry/Contact/Slice.lean`, whose Reeb-flow lemmas they use.

* On a hypersurface `ι : S → M` that is everywhere an immersion transverse to the Reeb field,
  `-d(ι^* α)` is symplectic
  (`TauCeti.SmoothForm.IsContactForm.isSymplectic_neg_mextDerivₗ_mpullback`), by Tau Ceti's
  `TauCeti.SmoothForm.IsContactForm.nondegenerate_bilinFormAt_mextDerivₗ_mpullback`.
* If `κ^* α = β + dg`, the map `(s, z) ↦ φ^R_{-z - g s} (κ s)`, with `φ^R` the local Reeb flow,
  pulls `α` back to `-(dz - β)` wherever it is defined
  (`TauCeti.SmoothForm.IsContactForm.mpullback_flowOf_neg_sub_apply`), since the Reeb flow out of
  `κ` pulls `α` back to `dt + κ^* α` (`TauCeti.mpullback_flowOf_comp_apply_eq_contactization`).
  Its proof follows the steps of the private lemma
  `mpullback_flowOf_comp_contactizationShift_comp_reassoc` of the proof of Tau Ceti's
  `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart`.

These are steps of the route of McDuff–Salamon, Exercise 3.5.22(i), to the Legendrian
neighbourhood theorem through a hypersurface tangent to `ker α`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §3.5, Exercise 3.5.22(i).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics
  109, Cambridge University Press, 2008, §2.5 (cited by Tau Ceti's proofs that this file uses
  and adapts).
-/

public section

open Function Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothForm.IsContactForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  [IsManifold J ∞ S]
  {α : SmoothForm I M ℝ 1}

/-- Let `ι : S → M` be a smooth map from a manifold of one dimension less which is, at every point,
an immersion whose image does not contain the Reeb vector of a contact form `α`. Then the two-form
`-d(ι^* α)` on `S` is symplectic. -/
theorem isSymplectic_neg_mextDerivₗ_mpullback (hα : α.IsContactForm)
    (hdim : finrank ℝ E' + 1 = finrank ℝ E) {ι : S → M} (hι : ContMDiff J I ∞ ι)
    (hιs : ∀ s, Injective (mfderiv J I ι s) ∧ α.reebVectorField (ι s) ∉ (mfderiv J I ι s).range) :
    SmoothTwoForm.IsSymplectic (-mextDerivₗ J 1 (SmoothForm.mpullback ι hι α)) :=
  ⟨(SmoothForm.isClosed_mextDerivₗ _).neg, SmoothTwoForm.IsNondegenerate.neg <|
    SmoothTwoForm.isNondegenerate_iff_separatingLeft.2 fun s v hv ↦
      (hα.nondegenerate_bilinFormAt_mextDerivₗ_mpullback hι hdim (hιs s).1 (hιs s).2).1 v
        fun w ↦ by rw [SmoothForm.bilinFormAt_apply]; exact hv w⟩

variable {ES HS S : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [TopologicalSpace HS]
  {IS : ModelWithCorners ℝ ES HS} [TopologicalSpace S] [ChartedSpace HS S] [IsManifold IS ∞ S]

/-- Let `κ : S → M` be a smooth map and `g` a smooth function on `S` with `κ^* α = β + dg`, for a
contact form `α` and a one-form `β` on `S`. At each point `(s, z)` of `S × ℝ` where the Reeb flow
`φ^R` of `α` is defined for the time `-z - g s` from `κ s`, the map `(s, z) ↦ φ^R_{-z - g s} (κ s)`
pulls `α` back to `-(dz - β)`, minus the contactization form of `β`. -/
theorem mpullback_flowOf_neg_sub_apply [I.Boundaryless] [T2Space M] (hα : α.IsContactForm)
    {κ : S → M} (hκ : ContMDiff IS I ∞ κ) {g : S → ℝ} (hg : ContMDiff IS 𝓘(ℝ) ∞ g)
    {β : SmoothForm IS S ℝ 1}
    (hκα : SmoothForm.mpullback κ hκ α = β + mextDerivₗ IS 0
      ⟨RoughForm.ofFunction _ g, (isSmoothForm_ofFunction_iff.2 hg).mem_smoothBundleForms⟩)
    {p : S × ℝ} (hp : (-p.2 - g p.1, κ p.1) ∈ flowDomain α.reebVectorField) :
    TauCeti.mpullback (IS.prod 𝓘(ℝ)) I
        (fun p : S × ℝ ↦ flowOf α.reebVectorField (-p.2 - g p.1) (κ p.1)) α.val p =
      (-β.contactization).val p := by
  have hR := hα.contMDiff_reebVectorField
  have hh : ContMDiff (IS.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ (fun p : S × ℝ ↦ -p.2 - g p.1) :=
    contMDiff_snd.neg.sub (hg.comp contMDiff_fst)
  have hχ := (contMDiff_fst (M := S) (N := ℝ)).prodMk hh
  have hFd : MDifferentiableAt _ I (fun q : S × ℝ ↦ flowOf α.reebVectorField q.2 (κ q.1))
      (p.1, -p.2 - g p.1) :=
    (contMDiffAt_flowOf_comp le_top hR contMDiffAt_snd (hκ.contMDiffAt.comp _ contMDiffAt_fst)
      hp).mdifferentiableAt (by simp)
  have hflow := mpullback_flowOf_comp_apply_eq_contactization hR hκ hα.apply_reebVectorField
    hα.interior_mextDeriv_reebVectorField (p := (p.1, -p.2 - g p.1)) hp
  have h1 : TauCeti.mpullback _ I
      (fun p : S × ℝ ↦ flowOf α.reebVectorField (-p.2 - g p.1) (κ p.1)) α.val p =
      (SmoothForm.mpullback (fun p : S × ℝ ↦ (p.1, -p.2 - g p.1)) hχ
        (-SmoothForm.mpullback κ hκ α).contactization).val p := by
    rw [show (fun p : S × ℝ ↦ flowOf α.reebVectorField (-p.2 - g p.1) (κ p.1)) =
        (fun q : S × ℝ ↦ flowOf α.reebVectorField q.2 (κ q.1)) ∘
          (fun p : S × ℝ ↦ (p.1, -p.2 - g p.1)) from rfl,
      mpullback_comp_at (hχ.mdifferentiableAt (by simp)) hFd, SmoothForm.coe_mpullback]
    exact TauCeti.mpullback_apply_congr hflow
  have hfst : MDifferentiable (IS.prod 𝓘(ℝ)) 𝓘(ℝ) (fun p : S × ℝ ↦ g p.1) :=
    (hg.comp (contMDiff_fst (n := ∞))).mdifferentiable (by simp)
  have hsnd : MDifferentiable (IS.prod 𝓘(ℝ)) 𝓘(ℝ) (fun p : S × ℝ ↦ p.2) :=
    (contMDiff_snd (n := ∞)).mdifferentiable (by simp)
  -- `d(-z - g) = -dz - dg`.
  have hdh : mextDeriv (RoughForm.ofFunction (IS.prod 𝓘(ℝ)) (fun p : S × ℝ ↦ -p.2 - g p.1)) =
      -mextDeriv (RoughForm.ofFunction _ (fun p : S × ℝ ↦ p.2)) -
        mextDeriv (RoughForm.ofFunction _ (fun p : S × ℝ ↦ g p.1)) := by
    rw [← mextDeriv_ofFunction_neg, ← mextDeriv_ofFunction_sub hsnd.neg hfst, Pi.sub_def,
      Pi.neg_def]
  have hfstα : (SmoothForm.mpullback (Prod.fst : S × ℝ → S) (contMDiff_fst (J := 𝓘(ℝ)))
      (SmoothForm.mpullback κ hκ α)).val =
      (SmoothForm.mpullback (Prod.fst : S × ℝ → S) contMDiff_fst β).val +
      mextDeriv (RoughForm.ofFunction _ (fun p : S × ℝ ↦ g p.1)) := by
    rw [hκα, map_add, Submodule.coe_add, ← SmoothForm.mextDerivₗ_mpullback, mextDerivₗ_apply,
      SmoothForm.coe_mpullback Prod.fst _ ⟨RoughForm.ofFunction _ g,
        (isSmoothForm_ofFunction_iff.2 hg).mem_smoothBundleForms⟩]
    exact congrArg₂ (· + ·) rfl (congrArg mextDeriv (mpullback_ofFunction _ _))
  rw [h1]
  refine congrFun ?_ p
  rw [SmoothForm.mpullback_prodMk_contactization _ contMDiff_fst hh, NegMemClass.coe_neg,
    SmoothForm.contactization_def, Submodule.coe_sub, SmoothForm.coe_mpullback Prod.snd,
    SmoothForm.mpullback_realLineCoordForm, map_neg, NegMemClass.coe_neg, hfstα, hdh]
  abel

end TauCeti.SmoothForm.IsContactForm

end
