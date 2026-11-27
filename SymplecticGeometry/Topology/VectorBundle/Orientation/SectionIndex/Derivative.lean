/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.SectionIndex.Degree
public import SymplecticGeometry.Topology.OpenPartialHomeomorph.SourceRestrict

/-!
# The local index at a zero with invertible derivative

Tau Ceti computes the local index of a section `s` of an oriented real vector bundle at a zero `z`
as the sign of the determinant of the derivative of `s` read in a chart `φ` and a linear
trivialization `e` (`TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt`).
Its statement takes an open neighbourhood `U` of `z` on which `z` is the only zero of `s` and `e`
reads the orientation of every fibre as a fixed orientation `ω`.

Here `TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt_of_eventually`
finds such a neighbourhood itself: it needs only that `z` lies in the base set of `e` and the
source of `φ`, and that `e` reads the orientation of the fibres near `z` as `ω`. That `z` is an
isolated zero follows from the invertibility of the derivative (`HasFDerivAt.eventually_ne`).

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 (indices of sections at isolated zeros).
-/

public section

open Bundle Filter Module Set Topology

namespace TauCeti.VectorBundleOrientation

variable {M E' : Type} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [ChartedSpace E' M] {n : ℕ}
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {E : M → Type}
  [TopologicalSpace (TotalSpace F E)] [∀ x, AddCommMonoid (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- **The local index at a zero with invertible derivative is the sign of the Jacobian.** Let `e`
be a linear trivialization of `E` and `φ` a chart of `M` with values in the model fibre `F`, both
defined at a zero `z` of `s`. Suppose that `e` reads the orientation of every fibre near `z` as
the orientation `ω` of `F`, and that `φ`, followed by the translation taking `φ z` to the origin,
carries the local orientation `oM z` to the local orientation of `F` selected by `ω`. If the
section, read in these coordinates as `y ↦ (e (s (φ⁻¹ y))).2`, has at `φ z` a derivative `A` of
nonzero determinant, then the local index of `s` at `z`, an isolated zero, is the sign of
`det A`. -/
theorem sectionIndex_eq_sign_det_of_hasFDerivAt_of_eventually
    (o : VectorBundleOrientation F E (Fin (n + 1))) (hF : finrank ℝ F = n + 1)
    (oM : HomologicalOrientation M E' (n + 1)) {s : ∀ x, E x}
    (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x))
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] (φ : OpenPartialHomeomorph M F) {z : M}
    (hsz : s z = 0) (hze : z ∈ e.baseSet) (hzφ : z ∈ φ.source)
    {ω : Orientation ℝ F (Fin (n + 1))}
    (ho : ∀ᶠ x in 𝓝 z, ∀ hx : x ∈ e.baseSet, e.mapOrientation (Fin (n + 1)) hx (o x) = ω)
    (hφ : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (φ.centeredSourceRestrict z) (S := {⟨z, hzφ⟩}) (T := {0})
        (φ.centeredSourceRestrict_preimage_zero hzφ).subset (n + 1)
        ((φ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hzφ⟩
          (n + 1)).symm (oM z)).val =
      (ω.localOrientation hF).val)
    {A : F →L[ℝ] F}
    (hA : HasFDerivAt (fun y ↦ (e (TotalSpace.mk' F (φ.symm y) (s (φ.symm y)))).2) A (φ z))
    (hdet : A.det ≠ 0) :
    o.sectionIndex hF oM hs z = SignType.sign A.det := by
  have := FiniteDimensional.of_finrank_eq_succ hF
  set f : F → F := fun y ↦ (e (TotalSpace.mk' F (φ.symm y) (s (φ.symm y)))).2 with hf
  -- `A` is invertible, so `φ z` is an isolated zero of `f`.
  have hne : ∀ᶠ y in 𝓝[≠] φ z, f y ≠ 0 :=
    hA.eventually_ne ⟨_, (A.toContinuousLinearEquivOfDetNeZero hdet).antilipschitzWith⟩
  have hne' : ∀ᶠ x in 𝓝 z, φ x ≠ φ z → f (φ x) ≠ 0 :=
    (φ.continuousAt hzφ).eventually (eventually_nhdsWithin_iff.1 hne)
  -- An open neighbourhood `U` of `z` on which everything holds.
  have hev : ∀ᶠ x in 𝓝 z, x ∈ e.baseSet ∧ x ∈ φ.source ∧
      (∀ hx : x ∈ e.baseSet, e.mapOrientation (Fin (n + 1)) hx (o x) = ω) ∧
      (φ x ≠ φ z → f (φ x) ≠ 0) :=
    (e.open_baseSet.eventually_mem hze).and ((φ.open_source.eventually_mem hzφ).and (ho.and hne'))
  obtain ⟨U, hUsub, hUo, hzU⟩ := mem_nhds_iff.1 hev
  have hUz : ∀ x ∈ U, s x = 0 → x = z := by
    intro x hx h0
    obtain ⟨hxe, hxφ, -, hx'⟩ := hUsub hx
    by_contra hxz
    refine hx' (fun h ↦ hxz (φ.injOn hxφ hzφ h)) ?_
    have hfx : f (φ x) = (e (TotalSpace.mk' F x (s x))).2 := by
      simp only [hf]
      rw [φ.left_inv hxφ]
    rw [hfx, h0, ← Trivialization.linearEquivAt_apply (R := ℝ) _ _ hxe, map_zero]
  refine sectionIndex_eq_sign_det_of_hasFDerivAt o hF oM hs e φ hUo hzU hUz hsz
    (fun x hx ↦ (hUsub hx).1) (fun x hx ↦ (hUsub hx).2.1) (fun x hx ↦ (hUsub hx).2.2.1 _) ?_ hA
    hdet
  -- Tau Ceti's lemma states the centred chart by its body.
  convert hφ using 4
  exact (φ.centeredSourceRestrict_def z).symm

end TauCeti.VectorBundleOrientation

end
