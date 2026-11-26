/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousAffineEquiv
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage
public import TauCeti.Analysis.Convex.LocalToGlobal

/-!
# Transporting convexity charts

Tau Ceti's `TauCeti.IsConvexChart f U` says that `U` is an open set on which `f : X → E` is an
open map onto a convex image with preconnected fibres. This file shows that the notion is
invariant under the changes of coordinates that occur when a map is put in a normal form: an
affine change of coordinates on the target, and a homeomorphism, or a partial homeomorphism such as
a chart, on the source.

## Main results

* `TauCeti.IsConvexChart.congr`: a convexity chart only depends on the map on the chart.
* `TauCeti.IsConvexChart.continuousAffineEquiv_comp`: composing with a continuous affine
  equivalence `e` of the target turns a convexity chart of `f` into one of `e ∘ f`; in particular
  `TauCeti.IsConvexChart.add_const` and `TauCeti.IsConvexChart.const_add` translate the target.
* `TauCeti.IsConvexChart.image_iff`: for a partial homeomorphism `e` and `U ⊆ e.source`,
  `e '' U` is a convexity chart of `f` if and only if `U` is one of `f ∘ e`;
  `TauCeti.IsConvexChart.comp_symm_image_iff` is the same statement for a map on the source of
  `e` written in the coordinates of `e`, and `TauCeti.IsConvexChart.image_homeomorph_iff` the one
  for a homeomorphism.

Both directions of `TauCeti.IsConvexChart.image_iff` are instances of Tau Ceti's
`TauCeti.IsConvexChart.source_inter_preimage`, applied to `e` and to `e.symm`.

The proof of `TauCeti.IsConvexChart.continuousAffineEquiv_comp` follows that of Tau Ceti's
`TauCeti.IsConvexChart.continuousLinearEquiv_comp`, with an affine equivalence in place of a linear
one.

## References

* [C. Bjorndahl and Y. Karshon, *Revisiting Tietze–Nakajima: local and global convexity for
  maps*][BjorndahlKarshon2010]
-/

public section

open Function Set Topology

namespace TauCeti.IsConvexChart

variable {X Y E F : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f g : X → E} {U : Set X}

/-- Being a convexity chart `U` of `f` only depends on the values of `f` on `U`. -/
theorem congr (hU : IsConvexChart f U) (h : EqOn f g U) : IsConvexChart g U where
  isOpen := hU.isOpen
  convex_image := h.image_eq ▸ hU.convex_image
  image_mem_nhdsWithin W hW hWo x hx := by
    rw [← h.image_eq, ← (h.mono hW).image_eq, ← h (hW hx)]
    exact hU.image_mem_nhdsWithin W hW hWo x hx
  isPreconnected_inter_preimage_singleton v := by
    rw [← h.inter_preimage_eq]
    exact hU.isPreconnected_inter_preimage_singleton v

/-- Composing with a continuous affine equivalence `e` of the target preserves convexity charts:
a convexity chart of `f` is one of `e ∘ f`. -/
theorem continuousAffineEquiv_comp (hU : IsConvexChart f U) (e : E ≃ᴬ[ℝ] F) :
    IsConvexChart (e ∘ f) U where
  isOpen := hU.isOpen
  convex_image := by
    rw [image_comp]
    exact hU.convex_image.affine_image (e : E →ᵃ[ℝ] F)
  image_mem_nhdsWithin W hW hWo x hx := by
    have h := (Homeomorph.ofClass e).isEmbedding.map_nhdsWithin_eq (f '' U) (f x)
    rw [Homeomorph.coe_ofClass] at h
    rw [image_comp, image_comp, comp_apply, ← h]
    exact Filter.image_mem_map (hU.image_mem_nhdsWithin W hW hWo x hx)
  isPreconnected_inter_preimage_singleton w := by
    convert hU.isPreconnected_inter_preimage_singleton (e.symm w) using 2
    ext x
    simp [e.eq_symm_apply]

/-- A convexity chart of `f` is one of its translate `fun x ↦ c + f x`. -/
theorem const_add (hU : IsConvexChart f U) (c : E) : IsConvexChart (fun x ↦ c + f x) U := by
  simpa [comp_def, ← ContinuousAffineEquiv.coe_coe, ContinuousAffineEquiv.constVAdd_coe] using
    hU.continuousAffineEquiv_comp (ContinuousAffineEquiv.constVAdd ℝ E c)

/-- A convexity chart of `f` is one of its translate `fun x ↦ f x + c`. -/
theorem add_const (hU : IsConvexChart f U) (c : E) : IsConvexChart (fun x ↦ f x + c) U := by
  simpa only [add_comm c] using hU.const_add c

/-- For a partial homeomorphism `e` and `U ⊆ e.source`, the image `e '' U` is a convexity chart of
`f` if and only if `U` is a convexity chart of `f ∘ e`. -/
theorem image_iff (e : OpenPartialHomeomorph X Y) (hUe : U ⊆ e.source) {f : Y → E} :
    IsConvexChart f (e '' U) ↔ IsConvexChart (f ∘ e) U := by
  have hUt : e '' U ⊆ e.target := (image_mono hUe).trans e.image_source_eq_target.subset
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' := h.source_inter_preimage hUt (f := f ∘ e) fun _ _ ↦ rfl
    rwa [inter_comm, e.injOn.preimage_image_inter hUe] at h'
  · have h' := h.source_inter_preimage (e := e.symm) (by rwa [e.symm_target]) (f := f)
      fun y hy ↦ by simp [e.right_inv (e.symm_source ▸ hy)]
    rwa [e.symm_source, ← e.image_eq_target_inter_inv_preimage hUe] at h'

/-- For a partial homeomorphism `e` and `U ⊆ e.source`, the image `e '' U` is a convexity chart of
`f ∘ e.symm`, the map `f` written in the coordinates given by `e`, if and only if `U` is a
convexity chart of `f`. -/
theorem comp_symm_image_iff (e : OpenPartialHomeomorph X Y) (hUe : U ⊆ e.source) :
    IsConvexChart (f ∘ e.symm) (e '' U) ↔ IsConvexChart f U := by
  rw [image_iff e hUe]
  have h : EqOn (f ∘ e.symm ∘ e) f U := fun x hx ↦ by simp [e.left_inv (hUe hx)]
  exact ⟨fun hU ↦ hU.congr h, fun hU ↦ hU.congr h.symm⟩

/-- For a homeomorphism `h`, the image `h '' U` is a convexity chart of `f` if and only if `U` is
a convexity chart of `f ∘ h`. -/
theorem image_homeomorph_iff (h : X ≃ₜ Y) {f : Y → E} :
    IsConvexChart f (h '' U) ↔ IsConvexChart (f ∘ h) U :=
  image_iff h.toOpenPartialHomeomorph (by simp)

end TauCeti.IsConvexChart

end
