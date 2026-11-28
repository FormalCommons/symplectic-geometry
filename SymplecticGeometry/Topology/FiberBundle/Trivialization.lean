/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Topology.FiberBundle.MapFiber
public import SymplecticGeometry.Topology.Homeomorph.Prod
import SymplecticGeometry.Logic.Equiv.Prod
import TauCeti.Topology.FiberBundle.Trivialization

/-!
# Trivializations read through homeomorphisms

API for Mathlib's operations that read a trivialization through a homeomorphism of its model fibre
or of its total space. Tau Ceti's change of model fibre of a fibre bundle
(`Bundle.Trivialization.transModelFiber`, `FiberBundle.ofModelFiberHomeomorph`, in
`TauCeti.Topology.FiberBundle.ModelFiber`) is built from these operations.

## Main definitions and results

* `Bundle.Trivialization.transFiberHomeomorph_source`, `_target`: the source and target of
  Mathlib's `Bundle.Trivialization.transFiberHomeomorph`, which composes a trivialization with a
  homeomorphism of the model fibre; Tau Ceti gives its base set and inverse.
* `Bundle.Trivialization.transFiberwiseHomeomorph`: a trivialization followed, over an open set
  `U` of its base set, by a homeomorphism `Φ` of `U × F` that preserves the `U` coordinate, so
  that the fibre coordinate over each `b ∈ U` is changed by the fibre of `Φ` over `b`; with its
  base set, source, target, value and inverse.
* `Bundle.Trivialization.coordChange_transFiberwiseHomeomorph_left`, `_right`: its coordinate
  changes with another trivialization are those of the original trivialization composed with
  the fibres of `Φ⁻¹` or of `Φ`.
* `Bundle.Trivialization.coordChange_transFiberwiseHomeomorph_symm_left`, `_right`: for
  `Φ (p, v) = (p, χ p v)` with each `χ p` a homeomorphism of `F`, the coordinate changes of the
  trivialization followed by `Φ⁻¹` are those of the original one composed with `χ b` or its
  inverse.
* `Bundle.Trivialization.mapFiberHomeomorph`: the fibre `TauCeti.MapFiber proj b` over a point `b`
  of the base set of a trivialization, identified with the model fibre.
* `Bundle.Trivialization.compactSpace_of_isProperMap`: the model fibre of a proper map is compact
  as soon as some trivialization has a point in its base set.
* `Bundle.Trivialization.compHomeomorph_apply`, `_baseSet`, `_source`, `_target`, `_symm_apply`:
  the map, base set, source, target and inverse of Mathlib's
  `Bundle.Trivialization.compHomeomorph`, which precomposes a trivialization with a homeomorphism
  of the total space.
-/

public section

open Bundle

namespace Bundle.Trivialization

section transFiberHomeomorph

variable {B F F' Z : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace F']
  [TopologicalSpace Z] {proj : Z → B} (e : Trivialization F proj) (h : F ≃ₜ F')

@[simp]
theorem transFiberHomeomorph_source : (e.transFiberHomeomorph h).source = e.source :=
  (rfl)

@[simp]
theorem transFiberHomeomorph_target :
    (e.transFiberHomeomorph h).target = e.baseSet ×ˢ Set.univ := by
  rw [target_eq, transFiberHomeomorph_baseSet]

end transFiberHomeomorph

section transFiberwiseHomeomorph

open Set

variable {B F Z : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace Z]
  {proj : Z → B} (e : Trivialization F proj) {U : TopologicalSpace.Opens B}
  (hU : (U : Set B) ⊆ e.baseSet) (Φ : U × F ≃ₜ U × F) (hΦ : ∀ q, (Φ q).1 = q.1)

/-- A homeomorphism `Φ` of `U × F`, read on `B × F`: on `U ×ˢ univ` it is `Φ` followed by the
inclusion, elsewhere the identity. -/
private noncomputable def fiberwiseFun (Φ : U × F ≃ₜ U × F) (q : B × F) : B × F :=
  open Classical in
  if h : q.1 ∈ U then (q.1, (Φ (⟨q.1, h⟩, q.2)).2) else q

private theorem fiberwiseFun_of_mem {q : B × F} (h : q.1 ∈ U) :
    fiberwiseFun Φ q = (q.1, (Φ (⟨q.1, h⟩, q.2)).2) :=
  dite_eq_left h

private theorem fiberwiseFun_fiberwiseFun (hΦ : ∀ q, (Φ q).1 = q.1) {q : B × F}
    (h : q.1 ∈ U) : fiberwiseFun Φ.symm (fiberwiseFun Φ q) = q := by
  rw [fiberwiseFun_of_mem Φ h,
    fiberwiseFun_of_mem Φ.symm (q := (q.1, (Φ (⟨q.1, h⟩, q.2)).2)) h]
  have : ((⟨q.1, h⟩ : U), (Φ (⟨q.1, h⟩, q.2)).2) = Φ (⟨q.1, h⟩, q.2) :=
    Prod.ext (hΦ (⟨q.1, h⟩, q.2)).symm rfl
  rw [this, Homeomorph.symm_apply_apply]

private theorem continuousOn_fiberwiseFun :
    ContinuousOn (fiberwiseFun Φ) ((U : Set B) ×ˢ univ) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : ((U : Set B) ×ˢ univ).domRestrict (fiberwiseFun Φ) =
      fun q ↦ (q.val.1, (Φ (⟨q.val.1, q.property.1⟩, q.val.2)).2) :=
    funext fun q ↦ fiberwiseFun_of_mem Φ q.property.1
  rw [this]
  fun_prop

/-- A homeomorphism `Φ` of `U × F` over `U`, as an open partial homeomorphism of `B × F` with
source and target `U ×ˢ univ`. -/
private noncomputable def fiberwiseOPH : OpenPartialHomeomorph (B × F) (B × F) where
  toFun := fiberwiseFun Φ
  invFun := fiberwiseFun Φ.symm
  source := (U : Set B) ×ˢ univ
  target := (U : Set B) ×ˢ univ
  map_source' q h := by rw [fiberwiseFun_of_mem Φ h.1]; exact ⟨h.1, mem_univ _⟩
  map_target' q h := by rw [fiberwiseFun_of_mem _ h.1]; exact ⟨h.1, mem_univ _⟩
  left_inv' q h := fiberwiseFun_fiberwiseFun Φ hΦ h.1
  right_inv' q h := by
    simpa using
      fiberwiseFun_fiberwiseFun Φ.symm
        (Equiv.fst_symm_apply_of_forall_fst_apply (Φ := Φ.toEquiv) hΦ) h.1
  open_source := U.isOpen.prod isOpen_univ
  open_target := U.isOpen.prod isOpen_univ
  continuousOn_toFun := continuousOn_fiberwiseFun Φ
  continuousOn_invFun := continuousOn_fiberwiseFun Φ.symm

private theorem coe_fiberwiseOPH : ⇑(fiberwiseOPH Φ hΦ) = fiberwiseFun Φ :=
  (rfl)

private theorem coe_fiberwiseOPH_symm : ⇑(fiberwiseOPH Φ hΦ).symm = fiberwiseFun Φ.symm :=
  (rfl)

private theorem fiberwiseOPH_source : (fiberwiseOPH Φ hΦ).source = (U : Set B) ×ˢ univ :=
  (rfl)

private theorem fiberwiseOPH_target : (fiberwiseOPH Φ hΦ).target = (U : Set B) ×ˢ univ :=
  (rfl)

/-- Let `e` be a trivialization of `proj` with model fibre `F`, `U` an open set inside its base
set, and `Φ` a homeomorphism of `U × F` over `U`. This is the trivialization with base set `U`
that is `e` followed by `Φ`: it sends `y` to `(proj y, (Φ (proj y, (e y).2)).2)`. When
`Φ (p, v) = (p, χ p v)`, it changes the fibre coordinate of `e` over `p` by `χ p`. -/
noncomputable def transFiberwiseHomeomorph : Trivialization F proj where
  toOpenPartialHomeomorph := e.toOpenPartialHomeomorph.trans (fiberwiseOPH Φ hΦ)
  baseSet := U
  open_baseSet := U.isOpen
  source_eq := by
    ext y
    simp only [OpenPartialHomeomorph.trans_source, fiberwiseOPH_source, mem_inter_iff,
      mem_preimage, e.mem_source, mem_prod, mem_univ, and_true, coe_coe]
    exact ⟨fun h ↦ e.coe_fst' h.1 ▸ h.2, fun h ↦ ⟨hU h, (e.coe_fst' (hU h)).symm ▸ h⟩⟩
  target_eq := by
    ext q
    simp only [OpenPartialHomeomorph.trans_target, fiberwiseOPH_target, coe_fiberwiseOPH_symm,
      mem_inter_iff, mem_preimage, e.mem_target, mem_prod, mem_univ, and_true]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, by rw [fiberwiseFun_of_mem _ h]; exact hU h⟩⟩
  proj_toFun y h := by
    simp only [OpenPartialHomeomorph.trans_source, fiberwiseOPH_source, mem_inter_iff,
      mem_preimage, e.mem_source, mem_prod, coe_coe] at h
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, coe_fiberwiseOPH, coe_coe,
      fiberwiseFun_of_mem Φ h.2.1]
    exact e.coe_fst' h.1

@[simp]
theorem transFiberwiseHomeomorph_baseSet : (e.transFiberwiseHomeomorph hU Φ hΦ).baseSet = U :=
  (rfl)

@[simp]
theorem transFiberwiseHomeomorph_source :
    (e.transFiberwiseHomeomorph hU Φ hΦ).source = proj ⁻¹' U := by
  rw [source_eq, transFiberwiseHomeomorph_baseSet]

@[simp]
theorem transFiberwiseHomeomorph_target :
    (e.transFiberwiseHomeomorph hU Φ hΦ).target = (U : Set B) ×ˢ univ := by
  rw [target_eq, transFiberwiseHomeomorph_baseSet]

/-- Over `U`, `e.transFiberwiseHomeomorph hU Φ hΦ` is `e` followed by `Φ`. -/
theorem transFiberwiseHomeomorph_apply {y : Z} (hy : proj y ∈ U) :
    e.transFiberwiseHomeomorph hU Φ hΦ y = (proj y, (Φ (⟨proj y, hy⟩, (e y).2)).2) := by
  have hy' : (e y).1 ∈ U := (e.coe_fst' (hU hy)).symm ▸ hy
  -- The trivialization is `e` followed by `fiberwiseOPH Φ hΦ`, by definition.
  change fiberwiseOPH Φ hΦ (e y) = _
  rw [coe_fiberwiseOPH, fiberwiseFun_of_mem Φ hy']
  simp only [e.coe_fst' (hU hy)]

/-- The inverse of `e.transFiberwiseHomeomorph hU Φ hΦ` sends `(b, v)`, for `b ∈ U`, to the
image under the inverse of `e` of `(b, (Φ⁻¹ (b, v)).2)`. -/
theorem transFiberwiseHomeomorph_symm_apply {b : B} (hb : b ∈ U) (v : F) :
    (e.transFiberwiseHomeomorph hU Φ hΦ).toOpenPartialHomeomorph.symm (b, v) =
      e.toOpenPartialHomeomorph.symm (b, (Φ.symm (⟨b, hb⟩, v)).2) := by
  -- The inverse is that of `fiberwiseOPH Φ hΦ` followed by that of `e`, by definition.
  change e.toOpenPartialHomeomorph.symm ((fiberwiseOPH Φ hΦ).symm (b, v)) = _
  rw [coe_fiberwiseOPH_symm, fiberwiseFun_of_mem _ hb]

/-- The coordinate change from `e.transFiberwiseHomeomorph hU Φ hΦ` to a trivialization `e'`
over `b ∈ U` is the fibre of `Φ⁻¹` over `b` followed by the coordinate change from `e`. -/
theorem coordChange_transFiberwiseHomeomorph_left (e' : Trivialization F proj) {b : B}
    (hb : b ∈ U) (v : F) :
    (e.transFiberwiseHomeomorph hU Φ hΦ).coordChange e' b v =
      e.coordChange e' b (Φ.symm (⟨b, hb⟩, v)).2 := by
  rw [coordChange, coordChange, transFiberwiseHomeomorph_symm_apply]

/-- The coordinate change from a trivialization `e'` to `e.transFiberwiseHomeomorph hU Φ hΦ`
over a point `b ∈ U` of the base set of `e'` is the coordinate change to `e` followed by the
fibre of `Φ` over `b`. -/
theorem coordChange_transFiberwiseHomeomorph_right (e' : Trivialization F proj) {b : B}
    (hb : b ∈ U) (hb' : b ∈ e'.baseSet) (v : F) :
    e'.coordChange (e.transFiberwiseHomeomorph hU Φ hΦ) b v =
      (Φ (⟨b, hb⟩, e'.coordChange e b v)).2 := by
  have h := e'.proj_symm_apply' (x := v) hb'
  rw [coordChange, coordChange, transFiberwiseHomeomorph_apply e hU Φ hΦ (h.symm ▸ hb)]
  simp_rw [h]

/-! For `Φ (p, v) = (p, χ p v)` with a family `χ` of homeomorphisms of `F`, the trivialization
`e` followed by the inverse of `Φ` reads the fibre coordinate `v` of `e` over `b ∈ U` as
`(χ b)⁻¹ v`. -/

section Family

variable {Φ} {χ : U → F ≃ₜ F} (hχ : ∀ q, Φ q = (q.1, χ q.1 q.2))
include hχ

/-- If `Φ (p, v) = (p, χ p v)`, the coordinate change over `b ∈ U` from `e` followed by the
inverse of `Φ` to a trivialization `e'` is `χ b` followed by the coordinate change from `e`. -/
theorem coordChange_transFiberwiseHomeomorph_symm_left (e' : Trivialization F proj) {b : B}
    (hb : b ∈ U) :
    (e.transFiberwiseHomeomorph hU Φ.symm
        (Homeomorph.fst_symm_apply_of_apply_eq_prodMk hχ)).coordChange e' b =
      e.coordChange e' b ∘ χ ⟨b, hb⟩ :=
  funext fun v ↦ by
    rw [coordChange_transFiberwiseHomeomorph_left _ _ _ _ _ hb, Homeomorph.symm_symm, hχ,
      Function.comp_apply]

/-- If `Φ (p, v) = (p, χ p v)`, the coordinate change over a point `b ∈ U` of the base set of a
trivialization `e'`, from `e'` to `e` followed by the inverse of `Φ`, is the coordinate change
to `e` followed by the inverse of `χ b`. -/
theorem coordChange_transFiberwiseHomeomorph_symm_right (e' : Trivialization F proj) {b : B}
    (hb : b ∈ U) (hb' : b ∈ e'.baseSet) :
    e'.coordChange
        (e.transFiberwiseHomeomorph hU Φ.symm (Homeomorph.fst_symm_apply_of_apply_eq_prodMk hχ))
        b =
      (χ ⟨b, hb⟩).symm ∘ e'.coordChange e b :=
  funext fun v ↦ by
    rw [coordChange_transFiberwiseHomeomorph_right _ _ _ _ _ hb hb', Function.comp_apply,
      Φ.symm_apply_eq.2 (by rw [hχ]; simp :
        _ = Φ (⟨b, hb⟩, (χ ⟨b, hb⟩).symm (e'.coordChange e b v)))]

end Family

end transFiberwiseHomeomorph

section mapFiberHomeomorph

variable {B F Z : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace Z]
  {proj : Z → B} (e : Trivialization F proj) {b : B} (hb : b ∈ e.baseSet)

/-- The fibre `TauCeti.MapFiber proj b` of `proj` over a point `b` of the base set of a
trivialization `e` is homeomorphic to the model fibre `F`, by the fibre coordinate of `e`. This is
Mathlib's `Bundle.Trivialization.preimageSingletonHomeomorph`, read on `TauCeti.MapFiber proj b`
rather than on the subtype `proj ⁻¹' {b}`. -/
def mapFiberHomeomorph : TauCeti.MapFiber proj b ≃ₜ F :=
  ((Homeomorph.refl Z).subtype fun _ ↦ Set.mem_singleton_iff.symm).trans
    (e.preimageSingletonHomeomorph hb)

@[simp]
theorem mapFiberHomeomorph_apply (x : TauCeti.MapFiber proj b) :
    e.mapFiberHomeomorph hb x = (e x).2 :=
  (rfl)

@[simp]
theorem mapFiberHomeomorph_symm_apply (v : F) :
    (e.mapFiberHomeomorph hb).symm v =
      ⟨e.toOpenPartialHomeomorph.symm (b, v), e.proj_symm_apply' hb⟩ :=
  (rfl)

include hb in
/-- If `proj` is a proper map with a trivialization `e` whose base set contains a point `b`, then
the model fibre `F` is compact, being homeomorphic to the compact fibre of `proj` over `b`. -/
theorem compactSpace_of_isProperMap (hp : IsProperMap proj) : CompactSpace F :=
  have := isCompact_iff_compactSpace.1 (hp.isCompact_preimage (isCompact_singleton (x := b)))
  (e.preimageSingletonHomeomorph hb).compactSpace

end mapFiberHomeomorph

section compHomeomorph

variable {B F Z Z' : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace Z]
  [TopologicalSpace Z'] {proj : Z → B} (e : Trivialization F proj) (h : Z' ≃ₜ Z)

@[simp]
theorem compHomeomorph_apply (x : Z') : e.compHomeomorph h x = e (h x) :=
  (rfl)

@[simp]
theorem compHomeomorph_baseSet : (e.compHomeomorph h).baseSet = e.baseSet :=
  (rfl)

@[simp]
theorem compHomeomorph_source : (e.compHomeomorph h).source = h ⁻¹' e.source :=
  (rfl)

@[simp]
theorem compHomeomorph_target : (e.compHomeomorph h).target = e.target :=
  (rfl)

/-- The inverse of `e.compHomeomorph h` sends `x` to the image under `h.symm` of the image of `x`
under the inverse of `e`. -/
@[simp]
theorem compHomeomorph_symm_apply (x : B × F) :
    (e.compHomeomorph h).toOpenPartialHomeomorph.symm x =
      h.symm (e.toOpenPartialHomeomorph.symm x) :=
  (rfl)

end compHomeomorph

end Bundle.Trivialization

end
