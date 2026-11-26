/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import SymplecticGeometry.Topology.VectorBundle.Core.Basic
public import TauCeti.Topology.FiberBundle.Pullback
public import TauCeti.Topology.VectorBundle.Core.Congr
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import TauCeti.Topology.VectorBundle.Trivialization

/-!
# The finite-rank core of a vector bundle with any finite-dimensional model

Tau Ceti's `TauCeti.FiniteRankBundleCore.ofBundle` presents a vector bundle whose model fibre is
literally `Fin n → 𝕜`. This file removes that restriction: for a vector bundle `E` over `B` with
a finite-dimensional model fibre `G` and `h : finrank 𝕜 G = n`,
`TauCeti.FiniteRankBundleCore.ofBundleOfFinrankEq 𝕜 G E h` is the finite-rank core of rank `n`
obtained from the point-indexed core `TauCeti.pointIndexedCore 𝕜 G E` by transporting its model
along `ContinuousLinearEquiv.ofFinrankEq` (`VectorBundleCore.congrModel`).

## Main definitions and results

* `ofBundleOfFinrankEqFiberEquiv`: the identification of each fibre of the core with the fibre of
  `E`;
* `ofBundleOfFinrankEqHomeomorph`: the identification of total spaces, over the identity of `B`,
  acting on each fibre by `ofBundleOfFinrankEqFiberEquiv`;
* `ofBundleOfFinrankEqIso`: a fibrewise isomorphism of bundles, continuous on total spaces, gives
  an isomorphism of their cores; this is the analogue of `ofBundleIso`, and the two bundles may
  have different models;
* `pullback_ofBundleOfFinrankEq`: pulling back the core is the core of the pulled-back bundle, the
  analogue of `pullback_ofBundle`.

The constructions follow Tau Ceti's `ofBundle` and `ofBundleIso`, and the use of `congrModel` in
`TauCeti.FiniteRankAtlas.whitneyStratumCore`; the proof of `pullback_ofBundleOfFinrankEq`
adapts that of Tau Ceti's `pullback_ofBundle`.
-/

public section

open Bundle Module

namespace TauCeti

namespace FiniteRankBundleCore

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B : Type*} [TopologicalSpace B]

section Basic

variable (𝕜) (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  (E : B → Type*) [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace G E)]
  [FiberBundle G E] [VectorBundle 𝕜 G E] {n : ℕ}

/-- The finite-rank core of rank `n` of a vector bundle `E` whose model `G` has dimension `n`: the
point-indexed core of `E`, with its model transported to `Fin n → 𝕜` along
`ContinuousLinearEquiv.ofFinrankEq`. -/
-- Expose the rank projection so that the fibre model reduces to `Fin n → 𝕜`.
@[expose, implicit_reducible]
noncomputable def ofBundleOfFinrankEq (h : finrank 𝕜 G = n) : FiniteRankBundleCore 𝕜 B where
  rank := n
  core := (pointIndexedCore 𝕜 G E).congrModel
    (ContinuousLinearEquiv.ofFinrankEq (h.trans (finrank_fin_fun 𝕜).symm))
  indexAt_eq x := (VectorBundleCore.indexAt_congrModel _ _ x).trans
    (pointIndexedCore_indexAt 𝕜 G E x)

@[simp] theorem rank_ofBundleOfFinrankEq (h : finrank 𝕜 G = n) :
    (ofBundleOfFinrankEq 𝕜 G E h).rank = n := (rfl)

theorem core_ofBundleOfFinrankEq (h : finrank 𝕜 G = n) :
    (ofBundleOfFinrankEq 𝕜 G E h).core = (pointIndexedCore 𝕜 G E).congrModel
      (ContinuousLinearEquiv.ofFinrankEq (h.trans (finrank_fin_fun 𝕜).symm)) := (rfl)

@[simp] theorem localTriv_baseSet_ofBundleOfFinrankEq (h : finrank 𝕜 G = n) (i : B) :
    ((ofBundleOfFinrankEq 𝕜 G E h).core.localTriv i).baseSet =
      (trivializationAt G E i).baseSet := by
  rw [core_ofBundleOfFinrankEq, VectorBundleCore.localTriv_baseSet_congrModel,
    pointIndexedCore_localTriv_baseSet]

/-- The transitions of the core are those of `E`, read in `Fin n → 𝕜`. -/
@[simp] theorem coordChange_ofBundleOfFinrankEq (h : finrank 𝕜 G = n) (i j x : B) :
    (ofBundleOfFinrankEq 𝕜 G E h).core.coordChange i j x =
      (ContinuousLinearEquiv.ofFinrankEq (h.trans (finrank_fin_fun 𝕜).symm)).arrowCongr
        (ContinuousLinearEquiv.ofFinrankEq (h.trans (finrank_fin_fun 𝕜).symm))
        ((trivializationAt G E i).coordChangeL 𝕜 (trivializationAt G E j) x : G →L[𝕜] G) := by
  rw [core_ofBundleOfFinrankEq, VectorBundleCore.coordChange_congrModel,
    pointIndexedCore_coordChange]

/-- The fibre of `ofBundleOfFinrankEq 𝕜 G E h` at `x` is identified with the fibre of `E`. -/
noncomputable def ofBundleOfFinrankEqFiberEquiv (h : finrank 𝕜 G = n) (x : B) :
    (ofBundleOfFinrankEq 𝕜 G E h).core.Fiber x ≃L[𝕜] E x :=
  (ContinuousLinearEquiv.ofFinrankEq (h.trans (finrank_fin_fun 𝕜).symm)).symm.trans
    (pointIndexedCoreFiberEquiv 𝕜 G E x)

@[simp] theorem ofBundleOfFinrankEqFiberEquiv_apply (h : finrank 𝕜 G = n) (x : B) (v : Fin n → 𝕜) :
    ofBundleOfFinrankEqFiberEquiv 𝕜 G E h x v = pointIndexedCoreFiberEquiv 𝕜 G E x
      ((ContinuousLinearEquiv.ofFinrankEq (h.trans (finrank_fin_fun 𝕜).symm)).symm v) := (rfl)

@[simp] theorem ofBundleOfFinrankEqFiberEquiv_symm_apply (h : finrank 𝕜 G = n) (x : B) (v : E x) :
    (ofBundleOfFinrankEqFiberEquiv 𝕜 G E h x).symm v =
      ContinuousLinearEquiv.ofFinrankEq (h.trans (finrank_fin_fun 𝕜).symm)
        ((pointIndexedCoreFiberEquiv 𝕜 G E x).symm v) := (rfl)

/-- The total space of `ofBundleOfFinrankEq 𝕜 G E h` is homeomorphic to that of `E`, over the
identity of `B`, by `ofBundleOfFinrankEqFiberEquiv` on each fibre. -/
noncomputable def ofBundleOfFinrankEqHomeomorph (h : finrank 𝕜 G = n) :
    (ofBundleOfFinrankEq 𝕜 G E h).core.TotalSpace ≃ₜ TotalSpace G E :=
  ((pointIndexedCore 𝕜 G E).congrModelHomeomorph
    (ContinuousLinearEquiv.ofFinrankEq (h.trans (finrank_fin_fun 𝕜).symm))).symm.trans
    (pointIndexedCoreHomeomorph 𝕜 G E)

@[simp] theorem ofBundleOfFinrankEqHomeomorph_apply (h : finrank 𝕜 G = n)
    (p : (ofBundleOfFinrankEq 𝕜 G E h).core.TotalSpace) :
    ofBundleOfFinrankEqHomeomorph 𝕜 G E h p =
      ⟨p.proj, ofBundleOfFinrankEqFiberEquiv 𝕜 G E h p.proj p.snd⟩ := by
  rw [ofBundleOfFinrankEqHomeomorph, Homeomorph.trans_apply,
    VectorBundleCore.congrModelHomeomorph_symm_apply, pointIndexedCoreHomeomorph_apply]
  rfl

@[simp] theorem ofBundleOfFinrankEqHomeomorph_symm_apply (h : finrank 𝕜 G = n)
    (p : TotalSpace G E) :
    (ofBundleOfFinrankEqHomeomorph 𝕜 G E h).symm p =
      ⟨p.proj, (ofBundleOfFinrankEqFiberEquiv 𝕜 G E h p.proj).symm p.snd⟩ := by
  rw [ofBundleOfFinrankEqHomeomorph, Homeomorph.symm_trans_apply, Homeomorph.symm_symm,
    pointIndexedCoreHomeomorph_symm_apply, VectorBundleCore.congrModelHomeomorph_apply]
  rfl

end Basic

section Iso

variable {G₀ : Type*} [NormedAddCommGroup G₀] [NormedSpace 𝕜 G₀] [FiniteDimensional 𝕜 G₀]
  {E₀ : B → Type*} [∀ x, AddCommMonoid (E₀ x)] [∀ x, Module 𝕜 (E₀ x)]
  [∀ x, TopologicalSpace (E₀ x)] [TopologicalSpace (TotalSpace G₀ E₀)]
  [FiberBundle G₀ E₀] [VectorBundle 𝕜 G₀ E₀]
  {G₁ : Type*} [NormedAddCommGroup G₁] [NormedSpace 𝕜 G₁] [FiniteDimensional 𝕜 G₁]
  {E₁ : B → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [TopologicalSpace (TotalSpace G₁ E₁)]
  [FiberBundle G₁ E₁] [VectorBundle 𝕜 G₁ E₁]
  {n₀ n₁ : ℕ} (h₀ : finrank 𝕜 G₀ = n₀) (h₁ : finrank 𝕜 G₁ = n₁)
  (Φ : ∀ x, E₀ x ≃L[𝕜] E₁ x)
  (hΦ : Continuous fun p : TotalSpace G₀ E₀ ↦ TotalSpace.mk' G₁ (E := E₁) p.proj (Φ p.proj p.snd))

/-- A fibrewise continuous linear equivalence of bundles, continuous on total spaces, induces an
isomorphism of their finite-rank cores, by `Φ` on each fibre read through
`ofBundleOfFinrankEqFiberEquiv`. -/
noncomputable def ofBundleOfFinrankEqIso :
    ofBundleOfFinrankEq 𝕜 G₀ E₀ h₀ ≅ ofBundleOfFinrankEq 𝕜 G₁ E₁ h₁ :=
  isoOfContinuousEquiv (fun x ↦ (ofBundleOfFinrankEqFiberEquiv 𝕜 G₀ E₀ h₀ x).trans
      ((Φ x).trans (ofBundleOfFinrankEqFiberEquiv 𝕜 G₁ E₁ h₁ x).symm)) <|
    ((ofBundleOfFinrankEqHomeomorph 𝕜 G₁ E₁ h₁).symm.continuous.comp
      (hΦ.comp (ofBundleOfFinrankEqHomeomorph 𝕜 G₀ E₀ h₀).continuous)).congr fun p ↦ by
        rw [Function.comp_apply, Function.comp_apply, ofBundleOfFinrankEqHomeomorph_apply,
          ofBundleOfFinrankEqHomeomorph_symm_apply]
        rfl

@[simp] theorem fiberMap_ofBundleOfFinrankEqIso_hom (x : B) :
    (ofBundleOfFinrankEqIso h₀ h₁ Φ hΦ).hom.fiberMap x =
      ContinuousLinearEquiv.toContinuousLinearMap
        ((ofBundleOfFinrankEqFiberEquiv 𝕜 G₀ E₀ h₀ x).trans
          ((Φ x).trans (ofBundleOfFinrankEqFiberEquiv 𝕜 G₁ E₁ h₁ x).symm)) := by
  rw [ofBundleOfFinrankEqIso]; exact fiberMap_isoOfContinuousEquiv_hom _ _ x

@[simp] theorem fiberMap_ofBundleOfFinrankEqIso_inv (x : B) :
    (ofBundleOfFinrankEqIso h₀ h₁ Φ hΦ).inv.fiberMap x =
      ContinuousLinearEquiv.toContinuousLinearMap
        ((ofBundleOfFinrankEqFiberEquiv 𝕜 G₀ E₀ h₀ x).trans
          ((Φ x).trans (ofBundleOfFinrankEqFiberEquiv 𝕜 G₁ E₁ h₁ x).symm)).symm := by
  rw [ofBundleOfFinrankEqIso]; exact fiberMap_isoOfContinuousEquiv_inv _ _ x

end Iso

section Pullback

variable {X : Type*} [TopologicalSpace X]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  (E : B → Type*) [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace G E)]
  [FiberBundle G E] [VectorBundle 𝕜 G E] {n : ℕ} (h : finrank 𝕜 G = n)

/-- Pulling back `ofBundleOfFinrankEq 𝕜 G E h` along `f` gives, strictly, the core of the
pulled-back bundle `f *ᵖ E`. -/
@[simp] theorem pullback_ofBundleOfFinrankEq (f : C(X, B)) :
    (ofBundleOfFinrankEq 𝕜 G E h).pullback f = ofBundleOfFinrankEq 𝕜 G ((⇑f) *ᵖ E) h := by
  have htriv (k : X) : trivializationAt G ((⇑f) *ᵖ E) k =
      (trivializationAt G E (f k)).pullback f :=
    FiberBundle.pullback_trivializationAt' (F := G) (E := E) f k
  dsimp only [pullback]
  congr 1
  refine VectorBundleCore.ext ?_ ?_ ?_
  · funext x
    -- The chart domains of a pulled-back core are preimages, by the definition of `pullback`.
    change f ⁻¹' (ofBundleOfFinrankEq 𝕜 G E h).core.baseSet (f x) =
      (ofBundleOfFinrankEq 𝕜 G ((⇑f) *ᵖ E) h).core.baseSet x
    rw [VectorBundleCore.baseSet_at, VectorBundleCore.baseSet_at,
      localTriv_baseSet_ofBundleOfFinrankEq, localTriv_baseSet_ofBundleOfFinrankEq, htriv x,
      Trivialization.pullback_baseSet]
  · funext x
    exact ((ofBundleOfFinrankEq 𝕜 G ((⇑f) *ᵖ E) h).indexAt_eq x).symm
  · funext i j x
    -- The transitions of a pulled-back core are evaluated at the images, by definition.
    change (ofBundleOfFinrankEq 𝕜 G E h).core.coordChange (f i) (f j) (f x) =
      (ofBundleOfFinrankEq 𝕜 G ((⇑f) *ᵖ E) h).core.coordChange i j x
    rw [coordChange_ofBundleOfFinrankEq, coordChange_ofBundleOfFinrankEq]
    congr 1
    simp only [htriv]
    set eᵢ := trivializationAt G E (f i); set eⱼ := trivializationAt G E (f j)
    by_cases hx : x ∈ (eᵢ.pullback f).baseSet ∩ (eⱼ.pullback f).baseSet
    · have hfx : f x ∈ eᵢ.baseSet ∩ eⱼ.baseSet := hx
      refine ContinuousLinearMap.ext fun v ↦ ?_; simp only [ContinuousLinearEquiv.coe_coe]
      rw [Trivialization.coordChangeL_apply' eᵢ eⱼ hfx,
        Trivialization.coordChangeL_apply' (eᵢ.pullback f) (eⱼ.pullback f) hx]
      exact (eᵢ.coordChange_pullback eⱼ f hfx.1 v).symm
    · have hfx : f x ∉ eᵢ.baseSet ∩ eⱼ.baseSet := hx
      rw [eᵢ.coordChangeL_of_notMem 𝕜 eⱼ hfx,
        (eᵢ.pullback f).coordChangeL_of_notMem 𝕜 (eⱼ.pullback f) hx]

end Pullback

end FiniteRankBundleCore

end TauCeti
