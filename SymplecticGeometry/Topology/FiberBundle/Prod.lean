/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import Mathlib.Topology.FiberBundle.Constructions

import TauCeti.Topology.FiberBundle.Prod

/-!
# Continuous maps of fibrewise products of bundles

The total space of the fibrewise product `E₁ ×ᵇ E₂` of two bundles over the same base carries
the topology induced by its diagonal map to `TotalSpace F₁ E₁ × TotalSpace F₂ E₂`
(`FiberBundle.Prod.isInducing_diag`), and each of its two components is continuous (Tau Ceti's
`FiberBundle.Prod.continuous_totalSpaceFst` and `FiberBundle.Prod.continuous_totalSpaceSnd`).
A map into the total space of `E₁ ×ᵇ E₂` is therefore continuous exactly when its two
components are. So two families of fibrewise maps that are continuous on total spaces give a
fibrewise product that is continuous on total spaces, and the fibrewise swap
`E₁ ×ᵇ E₂ → E₂ ×ᵇ E₁` is continuous on total spaces. None of these statements needs a bundle
structure or any algebraic structure on the fibres, only topologies on the total spaces. For
bundles of modules, the same holds for the isomorphisms `x ↦ (Φ₁ x).prodCongr (Φ₂ x)` and
`x ↦ ContinuousLinearEquiv.prodComm R (E₁ x) (E₂ x)`.

The statements about these maps are the continuous counterparts of `Bundle.Prod.contMDiff_prodMap`,
`Bundle.Prod.contMDiff_swap`, `Bundle.Prod.contMDiff_prodCongr` and
`Bundle.Prod.contMDiff_prodComm` in `SymplecticGeometry.Geometry.Manifold.VectorBundle.Prod`.

## Main results

* `Bundle.Prod.continuous_totalSpace_prod_iff`: a map into the total space of `E₁ ×ᵇ E₂` is
  continuous if and only if its two components into the total spaces of `E₁` and `E₂` are. It is
  the continuous counterpart of Tau Ceti's `Bundle.contMDiffAt_totalSpace_prod_iff`, and its
  proof is that of Tau Ceti's `TauCeti.PrincipalBundle.FiberProd.continuous_iff`, stated there
  for the fibre product of principal bundles.
* `Bundle.Prod.continuous_prodMap`: the fibrewise product `Prod.map (f₁ x) (f₂ x)` of two maps
  that are continuous on total spaces is continuous on total spaces.
* `Bundle.Prod.continuous_swap`: the swap `E₁ ×ᵇ E₂ → E₂ ×ᵇ E₁` is continuous on total spaces.
* `Bundle.Prod.continuous_prodCongr` and `Bundle.Prod.continuous_prodComm`: the same two
  statements for continuous linear equivalences of the fibres.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
  (direct sums of vector bundles).
-/

public section

open Bundle

variable {B : Type*} {F₁ F₂ F₃ F₄ : Type*} {E₁ E₂ E₃ E₄ : B → Type*}
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [TopologicalSpace (TotalSpace F₃ E₃)] [TopologicalSpace (TotalSpace F₄ E₄)]

namespace Bundle.Prod

/-- A map into the total space of the fibrewise product `E₁ ×ᵇ E₂` is continuous if and only if
its two components, as maps into the total spaces of `E₁` and `E₂`, are continuous. -/
theorem continuous_totalSpace_prod_iff {X : Type*} [TopologicalSpace X]
    {f : X → TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)} :
    Continuous f ↔ Continuous (fun y ↦ (⟨(f y).proj, (f y).snd.1⟩ : TotalSpace F₁ E₁)) ∧
      Continuous (fun y ↦ (⟨(f y).proj, (f y).snd.2⟩ : TotalSpace F₂ E₂)) :=
  (FiberBundle.Prod.isInducing_diag F₁ E₁ F₂ E₂).continuous_iff.trans continuous_prodMk

/-- If the fibrewise maps `f₁ : E₁ → E₃` and `f₂ : E₂ → E₄` are continuous on total spaces, so
is their fibrewise product `Prod.map (f₁ x) (f₂ x) : E₁ ×ᵇ E₂ → E₃ ×ᵇ E₄`. -/
theorem continuous_prodMap {f₁ : ∀ x, E₁ x → E₃ x} {f₂ : ∀ x, E₂ x → E₄ x}
    (h₁ : Continuous fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₃ p.proj (f₁ p.proj p.snd))
    (h₂ : Continuous fun p : TotalSpace F₂ E₂ ↦ TotalSpace.mk' F₄ p.proj (f₂ p.proj p.snd)) :
    Continuous fun p : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) ↦
      TotalSpace.mk' (F₃ × F₄) (E := E₃ ×ᵇ E₄) p.proj (Prod.map (f₁ p.proj) (f₂ p.proj) p.snd) :=
  continuous_totalSpace_prod_iff.2
    ⟨h₁.comp FiberBundle.Prod.continuous_totalSpaceFst,
      h₂.comp FiberBundle.Prod.continuous_totalSpaceSnd⟩

/-- The fibrewise swap `E₁ ×ᵇ E₂ → E₂ ×ᵇ E₁` is continuous on total spaces. -/
theorem continuous_swap :
    Continuous fun p : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) ↦
      TotalSpace.mk' (F₂ × F₁) (E := E₂ ×ᵇ E₁) p.proj p.snd.swap :=
  continuous_totalSpace_prod_iff.2
    ⟨FiberBundle.Prod.continuous_totalSpaceSnd, FiberBundle.Prod.continuous_totalSpaceFst⟩

section Module

variable {R : Type*} [Semiring R]
  [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module R (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module R (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, AddCommMonoid (E₃ x)] [∀ x, Module R (E₃ x)] [∀ x, TopologicalSpace (E₃ x)]
  [∀ x, AddCommMonoid (E₄ x)] [∀ x, Module R (E₄ x)] [∀ x, TopologicalSpace (E₄ x)]

/-- If the fibrewise isomorphisms `Φ₁ : E₁ → E₃` and `Φ₂ : E₂ → E₄` are continuous on total
spaces, so is their direct sum `x ↦ (Φ₁ x).prodCongr (Φ₂ x) : E₁ ×ᵇ E₂ → E₃ ×ᵇ E₄`. -/
theorem continuous_prodCongr {Φ₁ : ∀ x, E₁ x ≃L[R] E₃ x} {Φ₂ : ∀ x, E₂ x ≃L[R] E₄ x}
    (hΦ₁ : Continuous fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₃ p.proj (Φ₁ p.proj p.snd))
    (hΦ₂ : Continuous fun p : TotalSpace F₂ E₂ ↦ TotalSpace.mk' F₄ p.proj (Φ₂ p.proj p.snd)) :
    Continuous fun p : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) ↦
      TotalSpace.mk' (F₃ × F₄) (E := E₃ ×ᵇ E₄) p.proj
        (((Φ₁ p.proj).prodCongr (Φ₂ p.proj)) p.snd) := by
  simpa only [ContinuousLinearEquiv.prodCongr_apply, Prod.map] using
    continuous_prodMap (f₁ := fun x ↦ Φ₁ x) (f₂ := fun x ↦ Φ₂ x) hΦ₁ hΦ₂

/-- The fibrewise swap `x ↦ ContinuousLinearEquiv.prodComm R (E₁ x) (E₂ x)` is continuous on
total spaces. -/
theorem continuous_prodComm :
    Continuous fun p : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) ↦
      TotalSpace.mk' (F₂ × F₁) (E := E₂ ×ᵇ E₁) p.proj
        (ContinuousLinearEquiv.prodComm R (E₁ p.proj) (E₂ p.proj) p.snd) := by
  simpa only [ContinuousLinearEquiv.prodComm_apply] using continuous_swap

end Module

end Bundle.Prod

end
