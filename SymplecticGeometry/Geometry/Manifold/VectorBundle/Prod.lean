/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.Prod

/-!
# Smooth maps of direct-sum bundles

Two families of fibrewise maps between bundles over the same base whose maps of total spaces
are `C^n` give a `C^n` map of the direct-sum bundles, and the fibrewise swap of a direct-sum
bundle is `C^n` on total spaces. Both are stated for continuous linear equivalences of the
fibres, the bundle isomorphisms `x ↦ (Φ₁ x).prodCongr (Φ₂ x)` and
`x ↦ ContinuousLinearEquiv.prodComm 𝕜 (E₁ x) (E₂ x)`.

## Main results

* `Bundle.Prod.contMDiff_prodCongr`: the direct sum of two `C^n` maps of total spaces is `C^n`.
* `Bundle.Prod.contMDiff_prodComm`: the swap `E₁ ×ᵇ E₂ → E₂ ×ᵇ E₁` is `C^n` on total spaces.

Both follow from Tau Ceti's product criterion `Bundle.contMDiffAt_totalSpace_prod_iff`, with
`Bundle.Prod.contMDiff_fst` and `Bundle.Prod.contMDiff_snd`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
  (direct sums of vector bundles).
-/

public section

open Bundle
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {I : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F₁ F₂ F₃ F₄ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] [NormedAddCommGroup F₄] [NormedSpace 𝕜 F₄]
  {E₁ E₂ E₃ E₄ : B → Type*}
  [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, TopologicalSpace (E₂ x)] [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x, TopologicalSpace (E₃ x)] [∀ x, AddCommMonoid (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [∀ x, TopologicalSpace (E₄ x)] [∀ x, AddCommMonoid (E₄ x)] [∀ x, Module 𝕜 (E₄ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂]
  [TopologicalSpace (TotalSpace F₃ E₃)] [FiberBundle F₃ E₃]
  [TopologicalSpace (TotalSpace F₄ E₄)] [FiberBundle F₄ E₄]
  {n : WithTop ℕ∞}

namespace Bundle.Prod

/-- If the fibrewise maps `Φ₁ : E₁ → E₃` and `Φ₂ : E₂ → E₄` are `C^n` on total spaces, so is
their direct sum `E₁ ×ᵇ E₂ → E₃ ×ᵇ E₄`. -/
theorem contMDiff_prodCongr {Φ₁ : ∀ x, E₁ x ≃L[𝕜] E₃ x} {Φ₂ : ∀ x, E₂ x ≃L[𝕜] E₄ x}
    (hΦ₁ : ContMDiff (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₃)) n
      (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₃ p.proj (Φ₁ p.proj p.snd)))
    (hΦ₂ : ContMDiff (I.prod 𝓘(𝕜, F₂)) (I.prod 𝓘(𝕜, F₄)) n
      (fun p : TotalSpace F₂ E₂ ↦ TotalSpace.mk' F₄ p.proj (Φ₂ p.proj p.snd))) :
    ContMDiff (I.prod 𝓘(𝕜, F₁ × F₂)) (I.prod 𝓘(𝕜, F₃ × F₄)) n
      (fun p : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) ↦ TotalSpace.mk' (F₃ × F₄) (E := E₃ ×ᵇ E₄)
        p.proj (((Φ₁ p.proj).prodCongr (Φ₂ p.proj)) p.snd)) := fun p ↦ by
  simp only [ContinuousLinearEquiv.prodCongr_apply]
  exact contMDiffAt_totalSpace_prod_iff.2
    ⟨(hΦ₁.comp contMDiff_fst) p, (hΦ₂.comp contMDiff_snd) p⟩

/-- The fibrewise swap `E₁ ×ᵇ E₂ → E₂ ×ᵇ E₁` is `C^n` on total spaces. -/
theorem contMDiff_prodComm :
    ContMDiff (I.prod 𝓘(𝕜, F₁ × F₂)) (I.prod 𝓘(𝕜, F₂ × F₁)) n
      (fun p : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) ↦ TotalSpace.mk' (F₂ × F₁) (E := E₂ ×ᵇ E₁)
        p.proj (ContinuousLinearEquiv.prodComm 𝕜 (E₁ p.proj) (E₂ p.proj) p.snd)) := fun p ↦ by
  simp only [ContinuousLinearEquiv.prodComm_apply]
  exact contMDiffAt_totalSpace_prod_iff.2 ⟨contMDiff_snd p, contMDiff_fst p⟩

end Bundle.Prod

end
