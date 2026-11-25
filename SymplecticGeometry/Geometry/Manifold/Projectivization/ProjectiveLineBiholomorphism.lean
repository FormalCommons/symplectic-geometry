/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.Projectivization.ProjectiveLine
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Biholomorphisms of the projective line in affine coordinates

A map `f` of `ℂℙ¹ = ℙ ℂ (Fin 2 → ℂ)`, read through Tau Ceti's affine coordinate
`TauCeti.ProjectiveLine.affineParam i` near a point `y` and the affine chart `affineChart j` near
`f y`, is a function of one complex variable `t ↦ affineChart j (f (affineParam i t)) 0`. This
file shows that this function is `C^r` near the coordinate of `y` when `f` is `C^r` at `y`, and
that its derivative there does not vanish when `f` is a diffeomorphism: the inverse, read in the
same charts the other way round, is a left inverse near that point, and the chain rule gives the
product of the two derivatives as `1`.

## Main results

* `Projectivization.contDiffAt_affineChart_comp_affineParam`: the coordinate expression of a map
  that is `C^r` at `y` is `C^r` near the coordinate of `y`.
* `Projectivization.deriv_affineChart_diffeomorph_affineParam_ne_zero`: the coordinate expression
  of a complex diffeomorphism has nonzero derivative.
-/

public section

open Filter Set TauCeti.ProjectiveLine
open scoped ContDiff Manifold Topology LinearAlgebra.Projectivization

namespace Projectivization

variable {i j : Fin 2} {y : ℙ ℂ (Fin 2 → ℂ)} {r : WithTop ℕ∞}

/-- A map `f` of `ℂℙ¹` that is `C^r` at `y`, read in the affine coordinate `i` near `y` and the
affine chart `j` near `f y`, is a `C^r` function of one complex variable near the coordinate of
`y`. -/
theorem contDiffAt_affineChart_comp_affineParam {f : ℙ ℂ (Fin 2 → ℂ) → ℙ ℂ (Fin 2 → ℂ)}
    (hf : ContMDiffAt 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, Fin 1 → ℂ) r f y) (hy : y ∈ affineOpen i)
    (hfy : f y ∈ affineOpen j) :
    ContDiffAt ℂ r (fun t ↦ affineChart j (f (affineParam i t)) 0) (affineChart i y 0) := by
  have hT : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin 1 → ℂ) r (affineChart j ∘ f ∘ affineParam i)
      (affineChart i y 0) := by
    have hp : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin 1 → ℂ) r (f ∘ affineParam i) (affineChart i y 0) :=
      ContMDiffAt.comp (I' := 𝓘(ℂ, Fin 1 → ℂ)) _ (by rwa [affineParam_affineChart hy])
        (contMDiff_affineParam i).contMDiffAt
    refine ContMDiffAt.comp _ ?_ hp
    rw [Function.comp_apply, affineParam_affineChart hy]
    exact (contMDiffOn_affineChart (𝕜 := ℂ) (n := 1) j r).contMDiffAt
      ((isOpen_affineOpen j).mem_nhds hfy)
  have hT' : ContDiffAt ℂ r (affineChart j ∘ f ∘ affineParam i) (affineChart i y 0) :=
    contMDiffAt_iff_contDiffAt.1 hT
  exact (contDiff_apply (𝕜 := ℂ) (F' := fun _ : Fin 1 ↦ ℂ) 0).comp_contDiffAt _ hT'

/-- A `C^r` diffeomorphism `Ψ` of `ℂℙ¹` (`r ≠ 0`), read in the affine coordinate `i` near `y` and
the affine chart `j` near `Ψ y`, has nonzero derivative at the coordinate of `y`. -/
theorem deriv_affineChart_diffeomorph_affineParam_ne_zero
    (Ψ : ℙ ℂ (Fin 2 → ℂ) ≃ₘ^r⟮𝓘(ℂ, Fin 1 → ℂ), 𝓘(ℂ, Fin 1 → ℂ)⟯ ℙ ℂ (Fin 2 → ℂ)) (hr : r ≠ 0)
    (hy : y ∈ affineOpen i) (hΨy : Ψ y ∈ affineOpen j) :
    deriv (fun t ↦ affineChart j (Ψ (affineParam i t)) 0) (affineChart i y 0) ≠ 0 := by
  set h := fun t ↦ affineChart j (Ψ (affineParam i t)) 0
  set k := fun s ↦ affineChart i (Ψ.symm (affineParam j s)) 0
  have hhc : h (affineChart i y 0) = affineChart j (Ψ y) 0 := by
    simp only [h, affineParam_affineChart hy]
  have hh := contDiffAt_affineChart_comp_affineParam Ψ.contMDiff.contMDiffAt hy hΨy
  have hk := contDiffAt_affineChart_comp_affineParam Ψ.symm.contMDiff.contMDiffAt hΨy
    (by rwa [Diffeomorph.symm_apply_apply])
  -- `k` is a left inverse of `h` near the coordinate of `y`.
  have hev : k ∘ h =ᶠ[𝓝 (affineChart i y 0)] id := by
    have hc : ContinuousAt (Ψ ∘ affineParam i) (affineChart i y 0) :=
      (Ψ.continuous.comp (contMDiff_affineParam (n := 0) i).continuous).continuousAt
    have hmem : (Ψ ∘ affineParam i) (affineChart i y 0) ∈ affineOpen j := by
      rwa [Function.comp_apply, affineParam_affineChart hy]
    filter_upwards [hc.preimage_mem_nhds ((isOpen_affineOpen j).mem_nhds hmem)] with t ht
    simp [h, k, affineParam_affineChart (show Ψ (affineParam i t) ∈ affineOpen j from ht)]
  have h1 : HasDerivAt (k ∘ h) (deriv k (h (affineChart i y 0)) * deriv h (affineChart i y 0))
      (affineChart i y 0) := by
    refine HasDerivAt.comp _ ?_ (hh.differentiableAt hr).hasDerivAt
    rw [hhc]
    exact (hk.differentiableAt hr).hasDerivAt
  intro h0
  have h2 := h1.unique ((hasDerivAt_id _).congr_of_eventuallyEq hev)
  rw [h0, mul_zero] at h2
  exact zero_ne_one h2

end Projectivization

end
