/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.Instances.Projectivization
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Biholomorphisms of the projective line in affine coordinates

A biholomorphism `Ψ` of `ℂℙ¹ = ℙ ℂ (Fin 2 → ℂ)`, read through Tau Ceti's affine charts
`Projectivization.affineChart i` at a point `y` and `affineChart j` at `Ψ y`, is a function of
one complex variable `t ↦ affineChart j (Ψ [insertNth i 1 t]) 0`. This file shows that this
function is complex analytic near `affineChart i y 0` and that its derivative there does not
vanish: the inverse `Ψ.symm`, read in the same charts the other way round, is a left inverse
near that point, and the chain rule gives the product of the two derivatives as `1`.

## Main results

* `Projectivization.contDiffAt_affineChart_diffeomorph_affineChart_symm`: the coordinate
  expression is analytic (`ContDiffAt ℂ ω`).
* `Projectivization.deriv_affineChart_diffeomorph_affineChart_symm_ne_zero`: its derivative does
  not vanish.
-/

public section

open Filter Set
open scoped ContDiff Manifold Topology LinearAlgebra.Projectivization

namespace Projectivization

variable (Ψ : ℙ ℂ (Fin 2 → ℂ) ≃ₘ^ω⟮𝓘(ℂ, Fin 1 → ℂ), 𝓘(ℂ, Fin 1 → ℂ)⟯ ℙ ℂ (Fin 2 → ℂ))
  {i j : Fin 2} {y : ℙ ℂ (Fin 2 → ℂ)}

/-- A biholomorphism `Ψ` of `ℂℙ¹`, read in the affine chart `i` at `y` and the affine chart `j`
at `Ψ y`, is complex analytic near the coordinate of `y`. -/
theorem contDiffAt_affineChart_diffeomorph_affineChart_symm (hy : y ∈ affineOpen i)
    (hΨy : Ψ y ∈ affineOpen j) :
    ContDiffAt ℂ ω (fun t : ℂ ↦ affineChart j (Ψ ((affineChart i).symm fun _ ↦ t)) 0)
      (affineChart i y 0) := by
  have hy' : (affineChart i).symm (affineChart (K := ℂ) i y) = y :=
    (affineChart i).left_inv (by rwa [affineChart_source])
  have hT : ContMDiffAt 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, Fin 1 → ℂ) ω
      (affineChart j ∘ Ψ ∘ (affineChart i).symm) (affineChart i y) := by
    refine ContMDiffAt.comp _ ?_ (Ψ.contMDiff.contMDiffAt.comp _
      (contMDiff_affineChart_symm i ω).contMDiffAt)
    rw [Function.comp_apply, hy']
    exact (contMDiffOn_affineChart j ω).contMDiffAt ((isOpen_affineOpen j).mem_nhds hΨy)
  have hin : ContDiff ℂ ω (fun t : ℂ ↦ fun _ : Fin 1 ↦ t) := contDiff_pi.2 fun _ ↦ contDiff_id
  -- The point `affineChart i y` of `Fin 1 → ℂ` is the constant function of its coordinate.
  have hT' : ContDiffAt ℂ ω (affineChart j ∘ Ψ ∘ (affineChart i).symm)
      ((fun t : ℂ ↦ fun _ : Fin 1 ↦ t) (affineChart i y 0)) := by
    have hfin (w : Fin 1 → ℂ) : (fun _ ↦ w 0) = w := (eq_const_of_subsingleton w 0).symm
    simpa only [hfin] using
      contMDiffAt_iff_contDiffAt.1 hT
  have h3 := hT'.comp (affineChart i y 0) hin.contDiffAt
  exact (contDiff_apply (𝕜 := ℂ) (F' := fun _ : Fin 1 ↦ ℂ) 0).comp_contDiffAt _ h3

/-- A biholomorphism `Ψ` of `ℂℙ¹`, read in the affine chart `i` at `y` and the affine chart `j`
at `Ψ y`, has nonzero derivative at the coordinate of `y`. -/
theorem deriv_affineChart_diffeomorph_affineChart_symm_ne_zero (hy : y ∈ affineOpen i)
    (hΨy : Ψ y ∈ affineOpen j) :
    deriv (fun t : ℂ ↦ affineChart j (Ψ ((affineChart i).symm fun _ ↦ t)) 0)
      (affineChart i y 0) ≠ 0 := by
  set h := fun t : ℂ ↦ affineChart j (Ψ ((affineChart i).symm fun _ ↦ t)) 0
  set k := fun s : ℂ ↦ affineChart i (Ψ.symm ((affineChart j).symm fun _ ↦ s)) 0
  have hfin (w : Fin 1 → ℂ) : (fun _ ↦ w 0) = w := (eq_const_of_subsingleton w 0).symm
  have hy' : (affineChart i).symm (affineChart (K := ℂ) i y) = y :=
    (affineChart i).left_inv (by rwa [affineChart_source])
  have hhc : h (affineChart i y 0) = affineChart j (Ψ y) 0 := by
    simp only [h, hfin, hy']
  have hk := contDiffAt_affineChart_diffeomorph_affineChart_symm Ψ.symm (i := j) (j := i)
    (y := Ψ y) hΨy (by rwa [Diffeomorph.symm_apply_apply])
  have hh := contDiffAt_affineChart_diffeomorph_affineChart_symm Ψ hy hΨy
  -- `k` is a left inverse of `h` near `affineChart i y 0`.
  have hev : k ∘ h =ᶠ[𝓝 (affineChart i y 0)] id := by
    have hc : ContinuousAt (fun t : ℂ ↦ Ψ ((affineChart i).symm fun _ ↦ t))
        (affineChart i y 0) :=
      Ψ.continuous.continuousAt.comp ((continuous_affineChart_symm i).continuousAt.comp
        (continuous_pi fun _ ↦ continuous_id).continuousAt)
    have hmem : Ψ ((affineChart i).symm fun _ ↦ affineChart (K := ℂ) i y 0) ∈ affineOpen j := by
      rwa [hfin, hy']
    filter_upwards [hc ((isOpen_affineOpen j).mem_nhds hmem)] with t ht
    simp only [Function.comp_apply, h, k, hfin]
    rw [(affineChart j).left_inv (by rwa [affineChart_source]), Diffeomorph.symm_apply_apply,
      (affineChart i).right_inv (by simp), id_eq]
  have h1 : HasDerivAt (k ∘ h) (deriv k (h (affineChart i y 0)) * deriv h (affineChart i y 0))
      (affineChart i y 0) := by
    refine HasDerivAt.comp _ ?_ (hh.differentiableAt (by simp)).hasDerivAt
    rw [hhc]
    exact (hk.differentiableAt (by simp)).hasDerivAt
  intro h0
  have h2 := h1.unique ((hasDerivAt_id _).congr_of_eventuallyEq hev)
  rw [h0, mul_zero] at h2
  exact zero_ne_one h2

end Projectivization

end
