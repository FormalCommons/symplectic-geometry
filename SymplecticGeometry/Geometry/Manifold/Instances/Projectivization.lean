/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import TauCeti.Geometry.Manifold.Instances.Projectivization

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import SymplecticGeometry.LinearAlgebra.Projectivization.Basic

/-!
# The derivatives of the charts and transition maps of projective space

Tau Ceti's `TauCeti/Geometry/Manifold/Instances/Projectivization.lean` makes
`ℙ 𝕜 (Fin (n + 1) → 𝕜)` a manifold through the standard affine charts, whose transition maps are
smooth (`Fin.contDiffOn_insertNth_one_div`). This file computes their derivatives, which are the
coordinate changes of the tangent bundle of projective space in the standard charts.

## Main results

* `Projectivization.fderiv_affineChart_comp_affineChart_symm_apply`: the derivative of the
  transition map from the chart `i` to the chart `j`, in affine coordinates.
* `Projectivization.insertNth_fderiv_affineChart_comp_affineChart_symm`: the same derivative at a
  point `x` of `U_i ∩ U_j`, in homogeneous coordinates.
* `Projectivization.contMDiffAt_affineChart_prodMap`,
  `Projectivization.bijective_mfderiv_affineChart_prodMap` and
  `Projectivization.hasMFDerivAt_comp_affineChart_prodMap`: on a product of two projective
  spaces, the product of two standard affine charts is `C^r` with bijective differential on the
  product of the affine opens, and the chain rule for a function read in it.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 0,
  §2.
-/

public section

open scoped ContDiff LinearAlgebra.Projectivization Manifold

namespace Projectivization

variable {n : ℕ} {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- **The derivative of a transition map of projective space.** Where `w = [1 : z]`, with `1` in
position `i`, has nonzero `j`-th entry, the transition map from the chart `i` to the chart `j`,
`z ↦ (w (j.succAbove k) / w j)_k`, has derivative `ζ ↦ ((u (j.succAbove k) w j -
w (j.succAbove k) u j) / (w j)²)_k` at `z`, where `u = [0 : ζ]` has `0` in position `i`. -/
theorem fderiv_affineChart_comp_affineChart_symm_apply (i j : Fin (n + 1)) {z : Fin n → 𝕜}
    (hz : Fin.insertNth (α := fun _ ↦ 𝕜) i 1 z j ≠ 0) (ζ : Fin n → 𝕜) :
    fderiv 𝕜 (affineChart j ∘ (affineChart i).symm) z ζ = fun k ↦
      (Fin.insertNth (α := fun _ ↦ 𝕜) i 0 ζ (j.succAbove k) *
          Fin.insertNth (α := fun _ ↦ 𝕜) i 1 z j -
        Fin.insertNth (α := fun _ ↦ 𝕜) i 1 z (j.succAbove k) *
          Fin.insertNth (α := fun _ ↦ 𝕜) i 0 ζ j) /
        Fin.insertNth (α := fun _ ↦ 𝕜) i 1 z j ^ 2 := by
  set V := Fin.insertNth (α := fun _ ↦ 𝕜) i 1 z
  set U := Fin.insertNth (α := fun _ ↦ 𝕜) i 0 ζ
  have hT : (affineChart j ∘ (affineChart i).symm : (Fin n → 𝕜) → Fin n → 𝕜) = fun z ↦ fun k ↦
      Fin.insertNth (α := fun _ ↦ 𝕜) i 1 z (j.succAbove k) /
        Fin.insertNth (α := fun _ ↦ 𝕜) i 1 z j := funext (affineChart_symm_trans_apply i j)
  have hopen : IsOpen {z : Fin n → 𝕜 | Fin.insertNth (α := fun _ ↦ 𝕜) i 1 z j ≠ 0} :=
    isOpen_ne_fun ((continuous_apply j).comp
      ((continuous_const (y := (1 : 𝕜))).finInsertNth (A := fun _ ↦ 𝕜) i continuous_id))
      continuous_const
  have hd : DifferentiableAt 𝕜 (affineChart j ∘ (affineChart i).symm) z := by
    rw [hT]
    exact ((Fin.contDiffOn_insertNth_one_div (r := 1) i j).contDiffAt
      (hopen.mem_nhds hz)).differentiableAt one_ne_zero
  -- Both sides are the derivative at `0` of the transition map along the line `s ↦ z + s • ζ`.
  have h₁ := hd.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : 𝕜)) (f := fun s : 𝕜 ↦ z + s • ζ)
    (((hasDerivAt_id (0 : 𝕜)).smul_const ζ).const_add z) (by simp)
  have hline (s : 𝕜) : Fin.insertNth (α := fun _ ↦ 𝕜) i 1 (z + s • ζ) = V + s • U := by
    ext l
    induction l using i.succAboveCases <;> simp [V, U]
  have h₂ : HasDerivAt ((affineChart j ∘ (affineChart i).symm) ∘ fun s : 𝕜 ↦ z + s • ζ)
      (fun k ↦ (U (j.succAbove k) * V j - V (j.succAbove k) * U j) / V j ^ 2) 0 := by
    rw [hT]
    refine hasDerivAt_pi.2 fun k ↦ ?_
    simp only [Function.comp_def, hline, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := HasDerivAt.fun_div
      (HasDerivAt.const_add (V (j.succAbove k))
        ((hasDerivAt_id (0 : 𝕜)).mul_const (U (j.succAbove k))))
      (HasDerivAt.const_add (V j) ((hasDerivAt_id (0 : 𝕜)).mul_const (U j))) (by simpa using hz)
    simpa using this
  simpa using h₁.unique h₂

/-- **The derivative of a transition map in homogeneous coordinates.** At a point `x` of
`U_i ∩ U_j`, the derivative of the transition map from the chart `i` to the chart `j` sends `ζ` to
the vector whose homogeneous form `[0 : ·]`, with `0` in position `j`, is
`(x.rep i / x.rep j) • (u - u j • v)`, where `u = [0 : ζ]` has `0` in position `i` and `v` is
the representative of `x` with `v j = 1`. -/
theorem insertNth_fderiv_affineChart_comp_affineChart_symm (i j : Fin (n + 1))
    {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)} (hi : x ∈ affineOpen i) (hj : x ∈ affineOpen j)
    (ζ : Fin n → 𝕜) :
    Fin.insertNth (α := fun _ ↦ 𝕜) j 0
        (fderiv 𝕜 (affineChart j ∘ (affineChart i).symm) (affineChart i x) ζ) =
      (x.rep i / x.rep j) • (Fin.insertNth (α := fun _ ↦ 𝕜) i 0 ζ -
        Fin.insertNth (α := fun _ ↦ 𝕜) i 0 ζ j •
          Fin.insertNth (α := fun _ ↦ 𝕜) j 1 (affineChart j x)) := by
  have hi' := (mem_affineOpen_iff i x).1 hi
  have hj' := (mem_affineOpen_iff j x).1 hj
  have hV := insertNth_one_affineChart_eq_normalizedRep i hi
  rw [normalizedRep_def, LinearMap.proj_apply] at hV
  have hz : Fin.insertNth (α := fun _ ↦ 𝕜) i 1 (affineChart i x) j ≠ 0 := by
    simp [hV, hi', hj']
  rw [fderiv_affineChart_comp_affineChart_symm_apply i j hz, hV,
    insertNth_one_affineChart_eq_normalizedRep j hj, normalizedRep_def, LinearMap.proj_apply]
  ext l
  induction l using j.succAboveCases with
  | x => simp [hj']
  | p k =>
    simp only [Fin.insertNth_apply_succAbove, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    field_simp

section Prod

variable {m : ℕ} {i : Fin (m + 1)} {j : Fin (n + 1)}
  {x : ℙ 𝕜 (Fin (m + 1) → 𝕜) × ℙ 𝕜 (Fin (n + 1) → 𝕜)}

/-- The product of the standard affine charts `i` and `j` is `C^r` at every point of the product
of the affine opens `affineOpen i` and `affineOpen j`. -/
theorem contMDiffAt_affineChart_prodMap (hi : x.1 ∈ affineOpen i) (hj : x.2 ∈ affineOpen j)
    (r : ℕ∞ω) :
    ContMDiffAt (𝓘(𝕜, Fin m → 𝕜).prod 𝓘(𝕜, Fin n → 𝕜)) 𝓘(𝕜, (Fin m → 𝕜) × (Fin n → 𝕜)) r
      (Prod.map (affineChart i) (affineChart j)) x := by
  rw [Prod.map_def]
  exact (((contMDiffOn_affineChart i r).contMDiffAt ((isOpen_affineOpen i).mem_nhds hi)).comp x
    contMDiffAt_fst).prodMk_space
    (((contMDiffOn_affineChart j r).contMDiffAt ((isOpen_affineOpen j).mem_nhds hj)).comp x
      contMDiffAt_snd)

/-- The product of the standard affine charts `i` and `j` has a bijective differential at every
point of the product of the affine opens `affineOpen i` and `affineOpen j`. -/
theorem bijective_mfderiv_affineChart_prodMap (hi : x.1 ∈ affineOpen i)
    (hj : x.2 ∈ affineOpen j) :
    Function.Bijective (mfderiv (𝓘(𝕜, Fin m → 𝕜).prod 𝓘(𝕜, Fin n → 𝕜))
      𝓘(𝕜, (Fin m → 𝕜) × (Fin n → 𝕜)) (Prod.map (affineChart i) (affineChart j)) x) := by
  -- The product of the two affine charts is a chart of the product, whose differential at a
  -- point of its source is bijective.
  set e := (affineOpenPartialHomeomorph (K := 𝕜) i).prod (affineOpenPartialHomeomorph (K := 𝕜) j)
  have he : e ∈ atlas (ModelProd (Fin m → 𝕜) (Fin n → 𝕜))
      (ℙ 𝕜 (Fin (m + 1) → 𝕜) × ℙ 𝕜 (Fin (n + 1) → 𝕜)) :=
    Set.mem_image2_of_mem (affineOpenPartialHomeomorph_mem_atlas (𝕜 := 𝕜) i)
      (affineOpenPartialHomeomorph_mem_atlas (𝕜 := 𝕜) j)
  have hxe : x ∈ e.source := by simpa [e] using ⟨hi, hj⟩
  have hfun : ⇑e = Prod.map (affineChart i) (affineChart j) := by
    ext y <;> simp [e]
  have h := (mdifferentiable_of_mem_atlas (I := 𝓘(𝕜, Fin m → 𝕜).prod 𝓘(𝕜, Fin n → 𝕜)) he
    ).mfderiv_bijective hxe
  rwa [hfun, ← modelWithCornersSelf_prod] at h

/-- **The chain rule through the product of two affine charts.** If `G` has derivative `G'` at
the affine coordinates of a point `x` of the product of the affine opens `affineOpen i` and
`affineOpen j`, then `G` read in the product of the two affine charts has derivative `G'` composed
with the differential of that product of charts at `x`. -/
theorem hasMFDerivAt_comp_affineChart_prodMap {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {G : (Fin m → 𝕜) × (Fin n → 𝕜) → F}
    {G' : (Fin m → 𝕜) × (Fin n → 𝕜) →L[𝕜] F}
    (hG : HasFDerivAt G G' (affineChart i x.1, affineChart j x.2)) (hi : x.1 ∈ affineOpen i)
    (hj : x.2 ∈ affineOpen j) :
    HasMFDerivAt (𝓘(𝕜, Fin m → 𝕜).prod 𝓘(𝕜, Fin n → 𝕜)) 𝓘(𝕜, F)
      (G ∘ Prod.map (affineChart i) (affineChart j)) x
      (G'.comp (mfderiv (𝓘(𝕜, Fin m → 𝕜).prod 𝓘(𝕜, Fin n → 𝕜))
        𝓘(𝕜, (Fin m → 𝕜) × (Fin n → 𝕜)) (Prod.map (affineChart i) (affineChart j)) x)) :=
  hG.hasMFDerivAt.comp x
    ((contMDiffAt_affineChart_prodMap hi hj 1).mdifferentiableAt one_ne_zero).hasMFDerivAt

end Prod

end Projectivization

end
