/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.UnitInterval
public import TauCeti.Analysis.Matrix.ContinuousBilinearForm
public import TauCeti.Analysis.Matrix.HermitianSignature.Matrix
public import TauCeti.LinearAlgebra.QuadraticForm.Isometry
public import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Action
import TauCeti.Analysis.Matrix.HermitianSignature.Crossing
import SymplecticGeometry.Analysis.Calculus.Deriv.Matrix
import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Transverse
import SymplecticGeometry.Analysis.Matrix.EuclideanLin
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Matrix
import SymplecticGeometry.LinearAlgebra.Symplectic.Subspace

/-!
# Crossing forms of Lagrangian frames

Let `t ↦ Z t` be a frame of a path of Lagrangian subspaces of `(StdSpace ι, ω₀)`: real
`2n × n` matrices whose columns span `Λ t`. Robbin and Salamon's crossing form of the path at `t`,
relative to a subspace `V`, is the quadratic form `u ↦ ω₀(Z t u, Z' u)` for a derivative `Z'` of
`Z` at `t`, read on the vectors `u` with `Z t u ∈ V`, that is, on `Λ t ∩ V` in the coordinates of
the frame. This file defines it for single matrices and proves the facts about it that the
crossing-form formula for the Maslov index needs.

## Main definitions

* `SymplecticGeometry.lagrangianCrossingForm Z Z' V`: the quadratic form
  `u ↦ ω₀(Z u, Z' u)` on `V.comap (toEuclideanLin Z)`; it is homogeneous in `Z'`
  (`lagrangianCrossingForm_smul`) and vanishes where the image of `Z` meets `V` only in `0`
  (`lagrangianCrossingForm_eq_zero_of_inf_eq_bot`).

## Main results

* `SymplecticGeometry.lagrangianCrossingForm_vertical`: relative to the vertical Lagrangian
  `{x = 0}`, the form of the frame `fromRows X Y` is `u ↦ -⟪Y u, X' u⟫`.
* `SymplecticGeometry.lagrangianCrossingForm_graph`: for the frame `fromRows 1 A` of the graph of
  `A`, relative to the horizontal Lagrangian `{y = 0}`, it is Tau Ceti's `Matrix.crossingForm`.
* `SymplecticGeometry.stdForm_toEuclideanLin_comm_of_hasDerivWithinAt`: for a differentiable
  frame of isotropic subspaces, `(u, v) ↦ ω₀(Z t u, Z' v)` is symmetric, so it is the symmetric
  bilinear form of the crossing form.
* `SymplecticGeometry.lagrangianCrossingForm_mul_apply`, `lagrangianCrossingForm_mul_equivalent`:
  the form does not depend on the frame: under a change of frame `Z ↦ Z * g`, with derivative
  `Z' * g + Z * h`, it is the same form read in new coordinates.
* `SymplecticGeometry.lagrangianCrossingForm_symplectic_mul_apply`,
  `lagrangianCrossingForm_symplectic_mul_equivalent`: naturality under symplectic matrices.
* `SymplecticGeometry.LagrangianGrassmannian.eventually_not_crossing_of_regular`: a crossing with
  nondegenerate crossing form is isolated, for a family on `[0, 1]`;
  `eventually_nhdsNE_not_crossing_of_regular` is the same for a family on `ℝ`, and
  `eventually_nhdsLT_not_crossing_of_regular`, `eventually_nhdsGT_not_crossing_of_regular` its
  one-sided forms.

## Implementation notes

The isolation of regular crossings is reduced to Tau Ceti's theorem for paths of symmetric
bilinear forms. Given a Lagrangian `W` transverse to `V` and to `Λ t₀`, with `P` the projection
onto `V` along `W`, the bilinear forms `(u, v) ↦ ω₀(P (Z t u), Z t v)` are symmetric, are
nondegenerate only where `Λ t ∩ V = 0`, and at `t₀` have the crossing form of the frame as
their crossing form.

## References

* [J. Robbin and D. Salamon, *The Maslov index for paths*][RobbinSalamon1993], §2.
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3.
-/

public section

namespace SymplecticGeometry

open Matrix TauCeti Set Filter Topology
open scoped unitInterval

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "ℒ" ι => LagrangianGrassmannian (stdForm ι)

/-! ### The crossing form -/

/-- The **crossing form** of a frame `Z` and a matrix `Z'` relative to a subspace `V`: the
quadratic form `u ↦ ω₀(Z u, Z' u)` on the vectors `u` with `Z u ∈ V`. For a frame `Z t` of a path
of Lagrangians `Λ t` with derivative `Z'`, this is Robbin and Salamon's crossing form on
`Λ t ∩ V`, read in the coordinates of the frame; for `Z = fromRows X Y` and `Z' = fromRows X' Y'`
it is `u ↦ ⟪X u, Y' u⟫ - ⟪Y u, X' u⟫`. -/
noncomputable def lagrangianCrossingForm (Z Z' : Matrix (ι ⊕ ι) ι ℝ)
    (V : Submodule ℝ (StdSpace ι)) : QuadraticForm ℝ (V.comap (toEuclideanLin Z)) :=
  (LinearMap.BilinMap.toQuadraticMap
    ((stdForm ι).toBilinForm.compl₁₂ (toEuclideanLin Z) (toEuclideanLin Z'))).restrict
    (V.comap (toEuclideanLin Z))

theorem lagrangianCrossingForm_def (Z Z' : Matrix (ι ⊕ ι) ι ℝ) (V : Submodule ℝ (StdSpace ι)) :
    lagrangianCrossingForm Z Z' V =
      (LinearMap.BilinMap.toQuadraticMap
        ((stdForm ι).toBilinForm.compl₁₂ (toEuclideanLin Z) (toEuclideanLin Z'))).restrict
        (V.comap (toEuclideanLin Z)) :=
  (rfl)

@[simp]
theorem lagrangianCrossingForm_apply (Z Z' : Matrix (ι ⊕ ι) ι ℝ) (V : Submodule ℝ (StdSpace ι))
    (u : V.comap (toEuclideanLin Z)) :
    lagrangianCrossingForm Z Z' V u =
      stdForm ι (toEuclideanLin Z (u : EuclideanSpace ℝ ι)) (toEuclideanLin Z' u) := by
  simp [lagrangianCrossingForm_def]

/-- The crossing form is linear in the derivative: scaling `Z'` by `c` scales the form by `c`. -/
theorem lagrangianCrossingForm_smul (Z Z' : Matrix (ι ⊕ ι) ι ℝ) (c : ℝ)
    (V : Submodule ℝ (StdSpace ι)) :
    lagrangianCrossingForm Z (c • Z') V = c • lagrangianCrossingForm Z Z' V := by
  ext u
  simp

/-- Scaling the derivative by a nonzero constant does not change whether the crossing form is
nondegenerate. -/
theorem nondegenerate_lagrangianCrossingForm_smul_iff (Z Z' : Matrix (ι ⊕ ι) ι ℝ) {c : ℝ}
    (hc : c ≠ 0) (V : Submodule ℝ (StdSpace ι)) :
    (lagrangianCrossingForm Z (c • Z') V).Nondegenerate ↔
      (lagrangianCrossingForm Z Z' V).Nondegenerate := by
  rw [lagrangianCrossingForm_smul, QuadraticMap.nondegenerate_smul_iff (isUnit_iff_ne_zero.2 hc)]

/-- Away from a crossing, where the image of `Z` meets `V` only in `0`, the crossing form is
zero: its vectors `u` have `Z u = 0`. -/
theorem lagrangianCrossingForm_eq_zero_of_inf_eq_bot {Z : Matrix (ι ⊕ ι) ι ℝ}
    {V : Submodule ℝ (StdSpace ι)} (h : LinearMap.range (toEuclideanLin Z) ⊓ V = ⊥)
    (Z' : Matrix (ι ⊕ ι) ι ℝ) : lagrangianCrossingForm Z Z' V = 0 := by
  ext u
  have hu : toEuclideanLin Z (u : EuclideanSpace ℝ ι) = 0 :=
    (Submodule.mem_bot ℝ).1 (h ▸ ⟨⟨_, rfl⟩, u.property⟩)
  simp [hu]

/-- Relative to the vertical Lagrangian `{x = 0}`, where `X u = 0`, the crossing form of the
frame `fromRows X Y` and of `fromRows X' Y'` is `u ↦ -⟪Y u, X' u⟫`. -/
theorem lagrangianCrossingForm_vertical (X Y X' Y' : Matrix ι ι ℝ)
    (u : (LagrangianGrassmannian.vertical ι : Submodule ℝ (StdSpace ι)).comap
      (toEuclideanLin (fromRows X Y))) :
    lagrangianCrossingForm (fromRows X Y) (fromRows X' Y') (LagrangianGrassmannian.vertical ι) u =
      -((Y *ᵥ (u : EuclideanSpace ℝ ι).ofLp) ⬝ᵥ (X' *ᵥ (u : EuclideanSpace ℝ ι).ofLp)) := by
  have hX : X *ᵥ (u : EuclideanSpace ℝ ι).ofLp = 0 := by
    have hu := LagrangianGrassmannian.mem_vertical_iff.1
      (LagrangianGrassmannian.mem_toSubmodule.1 u.property)
    rwa [StdSpace.x_toEuclideanLin_fromRows] at hu
  have hx (i : ι) : (X *ᵥ (u : EuclideanSpace ℝ ι).ofLp) i = 0 := by rw [hX, Pi.zero_apply]
  simp only [lagrangianCrossingForm_apply, stdForm_apply, StdSpace.x_apply, StdSpace.y_apply]
  simp [toLpLin_apply, fromRows_mulVec, hx, dotProduct]

/-- For the frame `fromRows 1 A` of the graph `{(x, A x)}` and any `fromRows X' A'`, the crossing
form relative to the horizontal Lagrangian `{y = 0}` is Tau Ceti's crossing form
`x ↦ x ⬝ᵥ A' *ᵥ x` on the kernel of `A`. -/
theorem lagrangianCrossingForm_graph (A X' A' : Matrix ι ι ℝ) :
    (lagrangianCrossingForm (fromRows 1 A) (fromRows X' A')
      (LagrangianGrassmannian.horizontal ι)).Equivalent (A.crossingForm A') := by
  have hmem (u : EuclideanSpace ℝ ι) :
      u ∈ (LagrangianGrassmannian.horizontal ι : Submodule ℝ (StdSpace ι)).comap
        (toEuclideanLin (fromRows 1 A)) ↔ A *ᵥ u.ofLp = 0 := by
    rw [Submodule.mem_comap, LagrangianGrassmannian.coe_horizontal, LinearMap.mem_ker,
      StdSpace.y_toEuclideanLin_fromRows]
  have hmap : ((LagrangianGrassmannian.horizontal ι : Submodule ℝ (StdSpace ι)).comap
      (toEuclideanLin (fromRows 1 A))).map (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toLinearMap =
        LinearMap.ker A.mulVecLin := by
    ext x
    rw [Submodule.mem_map_equiv, hmem]
    simp
  refine ⟨⟨LinearEquiv.ofSubmodules _ _ _ hmap, fun u ↦ ?_⟩⟩
  have hu : A *ᵥ (u : EuclideanSpace ℝ ι).ofLp = 0 := (hmem _).1 u.property
  have hu' (i : ι) : (A *ᵥ (u : EuclideanSpace ℝ ι).ofLp) i = 0 := by rw [hu, Pi.zero_apply]
  simp only [crossingForm_apply, lagrangianCrossingForm_apply,
    stdForm_apply, StdSpace.x_apply, StdSpace.y_apply]
  simp [toLpLin_apply, fromRows_mulVec, hu', dotProduct]

/-! ### Symmetry -/

/-- **Symmetry of the crossing form.** Let `Z` be a path of matrices whose images are isotropic
on a set `s`, with derivative `Z'` within `s` at a point `t ∈ s` of unique differentiability.
Then `(u, v) ↦ ω₀(Z t u, Z' v)` is symmetric: it is the symmetric bilinear form whose quadratic
form is the crossing form (`QuadraticMap.associated`), and half of its `QuadraticMap.polar`. -/
theorem stdForm_toEuclideanLin_comm_of_hasDerivWithinAt {Z : ℝ → Matrix (ι ⊕ ι) ι ℝ}
    {Z' : Matrix (ι ⊕ ι) ι ℝ} {s : Set ℝ} {t : ℝ}
    (hZ : ∀ r ∈ s, (stdForm ι).IsIsotropic (LinearMap.range (toEuclideanLin (Z r))))
    (hd : HasDerivWithinAt Z Z' s t) (ht : t ∈ s) (hs : UniqueDiffWithinAt ℝ s t)
    (u v : EuclideanSpace ℝ ι) :
    stdForm ι (toEuclideanLin (Z t) u) (toEuclideanLin Z' v) =
      stdForm ι (toEuclideanLin (Z t) v) (toEuclideanLin Z' u) := by
  -- The Gram matrices of `ω₀` on the columns of `Z r` vanish on `s`, so their derivative does.
  have h0 : ∀ r ∈ s, (Z r)ᵀ * -J ι ℝ * Z r = 0 := by
    intro r hr
    refine (Matrix.toLinearMap₂' ℝ (N₂ := ℝ) (S₁ := ℝ) (S₂ := ℝ)).injective
      (LinearMap.ext₂ fun a b ↦ ?_)
    rw [Matrix.toLinearMap₂'_apply', map_zero, LinearMap.zero_apply, LinearMap.zero_apply,
      ← WithLp.ofLp_toLp 2 a, ← WithLp.ofLp_toLp 2 b, ← stdForm_toEuclideanLin_toEuclideanLin]
    exact SymplecticForm.isIsotropic_iff.1 (hZ r hr) _ ⟨_, rfl⟩ _ ⟨_, rfl⟩
  have hM : HasDerivWithinAt (fun r ↦ (Z r)ᵀ * -J ι ℝ * Z r)
      (Z'ᵀ * -J ι ℝ * Z t + (Z t)ᵀ * -J ι ℝ * Z') s t := by
    convert (hd.matrix_transpose.matrix_mul (hasDerivWithinAt_matrix_const _ s t)).matrix_mul hd
      using 1
    simp
  -- `UniqueDiffWithinAt.eq_deriv` reads matrices as functions `ι → ι → ℝ`.
  have hzero : Z'ᵀ * -J ι ℝ * Z t + (Z t)ᵀ * -J ι ℝ * Z' = 0 :=
    hs.eq_deriv (F := ι → ι → ℝ) _ hM
      ((hasDerivWithinAt_const t s (0 : ι → ι → ℝ)).congr h0 (h0 t ht))
  have key := congrArg (fun M : Matrix ι ι ℝ ↦ u.ofLp ⬝ᵥ (M *ᵥ v.ofLp)) hzero
  simp only [add_mulVec, dotProduct_add, zero_mulVec, dotProduct_zero] at key
  rw [← stdForm_toEuclideanLin_toEuclideanLin, ← stdForm_toEuclideanLin_toEuclideanLin] at key
  have h := (stdForm ι).neg_eq (toEuclideanLin Z' u) (toEuclideanLin (Z t) v)
  simp only at key h ⊢
  linarith

/-! ### Change of frame and naturality -/

/-- **Frame independence of the crossing form.** For a frame `Z` with isotropic image, the
crossing form of `Z * g` and `Z' * g + Z * h`, the frame and derivative after a change of frame
by `g` with derivative `h`, takes at `w` the value of the crossing form of `Z` and `Z'` at the
coordinates `g w` of the same vector `Z (g w)` in the old frame. -/
theorem lagrangianCrossingForm_mul_apply {Z : Matrix (ι ⊕ ι) ι ℝ}
    (hZ : (stdForm ι).IsIsotropic (LinearMap.range (toEuclideanLin Z)))
    (Z' : Matrix (ι ⊕ ι) ι ℝ) (V : Submodule ℝ (StdSpace ι)) (g h : Matrix ι ι ℝ)
    (w : V.comap (toEuclideanLin (Z * g))) :
    lagrangianCrossingForm (Z * g) (Z' * g + Z * h) V w =
      lagrangianCrossingForm Z Z' V ⟨toEuclideanLin g w, by
        simpa [toLpLin_mul_same] using w.property⟩ := by
  simp only [lagrangianCrossingForm_apply, toLpLin_mul_same, map_add, LinearMap.add_apply,
    LinearMap.comp_apply]
  have h0 := SymplecticForm.isIsotropic_iff.1 hZ _ ⟨toEuclideanLin g w, rfl⟩ _
    ⟨toEuclideanLin h w, rfl⟩
  simp only at h0
  rw [h0, add_zero]

/-- **Frame independence of the crossing form**, up to isometry: for an invertible `g`, the
crossing forms of `Z`, `Z'` and of `Z * g`, `Z' * g + Z * h` are equivalent. -/
theorem lagrangianCrossingForm_mul_equivalent {Z : Matrix (ι ⊕ ι) ι ℝ}
    (hZ : (stdForm ι).IsIsotropic (LinearMap.range (toEuclideanLin Z)))
    (Z' : Matrix (ι ⊕ ι) ι ℝ) (V : Submodule ℝ (StdSpace ι)) (g : GL ι ℝ) (h : Matrix ι ι ℝ) :
    (lagrangianCrossingForm Z Z' V).Equivalent
      (lagrangianCrossingForm (Z * (g : Matrix ι ι ℝ)) (Z' * (g : Matrix ι ι ℝ) + Z * h)
        V) := by
  let e := ((g : Matrix ι ι ℝ).toEuclideanCLE g.det_ne_zero).symm.toLinearEquiv
  have hmap : (V.comap (toEuclideanLin Z)).map (e : EuclideanSpace ℝ ι →ₗ[ℝ] _) =
      V.comap (toEuclideanLin (Z * (g : Matrix ι ι ℝ))) := by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext w
    simp [e, toLpLin_mul_same]
  refine ⟨⟨LinearEquiv.ofSubmodules e _ _ hmap, fun u ↦ ?_⟩⟩
  have hu := ContinuousLinearEquiv.apply_symm_apply
    ((g : Matrix ι ι ℝ).toEuclideanCLE g.det_ne_zero) (u : EuclideanSpace ℝ ι)
  rw [toEuclideanCLE_apply] at hu
  rw [lagrangianCrossingForm_mul_apply hZ]
  congr 1
  exact Subtype.ext hu
/-- **Naturality of the crossing form.** A symplectic matrix `Ψ` carries the crossing form of `Z`
and `Z'` relative to `V` to that of `Ψ * Z` and `Ψ * Z'` relative to `Ψ V`, on the same vectors
`u`. -/
theorem lagrangianCrossingForm_symplectic_mul_apply {Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ}
    (hΨ : Ψ ∈ symplecticGroup ι ℝ) (Z Z' : Matrix (ι ⊕ ι) ι ℝ) (V : Submodule ℝ (StdSpace ι))
    {u : EuclideanSpace ℝ ι} (hu : toEuclideanLin Z u ∈ V) :
    lagrangianCrossingForm (Ψ * Z) (Ψ * Z') (V.map (toEuclideanLin Ψ)) ⟨u, by
        rw [Submodule.mem_comap, toLpLin_mul_same, LinearMap.comp_apply]
        exact Submodule.mem_map_of_mem hu⟩ =
      lagrangianCrossingForm Z Z' V ⟨u, hu⟩ := by
  simp only [lagrangianCrossingForm_apply, toLpLin_mul_same, LinearMap.comp_apply]
  exact mem_symplecticGroup_iff_forall_stdForm.1 hΨ _ _

/-- **Naturality of the crossing form**, up to isometry: for a symplectic matrix `Ψ`, the
crossing forms of `Z`, `Z'` relative to `V` and of `Ψ * Z`, `Ψ * Z'` relative to `Ψ V` are
equivalent. -/
theorem lagrangianCrossingForm_symplectic_mul_equivalent {Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ}
    (hΨ : Ψ ∈ symplecticGroup ι ℝ) (Z Z' : Matrix (ι ⊕ ι) ι ℝ) (V : Submodule ℝ (StdSpace ι)) :
    (lagrangianCrossingForm Z Z' V).Equivalent
      (lagrangianCrossingForm (Ψ * Z) (Ψ * Z') (V.map (toEuclideanLin Ψ))) := by
  have hinj : Function.Injective (toEuclideanLin Ψ) := fun a b hab ↦
    (Ψ.toEuclideanCLE (SymplecticGroup.symplectic_det hΨ).ne_zero).injective (by simpa using hab)
  have hdom : V.comap (toEuclideanLin Z) =
      (V.map (toEuclideanLin Ψ)).comap (toEuclideanLin (Ψ * Z)) := by
    rw [toLpLin_mul_same, Submodule.comap_comp,
      Submodule.comap_map_eq_of_injective hinj]
  refine ⟨⟨LinearEquiv.ofEq _ _ hdom, fun u ↦ ?_⟩⟩
  exact lagrangianCrossingForm_symplectic_mul_apply hΨ Z Z' V u.property

/-! ### Regular crossings are isolated -/

section Isolated

variable {V W : Submodule ℝ (StdSpace ι)}

/-- The matrix of the bilinear form `(u, v) ↦ ω₀(P (Z₁ u), Z₂ v)`. -/
private noncomputable def projForm (P : StdSpace ι →ₗ[ℝ] StdSpace ι)
    (Z₁ Z₂ : Matrix (ι ⊕ ι) ι ℝ) : Matrix ι ι ℝ :=
  ((toEuclideanLin (𝕜 := ℝ) (m := ι ⊕ ι) (n := ι ⊕ ι)).symm P * Z₁)ᵀ * -J ι ℝ * Z₂

private theorem dotProduct_projForm_mulVec (P : StdSpace ι →ₗ[ℝ] StdSpace ι)
    (Z₁ Z₂ : Matrix (ι ⊕ ι) ι ℝ) (u v : ι → ℝ) :
    u ⬝ᵥ (projForm P Z₁ Z₂ *ᵥ v) =
      stdForm ι (P (toEuclideanLin Z₁ (WithLp.toLp 2 u)))
        (toEuclideanLin Z₂ (WithLp.toLp 2 v)) := by
  have hP : toEuclideanLin ((toEuclideanLin (𝕜 := ℝ) (m := ι ⊕ ι) (n := ι ⊕ ι)).symm P) = P :=
    LinearEquiv.apply_symm_apply _ _
  have h := stdForm_toEuclideanLin_toEuclideanLin
    ((toEuclideanLin (𝕜 := ℝ) (m := ι ⊕ ι) (n := ι ⊕ ι)).symm P * Z₁) Z₂ (WithLp.toLp 2 u)
    (WithLp.toLp 2 v)
  rw [toLpLin_mul_same, LinearMap.comp_apply, hP] at h
  exact h.symm

private theorem projForm_apply (P : StdSpace ι →ₗ[ℝ] StdSpace ι) (Z₁ Z₂ : Matrix (ι ⊕ ι) ι ℝ)
    (u v : ι → ℝ) :
    (projForm P Z₁ Z₂).toContinuousLinearMap₂' u v =
      stdForm ι (P (toEuclideanLin Z₁ (WithLp.toLp 2 u)))
        (toEuclideanLin Z₂ (WithLp.toLp 2 v)) := by
  rw [toContinuousLinearMap₂'_apply, dotProduct_projForm_mulVec]

/-- The derivative of `r ↦ (u, v) ↦ ω₀(P (Z r u), Z r v)`, as matrices. -/
private theorem hasDerivWithinAt_projForm (P : StdSpace ι →ₗ[ℝ] StdSpace ι)
    {Z : ℝ → Matrix (ι ⊕ ι) ι ℝ} {Z' : Matrix (ι ⊕ ι) ι ℝ} {s : Set ℝ} {t : ℝ}
    (hd : HasDerivWithinAt Z Z' s t) :
    HasDerivWithinAt (fun r ↦ projForm P (Z r) (Z r))
      (projForm P Z' (Z t) + projForm P (Z t) Z') s t := by
  have hc (C : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) := hasDerivWithinAt_matrix_const C s t
  convert (((hc (toEuclideanLin.symm P)).matrix_mul hd).matrix_transpose.matrix_mul
    (hc (-J ι ℝ))).matrix_mul hd using 1 <;>
  simp [projForm]

/-- The form `(u, v) ↦ ω₀(P (Z u), Z v)`, for the projection `P` onto an isotropic `V` along an
isotropic `W`, is symmetric when `Z` has isotropic image. -/
private theorem isSymm_projForm (hV : (stdForm ι).IsIsotropic V)
    (hW : (stdForm ι).IsIsotropic W) (hVW : IsCompl V W) {Z : Matrix (ι ⊕ ι) ι ℝ}
    (hZ : (stdForm ι).IsIsotropic (LinearMap.range (toEuclideanLin Z))) :
    (projForm (V.projection W hVW) Z Z).toContinuousLinearMap₂'.toBilinForm.IsSymm := by
  refine ⟨fun a b ↦ ?_⟩
  simp only [ContinuousLinearMap.toBilinForm_apply, projForm_apply]
  set x := toEuclideanLin Z (WithLp.toLp 2 a)
  set y := toEuclideanLin Z (WithLp.toLp 2 b)
  have hxW : x - V.projection W hVW x ∈ W := by
    rw [← Submodule.projection_eq_self_sub_projection]; exact Submodule.projection_apply_mem _ _
  have hyW : y - V.projection W hVW y ∈ W := by
    rw [← Submodule.projection_eq_self_sub_projection]; exact Submodule.projection_apply_mem _ _
  have h₁ := SymplecticForm.isIsotropic_iff.1 hW _ hxW _ hyW
  have h₂ := SymplecticForm.isIsotropic_iff.1 hV _ (Submodule.projection_apply_mem hVW x) _
    (Submodule.projection_apply_mem hVW y)
  have h₃ := SymplecticForm.isIsotropic_iff.1 hZ x ⟨_, rfl⟩ y ⟨_, rfl⟩
  have h₄ := (stdForm ι).neg_eq x (V.projection W hVW y)
  simp only [map_sub, LinearMap.sub_apply] at h₁
  linarith

/-- Where the form `(u, v) ↦ ω₀(P (Z u), Z v)` is nondegenerate, the image of `Z` meets `V` only
in `0`. -/
private theorem inf_eq_bot_of_nondegenerate (hVW : IsCompl V W) {Z : Matrix (ι ⊕ ι) ι ℝ}
    (hZ : (stdForm ι).IsIsotropic (LinearMap.range (toEuclideanLin Z)))
    (h : (projForm (V.projection W hVW) Z Z).toContinuousLinearMap₂'.toBilinForm.Nondegenerate) :
    LinearMap.range (toEuclideanLin Z) ⊓ V = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro _ ⟨⟨u, rfl⟩, hu⟩
  have h0 : u.ofLp = 0 := h.1 u.ofLp fun v ↦ by
    rw [ContinuousLinearMap.toBilinForm_apply, projForm_apply, WithLp.toLp_ofLp,
      Submodule.projection_apply_of_mem_left hVW hu]
    exact SymplecticForm.isIsotropic_iff.1 hZ _ ⟨_, rfl⟩ _ ⟨_, rfl⟩
  rw [show u = 0 from (WithLp.ofLp_injective 2).eq_iff.1 (by simpa using h0), map_zero]

/-- At a Lagrangian `Λ = range Z` transverse to `W`, the crossing form of the forms
`(u, v) ↦ ω₀(P (Z t u), Z t v)` at `t` is isometric to the crossing form of the frame. -/
private noncomputable def lagrangianCrossingFormIsometryEquivProjForm
    (hV : (stdForm ι).IsIsotropic V)
    (hVW : IsCompl V W) {Z : Matrix (ι ⊕ ι) ι ℝ}
    (hZ : (stdForm ι).IsLagrangian (LinearMap.range (toEuclideanLin Z)))
    (hWZ : Disjoint W (LinearMap.range (toEuclideanLin Z))) (Z' : Matrix (ι ⊕ ι) ι ℝ) :
    (lagrangianCrossingForm Z Z' V).IsometryEquiv
      (ContinuousLinearMap.crossingForm
        (projForm (V.projection W hVW) Z Z).toContinuousLinearMap₂'
        (projForm (V.projection W hVW) Z' Z +
          projForm (V.projection W hVW) Z Z').toContinuousLinearMap₂') := by
  set P := V.projection W hVW
  have hiso := hZ.isIsotropic
  have hker : (V.comap (toEuclideanLin Z)).map (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toLinearMap =
      (projForm P Z Z).toContinuousLinearMap₂'.ker := by
    ext a
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, LinearMap.mem_ker]
    rw [WithLp.coe_symm_linearEquiv]
    set x := toEuclideanLin Z (WithLp.toLp 2 a)
    constructor
    · intro ha
      refine ContinuousLinearMap.ext fun b ↦ ?_
      rw [ContinuousLinearMap.coe_coe, projForm_apply,
        Submodule.projection_apply_of_mem_left hVW ha]
      exact SymplecticForm.isIsotropic_iff.1 hiso _ ⟨_, rfl⟩ _ ⟨_, rfl⟩
    · intro ha
      -- `P x` is `ω₀`-orthogonal to the Lagrangian `range Z`, hence lies in it.
      have hPx : P x ∈ LinearMap.range (toEuclideanLin Z) := by
        rw [← hZ.orthogonal_eq, SymplecticForm.mem_orthogonal_iff]
        rintro _ ⟨b, rfl⟩
        have hb : stdForm ι (P x) (toEuclideanLin Z b) = 0 := by
          have hb := congrArg (fun f ↦ f b.ofLp) ha
          simpa only [ContinuousLinearMap.coe_coe, projForm_apply, WithLp.toLp_ofLp,
            zero_apply] using hb
        rw [← (stdForm ι).neg_eq]
        exact neg_eq_zero.2 hb
      -- so `x - P x` lies in `W ⊓ range Z = 0`.
      have hxW : x - P x ∈ W := by
        rw [← Submodule.projection_eq_self_sub_projection]; exact Submodule.projection_apply_mem _ _
      have hx : x - P x = 0 :=
        (Submodule.disjoint_def.1 hWZ) _ hxW (Submodule.sub_mem _ ⟨_, rfl⟩ hPx)
      rw [sub_eq_zero.1 hx]
      exact Submodule.projection_apply_mem _ _
  refine ⟨LinearEquiv.ofSubmodules _ _ _ hker, fun u ↦ ?_⟩
  have hu : toEuclideanLin Z (u : EuclideanSpace ℝ ι) ∈ V := u.property
  simp only [LinearMap.toFun_eq_coe, LinearEquiv.coe_coe, LinearEquiv.ofSubmodules_apply,
    ContinuousLinearMap.crossingForm_apply,
    toContinuousLinearMap₂'_apply, add_mulVec, dotProduct_add, dotProduct_projForm_mulVec,
    WithLp.coe_linearEquiv, WithLp.toLp_ofLp, lagrangianCrossingForm_apply]
  have h1 : P (toEuclideanLin Z (u : EuclideanSpace ℝ ι)) = toEuclideanLin Z u :=
    Submodule.projection_apply_of_mem_left hVW hu
  have h0 := SymplecticForm.isIsotropic_iff.1 hV _
    (Submodule.projection_apply_mem hVW (toEuclideanLin Z' (u : EuclideanSpace ℝ ι))) _ hu
  simp only at h0
  rw [h1, h0, zero_add]

/-- The setup for the isolation of a regular crossing at a frame `Z₀` of a Lagrangian `Λ₀`: a
Lagrangian `W` transverse to `V` and to `Λ₀` such that, for the projection `P` onto `V` along `W`,
the crossing form of the forms `(u, v) ↦ ω₀(P (Z u), Z v)` at `Z₀`, with derivative `Z'`, is
nondegenerate. -/
private theorem exists_projForm_crossingForm_nondegenerate (V : ℒ ι) {Λ₀ : ℒ ι}
    {Z₀ Z' : Matrix (ι ⊕ ι) ι ℝ} (hZ₀ : LinearMap.range (toEuclideanLin Z₀) = Λ₀)
    (hreg : (lagrangianCrossingForm Z₀ Z' V).Nondegenerate) :
    ∃ (W : ℒ ι) (hVW : IsCompl (V : Submodule ℝ (StdSpace ι)) W),
      (ContinuousLinearMap.crossingForm
        (projForm ((V : Submodule ℝ (StdSpace ι)).projection W hVW) Z₀ Z₀).toContinuousLinearMap₂'
        (projForm ((V : Submodule ℝ (StdSpace ι)).projection W hVW) Z' Z₀ +
          projForm ((V : Submodule ℝ (StdSpace ι)).projection W hVW) Z₀
            Z').toContinuousLinearMap₂').Nondegenerate := by
  obtain ⟨W, hWV, hWΛ⟩ := LagrangianGrassmannian.exists_isCompl_isCompl V Λ₀
  exact ⟨W, hWV.symm, (lagrangianCrossingFormIsometryEquivProjForm V.isLagrangian.isIsotropic
    hWV.symm (hZ₀ ▸ Λ₀.isLagrangian) (hZ₀ ▸ hWΛ.disjoint) Z').nondegenerate_iff.1 hreg⟩
end Isolated

namespace LagrangianGrassmannian

/-- **Regular crossings are isolated on the left.** Let `Z` be a frame of a family `Λ` of
Lagrangians at the times `r ≤ r₀` near `r₀`, with left derivative `Z'` at `r₀`. If the crossing
form of `Z r₀` and `Z'` relative to a Lagrangian `V` is nondegenerate, then `Λ r` is transverse to
`V` for all `r < r₀` near `r₀`. -/
theorem eventually_nhdsLT_not_crossing_of_regular {Λ : ℝ → ℒ ι} (V : ℒ ι)
    {Z : ℝ → Matrix (ι ⊕ ι) ι ℝ} {Z' : Matrix (ι ⊕ ι) ι ℝ} {r₀ : ℝ}
    (hZ : ∀ᶠ r in 𝓝[≤] r₀, LinearMap.range (toEuclideanLin (Z r)) = Λ r)
    (hd : HasDerivWithinAt Z Z' (Iic r₀) r₀)
    (hreg : (lagrangianCrossingForm (Z r₀) Z' V).Nondegenerate) :
    ∀ᶠ r in 𝓝[<] r₀, (Λ r : Submodule ℝ (StdSpace ι)) ⊓ V = ⊥ := by
  have hZ₀ : LinearMap.range (toEuclideanLin (Z r₀)) = Λ r₀ :=
    hZ.self_of_nhdsWithin self_mem_Iic
  obtain ⟨W, hVW, hreg'⟩ :=
    exists_projForm_crossingForm_nondegenerate V hZ₀ hreg
  have hsymm {r : ℝ} (hr : LinearMap.range (toEuclideanLin (Z r)) = Λ r) :=
    isSymm_projForm V.isLagrangian.isIsotropic W.isLagrangian.isIsotropic hVW
      (hr ▸ (Λ r).isLagrangian.isIsotropic)
  have hZ' : ∀ᶠ r in 𝓝[<] r₀, _ := hZ.filter_mono (nhdsWithin_mono _ Iio_subset_Iic_self)
  filter_upwards [ContinuousLinearMap.eventually_nhdsLT_nondegenerate_of_crossingForm_nondegenerate
    (hZ'.mono fun _ ↦ hsymm) (hsymm hZ₀) (hasDerivWithinAt_toContinuousLinearMap₂' fun i j ↦
      (hasDerivWithinAt_projForm _ hd).matrix_elem i j) hreg', hZ'] with r hr hZr
  rw [← hZr]
  exact inf_eq_bot_of_nondegenerate hVW (hZr ▸ (Λ r).isLagrangian.isIsotropic) hr

/-- **Regular crossings are isolated on the right.** Let `Z` be a frame of a family `Λ` of
Lagrangians at the times `r ≥ r₀` near `r₀`, with right derivative `Z'` at `r₀`. If the crossing
form of `Z r₀` and `Z'` relative to a Lagrangian `V` is nondegenerate, then `Λ r` is transverse to
`V` for all `r > r₀` near `r₀`. -/
theorem eventually_nhdsGT_not_crossing_of_regular {Λ : ℝ → ℒ ι} (V : ℒ ι)
    {Z : ℝ → Matrix (ι ⊕ ι) ι ℝ} {Z' : Matrix (ι ⊕ ι) ι ℝ} {r₀ : ℝ}
    (hZ : ∀ᶠ r in 𝓝[≥] r₀, LinearMap.range (toEuclideanLin (Z r)) = Λ r)
    (hd : HasDerivWithinAt Z Z' (Ici r₀) r₀)
    (hreg : (lagrangianCrossingForm (Z r₀) Z' V).Nondegenerate) :
    ∀ᶠ r in 𝓝[>] r₀, (Λ r : Submodule ℝ (StdSpace ι)) ⊓ V = ⊥ := by
  have hZ₀ : LinearMap.range (toEuclideanLin (Z r₀)) = Λ r₀ :=
    hZ.self_of_nhdsWithin self_mem_Ici
  obtain ⟨W, hVW, hreg'⟩ :=
    exists_projForm_crossingForm_nondegenerate V hZ₀ hreg
  have hsymm {r : ℝ} (hr : LinearMap.range (toEuclideanLin (Z r)) = Λ r) :=
    isSymm_projForm V.isLagrangian.isIsotropic W.isLagrangian.isIsotropic hVW
      (hr ▸ (Λ r).isLagrangian.isIsotropic)
  have hZ' : ∀ᶠ r in 𝓝[>] r₀, _ := hZ.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)
  filter_upwards [ContinuousLinearMap.eventually_nhdsGT_nondegenerate_of_crossingForm_nondegenerate
    (hZ'.mono fun _ ↦ hsymm) (hsymm hZ₀) (hasDerivWithinAt_toContinuousLinearMap₂' fun i j ↦
      (hasDerivWithinAt_projForm _ hd).matrix_elem i j) hreg', hZ'] with r hr hZr
  rw [← hZr]
  exact inf_eq_bot_of_nondegenerate hVW (hZr ▸ (Λ r).isLagrangian.isIsotropic) hr

/-- **Regular crossings are isolated.** Let `Z` be a frame of a family `Λ` of Lagrangians indexed
by `ℝ` near `r₀`, so that `LinearMap.range (toEuclideanLin (Z r)) = Λ r` for all `r` near `r₀`,
and let `Z` be differentiable at `r₀` with derivative `Z'`. If the crossing form of `Z r₀` and `Z'`
relative to a Lagrangian `V` is nondegenerate, then `Λ r` is transverse to `V` for all `r ≠ r₀`
near `r₀`. Neither continuity of `Λ` nor differentiability of `Z` away from `r₀` is needed. -/
theorem eventually_nhdsNE_not_crossing_of_regular {Λ : ℝ → ℒ ι} (V : ℒ ι)
    {Z : ℝ → Matrix (ι ⊕ ι) ι ℝ} {Z' : Matrix (ι ⊕ ι) ι ℝ} {r₀ : ℝ}
    (hZ : ∀ᶠ r in 𝓝 r₀, LinearMap.range (toEuclideanLin (Z r)) = Λ r)
    (hd : HasDerivAt Z Z' r₀) (hreg : (lagrangianCrossingForm (Z r₀) Z' V).Nondegenerate) :
    ∀ᶠ r in 𝓝[≠] r₀, (Λ r : Submodule ℝ (StdSpace ι)) ⊓ V = ⊥ := by
  rw [← nhdsLT_sup_nhdsGT, eventually_sup]
  exact ⟨eventually_nhdsLT_not_crossing_of_regular V (hZ.filter_mono nhdsWithin_le_nhds)
      hd.matrix_hasDerivWithinAt hreg,
    eventually_nhdsGT_not_crossing_of_regular V (hZ.filter_mono nhdsWithin_le_nhds)
      hd.matrix_hasDerivWithinAt hreg⟩

/-- **Regular crossings are isolated.** Let `Z` be a frame of a family `γ` of Lagrangians on
`[0, 1]`, `LinearMap.range (toEuclideanLin (Z t)) = γ t`, differentiable within `[0, 1]` at `t₀`
with derivative `Z'`. If the crossing form of `Z t₀` and `Z'` relative to a Lagrangian `V` is
nondegenerate, then `γ t` is transverse to `V` for all `t ≠ t₀` near `t₀`. Neither continuity of
`γ` nor differentiability of `Z` away from `t₀` is needed; `t₀` may be an end of `[0, 1]`. -/
theorem eventually_not_crossing_of_regular (γ : I → ℒ ι) (V : ℒ ι)
    {Z : ℝ → Matrix (ι ⊕ ι) ι ℝ} {Z' : Matrix (ι ⊕ ι) ι ℝ} {t₀ : I}
    (hZ : ∀ t : I, LinearMap.range (toEuclideanLin (Z t)) = γ t)
    (hd : HasDerivWithinAt Z Z' (Icc 0 1) t₀)
    (hreg : (lagrangianCrossingForm (Z t₀) Z' V).Nondegenerate) :
    ∀ᶠ t in 𝓝[≠] t₀, (γ t : Submodule ℝ (StdSpace ι)) ⊓ V = ⊥ := by
  obtain ⟨W, hVW, hreg'⟩ := exists_projForm_crossingForm_nondegenerate V (hZ t₀) hreg
  have hR :=
    ContinuousLinearMap.eventually_nhdsWithin_Icc_diff_nondegenerate_of_crossingForm_nondegenerate
      t₀.property (fun r hr ↦ isSymm_projForm V.isLagrangian.isIsotropic W.isLagrangian.isIsotropic
        hVW ((hZ ⟨r, hr⟩) ▸ (γ ⟨r, hr⟩).isLagrangian.isIsotropic))
      (hasDerivWithinAt_toContinuousLinearMap₂' fun i j ↦
        (hasDerivWithinAt_projForm _ hd).matrix_elem i j) hreg'
  -- Transfer from `[0, 1] ⊆ ℝ` to `I`.
  have htend : Tendsto (fun t : I ↦ (t : ℝ)) (𝓝[≠] t₀) (𝓝[Icc 0 1 \ {(t₀ : ℝ)}] (t₀ : ℝ)) :=
    continuous_subtypeVal.continuousWithinAt.tendsto_nhdsWithin fun t ht ↦
      ⟨t.property, fun h ↦ ht (Subtype.ext h)⟩
  filter_upwards [htend.eventually hR] with t ht
  rw [← hZ t]
  exact inf_eq_bot_of_nondegenerate hVW ((hZ t).symm ▸ (γ t).isLagrangian.isIsotropic) ht

end LagrangianGrassmannian

end SymplecticGeometry

end
