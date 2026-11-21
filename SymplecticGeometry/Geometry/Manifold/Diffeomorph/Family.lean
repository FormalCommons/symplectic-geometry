/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod

/-!
# Smooth families of diffeomorphisms

A family `ψ : P → M ≃ₘ^n⟮I, I⟯ M` of diffeomorphisms of `M`, indexed by a manifold `P`, is jointly
`C^n` when `(p, x) ↦ ψ_p x` is `C^n` on `P × M`. This file shows that the inverses of such a
family are then jointly `C^n` too, when `M` and `P` are finite-dimensional and boundaryless and
`1 ≤ n`.

## Main results

* `Diffeomorph.contMDiff_symm_eval`: the inverses `(p, y) ↦ ψ_p⁻¹ y` of a jointly `C^n` family
  of `C^n` diffeomorphisms are jointly `C^n`.

## Implementation notes

The map `F : (p, x) ↦ (p, ψ_p x)` of `P × M` is a bijection with injective differential, since
each `dψ_p` is injective. So the inverse function theorem (Tau Ceti's
`TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv`, then Mathlib's
`IsLocalDiffeomorph.diffeomorphOfBijective`) makes `F` a diffeomorphism, whose inverse is
`(p, y) ↦ (p, ψ_p⁻¹ y)`. The statement is the smooth counterpart of Tau Ceti's
`TauCeti.continuous_equiv_symm_eval`, after which it is named.
-/

public section

open Set
open scoped Manifold ContDiff

variable {E E' H H' M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H] [TopologicalSpace H'] {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace P] [ChartedSpace H' P] {n : ℕ∞ω}
  [IsManifold I n M] [IsManifold J n P] [BoundarylessManifold I M] [BoundarylessManifold J P]

/-- On a finite-dimensional boundaryless manifold, the inverses of a jointly `C^n` family of
`C^n` diffeomorphisms, `1 ≤ n`, over a finite-dimensional boundaryless parameter manifold `P` are
jointly `C^n`: `(p, y) ↦ ψ_p⁻¹ y` is `C^n` on `P × M`. -/
theorem Diffeomorph.contMDiff_symm_eval {ψ : P → M ≃ₘ^n⟮I, I⟯ M} (hn : 1 ≤ n)
    (hψ : ContMDiff (J.prod I) I n (fun p : P × M ↦ ψ p.1 p.2)) :
    ContMDiff (J.prod I) I n (fun p : P × M ↦ (ψ p.1).symm p.2) := by
  have hn₀ : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  set F : P × M → P × M := fun p ↦ (p.1, ψ p.1 p.2) with hF
  have hFs : ContMDiff (J.prod I) (J.prod I) n F := contMDiff_fst.prodMk hψ
  -- The differential of `F` is `(v, w) ↦ (v, ∂ₚψ v + dψ_p w)`, which is injective since each
  -- `dψ_p` is.
  have hinj (q : P × M) : Function.Injective (mfderiv (J.prod I) (J.prod I) F q) := by
    have hd : MDifferentiableAt (J.prod I) I (fun p : P × M ↦ ψ p.1 p.2) q :=
      hψ.mdifferentiableAt hn₀
    refine (injective_iff_map_eq_zero _).2 ?_
    rintro ⟨v, w⟩ h
    rw [hF, mfderiv_prodMk mdifferentiableAt_fst hd] at h
    obtain ⟨h₁, h₂⟩ := Prod.ext_iff.1 ((ContinuousLinearMap.prod_apply _ _ (v, w)).symm.trans h)
    rw [mfderiv_fst] at h₁
    obtain rfl : v = 0 := h₁
    have h₃ : mfderiv I I (ψ q.1) q.2 w = 0 := (hd.mfderiv_curry_right_apply w).symm.trans h₂
    obtain rfl : w = 0 := ((ψ q.1).isInvertible_mfderiv hn₀ (x := q.2)).injective
      (h₃.trans (map_zero _).symm)
    rfl
  have hloc : IsLocalDiffeomorph (J.prod I) (J.prod I) n F := fun q ↦
    TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv hFs.contMDiffOn isOpen_univ (mem_univ q)
      BoundarylessManifold.isInteriorPoint hn (hinj q) rfl
  have hbij : Function.Bijective F := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun p ↦ (p.1, (ψ p.1).symm p.2), ?_, ?_⟩ <;>
      intro p <;> simp [F]
  set D := hloc.diffeomorphOfBijective hbij
  have hD : ∀ p : P × M, D.symm p = (p.1, (ψ p.1).symm p.2) := fun p ↦ by
    have h : D (p.1, (ψ p.1).symm p.2) = p := by
      rw [IsLocalDiffeomorph.coe_diffeomorphOfBijective]
      simp [F]
    exact (congrArg D.symm h).symm.trans (D.symm_apply_apply _)
  exact (contMDiff_snd.comp D.symm.contMDiff).congr fun p ↦ by simp [hD]

end
