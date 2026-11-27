/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.SpecialFunctions.Complex.CircleMap
public import TauCeti.AlgebraicTopology.FundamentalGroup.PuncturedStarConvex
public import TauCeti.Topology.Homotopy.Path

import Mathlib.Data.Int.Cast.Lemmas
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph

/-!
# The fundamental group of a punctured plane

A linear isometry `φ : ℂ ≃ₗᵢ[ℝ] E` identifies `E ∖ {0}` with `ℂ ∖ {0}`, whose fundamental group
Tau Ceti computes as `ℤ` (`StarConvex.fundamentalGroupMulEquivInt`). This file carries that
computation over to `E`, with the circle `t ↦ φ (r e^{2πit})` as generator. For
`E = EuclideanSpace ℝ (Fin 2)`, take `φ = Complex.orthonormalBasisOneI.repr`.

## Main definitions

* `LinearIsometryEquiv.complSingletonHomeomorph`: a linear isometry restricts to a homeomorphism
  of the complements of the origin.
* `LinearIsometryEquiv.circleLoop φ hr`: the loop `t ↦ φ (r e^{2πit})` in `E ∖ {0}`, the image of
  `circlePath 0 r 0` under `φ`, based at `LinearIsometryEquiv.circleBasepoint φ hr = φ r`.
* `LinearIsometryEquiv.fundamentalGroupComplSingletonMulEquivInt`: `π₁(E ∖ {0}, φ r) ≃* ℤ`.

## Main results

* `LinearIsometryEquiv.fundamentalGroupComplSingletonMulEquivInt_circleLoop`: the class of
  `circleLoop φ hr` corresponds to `1 : ℤ`.
* `LinearIsometryEquiv.fundamentalGroupComplSingleton_hom_ext`: homomorphisms out of
  `π₁(E ∖ {0}, φ r)` are determined by their value on the class of `circleLoop φ hr`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 1.7
  (`π₁(S¹) ≅ ℤ`).
-/

public section

open Set TauCeti

namespace LinearIsometryEquiv

section Homeomorph

variable {R V W : Type*} [Semiring R] [SeminormedAddCommGroup V] [SeminormedAddCommGroup W]
  [Module R V] [Module R W]

/-- A linear isometry `f : V ≃ₗᵢ[R] W` restricts to a homeomorphism `V ∖ {0} ≃ₜ W ∖ {0}`. -/
def complSingletonHomeomorph (f : V ≃ₗᵢ[R] W) : ({0}ᶜ : Set V) ≃ₜ ({0}ᶜ : Set W) :=
  f.toHomeomorph.subtype fun x ↦ by simp

@[simp]
theorem coe_complSingletonHomeomorph_apply (f : V ≃ₗᵢ[R] W) (x : ({0}ᶜ : Set V)) :
    (f.complSingletonHomeomorph x : W) = f x :=
  (rfl)

@[simp]
theorem coe_complSingletonHomeomorph_symm_apply (f : V ≃ₗᵢ[R] W) (y : ({0}ᶜ : Set W)) :
    (f.complSingletonHomeomorph.symm y : V) = f.symm y :=
  (rfl)

end Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : ℂ ≃ₗᵢ[ℝ] E) {r : ℝ}
  (hr : 0 < r)

/-- The point `φ r` of `E ∖ {0}`, the basepoint of `circleLoop φ hr`. -/
noncomputable def circleBasepoint : ({0}ᶜ : Set E) :=
  ⟨φ r, by simpa using hr.ne'⟩

@[simp]
theorem coe_circleBasepoint : (φ.circleBasepoint hr : E) = φ r :=
  (rfl)

/-- The loop `t ↦ φ (r e^{2πit})` in `E ∖ {0}`, the image of `circlePath 0 r 0` under `φ`: it goes
once around the origin, counterclockwise in the coordinates `φ`. -/
noncomputable def circleLoop : Path (φ.circleBasepoint hr) (φ.circleBasepoint hr) :=
  Path.codRestrict (((circlePath 0 r 0).map φ.continuous).cast (by simp [circleMap_zero])
    (by simp [circleMap_zero]))
    fun t ↦ by simpa using hr.ne'

theorem circleLoop_def :
    φ.circleLoop hr = Path.codRestrict (((circlePath 0 r 0).map φ.continuous).cast
      (by simp [circleMap_zero]) (by simp [circleMap_zero])) fun _ ↦ by simpa using hr.ne' :=
  (rfl)

@[simp]
theorem coe_circleLoop_apply (t : unitInterval) :
    (φ.circleLoop hr t : E) = φ (circleMap 0 r (2 * Real.pi * t)) := by
  simp [circleLoop_def]

/-- `ℂ ∖ {0}`, written as Tau Ceti's `StarConvex` API writes it, is homeomorphic to `E ∖ {0}` by
`φ`. -/
private noncomputable def univDiffHomeomorph : ↥((univ : Set ℂ) \ {0}) ≃ₜ ({0}ᶜ : Set E) :=
  (Homeomorph.setCongr (compl_eq_univ_sdiff _).symm).trans φ.complSingletonHomeomorph

@[simp]
private theorem coe_univDiffHomeomorph_apply (z : ↥((univ : Set ℂ) \ {0})) :
    (univDiffHomeomorph φ z : E) = φ z :=
  (rfl)

/-- The basepoint of `StarConvex.fundamentalGroupMulEquivInt` is carried to `φ r`. -/
private theorem univDiffHomeomorph_sphereHomotopyEquiv :
    univDiffHomeomorph φ ((starConvex_univ 0).sphereHomotopyEquiv hr (subset_univ _)
      ((sphereCircleHomeomorph 0 hr).symm 1)) = φ.circleBasepoint hr :=
  Subtype.ext (by simp)

/-- **The fundamental group of a punctured plane is `ℤ`.** For a real normed space `E`
identified with `ℂ` by the linear isometry `φ`, the fundamental group of `E ∖ {0}` at `φ r`, for
`r > 0`, is infinite cyclic. -/
noncomputable def fundamentalGroupComplSingletonMulEquivInt :
    FundamentalGroup ({0}ᶜ : Set E) (φ.circleBasepoint hr) ≃* Multiplicative ℤ :=
  (FundamentalGroup.homeomorphMulEquivOfEq (univDiffHomeomorph φ)
    (univDiffHomeomorph_sphereHomotopyEquiv φ hr)).symm.trans
      ((starConvex_univ 0).fundamentalGroupMulEquivInt hr (subset_univ _) _)

/-- The loop `circleLoop φ hr` generates the fundamental group of `E ∖ {0}`: it corresponds to
`1 : ℤ`. -/
theorem fundamentalGroupComplSingletonMulEquivInt_circleLoop :
    φ.fundamentalGroupComplSingletonMulEquivInt hr
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (φ.circleLoop hr))) =
      Multiplicative.ofAdd 1 := by
  -- Carried to `ℂ ∖ {0}`, the loop is `Complex.sphereLoop`, up to the basepoint equation.
  have key : ∀ (y : ({0}ᶜ : Set E)) (hy : univDiffHomeomorph φ
      ((starConvex_univ 0).sphereHomotopyEquiv hr (subset_univ _)
        ((sphereCircleHomeomorph 0 hr).symm 1)) = y) (γ : Path y y),
      (∀ t, (γ t : E) = φ (circleMap 0 r (2 * Real.pi * t))) →
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) =
        FundamentalGroup.homeomorphMulEquivOfEq (univDiffHomeomorph φ) hy
          (FundamentalGroup.map ((starConvex_univ 0).sphereHomotopyEquiv hr (subset_univ _)).toFun
            _ (FundamentalGroup.fromPath
              (Path.Homotopic.Quotient.mk (Complex.sphereLoop 0 hr)))) := by
    intro y hy γ hγ
    rw [TauCeti.FundamentalGroup.map_fromPath, FundamentalGroup.homeomorphMulEquivOfEq_fromPath_mk,
      Path.map_map]
    congr 2
    ext t
    simp [hγ]
  rw [fundamentalGroupComplSingletonMulEquivInt, MulEquiv.trans_apply,
    (MulEquiv.symm_apply_eq _).mpr
      (key _ (univDiffHomeomorph_sphereHomotopyEquiv φ hr) _ (coe_circleLoop_apply φ hr)),
    StarConvex.fundamentalGroupMulEquivInt_sphereLoop]

/-- Two homomorphisms out of `π₁(E ∖ {0}, φ r)` are equal once they agree on the class of
`circleLoop φ hr`, which generates it. -/
theorem fundamentalGroupComplSingleton_hom_ext {M : Type*} [Monoid M]
    {f f' : FundamentalGroup ({0}ᶜ : Set E) (φ.circleBasepoint hr) →* M}
    (h : f (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (φ.circleLoop hr))) =
      f' (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (φ.circleLoop hr)))) :
    f = f' := by
  set ε := φ.fundamentalGroupComplSingletonMulEquivInt hr
  have hε : ε.symm (Multiplicative.ofAdd 1) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (φ.circleLoop hr)) := by
    rw [MulEquiv.symm_apply_eq, fundamentalGroupComplSingletonMulEquivInt_circleLoop]
  have : f.comp ε.symm.toMonoidHom = f'.comp ε.symm.toMonoidHom :=
    MonoidHom.ext_mint (by simpa [hε] using h)
  ext x
  simpa using DFunLike.congr_fun this (ε x)

end LinearIsometryEquiv

end
