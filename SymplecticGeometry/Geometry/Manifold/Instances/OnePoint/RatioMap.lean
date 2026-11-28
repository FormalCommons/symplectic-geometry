/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.TwistCore
import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint
import SymplecticGeometry.Topology.VectorBundle.ZeroSet
import TauCeti.Geometry.Manifold.Instances.OnePoint.Tangent.Basic

/-!
# The map of the Riemann sphere given by two sections of `𝒪(k)`

Let `s` and `t` be `C^n` sections of the line bundle `𝒪(k) = OnePoint.twistCore k` on the
Riemann sphere, regarded as a real vector bundle over the underlying real surface, with no common
zero. Since `s x` and `t x` lie in the same line, the point `[s x : t x]` of `ℙ¹(ℂ)` is well
defined; read through Mathlib's identification `OnePoint.equivProjectivization` of `OnePoint ℂ`
with `ℙ¹(ℂ)`, it is `s x / t x` where `t x ≠ 0` and `∞` where `t x = 0`.

## Main definitions and results

* `OnePoint.equivProjectivization_symm_mk_eventuallyEq_coe_div`: near a point where `t` does not
  vanish, `x ↦ [s x : t x]` is the inclusion of `ℂ` applied to the quotient `s / t`.
* `OnePoint.equivProjectivization_symm_mk_eventuallyEq_invChart_symm_div`: near a point where `s`
  does not vanish, it is the inverse of the inverted chart `OnePoint.invChart` applied to `t / s`.
* `OnePoint.contMDiff_equivProjectivization_symm_mk_twistCore`: the map `x ↦ [s x : t x]` is
  `C^n`, for sections written as functions `OnePoint ℂ → ℂ`, as Tau Ceti writes them.
* `OnePoint.ratioMap`: that map, as an element of `C^n⟮𝓘(ℝ, ℂ), OnePoint ℂ; 𝓘(ℝ, ℂ), OnePoint ℂ⟯`,
  for a pair `(s, t)` of `C^n` sections of `𝒪(k)` without common zero.
* `OnePoint.ratioMap_apply`: its value, through `OnePoint.equivProjectivization`.
* `OnePoint.ratioMap_apply_of_ne_zero`: where `t x ≠ 0`, the value is `s x / t x`.
* `OnePoint.ratioMap_apply_of_eq_zero`: where `t x = 0`, the value is `∞`.
* `OnePoint.ratioMap_apply_eq_invChart_symm`: where `s x ≠ 0`, the value is the inverse of the
  inverted chart applied to `t x / s x`.

The fibres of `𝒪(k)` are `ℂ`, but not reducibly so, so the division of two values of sections
does not elaborate; the value lemmas of `ratioMap` therefore take the values as complex numbers
`a` and `b` with `s x = a` and `t x = b`.

The two local forms give smoothness: the quotients are `C^n` by
`OnePoint.contMDiffAt_div_twistCore`, and the inclusion of `ℂ` and the inverse of the inverted
chart are smooth (Tau Ceti's `OnePoint.contMDiff_coe_real` and
`OnePoint.contMDiff_invChart_symm_real`). `SymplecticGeometry.contMDiff_uniformizingMap` is
derived from these results.
-/

public section

open Bundle Filter TauCeti
open scoped Manifold ContDiff Topology OnePoint VectorBundle.ComplexToReal

noncomputable section

namespace OnePoint

variable {k : ℤ} {n : ℕ∞ω} {s t : OnePoint ℂ → ℂ} {x : OnePoint ℂ}

/-- Near a point where the section `t` of `𝒪(k)`, continuous there, does not vanish,
`y ↦ [s y : t y]` is the inclusion of `ℂ` applied to the quotient `s / t`. -/
theorem equivProjectivization_symm_mk_eventuallyEq_coe_div (hst : ∀ y, ![s y, t y] ≠ 0)
    (ht : ContinuousAt (fun y ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) k).Fiber) y (t y)) x)
    (hx : t x ≠ 0) :
    (fun y ↦ (equivProjectivization ℂ).symm (Projectivization.mk ℂ ![s y, t y] (hst y))) =ᶠ[𝓝 x]
      (↑) ∘ fun y ↦ s y / t y := by
  filter_upwards [VectorBundle.eventually_ne_zero ℂ (b := id) ht hx] with y hy
  exact equivProjectivization_symm_mk_of_ne_zero (hst y) hy

/-- Near a point where the section `s` of `𝒪(k)`, continuous there, does not vanish,
`y ↦ [s y : t y]` is the inverse of the inverted chart applied to the quotient `t / s`. -/
theorem equivProjectivization_symm_mk_eventuallyEq_invChart_symm_div
    (hst : ∀ y, ![s y, t y] ≠ 0)
    (hs : ContinuousAt (fun y ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) k).Fiber) y (s y)) x)
    (hx : s x ≠ 0) :
    (fun y ↦ (equivProjectivization ℂ).symm (Projectivization.mk ℂ ![s y, t y] (hst y))) =ᶠ[𝓝 x]
      invChart.symm ∘ fun y ↦ t y / s y := by
  filter_upwards [VectorBundle.eventually_ne_zero ℂ (b := id) hs hx] with y hy
  exact equivProjectivization_symm_mk_eq_invChart_symm (hst y) hy

/-- **The map `[s : t]` is smooth.** For `C^n` sections `s` and `t` of `𝒪(k)`, for the real
structure, without common zero, the map `x ↦ [s x : t x]` of the Riemann sphere, read through
`OnePoint.equivProjectivization`, is `C^n`. -/
theorem contMDiff_equivProjectivization_symm_mk_twistCore
    (hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) n
      (fun y ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) k).Fiber) y (s y)))
    (ht : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) n
      (fun y ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) k).Fiber) y (t y)))
    (hst : ∀ y, ![s y, t y] ≠ 0) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n
      (fun y ↦ (equivProjectivization ℂ).symm (Projectivization.mk ℂ ![s y, t y] (hst y))) := by
  intro x
  by_cases hx : t x = 0
  · -- Near `x`, where `s` does not vanish, the map reads through the inverted chart.
    have hsx : s x ≠ 0 := fun h ↦ hst x (by simp [h, hx])
    exact (contMDiff_invChart_symm_real.contMDiffAt.comp x
      (contMDiffAt_div_twistCore k (ht x) (hs x) hsx)).congr_of_eventuallyEq
      (equivProjectivization_symm_mk_eventuallyEq_invChart_symm_div hst (hs x).continuousAt hsx)
  · -- Near `x`, where `t` does not vanish, the map reads through the inclusion of `ℂ`.
    exact (contMDiff_coe_real.contMDiffAt.comp x
      (contMDiffAt_div_twistCore k (hs x) (ht x) hx)).congr_of_eventuallyEq
      (equivProjectivization_symm_mk_eventuallyEq_coe_div hst (ht x).continuousAt hx)

variable (p : {p : Cₛ^n⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) k).Fiber⟯ ×
  Cₛ^n⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) k).Fiber⟯ // ∀ x, (![p.1 x, p.2 x] : Fin 2 → ℂ) ≠ 0})

/-- The map `x ↦ [s x : t x]` of the Riemann sphere, for a pair `(s, t)` of `C^n` sections of
`𝒪(k)`, for the real structure, without common zero, as a `C^n` map. Its value is read through
the identification `OnePoint.equivProjectivization` of `OnePoint ℂ` with `ℙ¹(ℂ)`. -/
def ratioMap : C^n⟮𝓘(ℝ, ℂ), OnePoint ℂ; 𝓘(ℝ, ℂ), OnePoint ℂ⟯ :=
  ⟨fun x ↦ (equivProjectivization ℂ).symm
      (Projectivization.mk ℂ (![p.val.1 x, p.val.2 x] : Fin 2 → ℂ) (p.property x)),
    contMDiff_equivProjectivization_symm_mk_twistCore p.val.1.contMDiff p.val.2.contMDiff
      p.property⟩

/-- The value of `ratioMap` at `x` is the point `[s x : t x]` of `ℙ¹(ℂ)`, read in
`OnePoint ℂ`. -/
@[simp]
theorem ratioMap_apply (x : OnePoint ℂ) :
    ratioMap p x = (equivProjectivization ℂ).symm
      (Projectivization.mk ℂ (![p.val.1 x, p.val.2 x] : Fin 2 → ℂ) (p.property x)) :=
  (rfl)

/-- At a point where `t` takes the nonzero value `b` and `s` the value `a`, `ratioMap` takes the
value `a / b`. The values are taken as complex numbers, which the fibres of `𝒪(k)` are. -/
theorem ratioMap_apply_of_ne_zero {a b : ℂ} (ha : p.val.1 x = a) (hb : p.val.2 x = b)
    (hb₀ : b ≠ 0) : ratioMap p x = ((a / b : ℂ) : OnePoint ℂ) := by
  subst ha hb
  rw [ratioMap_apply]
  exact equivProjectivization_symm_mk_of_ne_zero (p.property x) hb₀

/-- At a zero of `t`, `ratioMap` takes the value `∞`. -/
theorem ratioMap_apply_of_eq_zero (hx : p.val.2 x = 0) : ratioMap p x = (∞ : OnePoint ℂ) := by
  rw [ratioMap_apply, equivProjectivization_symm_apply_mk]
  split_ifs with h
  · rfl
  · exact absurd hx h

/-- At a point where `s` takes the nonzero value `a` and `t` the value `b`, `ratioMap` takes the
value of the inverse of the inverted chart at `b / a`. -/
theorem ratioMap_apply_eq_invChart_symm {a b : ℂ} (ha : p.val.1 x = a) (hb : p.val.2 x = b)
    (ha₀ : a ≠ 0) : ratioMap p x = invChart.symm (b / a) := by
  subst ha hb
  rw [ratioMap_apply]
  exact equivProjectivization_symm_mk_eq_invChart_symm (p.property x) ha₀

end OnePoint

end
