/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Basic

/-!
# Slices of a diffeotopy that keeps a parameter

Let `Φ` be a diffeotopy of a product `N × M` that keeps the parameter, `(Φ (t, (q, x))).1 = q`.
Then for every parameter `q : N` and time `t` the map `x ↦ (Φ (t, (q, x))).2` is a
diffeomorphism of `M` (`TauCeti.Diffeotopy.slice`), the slice at `q` of the time-`t` slice of
`Φ` (`Diffeomorph.slice`). These diffeomorphisms form a smooth family over `N × [0, 1]`
(`TauCeti.Diffeotopy.contMDiff_slice`) that is the identity at time `0`
(`TauCeti.Diffeotopy.slice_zero`).

## Main definitions

* `TauCeti.Diffeotopy.slice Φ hΦ q t`: the diffeomorphism `x ↦ (Φ (t, (q, x))).2` of `M`.

## Main results

* `TauCeti.Diffeotopy.contMDiff_slice`: the family `((q, t), x) ↦ Φ.slice hΦ q t x` is smooth.
* `TauCeti.Diffeotopy.slice_zero`: the slices at time `0` are the identity.
-/

public noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.Diffeotopy

variable {E E' H H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E H} {J' : ModelWithCorners ℝ E' H'}
  {N M : Type*} [TopologicalSpace N] [ChartedSpace H N] [TopologicalSpace M] [ChartedSpace H' M]
  {n : ℕ∞ω}

section slice

variable (Φ : Diffeotopy (J.prod J') n (N × M)) (hΦ : ∀ t p, (Φ (t, p)).1 = p.1)

/-- The slice at a parameter `q : N` and a time `t` of a diffeotopy `Φ` of `N × M` that keeps the
parameter: the diffeomorphism `x ↦ (Φ (t, (q, x))).2` of `M`. -/
def slice (q : N) (t : unitInterval) : M ≃ₘ^n⟮J', J'⟯ M :=
  (Φ.timeSlice t).slice (fun p ↦ by rw [timeSlice_apply, hΦ]) q

theorem slice_def (q : N) (t : unitInterval) :
    Φ.slice hΦ q t = (Φ.timeSlice t).slice (fun p ↦ by rw [timeSlice_apply, hΦ]) q :=
  (rfl)

@[simp]
theorem slice_apply (q : N) (t : unitInterval) (x : M) :
    Φ.slice hΦ q t x = (Φ (t, (q, x))).2 := by
  rw [slice_def, Diffeomorph.slice_apply, timeSlice_apply]

theorem coe_slice (q : N) (t : unitInterval) :
    ⇑(Φ.slice hΦ q t) = fun x ↦ (Φ (t, (q, x))).2 :=
  funext (Φ.slice_apply hΦ q t)

@[simp]
theorem symm_slice_apply (q : N) (t : unitInterval) (y : M) :
    (Φ.slice hΦ q t).symm y = (Φ.symm (t, (q, y))).2 := by
  rw [slice_def, Diffeomorph.symm_slice_apply, symm_timeSlice_apply]

/-- A diffeotopy that keeps the parameter acts on `(q, x)` at time `t` through its slice. -/
theorem apply_eq_slice (t : unitInterval) (p : N × M) :
    Φ (t, p) = (p.1, Φ.slice hΦ p.1 t p.2) :=
  Prod.ext (hΦ t p) (Φ.slice_apply hΦ p.1 t p.2).symm

/-- The slices of a diffeotopy at time `0` are the identity. -/
@[simp]
theorem slice_zero (q : N) : Φ.slice hΦ q 0 = Diffeomorph.refl J' M n :=
  Diffeomorph.ext fun x ↦ by rw [slice_apply, apply_zero, Diffeomorph.coe_refl, id_eq]

/-- The slices of a diffeotopy that keeps the parameter form a smooth family over
`N × [0, 1]`. -/
theorem contMDiff_slice :
    ContMDiff ((J.prod (𝓡∂ 1)).prod J') J' n
      fun p : (N × unitInterval) × M ↦ Φ.slice hΦ p.1.1 p.1.2 p.2 := by
  simp only [slice_apply]
  exact contMDiff_snd.comp (Φ.contMDiff.comp (contMDiff_fst.snd.prodMk
    (contMDiff_fst.fst.prodMk contMDiff_snd)))

end slice

end TauCeti.Diffeotopy

end
