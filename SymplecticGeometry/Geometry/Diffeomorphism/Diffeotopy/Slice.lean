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

Reading the parameter through a smooth map `π : S → N` gives a diffeotopy of `S × M` that keeps
the parameter, whose slice at `q` is the slice of `Φ` at `π q`
(`TauCeti.Diffeotopy.pullbackParam`, `TauCeti.Diffeotopy.slice_pullbackParam`).

## Main definitions

* `TauCeti.Diffeotopy.slice Φ hΦ q t`: the diffeomorphism `x ↦ (Φ (t, (q, x))).2` of `M`.
* `TauCeti.Diffeotopy.pullbackParam Φ hΦ hπ`: the diffeotopy
  `(t, (q, x)) ↦ (q, (Φ (t, (π q, x))).2)` of `S × M`, for a smooth map `π : S → N`.

## Main results

* `TauCeti.Diffeotopy.contMDiff_slice`: the family `((q, t), x) ↦ Φ.slice hΦ q t x` is smooth.
* `TauCeti.Diffeotopy.slice_zero`: the slices at time `0` are the identity.
* `TauCeti.Diffeotopy.slice_pullbackParam`: the slice at `q` of the pullback along `π` is the
  slice of `Φ` at `π q`.
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

/-! ### Pulling back along a map of parameter spaces -/

section pullbackParam

variable {E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ E'' H''} {S : Type*} [TopologicalSpace S] [ChartedSpace H'' S]
  (Φ : Diffeotopy (J.prod J') n (N × M)) (hΦ : ∀ t p, (Φ (t, p)).1 = p.1)
  {π : S → N} (hπ : ContMDiff K J n π)

/-- The pullback of a diffeotopy `Φ` of `N × M` that keeps the parameter along a smooth map
`π : S → N` of parameter spaces: the diffeotopy `(t, (q, x)) ↦ (q, (Φ (t, (π q, x))).2)` of
`S × M`. -/
def pullbackParam : Diffeotopy (K.prod J') n (S × M) where
  toDiffeomorph :=
    { toFun := fun p ↦ (p.1, (p.2.1, Φ.slice hΦ (π p.2.1) p.1 p.2.2))
      invFun := fun p ↦ (p.1, (p.2.1, (Φ.slice hΦ (π p.2.1) p.1).symm p.2.2))
      left_inv := fun p ↦ by simp only [Diffeomorph.symm_apply_apply]
      right_inv := fun p ↦ by simp only [Diffeomorph.apply_symm_apply]
      contMDiff_toFun := by
        simp only [slice_apply]
        exact contMDiff_fst.prodMk (contMDiff_snd.fst.prodMk (contMDiff_snd.comp
          (Φ.contMDiff.comp (contMDiff_fst.prodMk
            ((hπ.comp contMDiff_snd.fst).prodMk contMDiff_snd.snd)))))
      contMDiff_invFun := by
        simp only [symm_slice_apply]
        exact contMDiff_fst.prodMk (contMDiff_snd.fst.prodMk (contMDiff_snd.comp
          (Φ.symm.contMDiff.comp (contMDiff_fst.prodMk
            ((hπ.comp contMDiff_snd.fst).prodMk contMDiff_snd.snd))))) }
  fst_apply _ := rfl
  snd_apply_zero' p := Prod.ext rfl (DFunLike.congr_fun (Φ.slice_zero hΦ (π p.1)) p.2)

/-- The pullback `Φ.pullbackParam hΦ hπ` sends `(t, (q, x))` to `(q, (Φ (t, (π q, x))).2)`. -/
@[simp]
theorem pullbackParam_apply (p : unitInterval × S × M) :
    Φ.pullbackParam hΦ hπ p = (p.2.1, (Φ (p.1, (π p.2.1, p.2.2))).2) := by
  rw [coe_apply]
  exact congrArg (Prod.mk p.2.1) (Φ.slice_apply hΦ (π p.2.1) p.1 p.2.2)

/-- The pullback `Φ.pullbackParam hΦ hπ` keeps the parameter in `S`. -/
theorem fst_pullbackParam_apply (t : unitInterval) (p : S × M) :
    (Φ.pullbackParam hΦ hπ (t, p)).1 = p.1 := by
  rw [pullbackParam_apply]

/-- The inverse of the pullback `Φ.pullbackParam hΦ hπ` sends `(t, (q, y))` to
`(q, (Φ.symm (t, (π q, y))).2)`. -/
theorem symm_pullbackParam_apply (p : unitInterval × S × M) :
    (Φ.pullbackParam hΦ hπ).symm p = (p.2.1, (Φ.symm (p.1, (π p.2.1, p.2.2))).2) := by
  rw [symm_apply]
  exact congrArg (Prod.mk p.2.1) (Φ.symm_slice_apply hΦ (π p.2.1) p.1 p.2.2)

/-- The slice at `q` of the pullback `Φ.pullbackParam hΦ hπ` is the slice of `Φ` at `π q`. -/
@[simp]
theorem slice_pullbackParam (q : S) (t : unitInterval) :
    (Φ.pullbackParam hΦ hπ).slice (Φ.fst_pullbackParam_apply hΦ hπ) q t = Φ.slice hΦ (π q) t :=
  Diffeomorph.ext fun x ↦ by rw [slice_apply, slice_apply, pullbackParam_apply]

/-- The pullback `Φ.pullbackParam hΦ hπ` fixes `(q, x)` at time `t` if `Φ` fixes `(π q, x)` at
time `t`. -/
theorem pullbackParam_apply_eq_self {t : unitInterval} {q : S} {x : M}
    (h : Φ (t, (π q, x)) = (π q, x)) : Φ.pullbackParam hΦ hπ (t, (q, x)) = (q, x) := by
  rw [pullbackParam_apply, h]

end pullbackParam

end TauCeti.Diffeotopy

end
