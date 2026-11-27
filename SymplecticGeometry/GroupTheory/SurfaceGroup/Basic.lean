/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.GroupTheory.SurfaceGroup.Basic

/-!
# Renaming the indices of orientable surface groups

Tau Ceti's orientable surface group `TauCeti.SurfaceGroup.Orientable g m` depends on the genus `g`
and on the number `m` of peripheral elements. Equal parameters given by different terms, such as
`1 + g` and `g + 1`, give groups that are equal only up to a cast. This file gives the isomorphism
between them that sends each generator to the generator of the same index.

## Main definitions

* `TauCeti.SurfaceGroup.Orientable.congr`: for `g = g'` and `m = m'`, the isomorphism
  `S⁺(g, m) ≃* S⁺(g', m')` sending `aᵢ`, `bᵢ` and `pⱼ` to the generators of `S⁺(g', m')` with the
  same indices, carried along `Fin.cast`; its inverse, identity and composition lemmas
  `TauCeti.SurfaceGroup.Orientable.congr_symm`, `congr_refl` and `congr_trans`, and its
  composition on elements `congr_congr`.

The surface groups and their presentation are those of Tau Ceti's
`TauCeti/GroupTheory/SurfaceGroup/Basic.lean`.

It is built from the universal property `TauCeti.SurfaceGroup.Orientable.lift` in both
directions, so that its values on the generators hold without casts.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, Section 1.2.
-/

public section

namespace TauCeti

namespace SurfaceGroup

namespace Orientable

variable {g g' g'' m m' m'' : ℕ}

/-- The homomorphism `S⁺(g, m) →* S⁺(g', m')` sending each generator to the generator of the same
index, for `g = g'` and `m = m'`. It is a step of `TauCeti.SurfaceGroup.Orientable.congr`. -/
private def congrHom (hg : g = g') (hm : m = m') : Orientable g m →* Orientable g' m' :=
  lift (fun i ↦ a g' m' (Fin.cast hg i)) (fun i ↦ b g' m' (Fin.cast hg i))
    (fun j ↦ peripheral g' m' (Fin.cast hm j)) (by subst hg hm; simp)

/-- **Renaming the parameters of an orientable surface group.** For `g = g'` and `m = m'`, the
isomorphism `S⁺(g, m) ≃* S⁺(g', m')` sending `aᵢ`, `bᵢ` and `pⱼ` to the generators of `S⁺(g', m')`
of the same indices, carried along `Fin.cast`. -/
def congr (hg : g = g') (hm : m = m') : Orientable g m ≃* Orientable g' m' :=
  (congrHom hg hm).toMulEquiv (congrHom hg.symm hm.symm)
    (by ext <;> simp [congrHom]) (by ext <;> simp [congrHom])

@[simp]
theorem congr_a (hg : g = g') (hm : m = m') (i : Fin g) :
    congr hg hm (a g m i) = a g' m' (Fin.cast hg i) :=
  lift_a ..

@[simp]
theorem congr_b (hg : g = g') (hm : m = m') (i : Fin g) :
    congr hg hm (b g m i) = b g' m' (Fin.cast hg i) :=
  lift_b ..

@[simp]
theorem congr_peripheral (hg : g = g') (hm : m = m') (j : Fin m) :
    congr hg hm (peripheral g m j) = peripheral g' m' (Fin.cast hm j) :=
  lift_peripheral ..

/-- The congruence along `g = g` and `m = m` is the identity. -/
@[simp]
theorem congr_refl : congr (rfl : g = g) (rfl : m = m) = MulEquiv.refl _ :=
  MulEquiv.toMonoidHom_injective <| by ext <;> simp

/-- Two congruences compose to the congruence along the composed equalities. -/
@[simp]
theorem congr_trans (hg : g = g') (hm : m = m') (hg' : g' = g'') (hm' : m' = m'') :
    (congr hg hm).trans (congr hg' hm') = congr (hg.trans hg') (hm.trans hm') :=
  MulEquiv.toMonoidHom_injective <| by ext <;> simp

/-- Applying two congruences in turn is applying the congruence along the composed equalities. -/
@[simp]
theorem congr_congr (hg : g = g') (hm : m = m') (hg' : g' = g'') (hm' : m' = m'')
    (x : Orientable g m) :
    congr hg' hm' (congr hg hm x) = congr (hg.trans hg') (hm.trans hm') x := by
  rw [← MulEquiv.trans_apply, congr_trans]

/-- The inverse of the congruence along `g = g'` and `m = m'` is the congruence along the reversed
equalities. -/
@[simp]
theorem congr_symm (hg : g = g') (hm : m = m') : (congr hg hm).symm = congr hg.symm hm.symm :=
  MulEquiv.ext fun x ↦ by
    rw [MulEquiv.symm_apply_eq, ← MulEquiv.trans_apply, congr_trans, congr_refl,
      MulEquiv.refl_apply]

end Orientable

end SurfaceGroup

end TauCeti

end
