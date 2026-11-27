/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import TauCeti.Topology.Homotopy.AddCircle
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.Basic
import SymplecticGeometry.GroupTheory.Subgroup.NormalClosure
import SymplecticGeometry.Topology.Homotopy.AddCircle
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange

/-!
# Free homotopies of circle maps and their based loops

Tau Ceti reads a map `f : C(AddCircle p, X)` as the loop `f.toLoop`, `t ↦ f (t * p)`, at `f 0`.
This file relates free homotopies of such maps to their loops in the fundamental group.

* A homotopy `H` from `f₀` to `f₁` carries the class of `f₀.toLoop` to that of `f₁.toLoop` under
  the change of base point along the track `H.evalAt 0` of `0`. The loop `f.toLoop` is the image
  under `f` of the loop `(ContinuousMap.id _).toLoop` of the circle
  (`ContinuousMap.toLoop_comp`), so this is Tau Ceti's
  `ContinuousMap.Homotopy.fundamentalGroupMulEquivOfPath_evalAt_map` on that loop.
* Hence freely homotopic maps `f₀`, `f₁`, brought to a common base point `x` by conjugating
  their loops with paths, give conjugate classes in `π₁(X, x)`, whatever paths are used.
* So if `f i` and `g i` are freely homotopic for each `i`, the two families of loops brought to
  `x` normally generate the same subgroup of `π₁(X, x)`.

Every loop is the loop of a circle map (`ContinuousMap.toLoop_toAddCircle`, in
`SymplecticGeometry.Topology.Homotopy.AddCircle`), so these statements cover all loops.

## Main results

* `ContinuousMap.Homotopy.fundamentalGroupMulEquivOfPath_evalAt_toLoop`,
  `ContinuousMap.Homotopic.exists_fundamentalGroupMulEquivOfPath_toLoop`: freely homotopic circle
  maps have loops that correspond under a change of base point.
* `ContinuousMap.Homotopic.isConj_fromPath_toLoop`: freely homotopic circle maps, conjugated to a
  common base point, give conjugate classes in `π₁(X, x)`.
* `ContinuousMap.normalClosure_range_toLoop_eq_of_homotopic`: termwise freely homotopic families
  of circle maps, conjugated to a common base point, have the same normal closure in `π₁(X, x)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, §1.1, Exercise 6 (free homotopy classes of loops and
  conjugacy classes in `π₁`) and Exercise 2 (change of base point).
-/

public section

noncomputable section

open FundamentalGroup
open scoped unitInterval

variable {p : ℝ} {X : Type*} [TopologicalSpace X]

namespace ContinuousMap

/-- **Free homotopies of circle maps and based loops.** A homotopy `H` from `f₀` to `f₁` carries
the class of the loop of `f₀` to the class of the loop of `f₁`, under the change of base point
along the track `H.evalAt 0` of the base point `0` of the circle. -/
theorem Homotopy.fundamentalGroupMulEquivOfPath_evalAt_toLoop {f₀ f₁ : C(AddCircle p, X)}
    (H : f₀.Homotopy f₁) :
    fundamentalGroupMulEquivOfPath (H.evalAt 0) (fromPath (.mk f₀.toLoop)) =
      fromPath (.mk f₁.toLoop) := by
  -- The loop of a circle map `f` is the image under `f` of the loop `ℓ` of the identity.
  let ℓ : Path (0 : AddCircle p) 0 := (ContinuousMap.id (AddCircle p)).toLoop
  -- `f.comp (ContinuousMap.id _)` is `f` by definition, so `toLoop_comp` applies as it is.
  have hℓ (f : C(AddCircle p, X)) : ℓ.map f.continuous = f.toLoop :=
    (toLoop_comp f (ContinuousMap.id _)).symm
  have h := H.fundamentalGroupMulEquivOfPath_evalAt_map 0 (fromPath (.mk ℓ))
  rwa [TauCeti.FundamentalGroup.map_fromPath, TauCeti.FundamentalGroup.map_fromPath, hℓ, hℓ] at h

/-- **Loops of freely homotopic circle maps correspond under a change of base point.** If `f₀` and
`f₁` are homotopic, the change of base point along some path from `f₀ 0` to `f₁ 0` carries the
class of the loop of `f₀` to the class of the loop of `f₁`. -/
theorem Homotopic.exists_fundamentalGroupMulEquivOfPath_toLoop {f₀ f₁ : C(AddCircle p, X)}
    (h : f₀.Homotopic f₁) :
    ∃ γ : Path (f₀ 0) (f₁ 0),
      fundamentalGroupMulEquivOfPath γ (fromPath (.mk f₀.toLoop)) = fromPath (.mk f₁.toLoop) :=
  let ⟨H⟩ := h
  ⟨H.evalAt 0, H.fundamentalGroupMulEquivOfPath_evalAt_toLoop⟩

variable {x : X}

/-- **Freely homotopic circle maps give conjugate loops.** If `f₀` and `f₁` are homotopic, and
their loops are brought to a common base point `x` along paths `χ` to `f₀ 0` and `ψ` to `f₁ 0`,
then the classes of `χ · f₀.toLoop · χ⁻¹` and `ψ · f₁.toLoop · ψ⁻¹` are conjugate in
`π₁(X, x)`. -/
theorem Homotopic.isConj_fromPath_toLoop {f₀ f₁ : C(AddCircle p, X)} (h : f₀.Homotopic f₁)
    (χ : Path x (f₀ 0)) (ψ : Path x (f₁ 0)) :
    IsConj (fromPath (.mk (χ.trans (f₀.toLoop.trans χ.symm))))
      (fromPath (.mk (ψ.trans (f₁.toLoop.trans ψ.symm)))) := by
  obtain ⟨δ, hδ⟩ := h.exists_fundamentalGroupMulEquivOfPath_toLoop
  -- Both loops are changes of base point of the class of `f₀.toLoop`, along `χ⁻¹` and along
  -- `δ · ψ⁻¹`; they differ by the change of base point along the loop `χ · δ · ψ⁻¹` at `x`,
  -- which is a conjugation.
  have hℓ : fundamentalGroupMulEquivOfPath (χ.trans (δ.trans ψ.symm))
      (fromPath (.mk (χ.trans (f₀.toLoop.trans χ.symm)))) =
        fromPath (.mk (ψ.trans (f₁.toLoop.trans ψ.symm))) := by
    rw [← fundamentalGroupMulEquivOfPath_symm_fromPath_mk,
      ← fundamentalGroupMulEquivOfPath_symm_fromPath_mk, ← hδ]
    simp only [fundamentalGroupMulEquivOfPath_trans, fundamentalGroupMulEquivOfPath_symm,
      MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rw [← hℓ, fundamentalGroupMulEquivOfPath_loop_apply]
  exact isConj_iff.2 ⟨_, rfl⟩

/-- **Free homotopies preserve the normal closure of a family of loops.** Let `f i` and `g i` be
homotopic circle maps for each `i`, and bring their loops to a common base point `x` along paths
`χ i` to `f i 0` and `ψ i` to `g i 0`. Then the loops `χ i · (f i).toLoop · (χ i)⁻¹` and
`ψ i · (g i).toLoop · (ψ i)⁻¹` normally generate the same subgroup of `π₁(X, x)`. -/
theorem normalClosure_range_toLoop_eq_of_homotopic {ι : Sort*} {f g : ι → C(AddCircle p, X)}
    (h : ∀ i, (f i).Homotopic (g i)) (χ : ∀ i, Path x (f i 0)) (ψ : ∀ i, Path x (g i 0)) :
    Subgroup.normalClosure
        (Set.range fun i ↦ fromPath (.mk ((χ i).trans ((f i).toLoop.trans (χ i).symm)))) =
      Subgroup.normalClosure
        (Set.range fun i ↦ fromPath (.mk ((ψ i).trans ((g i).toLoop.trans (ψ i).symm)))) :=
  Subgroup.normalClosure_range_eq_of_isConj fun i ↦ (h i).isConj_fromPath_toLoop (χ i) (ψ i)

end ContinuousMap
