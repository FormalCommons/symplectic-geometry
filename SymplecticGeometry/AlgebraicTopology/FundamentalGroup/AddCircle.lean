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
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange

/-!
# Free homotopies of circle maps and their based loops

Tau Ceti reads a map `f : C(AddCircle p, X)` as the loop `f.toLoop`, `t ↦ f (t * p)`, at `f 0`.
This file relates free homotopies of such maps to their loops in the fundamental group.

* A homotopy `H` from `f₀` to `f₁` carries the class of `f₀.toLoop` to that of `f₁.toLoop` under
  the change of base point along the track `H.evalAt 0` of `0`. The loop `f.toLoop` is the image
  under `f` of the loop `(ContinuousMap.id _).toLoop` of the circle, so this is Tau Ceti's
  `ContinuousMap.Homotopy.fundamentalGroupMulEquivOfPath_evalAt_map` on that loop.
* Conversely, for `0 < p` every loop `γ` at `x` is the loop of a circle map: `γ.toAddCircle p`,
  the map `t ↦ γ (t / p)` on `[0, p]` descended to `AddCircle p`, has loop `γ` itself. The
  construction, and the proof that it sends `t * p` to `γ t`, follow Tau Ceti's `Path.toCircle` and
  `Path.toCircle_unitToCircle`, which do the same for `Circle`.
* Hence, if `f i` and `g i` are freely homotopic for each `i`, and both families are brought to a
  common base point `x` by conjugating with paths, then the two families of loops at `x`
  normally generate the same subgroup of `π₁(X, x)`, whatever paths are used: each loop of one
  family is conjugate to the corresponding loop of the other.

## Main definitions

* `Path.toAddCircle`: a loop at `x`, read as a map from `AddCircle p`.

## Main results

* `ContinuousMap.Homotopy.fundamentalGroupMulEquivOfPath_evalAt_toLoop`,
  `ContinuousMap.Homotopic.exists_fundamentalGroupMulEquivOfPath_toLoop`: freely homotopic circle
  maps have loops that correspond under a change of base point.
* `ContinuousMap.toLoop_toAddCircle`: the loop of `γ.toAddCircle p` is `γ`.
* `ContinuousMap.normalClosure_range_toLoop_eq_of_homotopic`: termwise freely homotopic families
  of circle maps, conjugated to a common base point, have the same normal closure in `π₁(X, x)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, §1.1, Exercise 1.1.2 (free homotopy classes of loops and
  conjugacy classes in `π₁`).
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
  have hℓ (f : C(AddCircle p, X)) : ℓ.map f.continuous = f.toLoop := by
    ext t
    rw [Path.map_coe, Function.comp_apply, toLoop_apply]
    exact congrArg f ((toLoop_apply _ t).trans (ContinuousMap.id_apply _))
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

end ContinuousMap

namespace Path

variable [Fact (0 < p)] {x : X}

variable (p) in
/-- A loop `γ` at `x`, read as a map from the circle `AddCircle p`: the class of `s ∈ [0, p)` goes
to `γ (s / p)`. -/
def toAddCircle (γ : Path x x) : C(AddCircle p, X) where
  toFun := AddCircle.liftIco p 0 fun s ↦ γ.extend (s / p)
  continuous_toFun := AddCircle.liftIco_zero_continuous
    (by simp [div_self (Fact.out : 0 < p).ne'])
    (γ.continuous_extend.comp (continuous_id.div_const p)).continuousOn

/-- The point `t * p` of the circle goes to `γ t`. -/
@[simp]
theorem toAddCircle_apply_mul (γ : Path x x) (t : I) :
    γ.toAddCircle p ((t * p : ℝ) : AddCircle p) = γ t := by
  have hp : 0 < p := Fact.out
  rcases eq_or_lt_of_le t.property.2 with ht | ht
  · rw [show t = 1 from Subtype.ext ht, Set.Icc.coe_one, one_mul, AddCircle.coe_period,
      ← AddCircle.coe_zero (p := p), toAddCircle, ContinuousMap.coe_mk,
      AddCircle.liftIco_zero_coe_apply ⟨le_rfl, hp⟩, zero_div, γ.extend_zero, γ.target]
  · rw [toAddCircle, ContinuousMap.coe_mk, AddCircle.liftIco_zero_coe_apply
      ⟨mul_nonneg t.property.1 hp.le, by nlinarith⟩, mul_div_cancel_right₀ _ hp.ne',
      γ.extend_extends']

/-- The base point `0` of the circle goes to the base point of the loop. -/
@[simp]
theorem toAddCircle_zero (γ : Path x x) : γ.toAddCircle p 0 = x := by
  simpa using γ.toAddCircle_apply_mul (p := p) 0

end Path

namespace ContinuousMap

variable {x : X}

/-- **Every loop is the loop of a circle map.** The loop of `γ.toAddCircle p` is `γ`, read at `x`
through `γ.toAddCircle p 0 = x`. -/
theorem toLoop_toAddCircle [Fact (0 < p)] (γ : Path x x) :
    (γ.toAddCircle p).toLoop = γ.cast γ.toAddCircle_zero γ.toAddCircle_zero := by
  ext t
  simp

/-- **Free homotopies preserve the normal closure of a family of loops.** Let `f i` and `g i` be
homotopic circle maps for each `i`, and bring their loops to a common base point `x` along paths
`χ i` to `f i 0` and `ψ i` to `g i 0`. Then the loops `χ i · (f i).toLoop · (χ i)⁻¹` and
`ψ i · (g i).toLoop · (ψ i)⁻¹` normally generate the same subgroup of `π₁(X, x)`. -/
theorem normalClosure_range_toLoop_eq_of_homotopic {ι : Sort*} {f g : ι → C(AddCircle p, X)}
    (h : ∀ i, (f i).Homotopic (g i)) (χ : ∀ i, Path x (f i 0)) (ψ : ∀ i, Path x (g i 0)) :
    Subgroup.normalClosure
        (Set.range fun i ↦ fromPath (.mk ((χ i).trans ((f i).toLoop.trans (χ i).symm)))) =
      Subgroup.normalClosure
        (Set.range fun i ↦ fromPath (.mk ((ψ i).trans ((g i).toLoop.trans (ψ i).symm)))) := by
  refine Subgroup.normalClosure_range_eq_of_isConj fun i ↦ ?_
  obtain ⟨δ, hδ⟩ := (h i).exists_fundamentalGroupMulEquivOfPath_toLoop
  -- Both loops are changes of base point of the class of `(f i).toLoop`, along `(χ i)⁻¹` and
  -- along `δ · (ψ i)⁻¹`; they differ by the change of base point along the loop
  -- `χ i · δ · (ψ i)⁻¹` at `x`, which is a conjugation.
  have hℓ : fundamentalGroupMulEquivOfPath ((χ i).trans (δ.trans (ψ i).symm))
      (fromPath (.mk ((χ i).trans ((f i).toLoop.trans (χ i).symm)))) =
        fromPath (.mk ((ψ i).trans ((g i).toLoop.trans (ψ i).symm))) := by
    rw [← fundamentalGroupMulEquivOfPath_symm_fromPath_mk,
      ← fundamentalGroupMulEquivOfPath_symm_fromPath_mk, ← hδ]
    simp only [fundamentalGroupMulEquivOfPath_trans, fundamentalGroupMulEquivOfPath_symm,
      MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rw [← hℓ, fundamentalGroupMulEquivOfPath_loop_apply]
  exact isConj_iff.2 ⟨_, rfl⟩

end ContinuousMap
