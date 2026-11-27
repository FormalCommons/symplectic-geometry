/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.Topology.Homotopy.Equiv
public import SymplecticGeometry.Topology.Sets.Annulus
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Open annuli up to homotopy

For a real normed space `E`, this file shows that the open annulus `a < ‖x‖ < b` is path
connected when `0 ≤ a < b` and `E` has dimension at least two, and that for `0 ≤ a' ≤ a < b`
the inclusion of the annulus `a < ‖x‖ < b` into the annulus `a' < ‖x‖ < b` is a homotopy
equivalence. A homotopy inverse pushes each point radially out to norm at least `m = (a + b) / 2`,
`x ↦ max 1 (m / ‖x‖) • x`, and both composites are homotopic to the identity by the straight-line
homotopy, which moves each point along its ray between norms `‖x‖` and `max ‖x‖ m`.

## Main results

* `SymplecticGeometry.isPathConnected_annulus`: the annulus is path connected.
* `SymplecticGeometry.annulusHomotopyEquiv`: the inclusion of `annulus E a b` into
  `annulus E a' b` as a homotopy equivalence, with `SymplecticGeometry.annulusHomotopyEquiv_toFun`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, Chapter 0 (deformation retractions).
-/

public section

open Set unitInterval

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For `0 ≤ a < b`, the open annulus `a < ‖x‖ < b` of a real normed space of dimension at least
two is path connected. -/
theorem isPathConnected_annulus (h : 1 < Module.rank ℝ E) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    IsPathConnected (annulus E a b : Set E) := by
  have hS := (isPathConnected_sphere h (0 : E) zero_le_one).prod
    ((convex_Ioo a b).isPathConnected (nonempty_Ioo.2 hab))
  convert hS.image (f := fun p : E × ℝ ↦ p.2 • p.1) (by fun_prop) using 1
  ext x
  simp only [coe_annulus, mem_ofPred_eq, mem_image, Prod.exists, mem_prod, mem_sphere_iff_norm,
    sub_zero, mem_Ioo]
  refine ⟨fun hx ↦ ⟨‖x‖⁻¹ • x, ‖x‖, ⟨?_, hx⟩, ?_⟩, ?_⟩
  · have : ‖x‖ ≠ 0 := (ha.trans_lt hx.1).ne'
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ this]
  · have : ‖x‖ ≠ 0 := (ha.trans_lt hx.1).ne'
    rw [smul_smul, mul_inv_cancel₀ this, one_smul]
  · rintro ⟨u, r, ⟨hu, hr⟩, rfl⟩
    rwa [norm_smul, hu, mul_one, Real.norm_of_nonneg (ha.trans hr.1.le)]

section HomotopyEquiv

variable {a a' b c m : ℝ}

/-- The scalar `1 - t + t max 1 (m / ‖x‖)` of the straight-line homotopy from `x` to the point
`max 1 (m / ‖x‖) • x` of norm `max ‖x‖ m` on its ray. -/
private noncomputable def pushScalar (m : ℝ) (t : I) (x : E) : ℝ :=
  1 - t + t * max 1 (m / ‖x‖)

omit [NormedSpace ℝ E] in
private theorem one_le_pushScalar (m : ℝ) (t : I) (x : E) : 1 ≤ pushScalar m t x := by
  have := le_max_left 1 (m / ‖x‖)
  have := t.property.1
  unfold pushScalar
  nlinarith

private theorem norm_pushScalar_smul (m : ℝ) (t : I) {x : E} (hx : x ≠ 0) :
    ‖pushScalar m t x • x‖ = (1 - t) * ‖x‖ + t * max ‖x‖ m := by
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [norm_smul, Real.norm_of_nonneg ((zero_le_one).trans (one_le_pushScalar m t x)),
    pushScalar, add_mul, mul_assoc, max_mul_of_nonneg _ _ hx'.le, one_mul,
    div_mul_cancel₀ _ hx'.ne']

/-- For `0 ≤ c` and `m < b`, `x ↦ pushScalar m t x • x` keeps the annulus `c < ‖x‖ < b`. -/
private theorem pushScalar_smul_mem (hc : 0 ≤ c) (hm : m < b) (t : I) {x : E}
    (hx : x ∈ annulus E c b) : pushScalar m t x • x ∈ annulus E c b := by
  have hx0 := ne_zero_of_mem_annulus hc hx
  rw [mem_annulus, norm_pushScalar_smul m t hx0]
  obtain ⟨h₁, h₂⟩ := mem_annulus.1 hx
  have ht₀ := t.property.1
  have ht₁ := t.property.2
  have hmax₁ := le_max_left ‖x‖ m
  have hmax₂ : max ‖x‖ m < b := max_lt h₂ hm
  constructor <;> nlinarith

/-- The straight-line motion `(t, x) ↦ pushScalar m t x • x` on the annulus `c < ‖x‖ < b`, for
`0 ≤ c` and `m < b`. -/
private noncomputable def pushMotion (hc : 0 ≤ c) (hm : m < b) :
    C(I × annulus E c b, annulus E c b) where
  toFun p := ⟨pushScalar m p.1 (p.2 : E) • (p.2 : E), pushScalar_smul_mem hc hm p.1 p.2.property⟩
  continuous_toFun := by
    have h0 : ∀ p : I × annulus E c b, ‖(p.2 : E)‖ ≠ 0 := fun p ↦
      norm_ne_zero_iff.2 (ne_zero_of_mem_annulus hc p.2.property)
    refine Continuous.subtype_mk ?_ _
    unfold pushScalar
    fun_prop (disch := exact h0 _)

/-- The straight-line homotopy on the annulus `c < ‖x‖ < b` from the identity to the radial push
`x ↦ max 1 (m / ‖x‖) • x`, for `0 ≤ c` and `m < b`. -/
private noncomputable def pushHomotopy (hc : 0 ≤ c) (hm : m < b) :
    (ContinuousMap.id (annulus E c b)).Homotopy
      ((pushMotion hc hm).comp ((ContinuousMap.const _ 1).prodMk (ContinuousMap.id _))) where
  toFun := pushMotion hc hm
  continuous_toFun := (pushMotion hc hm).continuous
  map_zero_left x := Subtype.ext (by simp [pushMotion, pushScalar])
  map_one_left _ := rfl

/-- For `0 ≤ a' ≤ a < b`, the inclusion of the annulus `a < ‖x‖ < b` into the annulus
`a' < ‖x‖ < b`, as a homotopy equivalence. -/
noncomputable def annulusHomotopyEquiv (ha' : 0 ≤ a') (h : a' ≤ a) (hab : a < b) :
    ContinuousMap.HomotopyEquiv (annulus E a b) (annulus E a' b) where
  toFun := ContinuousMap.inclusion (annulus_mono h le_rfl)
  invFun :=
    { toFun x := ⟨pushScalar ((a + b) / 2) 1 (x : E) • (x : E), by
        have hx0 := ne_zero_of_mem_annulus ha' x.property
        rw [mem_annulus, norm_pushScalar_smul _ 1 hx0]
        simp only [Icc.coe_one, sub_self, zero_mul, one_mul, zero_add]
        exact ⟨(by linarith : a < (a + b) / 2).trans_le (le_max_right _ _),
          max_lt (mem_annulus.1 x.property).2 (by linarith)⟩⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact continuous_subtypeVal.comp ((pushMotion ha' (by linarith : (a + b) / 2 < b)).comp
          ((ContinuousMap.const _ 1).prodMk (ContinuousMap.id _))).continuous }
  left_inv := ⟨(pushHomotopy (ha'.trans h) (by linarith : (a + b) / 2 < b)).symm.cast
    (by ext; rfl) rfl⟩
  right_inv := ⟨(pushHomotopy ha' (by linarith : (a + b) / 2 < b)).symm.cast
    (by ext; rfl) rfl⟩

@[simp]
theorem annulusHomotopyEquiv_toFun (ha' : 0 ≤ a') (h : a' ≤ a) (hab : a < b) :
    (annulusHomotopyEquiv (E := E) ha' h hab).toFun =
      ContinuousMap.inclusion (annulus_mono (E := E) h (le_refl b)) :=
  (rfl)

end HomotopyEquiv

end SymplecticGeometry

end
