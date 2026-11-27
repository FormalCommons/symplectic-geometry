/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.LinearCombination
import SymplecticGeometry.LinearAlgebra.BilinearForm.Nondegenerate

/-!
# Adding a large multiple of a pulled-back form

Let `τ` be an alternating bilinear form on `V`, `L : V →ₗ U` a surjective linear map and `β` a
nondegenerate alternating form on `U`, and write `P = β.comp L L` for the pull-back of `β`
along `L`. Suppose that `τ` restricts to a nondegenerate form on `ker L`. This file shows that
`τ + c • P` is nondegenerate for all large `c`, which is the linear algebra of step 2 in the proof
of Thurston's theorem on symplectic fibrations (McDuff–Salamon, Theorem 6.1.4): there `V` is a
tangent space of the total space, `U` the tangent space of the base and `L` the differential of
the projection.

## Main results

* `LinearMap.BilinForm.nondegenerate_add_smul_comp_iff`: the `τ`-orthogonal `H` of `ker L`
  is a complement of `ker L` (Mathlib's `isCompl_orthogonal_of_restrict_nondegenerate`), and
  `τ + c • P` is block diagonal for `H ⊕ ker L` and agrees with `τ` on `ker L`; so it is
  nondegenerate exactly when its restriction to `H` is.
* `LinearMap.BilinForm.nondegenerate_restrict_orthogonal_ker_comp`: `P` is nondegenerate on
  `H`.
* `LinearMap.BilinForm.pullbackProd τ β L s`: the form
  `((u, a), (v, b)) ↦ τ u v + β (L u) b + β a (L v) - s * β a b` on `V × U`. For `s ≠ 0` it is
  nondegenerate exactly when `τ + s⁻¹ • P` is
  (`LinearMap.BilinForm.nondegenerate_pullbackProd_iff_of_ne_zero`), and for `s = 0` exactly
  when `τ` is nondegenerate on `ker L` (`LinearMap.BilinForm.nondegenerate_pullbackProd_zero_iff`).
  Since it depends continuously on `s`, its nondegeneracy at `s = 0` spreads to a neighbourhood
  of `0` (`LinearMap.BilinForm.eventually_nondegenerate_pullbackProd`); this is the form in which
  a bound can be made uniform over a compact family.
* `LinearMap.BilinForm.exists_forall_ge_nondegenerate_add_smul_comp`: over `ℝ`, there is `c₀`
  with `τ + c • P` nondegenerate for all `c ≥ c₀`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 6.1.4
* [V. Guillemin, E. Lerman and S. Sternberg, *Symplectic Fibrations and Multiplicity
  Diagrams*][GuilleminLermanSternberg1996], §1.5
-/

public section

open Filter Topology
open LinearMap (BilinForm)

namespace LinearMap.BilinForm

section CommSemiring

variable {R V U : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V] [AddCommMonoid U]
  [Module R U]

/-- The pull-back of a reflexive bilinear form along a linear map is reflexive. -/
theorem IsRefl.comp {β : BilinForm R U} (hβ : β.IsRefl) (L : V →ₗ[R] U) :
    (β.comp L L).IsRefl :=
  fun x y h ↦ by simpa using hβ (L x) (L y) (by simpa using h)

/-- The pull-back of an alternating bilinear form along a linear map is alternating. -/
theorem IsAlt.comp {β : BilinForm R U} (hβ : β.IsAlt) (L : V →ₗ[R] U) :
    (β.comp L L).IsAlt :=
  fun x ↦ by simpa using hβ.self_eq_zero (L x)

/-- Adding a multiple of a form pulled back along `L` does not change the restriction to
`ker L`. -/
@[simp]
theorem restrict_ker_add_smul_comp (τ : BilinForm R V) (β : BilinForm R U) (L : V →ₗ[R] U)
    (c : R) : (τ + c • β.comp L L).restrict (LinearMap.ker L) = τ.restrict (LinearMap.ker L) :=
  LinearMap.ext₂ fun x y ↦ by simp [LinearMap.mem_ker.1 x.property]

end CommSemiring

section CommRing

variable {R V U : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup U]
  [Module R U]

/-- The bilinear form `((u, a), (v, b)) ↦ τ u v + β (L u) b + β a (L v) - s * β a b` on
`V × U`. For `s ≠ 0` it is nondegenerate exactly when `τ + s⁻¹ • β.comp L L` is, and at
`s = 0` exactly when `τ` is nondegenerate on `ker L`. -/
noncomputable def pullbackProd (τ : BilinForm R V) (β : BilinForm R U) (L : V →ₗ[R] U) (s : R) :
    BilinForm R (V × U) :=
  τ.comp (LinearMap.fst R V U) (LinearMap.fst R V U) +
    β.comp (L ∘ₗ LinearMap.fst R V U) (LinearMap.snd R V U) +
    β.comp (LinearMap.snd R V U) (L ∘ₗ LinearMap.fst R V U) -
    s • β.comp (LinearMap.snd R V U) (LinearMap.snd R V U)

variable {τ : BilinForm R V} {β : BilinForm R U} {L : V →ₗ[R] U}

@[simp]
theorem pullbackProd_apply (τ : BilinForm R V) (β : BilinForm R U) (L : V →ₗ[R] U) (s : R)
    (x y : V × U) :
    pullbackProd τ β L s x y = τ x.1 y.1 + β (L x.1) y.2 + β x.2 (L y.1) - s * β x.2 y.2 := by
  simp [pullbackProd]

/-- `pullbackProd τ β L s` is affine in `s`. -/
theorem pullbackProd_eq_sub_smul (τ : BilinForm R V) (β : BilinForm R U) (L : V →ₗ[R] U)
    (s : R) : pullbackProd τ β L s =
      pullbackProd τ β L 0 - s • β.comp (LinearMap.snd R V U) (LinearMap.snd R V U) :=
  LinearMap.ext₂ fun x y ↦ by simp

/-- `pullbackProd τ β L s` is alternating when `τ` and `β` are. -/
theorem IsAlt.pullbackProd (hτ : τ.IsAlt) (hβ : β.IsAlt) (L : V →ₗ[R] U) (s : R) :
    (pullbackProd τ β L s).IsAlt := fun x ↦ by
  simp [hτ.self_eq_zero, hβ.self_eq_zero, ← hβ.neg_eq x.2 (L x.1)]

end CommRing

section Field

variable {𝕜 V U : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddCommGroup U] [Module 𝕜 U]
  {τ : BilinForm 𝕜 V} {β : BilinForm 𝕜 U} {L : V →ₗ[𝕜] U}

/-- If `τ` is alternating and nondegenerate on `ker L`, and `β` is alternating, then
`τ + c • β.comp L L` is nondegenerate exactly when its restriction to the `τ`-orthogonal of
`ker L` is: the form is block diagonal for this complement of `ker L`, and on `ker L` it is
`τ`. -/
theorem nondegenerate_add_smul_comp_iff [FiniteDimensional 𝕜 V] (hτ : τ.IsAlt)
    (hβ : β.IsAlt) (hτL : (τ.restrict (LinearMap.ker L)).Nondegenerate) (c : 𝕜) :
    (τ + c • β.comp L L).Nondegenerate ↔
      ((τ + c • β.comp L L).restrict (τ.orthogonal (LinearMap.ker L))).Nondegenerate := by
  have hc := τ.isCompl_orthogonal_of_restrict_nondegenerate hτ.isRefl hτL
  rw [(hτ.add ((hβ.comp L).smul c)).isRefl.nondegenerate_iff_of_isCompl hc
    fun w hw h hh ↦ ?_, restrict_ker_add_smul_comp, and_iff_right hτL]
  simp [LinearMap.mem_ker.1 hw, (mem_orthogonal_iff.1 hh) w hw]

/-- If `τ` is reflexive and nondegenerate on `ker L`, `L` is surjective and `β` is reflexive and
nondegenerate, then the pull-back `β.comp L L` is nondegenerate on the `τ`-orthogonal of
`ker L`. -/
theorem nondegenerate_restrict_orthogonal_ker_comp [FiniteDimensional 𝕜 V] (hτ : τ.IsRefl)
    (hτL : (τ.restrict (LinearMap.ker L)).Nondegenerate) (hβ : β.IsRefl)
    (hβn : β.Nondegenerate) (hL : Function.Surjective L) :
    ((β.comp L L).restrict (τ.orthogonal (LinearMap.ker L))).Nondegenerate := by
  have hc := τ.isCompl_orthogonal_of_restrict_nondegenerate hτ hτL
  rw [(hβ.comp L).nondegenerate_restrict_iff]
  intro u hu hP
  have hLu : L u = 0 := hβn.1 _ fun b ↦ by
    obtain ⟨v, rfl⟩ := hL b
    obtain ⟨w, h, hw, hh, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.1 hc.codisjoint v
    simpa [LinearMap.mem_ker.1 hw] using hP h hh
  exact Submodule.disjoint_def.1 hc.disjoint u hLu hu

/-- For `s ≠ 0`, `pullbackProd τ β L s` is nondegenerate exactly when `τ + s⁻¹ • β.comp L L`
is: its kernel is the image of the kernel of the latter under `u ↦ (u, s⁻¹ • L u)`. -/
theorem nondegenerate_pullbackProd_iff_of_ne_zero (hτ : τ.IsAlt) (hβ : β.IsAlt)
    (hβn : β.Nondegenerate) {s : 𝕜} (hs : s ≠ 0) :
    (pullbackProd τ β L s).Nondegenerate ↔ (τ + s⁻¹ • β.comp L L).Nondegenerate := by
  rw [Nondegenerate, Nondegenerate,
    (hτ.pullbackProd hβ L s).isRefl.nondegenerate_iff_separatingLeft,
    (hτ.add ((hβ.comp L).smul _)).isRefl.nondegenerate_iff_separatingLeft]
  constructor
  · intro h u hu
    refine congrArg Prod.fst (h (u, s⁻¹ • L u) fun y ↦ ?_)
    have := hu y.1
    simp only [LinearMap.add_apply, LinearMap.smul_apply, comp_apply, smul_eq_mul] at this
    simp only [pullbackProd_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    linear_combination this - β (L u) y.2 * mul_inv_cancel₀ hs
  · rintro h ⟨u, a⟩ hx
    have h1 : L u = s • a := by
      rw [← sub_eq_zero]
      refine hβn.1 _ fun b ↦ ?_
      simpa [sub_eq_add_neg] using hx (0, b)
    have hu : u = 0 := h u fun v ↦ by
      have := hx (v, 0)
      simp only [pullbackProd_apply, map_zero, add_zero, mul_zero, sub_zero] at this
      simp only [LinearMap.add_apply, LinearMap.smul_apply, comp_apply, smul_eq_mul, h1, map_smul]
      rw [inv_mul_cancel_left₀ hs, this]
    subst hu
    rw [map_zero, eq_comm, smul_eq_zero] at h1
    simp [h1.resolve_left hs]

/-- If `U` is finite-dimensional, `β` is alternating and nondegenerate and `L` is surjective,
then `pullbackProd τ β L 0` is nondegenerate exactly when `τ` is nondegenerate on `ker L`. -/
theorem nondegenerate_pullbackProd_zero_iff [FiniteDimensional 𝕜 U] (hτ : τ.IsAlt)
    (hβ : β.IsAlt) (hβn : β.Nondegenerate) (hL : Function.Surjective L) :
    (pullbackProd τ β L 0).Nondegenerate ↔ (τ.restrict (LinearMap.ker L)).Nondegenerate := by
  rw [Nondegenerate, (hτ.pullbackProd hβ L 0).isRefl.nondegenerate_iff_separatingLeft,
    hτ.isRefl.nondegenerate_restrict_iff]
  constructor
  · intro h u hu hτu
    obtain ⟨g, hg⟩ := L.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hL)
    have hg' (v : V) : τ u (g (L v)) = τ u v := by
      have hv : g (L v) - v ∈ LinearMap.ker L := by
        rw [LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply L g, hg, LinearMap.id_apply,
          sub_self]
      rw [← sub_eq_zero, ← map_sub, hτu _ hv]
    refine congrArg Prod.fst (h (u, (β.toDual hβn).symm (-(τ u ∘ₗ g))) fun y ↦ ?_)
    simp [LinearMap.mem_ker.1 hu, hg']
  · rintro h ⟨u, a⟩ hx
    have hLu : L u = 0 := hβn.1 _ fun b ↦ by simpa using hx (0, b)
    have hu : u = 0 := h u hLu fun w hw ↦ by
      simpa [LinearMap.mem_ker.1 hw] using hx (w, 0)
    subst hu
    have ha : a = 0 := hβn.1 _ fun b ↦ by
      obtain ⟨v, rfl⟩ := hL b
      simpa using hx (v, 0)
    simp [ha]

/-- Nondegeneracy of `pullbackProd τ β L s` at `s = 0` persists for all `s` near `0`. -/
theorem eventually_nondegenerate_pullbackProd [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
    [T1Space 𝕜] [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 U]
    (h : (pullbackProd τ β L 0).Nondegenerate) :
    ∀ᶠ s in 𝓝 0, (pullbackProd τ β L s).Nondegenerate := by
  let b := Module.finBasis 𝕜 (V × U)
  set M₀ := toMatrix b (pullbackProd τ β L 0) with hM₀
  set N := toMatrix b (β.comp (LinearMap.snd 𝕜 V U) (LinearMap.snd 𝕜 V U)) with hN
  have hb (s : 𝕜) : toMatrix b (pullbackProd τ β L s) = M₀ - s • N := by
    ext i j
    simp only [hM₀, hN, toMatrix_apply, pullbackProd_apply, Matrix.sub_apply, Matrix.smul_apply,
      comp_apply, LinearMap.snd_apply, smul_eq_mul]
    ring
  have hc : Continuous fun s : 𝕜 ↦ (M₀ - s • N).det := by fun_prop
  have h0 : (M₀ - (0 : 𝕜) • N).det ≠ 0 := by
    rw [zero_smul, sub_zero]
    exact (nondegenerate_iff_det_ne_zero b).1 h
  filter_upwards [hc.continuousAt.eventually_ne h0] with s hs
  rw [nondegenerate_iff_det_ne_zero b, hb]
  exact hs

end Field

section Real

variable {V U : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup U] [Module ℝ U]
  [FiniteDimensional ℝ V] [FiniteDimensional ℝ U] {τ : BilinForm ℝ V} {β : BilinForm ℝ U}
  {L : V →ₗ[ℝ] U}

/-- Let `τ` and `β` be alternating forms, `β` nondegenerate, `L` surjective, and `τ`
nondegenerate on `ker L`. Then `τ + c • β.comp L L` is nondegenerate for all large `c`. -/
theorem exists_forall_ge_nondegenerate_add_smul_comp (hτ : τ.IsAlt) (hβ : β.IsAlt)
    (hβn : β.Nondegenerate) (hL : Function.Surjective L)
    (hτL : (τ.restrict (LinearMap.ker L)).Nondegenerate) :
    ∃ c₀ : ℝ, ∀ c ≥ c₀, (τ + c • β.comp L L).Nondegenerate := by
  have h := eventually_nondegenerate_pullbackProd
    ((nondegenerate_pullbackProd_zero_iff hτ hβ hβn hL).2 hτL)
  refine eventually_atTop.1 ?_
  filter_upwards [tendsto_inv_atTop_zero.eventually h, eventually_gt_atTop 0] with c hc hc₀
  rwa [nondegenerate_pullbackProd_iff_of_ne_zero hτ hβ hβn (inv_ne_zero hc₀.ne'), inv_inv] at hc

end Real

end LinearMap.BilinForm

end
