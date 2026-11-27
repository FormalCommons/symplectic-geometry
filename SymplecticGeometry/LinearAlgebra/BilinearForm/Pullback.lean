/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.BilinearForm.Basic
import TauCeti.Topology.Algebra.Module.BilinearForm
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
  `τ + c • P` is block diagonal for `H ⊕ ker L`
  (`LinearMap.BilinForm.add_smul_comp_eq_zero_of_mem_ker_of_mem_orthogonal` and
  `LinearMap.BilinForm.add_smul_comp_eq_zero_of_mem_orthogonal_of_mem_ker`) and agrees with `τ`
  on `ker L` (`LinearMap.BilinForm.restrict_ker_add_smul_comp`); so it is nondegenerate exactly
  when its restriction to `H` is.
* `LinearMap.BilinForm.nondegenerate_restrict_orthogonal_ker_comp`: `P` is nondegenerate on
  `H`.
* `LinearMap.BilinForm.pullbackProd τ β L s`: the form
  `((u, a), (v, b)) ↦ τ u v + β (L u) b + β a (L v) - s * β a b` on `V × U`. For `s ≠ 0` it is
  nondegenerate exactly when `τ + s⁻¹ • P` is
  (`LinearMap.BilinForm.nondegenerate_pullbackProd_iff_of_ne_zero`), and for `s = 0` exactly
  when `τ` is nondegenerate on `ker L` (`LinearMap.BilinForm.nondegenerate_pullbackProd_zero_iff`).
  Since it depends continuously on `s`, its nondegeneracy at `s = 0` spreads to a neighbourhood
  of `0` (`LinearMap.BilinForm.eventually_nondegenerate_pullbackProd`); this is the form in which
  a bound can be made uniform over a compact family. It commutes with carrying `τ`, `β` and `L`
  along linear equivalences (`LinearMap.BilinForm.pullbackProd_congr`). In finite dimensions,
  nondegeneracy also persists when `τ`, `β`, `L` and `s` vary continuously together
  (`LinearMap.BilinForm.eventually_nondegenerate_pullbackProd_of_continuousAt`).
* `LinearMap.BilinForm.exists_forall_ge_nondegenerate_add_smul_comp`: over an ordered field with
  its order topology, such as `ℝ`, there is `c₀` with `τ + c • P` nondegenerate for all `c ≥ c₀`.

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

/-- `τ + c • β.comp L L` pairs `ker L` with its `τ`-orthogonal to zero. -/
theorem add_smul_comp_eq_zero_of_mem_ker_of_mem_orthogonal (τ : BilinForm R V)
    (β : BilinForm R U) {L : V →ₗ[R] U} (c : R) {w h : V} (hw : w ∈ LinearMap.ker L)
    (hh : h ∈ τ.orthogonal (LinearMap.ker L)) : (τ + c • β.comp L L) w h = 0 := by
  simp [LinearMap.mem_ker.1 hw, mem_orthogonal_iff.1 hh w hw]

/-- If `τ` is reflexive, then `τ + c • β.comp L L` pairs the `τ`-orthogonal of `ker L` with
`ker L` to zero. -/
theorem add_smul_comp_eq_zero_of_mem_orthogonal_of_mem_ker {τ : BilinForm R V} (hτ : τ.IsRefl)
    (β : BilinForm R U) {L : V →ₗ[R] U} (c : R) {h w : V}
    (hh : h ∈ τ.orthogonal (LinearMap.ker L)) (hw : w ∈ LinearMap.ker L) :
    (τ + c • β.comp L L) h w = 0 := by
  simp [LinearMap.mem_ker.1 hw, hτ _ _ (mem_orthogonal_iff.1 hh w hw)]

end CommSemiring

section CommRing

variable {R V U : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup U]
  [Module R U]

/-- The bilinear form `((u, a), (v, b)) ↦ τ u v + β (L u) b + β a (L v) - s * β a b` on
`V × U`. When `τ` and `β` are alternating and `β` is nondegenerate, for `s ≠ 0` it is
nondegenerate exactly when `τ + s⁻¹ • β.comp L L` is, and, if moreover `U` is finite-dimensional
and `L` surjective, at `s = 0` exactly when `τ` is nondegenerate on `ker L`. -/
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

/-- `pullbackProd` commutes with carrying `τ`, `β` and `L` along linear equivalences
`e : V ≃ₗ V'` and `e' : U ≃ₗ U'`: the result is `pullbackProd τ β L s` carried along
`e.prodCongr e'`. -/
theorem pullbackProd_congr {V' U' : Type*} [AddCommGroup V'] [Module R V'] [AddCommGroup U']
    [Module R U'] (e : V ≃ₗ[R] V') (e' : U ≃ₗ[R] U') (τ : BilinForm R V) (β : BilinForm R U)
    (L : V →ₗ[R] U) (s : R) :
    pullbackProd (congr e τ) (congr e' β) (e'.toLinearMap ∘ₗ L ∘ₗ e.symm.toLinearMap) s =
      congr (e.prodCongr e') (pullbackProd τ β L s) :=
  LinearMap.ext₂ fun _ _ ↦ by simp

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
    fun w hw h hh ↦ add_smul_comp_eq_zero_of_mem_ker_of_mem_orthogonal τ β c hw hh,
    restrict_ker_add_smul_comp, and_iff_right hτL]

/-- If `τ` is reflexive and nondegenerate on `ker L`, `L` is surjective and `β` is reflexive and
nondegenerate, then the pull-back `β.comp L L` is nondegenerate on the `τ`-orthogonal of
`ker L`. -/
theorem nondegenerate_restrict_orthogonal_ker_comp [FiniteDimensional 𝕜 V] (hτ : τ.IsRefl)
    (hτL : (τ.restrict (LinearMap.ker L)).Nondegenerate) (hβ : β.IsRefl)
    (hβn : β.Nondegenerate) (hL : Function.Surjective L) :
    ((β.comp L L).restrict (τ.orthogonal (LinearMap.ker L))).Nondegenerate := by
  have hc := τ.isCompl_orthogonal_of_restrict_nondegenerate hτ hτL
  rw [IsRefl.nondegenerate_restrict_iff (B := β.comp L L) (hβ.compl₁₂ L)]
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
    ∀ᶠ s in 𝓝 0, (pullbackProd τ β L s).Nondegenerate :=
  (TauCeti.isOpen_setOf_nondegenerate (B := pullbackProd τ β L) fun v w ↦ by
    simp only [pullbackProd_apply]; fun_prop).mem_nhds h

end Field

section Ordered

variable {𝕜 V U : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
  [OrderTopology 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddCommGroup U] [Module 𝕜 U]
  [FiniteDimensional 𝕜 V] {τ : BilinForm 𝕜 V} {β : BilinForm 𝕜 U} {L : V →ₗ[𝕜] U}

/-- Over an ordered field, let `τ` and `β` be alternating forms on `V` and `U`, with `V`
finite-dimensional, `β` nondegenerate, `L` surjective, and `τ` nondegenerate on `ker L`. Then
`τ + c • β.comp L L` is nondegenerate for all large `c`. -/
theorem exists_forall_ge_nondegenerate_add_smul_comp (hτ : τ.IsAlt) (hβ : β.IsAlt)
    (hβn : β.Nondegenerate) (hL : Function.Surjective L)
    (hτL : (τ.restrict (LinearMap.ker L)).Nondegenerate) :
    ∃ c₀ : 𝕜, ∀ c ≥ c₀, (τ + c • β.comp L L).Nondegenerate := by
  have := Module.Finite.of_surjective L hL
  have h := eventually_nondegenerate_pullbackProd
    ((nondegenerate_pullbackProd_zero_iff hτ hβ hβn hL).2 hτL)
  refine eventually_atTop.1 ?_
  filter_upwards [tendsto_inv_atTop_zero.eventually h, eventually_gt_atTop 0] with c hc hc₀
  rwa [nondegenerate_pullbackProd_iff_of_ne_zero hτ hβ hβn (inv_ne_zero hc₀.ne'), inv_inv] at hc

end Ordered

section Normed

variable {X 𝕜 V U : Type*} [TopologicalSpace X] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V] [NormedAddCommGroup U]
  [NormedSpace 𝕜 U] [FiniteDimensional 𝕜 U]

/-- In finite dimensions, let the continuous bilinear forms `τ y` and `β y`, the continuous
linear map `L y` and the scalar `s y` depend on a point `y` of a topological space, continuously
at `x`. If `pullbackProd (τ x) (β x) (L x) (s x)` is nondegenerate, then so is
`pullbackProd (τ y) (β y) (L y) (s y)` for every `y` near `x`. -/
theorem eventually_nondegenerate_pullbackProd_of_continuousAt {τ : X → V →L[𝕜] V →L[𝕜] 𝕜}
    {β : X → U →L[𝕜] U →L[𝕜] 𝕜} {L : X → V →L[𝕜] U} {s : X → 𝕜} {x : X}
    (hτ : ContinuousAt τ x) (hβ : ContinuousAt β x) (hL : ContinuousAt L x)
    (hs : ContinuousAt s x)
    (h : (pullbackProd (τ x).toBilinForm (β x).toBilinForm (L x : V →ₗ[𝕜] U) (s x)).Nondegenerate) :
    ∀ᶠ y in 𝓝 x,
      (pullbackProd (τ y).toBilinForm (β y).toBilinForm (L y : V →ₗ[𝕜] U) (s y)).Nondegenerate := by
  -- Nondegeneracy is open in the space of all quadruples `(τ, β, L, s)`.
  have hO := TauCeti.isOpen_setOf_nondegenerate (B := fun q :
      (V →L[𝕜] V →L[𝕜] 𝕜) × (U →L[𝕜] U →L[𝕜] 𝕜) × (V →L[𝕜] U) × 𝕜 ↦
      pullbackProd q.1.toBilinForm q.2.1.toBilinForm (q.2.2.1 : V →ₗ[𝕜] U) q.2.2.2) fun v w ↦ by
    simp only [pullbackProd_apply, ContinuousLinearMap.toBilinForm_apply,
      ContinuousLinearMap.coe_coe]
    fun_prop
  exact (hτ.prodMk (hβ.prodMk (hL.prodMk hs))).eventually (hO.mem_nhds h)

end Normed

end LinearMap.BilinForm

end
