/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
import TauCeti.Geometry.Manifold.Flow.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Time changes along a complete flow

Let `φ` be the flow of a complete `C¹` vector field `v` on a Hausdorff boundaryless manifold
`M`, and `τ : M → ℝ` a bounded differentiable function with `1 + dτ(v) > 0` everywhere. This
file shows that the time change `Ψ x = φ (τ x) x`, which moves each point along its own orbit for
the time `τ x`, is a diffeomorphism.

Along the orbit of `x`, `Ψ (φ t x) = φ (t + τ (φ t x)) x`, and the reparametrization
`t ↦ t + τ (φ t x)` has derivative `1 + dτ(v)` at `φ t x`. So it is strictly increasing, and it
is onto `ℝ` because `τ` is bounded. This makes `Ψ` bijective: if `Ψ a = Ψ b`, then
`b = φ s a` with `s = τ a - τ b`, and the reparametrization along the orbit of `a` takes the same
value `τ a` at `s` and at `0`. The differential of `Ψ` is `dφ_{τ x} ∘ (id + dτ ⊗ v)`, since the
time-`t` map preserves `v`, and `id + dτ ⊗ v` is injective where `1 + dτ(v) ≠ 0`. So in finite
dimension `Ψ` is a local diffeomorphism by Tau Ceti's inverse function theorem
(`TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv`), hence a diffeomorphism.

The hypothesis holds for every multiple `c • τ` with `c ∈ [0, 1]`, since `1 + c dτ(v)` is a convex
combination of `1` and `1 + dτ(v)`; so each `c • τ` gives a time change that is a diffeomorphism
too, joining the identity (`c = 0`) to `Ψ` (`c = 1`). A continuous `τ` with compact support is
bounded, so all of this applies to it. This time change varies the time from point to point;
it differs from Tau Ceti's `Flow.timeChange`, which multiplies the time by a constant.

## Main results

* `Flow.surjective_add_apply`: for any flow `φ` of `ℝ` and continuous bounded `τ`, the
  reparametrization `t ↦ t + τ (φ t x)` of an orbit is onto `ℝ`.
* `Flow.bijective_apply_self`: for any flow `φ` of `ℝ`, the time change `x ↦ φ (τ x) x` is
  bijective if each reparametrization `t ↦ t + τ (φ t x)` is.
* `TauCeti.hasDerivAt_add_apply_globalFlow`: the derivative of `t ↦ t + τ (φ t x)`.
* `TauCeti.strictMono_add_apply_globalFlow`: the reparametrization is strictly increasing.
* `TauCeti.bijective_globalFlow_timeChange`: the time change is bijective.
* `TauCeti.injective_mfderiv_globalFlow_timeChange`: its differential is injective, and
  `TauCeti.isLocalDiffeomorph_globalFlow_timeChange`: it is a local diffeomorphism.
* `TauCeti.globalFlowTimeChangeDiffeomorph`: the time change of a complete `C^n` field (`1 ≤ n`)
  for a `C^n` time `τ`, as a `C^n` diffeomorphism; `TauCeti.globalFlowTimeChangeDiffeomorph_apply`
  gives its value.
* `TauCeti.one_add_mvfderiv_const_smul_pos`: the hypothesis `1 + dτ(v) > 0` passes to `c • τ` for
  `c ∈ [0, 1]`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Theorem 3.1 (moving sublevels along the flow of a rescaled gradient field).
-/

public section

open Set Function
open scoped Manifold ContDiff

namespace Flow

variable {M : Type*} [TopologicalSpace M] (ϕ : Flow ℝ M) {τ : M → ℝ}

/-- If `τ` is continuous and bounded, the reparametrization `s ↦ s + τ (ϕ s x)` of the orbit of
`x` is onto `ℝ`. -/
theorem surjective_add_apply (hτ : Continuous τ) (hτb : Bornology.IsBounded (range τ)) (x : M) :
    Surjective (fun s ↦ s + τ (ϕ s x)) := by
  obtain ⟨C, hC⟩ := hτb.subset_closedBall 0
  have hle (y : M) : |τ y| ≤ C := by simpa using hC (mem_range_self y)
  intro r
  have hcont : Continuous (fun s ↦ s + τ (ϕ s x)) :=
    continuous_id.add (hτ.comp (ϕ.continuous continuous_id continuous_const))
  refine intermediate_value_univ (r - C) (r + C) hcont ⟨?_, ?_⟩
  · linarith [(abs_le.1 (hle (ϕ (r - C) x))).2]
  · linarith [(abs_le.1 (hle (ϕ (r + C) x))).1]

/-- If the reparametrization `s ↦ s + τ (ϕ s x)` of every orbit is a bijection of `ℝ`, then the
time change `x ↦ ϕ (τ x) x` is a bijection of `M`. -/
theorem bijective_apply_self (hinj : ∀ x, Injective (fun s ↦ s + τ (ϕ s x)))
    (hsurj : ∀ x, Surjective (fun s ↦ s + τ (ϕ s x))) : Bijective (fun x ↦ ϕ (τ x) x) := by
  refine ⟨fun a b hab ↦ ?_, fun y ↦ ?_⟩
  · -- `b` lies on the orbit of `a`, at time `s = τ a - τ b`.
    have hb : b = ϕ (τ a - τ b) a := by
      rw [sub_eq_neg_add, Flow.map_add, ← show ϕ (τ b) b = ϕ (τ a) a from hab.symm,
        ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
    have hs : τ a - τ b = 0 := by
      refine hinj a ?_
      simp only [← hb, Flow.map_zero_apply]
      ring
    rw [hb, hs, Flow.map_zero_apply]
  · obtain ⟨t, ht⟩ := hsurj y 0
    refine ⟨ϕ t y, ?_⟩
    simp only at ht ⊢
    rw [← Flow.map_add, add_comm, ht, Flow.map_zero_apply]

end Flow

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x}
  (hv : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
  (hcomplete : IsCompleteVectorField v) {τ : M → ℝ}

omit [CompleteSpace E] [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M] in
/-- If `1 + dτ(v) > 0` at `y`, then `1 + d(c • τ)(v) > 0` at `y` for every `c ∈ [0, 1]`, since
it is a convex combination of `1` and `1 + dτ(v)`. -/
theorem one_add_mvfderiv_const_smul_pos {y : M} {c : ℝ} (hc : c ∈ Icc 0 1)
    (hpos : 0 < 1 + mvfderiv I τ y (v y)) : 0 < 1 + mvfderiv I (c • τ) y (v y) := by
  rw [mvfderiv_const_smul_field, smul_apply, smul_eq_mul]
  rcases hc.2.lt_or_eq with hc1 | rfl
  · nlinarith [hc.1]
  · rwa [one_mul]

include hv hcomplete

/-- The reparametrization `t ↦ t + τ (φ t x)` of the orbit of `x` has derivative `1 + dτ(v)` at
`φ t x`. -/
theorem hasDerivAt_add_apply_globalFlow (hτ : MDifferentiable I 𝓘(ℝ) τ) (t : ℝ) (x : M) :
    HasDerivAt (fun s ↦ s + τ (globalFlow v hv hcomplete s x))
      (1 + mvfderiv I τ (globalFlow v hv hcomplete t x) (v (globalFlow v hv hcomplete t x))) t := by
  rw [← flowOf_eq_globalFlow hv hcomplete]
  exact (hasDerivAt_id t).add
    (hasDerivAt_comp_flowOf hv (hcomplete.mem_flowDomain t x) (hτ _))

/-- If `1 + dτ(v) > 0` everywhere, the reparametrization `t ↦ t + τ (φ t x)` of each orbit is
strictly increasing. -/
theorem strictMono_add_apply_globalFlow (hτ : MDifferentiable I 𝓘(ℝ) τ)
    (hpos : ∀ y, 0 < 1 + mvfderiv I τ y (v y)) (x : M) :
    StrictMono (fun s ↦ s + τ (globalFlow v hv hcomplete s x)) :=
  strictMono_of_deriv_pos fun t ↦
    (hasDerivAt_add_apply_globalFlow hv hcomplete hτ t x).deriv ▸ hpos _

/-- **The time change along a complete flow is bijective.** If `τ` is differentiable and bounded
and `1 + dτ(v) > 0` everywhere, then `x ↦ φ (τ x) x` is a bijection of `M`. -/
theorem bijective_globalFlow_timeChange (hτ : MDifferentiable I 𝓘(ℝ) τ)
    (hτb : Bornology.IsBounded (range τ)) (hpos : ∀ y, 0 < 1 + mvfderiv I τ y (v y)) :
    Bijective (fun x ↦ globalFlow v hv hcomplete (τ x) x) :=
  (globalFlow v hv hcomplete).bijective_apply_self
    (fun x ↦ (strictMono_add_apply_globalFlow hv hcomplete hτ hpos x).injective)
    ((globalFlow v hv hcomplete).surjective_add_apply hτ.continuous hτb)

/-- **The differential of a time change.** If `τ` is differentiable at `x` and
`1 + dτ(v) ≠ 0` at `x`, the differential at `x` of the time change `z ↦ φ (τ z) z` is
injective. -/
theorem injective_mfderiv_globalFlow_timeChange {x : M}
    (hτ : MDifferentiableAt I 𝓘(ℝ) τ x) (hx : 1 + mvfderiv I τ x (v x) ≠ 0) :
    Injective (mfderiv I I (fun z ↦ globalFlow v hv hcomplete (τ z) z) x) := by
  rw [← flowOf_eq_globalFlow hv hcomplete]
  -- The differential is `dφ_{τ x} ∘ (id + dτ ⊗ v)`, since `dφ_{τ x}` carries `v x` to `v (Ψ x)`.
  have hd (w : TangentSpace I x) :
      mfderiv I I (fun z ↦ flowOf v (τ z) z) x w =
        mfderiv I I (flowOf v (τ x)) x (mvfderiv I τ x w • v x + w) := by
    have h := mfderiv_flowOf_comp_prodMk_apply (f := id) hv hτ mdifferentiableAt_id
      (hcomplete.mem_flowDomain _ _) w
    rw [mfderiv_id, ContinuousLinearMap.id_apply] at h
    rw [map_add, map_smul, mfderiv_flowOf_apply_self hv (hcomplete.mem_flowDomain _ _)]
    exact h
  refine (injective_iff_map_eq_zero _).2 fun w hw ↦ ?_
  have h0 : mvfderiv I τ x w • v x + w = 0 :=
    injective_mfderiv_flowOf hv hcomplete (τ x) x (by rw [← hd, map_zero]; exact hw)
  -- Applying `dτ` gives `dτ(w) (1 + dτ(v)) = 0`, so `dτ(w) = 0`, and then `w = 0`.
  have h1 : mvfderiv I τ x w * (1 + mvfderiv I τ x (v x)) = 0 := by
    have := congrArg (mvfderiv I τ x) h0
    rw [map_add, map_smul, map_zero, smul_eq_mul] at this
    linarith
  have h2 : mvfderiv I τ x w = 0 := (mul_eq_zero.1 h1).resolve_right hx
  simpa [h2] using h0

omit hv in
/-- **A time change along a complete flow is a local diffeomorphism.** Let `v` be a complete
`C^n` vector field, `1 ≤ n`, on a finite-dimensional Hausdorff boundaryless manifold, with flow
`φ`, and `τ` a `C^n` function with `1 + dτ(v) ≠ 0` everywhere. Then `x ↦ φ (τ x) x` is a `C^n`
local diffeomorphism. -/
theorem isLocalDiffeomorph_globalFlow_timeChange [FiniteDimensional ℝ E] {n : ℕ∞} (hn : 1 ≤ n)
    [IsManifold I n M] (hvn : ContMDiff I I.tangent n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hτ : ContMDiff I 𝓘(ℝ) n τ) (hne : ∀ y, 1 + mvfderiv I τ y (v y) ≠ 0) :
    IsLocalDiffeomorph I I n
      (fun x ↦ globalFlow v (hvn.of_le (by exact_mod_cast hn)) hcomplete (τ x) x) := fun x ↦
  isLocalDiffeomorphAt_of_injective_mfderiv (s := univ)
    ((contMDiff_globalFlow_uncurry hcomplete hn hvn).comp (hτ.prodMk contMDiff_id)).contMDiffOn
    isOpen_univ (mem_univ x) BoundarylessManifold.isInteriorPoint (by exact_mod_cast hn)
    (injective_mfderiv_globalFlow_timeChange _ hcomplete
      ((hτ.mdifferentiable (by exact_mod_cast (zero_lt_one.trans_le hn).ne')) x) (hne x)) rfl

omit hv in
/-- **A time change along a complete flow is a diffeomorphism.** Let `v` be a complete `C^n`
vector field, `1 ≤ n`, on a finite-dimensional Hausdorff boundaryless manifold, with flow `φ`, and
`τ` a bounded `C^n` function with `1 + dτ(v) > 0` everywhere. Then `x ↦ φ (τ x) x` is a `C^n`
diffeomorphism of `M` (`globalFlowTimeChangeDiffeomorph_apply`). -/
noncomputable def globalFlowTimeChangeDiffeomorph [FiniteDimensional ℝ E] {n : ℕ∞} (hn : 1 ≤ n)
    [IsManifold I n M] (hvn : ContMDiff I I.tangent n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hτ : ContMDiff I 𝓘(ℝ) n τ) (hτb : Bornology.IsBounded (range τ))
    (hpos : ∀ y, 0 < 1 + mvfderiv I τ y (v y)) : M ≃ₘ^n⟮I, I⟯ M :=
  (isLocalDiffeomorph_globalFlow_timeChange hcomplete hn hvn hτ fun y ↦ (hpos y).ne')
    |>.diffeomorphOfBijective <| bijective_globalFlow_timeChange _ hcomplete
      (hτ.mdifferentiable (by exact_mod_cast (zero_lt_one.trans_le hn).ne')) hτb hpos

omit hv in
/-- The diffeomorphism `globalFlowTimeChangeDiffeomorph` moves `x` along the flow for time
`τ x`. -/
@[simp]
theorem globalFlowTimeChangeDiffeomorph_apply [FiniteDimensional ℝ E] {n : ℕ∞} (hn : 1 ≤ n)
    [IsManifold I n M] (hvn : ContMDiff I I.tangent n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hτ : ContMDiff I 𝓘(ℝ) n τ) (hτb : Bornology.IsBounded (range τ))
    (hpos : ∀ y, 0 < 1 + mvfderiv I τ y (v y)) (x : M) :
    globalFlowTimeChangeDiffeomorph hcomplete hn hvn hτ hτb hpos x =
      globalFlow v (hvn.of_le (by exact_mod_cast hn)) hcomplete (τ x) x := by
  rw [globalFlowTimeChangeDiffeomorph, IsLocalDiffeomorph.coe_diffeomorphOfBijective]

end TauCeti

end
