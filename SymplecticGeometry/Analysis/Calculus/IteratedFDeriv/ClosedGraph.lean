/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Separation.Regular

/-!
# Derivative bounds for linear families of `Cʲ` functions

Let `X` be a Banach space and `x ↦ f x` a family of functions `E → F`, linear in `x` on an open set
`s`, each of class `Cʲ` on `s`. If the values of `f x` are bounded on every compact subset of `s`
by a constant multiple of `‖x‖`, then so are its derivatives up to order `j`
(`SymplecticGeometry.exists_forall_norm_iteratedFDeriv_le`).

The proof is the closed graph theorem, applied order by order. Fix an open `U` with compact closure
`L ⊆ s` around the compact set. The map sending `x` to the derivative of order `m + 1` of `f x` on
`L`, a linear map into the Banach space of bounded continuous functions on `L`, has a closed graph
once the derivatives of order `m` are bounded: uniform convergence of the derivatives of order
`m + 1` on `U`, with pointwise convergence of those of order `m`, identifies the limit as the
derivative (`hasFDerivAt_of_tendstoUniformlyOn`), and continuous functions on `L` that agree on `U`
are equal. The closed graph step is stated on its own for any linear family of continuous
functions on a compact set (`SymplecticGeometry.exists_norm_le_of_tendstoUniformly`).

## References

* W. Rudin, *Functional Analysis*, 2nd ed., McGraw-Hill (1991), Theorem 2.15 (the closed
  graph theorem).
* W. Rudin, *Principles of Mathematical Analysis*, 3rd ed., McGraw-Hill (1976), Theorem 7.17
  (uniform limits of derivatives).
-/

public section

open Filter Set Topology
open scoped BoundedContinuousFunction

namespace SymplecticGeometry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The closed graph theorem for linear families of continuous functions.** Let `h x`, for `x`
in a Banach space `X`, be functions that are continuous on a compact set `L` and depend linearly
on `x` at each point of `L`. If, whenever `u n → x` and `h (u n)` converge uniformly on `L` to some
`φ`, the limit `φ` is `h x` on `L`, then the values of `h x` on `L` are bounded by a constant
multiple of `‖x‖`. -/
theorem exists_norm_le_of_tendstoUniformly {Y : Type*} [TopologicalSpace Y] {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] {L : Set Y} [CompactSpace L]
    (h : X → Y → H)
    (hc : ∀ x, ContinuousOn (h x) L)
    (hadd : ∀ x x', ∀ y ∈ L, h (x + x') y = h x y + h x' y)
    (hsmul : ∀ (c : ℝ) x, ∀ y ∈ L, h (c • x) y = c • h x y)
    (hclosed : ∀ (u : ℕ → X) (x : X) (φ : L → H), Tendsto u atTop (𝓝 x) →
      TendstoUniformly (fun n (y : L) ↦ h (u n) y) φ atTop → ∀ y : L, φ y = h x y) :
    ∃ C, ∀ x, ∀ y ∈ L, ‖h x y‖ ≤ C * ‖x‖ := by
  let T : X →ₗ[ℝ] (L →ᵇ H) :=
    { toFun x := .mkOfCompact ⟨L.domRestrict (h x), (hc x).domRestrict⟩
      map_add' x x' := by
        ext y
        simpa only [BoundedContinuousFunction.mkOfCompact_apply, FunLike.coe_add, Pi.add_apply,
          ContinuousMap.coe_mk, Set.domRestrict_apply] using hadd x x' y y.property
      map_smul' c x := by
        ext y
        simpa only [BoundedContinuousFunction.mkOfCompact_apply, FunLike.coe_smul, Pi.smul_apply,
          RingHom.id_apply, ContinuousMap.coe_mk, Set.domRestrict_apply] using
            hsmul c x y y.property }
  have hT (x : X) (y : L) : T x y = h x y := by
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk, BoundedContinuousFunction.mkOfCompact_apply,
      ContinuousMap.coe_mk, Set.domRestrict_apply]
  have hTc : Continuous T := T.continuous_of_seq_closed_graph fun u x φ hu hφ ↦ by
    have hφ' := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1 hφ
    simp only [Function.comp_apply] at hφ'
    ext y
    rw [hclosed u x φ hu hφ' y, hT]
  refine ⟨‖(⟨T, hTc⟩ : X →L[ℝ] (L →ᵇ H))‖, fun x y hy ↦ ?_⟩
  calc ‖h x y‖ = ‖(⟨T, hTc⟩ : X →L[ℝ] (L →ᵇ H)) x ⟨y, hy⟩‖ := by
        rw [ContinuousLinearMap.coe_mk', hT]
    _ ≤ ‖(⟨T, hTc⟩ : X →L[ℝ] (L →ᵇ H)) x‖ := BoundedContinuousFunction.norm_coe_le_norm _ _
    _ ≤ _ := ContinuousLinearMap.le_opNorm _ x

/-- **Bounds for derivatives from bounds for values.** Let `g x`, for `x` in a Banach space `X`,
be functions on `E` that depend linearly on `x` on the closure of an open set `U`, which is
compact, with derivatives `g' x` on `U` that are continuous and linear in `x` on the closure. If the
values of `g x` on the closure of `U` are bounded by a constant multiple of `‖x‖`, then so are the
derivatives `g' x`. -/
private theorem exists_norm_fderiv_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {U : Set E} (hU : IsOpen U) [CompactSpace (closure U)]
    (g : X → E → G) (g' : X → E → E →L[ℝ] G)
    (hg : ∀ x, ∀ y ∈ U, HasFDerivAt (g x) (g' x y) y)
    (hc : ∀ x, ContinuousOn (g' x) (closure U))
    (hadd : ∀ x x', ∀ y ∈ closure U, g (x + x') y = g x y + g x' y)
    (hadd' : ∀ x x', ∀ y ∈ closure U, g' (x + x') y = g' x y + g' x' y)
    (hsmul' : ∀ (c : ℝ) x, ∀ y ∈ closure U, g' (c • x) y = c • g' x y)
    (h0 : ∃ C, ∀ x, ∀ y ∈ closure U, ‖g x y‖ ≤ C * ‖x‖) :
    ∃ C, ∀ x, ∀ y ∈ closure U, ‖g' x y‖ ≤ C * ‖x‖ := by
  classical
  obtain ⟨C, hC⟩ := h0
  refine exists_norm_le_of_tendstoUniformly g' hc hadd' hsmul' fun u x φ hu hφ ↦ ?_
  let φ' : E → E →L[ℝ] G := fun y ↦ if hy : y ∈ closure U then φ ⟨y, hy⟩ else 0
  -- On `U`, the limit `φ` is the derivative of `g x`.
  have hU' : ∀ y (hy : y ∈ U), φ ⟨y, subset_closure hy⟩ = g' x y := by
    intro y hy
    have hD : HasFDerivAt (g x) (φ' y) y := by
      refine hasFDerivAt_of_tendstoUniformlyOn (l := atTop) (f := fun n ↦ g (u n))
        (f' := fun n ↦ g' (u n))
        hU ?_ (fun n ↦ hg (u n)) ?_ hy
      · refine Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_
        filter_upwards [Metric.tendstoUniformly_iff.1 hφ ε hε] with n hn z hz
        simpa only [φ', subset_closure hz, ↓reduceDIte] using hn ⟨z, subset_closure hz⟩
      · intro z hz
        have hzL := subset_closure hz
        have hsub (n : ℕ) : g (u n) z - g x z = g (u n - x) z := by
          rw [sub_eq_iff_eq_add, ← hadd _ _ _ hzL, sub_add_cancel]
        refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ ↦ norm_nonneg _)
          (fun n ↦ (hsub n).symm ▸ hC (u n - x) z hzL) ?_)
        simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hu).const_mul C
    have := hD.unique (hg x y hy)
    simpa only [φ', subset_closure hy, ↓reduceDIte] using this
  -- Continuous functions on `closure U` that agree on `U` are equal.
  have hd : Dense {p : closure U | (p : E) ∈ U} := Subtype.dense_iff.2 <|
    closure_mono fun y hy ↦ ⟨⟨y, subset_closure hy⟩, hy, rfl⟩
  -- `Set.domRestrict` is the composition with the coercion, which `exact` unfolds.
  have hφc : Continuous φ :=
    hφ.continuous (Frequently.of_forall fun n ↦ by exact (hc (u n)).domRestrict)
  refine congrFun (Continuous.ext_on hd hφc (hc x).domRestrict fun p hp ↦ hU' p hp)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : X → E → F} {s : Set E} {j : ℕ}

omit [NormedSpace ℝ X] [CompleteSpace X] [CompleteSpace F] in
/-- The derivatives of order at most `j` of a family of `Cʲ` functions on an open set `s` that
depends additively on the parameter at each point of `s` depend additively on it too. -/
private theorem iteratedFDeriv_add_of_mem (hs : IsOpen s) (hf : ∀ x, ContDiffOn ℝ j (f x) s)
    (hadd : ∀ x x', ∀ y ∈ s, f (x + x') y = f x y + f x' y) {m : ℕ} (hm : m ≤ j) (x x' : X)
    {y : E} (hy : y ∈ s) :
    iteratedFDeriv ℝ m (f (x + x')) y =
      iteratedFDeriv ℝ m (f x) y + iteratedFDeriv ℝ m (f x') y := by
  have hev : f (x + x') =ᶠ[𝓝 y] f x + f x' :=
    eventually_of_mem (hs.mem_nhds hy) fun z hz ↦ hadd x x' z hz
  have hmj : (m : WithTop ℕ∞) ≤ j := by exact_mod_cast hm
  rw [(hev.iteratedFDeriv ℝ m).eq_of_nhds]
  exact iteratedFDeriv_add_apply (((hf x).contDiffAt (hs.mem_nhds hy)).of_le hmj)
    (((hf x').contDiffAt (hs.mem_nhds hy)).of_le hmj)

omit [CompleteSpace X] [CompleteSpace F] in
/-- The scalar counterpart of `iteratedFDeriv_add_of_mem`. -/
private theorem iteratedFDeriv_smul_of_mem (hs : IsOpen s) (hf : ∀ x, ContDiffOn ℝ j (f x) s)
    (hsmul : ∀ (c : ℝ) x, ∀ y ∈ s, f (c • x) y = c • f x y) {m : ℕ} (hm : m ≤ j) (c : ℝ)
    (x : X) {y : E} (hy : y ∈ s) :
    iteratedFDeriv ℝ m (f (c • x)) y = c • iteratedFDeriv ℝ m (f x) y := by
  have hev : f (c • x) =ᶠ[𝓝 y] c • f x :=
    eventually_of_mem (hs.mem_nhds hy) fun z hz ↦ hsmul c x z hz
  have hmj : (m : WithTop ℕ∞) ≤ j := by exact_mod_cast hm
  rw [(hev.iteratedFDeriv ℝ m).eq_of_nhds]
  exact iteratedFDeriv_const_smul_apply (((hf x).contDiffAt (hs.mem_nhds hy)).of_le hmj)

/-- **Derivative bounds for linear families of `Cʲ` functions.** Let `X` be a Banach space and
`f x : E → F`, for `x : X`, functions that are `Cʲ` on an open set `s` and depend linearly on `x`
at each point of `s`. If on every compact subset of `s` the values of `f x` are bounded by a
constant multiple of `‖x‖`, then on every compact subset `K` of `s` the derivatives of `f x` of
order at most `j` are bounded by a constant multiple of `‖x‖`, the constant depending on `K` but
not on `x`. -/
theorem exists_forall_norm_iteratedFDeriv_le [LocallyCompactSpace E] (hs : IsOpen s)
    (hf : ∀ x, ContDiffOn ℝ j (f x) s)
    (hadd : ∀ x x', ∀ y ∈ s, f (x + x') y = f x y + f x' y)
    (hsmul : ∀ (c : ℝ) x, ∀ y ∈ s, f (c • x) y = c • f x y)
    (h0 : ∀ K ⊆ s, IsCompact K → ∃ C, ∀ x, ∀ y ∈ K, ‖f x y‖ ≤ C * ‖x‖)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ C, ∀ x, ∀ y ∈ K, ∀ m ≤ j, ‖iteratedFDeriv ℝ m (f x) y‖ ≤ C * ‖x‖ := by
  obtain ⟨U, hU, hKU, hUs, hUc⟩ := exists_open_between_and_isCompact_closure hK hs hKs
  have : CompactSpace (closure U) := isCompact_iff_compactSpace.1 hUc
  suffices H : ∀ m ≤ j, ∃ C, ∀ k ≤ m, ∀ x, ∀ y ∈ closure U,
      ‖iteratedFDeriv ℝ k (f x) y‖ ≤ C * ‖x‖ by
    obtain ⟨C, hC⟩ := H j le_rfl
    exact ⟨C, fun x y hy m hm ↦ hC m hm x y (subset_closure (hKU hy))⟩
  intro m
  induction m with
  | zero =>
    intro _
    obtain ⟨C, hC⟩ := h0 _ hUs hUc
    refine ⟨C, fun k hk x y hy ↦ ?_⟩
    rw [Nat.le_zero.1 hk, norm_iteratedFDeriv_zero]
    exact hC x y hy
  | succ m ih =>
    intro hm
    obtain ⟨C, hC⟩ := ih (by omega)
    have hlt : (m : WithTop ℕ∞) < j := by exact_mod_cast hm
    let curry := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F
    obtain ⟨C', hC'⟩ := exists_norm_fderiv_le hU (fun x ↦ iteratedFDeriv ℝ m (f x))
      (fun x y ↦ curry (iteratedFDeriv ℝ (m + 1) (f x) y))
      (fun x y hy ↦ by
        have hd := ((hf x).contDiffAt
          (hs.mem_nhds (hUs (subset_closure hy)))).differentiableAt_iteratedFDeriv hlt
        rw [← Function.comp_apply (f := curry), ← fderiv_iteratedFDeriv]
        exact hd.hasFDerivAt)
      (fun x ↦ curry.continuous.comp_continuousOn
        ((ContinuousOn.continuousOn_iteratedFDeriv (hf x) hs (by exact_mod_cast hm)).mono hUs))
      (fun x x' y hy ↦ iteratedFDeriv_add_of_mem hs hf hadd (by omega) x x' (hUs hy))
      (fun x x' y hy ↦ by
        rw [iteratedFDeriv_add_of_mem hs hf hadd hm x x' (hUs hy), map_add])
      (fun c x y hy ↦ by
        rw [iteratedFDeriv_smul_of_mem hs hf hsmul hm c x (hUs hy), map_smul])
      ⟨C, hC m le_rfl⟩
    refine ⟨max C C', fun k hk x y hy ↦ ?_⟩
    rcases Nat.lt_or_eq_of_le hk with hk | rfl
    · exact (hC k (by omega) x y hy).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · have := hC' x y hy
      rw [LinearIsometryEquiv.norm_map] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

end SymplecticGeometry

end
