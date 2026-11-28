/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.HPrinciple.Relative.Stage
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Exhaustion
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.InfiniteConcat
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.TimeExtension
import Mathlib.Geometry.Manifold.Instances.Icc
import SymplecticGeometry.Geometry.Manifold.Morse.Core.Exhaustion
import TauCeti.Geometry.Manifold.DifferentialForm.Squared
import TauCeti.Geometry.Symplectic.ExistsCompatible

/-!
# The parametric relative h-principle for symplectic forms

Let `M` be a manifold without boundary none of whose connected components is compact, `L` a
finite-dimensional normed space, `K ⊆ L` compact and `P₀ ⊆ L` closed. Given a smooth family `τ`
of two-forms on `M` over `L`, nondegenerate over `K`, and a smooth family `α` of closed two-forms,
all in the class of a two-form `α₀` and equal to `τ` over `P₀`, there is a smooth homotopy `H` of
`τ` over `L × [0, 1]` through forms that are nondegenerate over `K`, through closed forms in the
class of `α₀` over `P₀`, and ending in closed forms in the class of `α₀`
(`SymplecticGeometry.exists_isSmoothFamily_homotopy_closed`).

For a family over `[0, 1]`, the corollary
`SymplecticGeometry.exists_isSmoothFamily_homotopy_closed_unitInterval` extends `τ` to `ℝ`
(`SymplecticGeometry.IsSmoothFamily.exists_extend`), takes `K = [0, 1]`, and restricts `H` to
`[0, 1] × [0, 1]`. When the ends of `τ` are closed in the class of `α₀`, the segment between
them is a family `α` for `P₀ = {0, 1}`
(`SymplecticGeometry.exists_isSmoothFamily_homotopy_closed_unitInterval_of_ends`).

The continuous version (`SymplecticGeometry.exists_continuousMap_homotopy_closed`) is the same
statement for a compact Hausdorff space `P` of parameters, with the smooth two-forms on the
tangent bundle of `M` given the frame topology of a covering frame system: a continuous family
`τ : C(P, X)` into the space `X` of nondegenerate two-forms, and a family `α` continuous into the
frame topology, give a homotopy `H : C(P × [0, 1], X)`.

## Proof

`SymplecticGeometry.exists_isMorse_bandCore_seq` gives a proper Morse function `g` and levels
`d k < e k < d (k + 1)` tending to infinity, with band cores for `(d k, e k, e (k + 1))`. The data
carried from stage to stage are the families `τ`, `α`, `β` of the stages of `Relative/Stage.lean`,
the open set `N ⊇ {g ≤ e k}` on which `τ = α + d β`, and a one-form `δ` with `α = αs + d δ` for
the starting family `αs`; each version adds the regularity of these families in the parameter.
Stage `k` is `SymplecticGeometry.BandCore.exists_stage_family`, or
`SymplecticGeometry.BandCore.exists_stage_continuous_family`; it changes nothing near
`{g ≤ e k}`. The stages, run on the times `[1 - 2⁻ᵏ, 1 - 2⁻ᵏ⁻¹]`, settle on the open cover by
the sets `{g < e (k + 1)}`, and the end of stage `k` is `αs + d (δ + β)` there. The one-forms
`δ + β` settle on that cover too, and their limit `θ` (`TauCeti.SmoothForm.exists_eq_limit`)
gives the end `αs + d θ` of the concatenation, closed and in the class. Over `P₀` every stage
runs through closed forms in the class. The recursion and this argument do not depend on the
regularity, and are shared by both versions. The concatenation is smooth by
`SymplecticGeometry.IsSmoothFamily.infiniteConcat`, and continuous into the frame topology by
`SymplecticGeometry.Bundle.ContMDiffTwoForm.continuous_tangentEquiv_symm_infiniteConcat`.

In the continuous version the one-forms of each stage are `B (u l)`, for a smooth family `B`
over a finite-dimensional normed space and a continuous `u`. Each stage enlarges that space, so
the recursion carries it as `Fin m → ℝ`, identified with the space that the stage returns by
`ContinuousLinearEquiv.ofFinrankEq`.

When `M` is empty or there are no parameters to make nondegenerate, the constant homotopy works.
Otherwise a nondegenerate form at a point makes the dimension even
(`TauCeti.SymplecticForm.even_finrank`), as `SymplecticGeometry.exists_isMorse_bandCore_seq`
requires.

## Main results

* `SymplecticGeometry.exists_isSmoothFamily_homotopy_closed`: the smooth version of the
  parametric relative h-principle.
* `SymplecticGeometry.exists_isSmoothFamily_homotopy_closed_unitInterval`: the same for a family
  over `[0, 1]`.
* `SymplecticGeometry.exists_isSmoothFamily_homotopy_closed_unitInterval_of_ends`: the case of a
  path whose ends are closed in the class of `α₀`, with `P₀ = {0, 1}`.
* `SymplecticGeometry.exists_continuousMap_homotopy_closed`: the continuous version, over a
  compact Hausdorff space.
* `SymplecticGeometry.exists_continuousMap_homotopy_closed_of_ends`: the continuous version for
  a path whose ends are closed in the class of `α₀`, with `P₀ = {0, 1}`.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-principle*][EliashbergMishachev2002],
  §10.2.
-/

public section

open Set Filter TauCeti
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Stages

variable {P : Type*}

/-- The data carried from one stage of the relative h-principle to the next, at the level `a` of
`g`, without regularity in the parameter: families `τ`, `α`, `β` over `P`, with `α l` closed and
`τ l` nondegenerate for `l ∈ K`, such that `τ l = α l + d (β l)` on an open `N ⊇ {g ≤ a}`, and
everywhere for `l ∈ P₀`; and one-forms `δ l` with `α l = αs l + d (δ l)` for the starting family
`αs`. -/
private structure StageData (I : ModelWithCorners ℝ E H) (M P : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (g : M → ℝ) (a : ℝ) (K P₀ : Set P)
    (αs : P → SmoothTwoForm I M) where
  τ : P → SmoothTwoForm I M
  α : P → SmoothTwoForm I M
  β : P → SmoothForm I M ℝ 1
  δ : P → SmoothForm I M ℝ 1
  N : Set M
  hαc : ∀ l, mextDerivₗ I 2 (α l) = 0
  hnd : ∀ l ∈ K, (τ l).IsNondegenerate
  hN : IsOpen N
  haN : {x | g x ≤ a} ⊆ N
  hτN : ∀ l, ∀ x ∈ N, (τ l).val x = (α l + mextDerivₗ I 1 (β l)).val x
  hτP₀ : ∀ l ∈ P₀, τ l = α l + mextDerivₗ I 1 (β l)
  hδ : ∀ l, α l = αs l + mextDerivₗ I 1 (δ l)

/-- The data of the first stage, below every value of `g`: the given `τ` and `α`, with `β = 0`,
`δ = 0` and `N = ∅`. -/
private noncomputable def StageData.init {g : M → ℝ} {a : ℝ} (ha : ∀ x, a < g x) {K P₀ : Set P}
    {τ α : P → SmoothTwoForm I M} (hαc : ∀ l, mextDerivₗ I 2 (α l) = 0)
    (hnd : ∀ l ∈ K, (τ l).IsNondegenerate) (hP₀α : ∀ l ∈ P₀, α l = τ l) :
    StageData I M P g a K P₀ α where
  τ := τ
  α := α
  β := 0
  δ := 0
  N := ∅
  hαc := hαc
  hnd := hnd
  hN := isOpen_empty
  haN := fun x hx ↦ absurd (show g x ≤ a from hx) (ha x).not_ge
  hτN := fun _ _ hx ↦ absurd hx (notMem_empty _)
  hτP₀ := fun l hl ↦ by simp [hP₀α l hl]
  hδ := fun l ↦ by simp

/-- The data of the next stage, at the level `b`, from the outputs of a stage on `s`: the
homotopy `H`, whose end `H (·, 1)` is the new `τ`, closed forms `α' l = s.α l + d (γ l)`,
one-forms `β'` and an open `N' ⊇ {g ≤ b}` on which `H (l, 1) = α' l + d (β' l)`. The new `δ` is
`s.δ + γ`, so `δ + β` does not change on a set `V` where `γ` vanishes and `β'` agrees with
`s.β`. -/
private theorem StageData.exists_next {g : M → ℝ} {a b : ℝ} {K P₀ : Set P}
    {αs : P → SmoothTwoForm I M} (s : StageData I M P g a K P₀ αs)
    {H : P × unitInterval → SmoothTwoForm I M} {α' : P → SmoothTwoForm I M}
    {β' γ : P → SmoothForm I M ℝ 1} {N' V : Set M} (hα'c : ∀ l, mextDerivₗ I 2 (α' l) = 0)
    (hγ : ∀ l, α' l = s.α l + mextDerivₗ I 1 (γ l)) (hnd : ∀ l ∈ K, (H (l, 1)).IsNondegenerate)
    (hN' : IsOpen N') (hbN' : {x | g x ≤ b} ⊆ N')
    (hHN' : ∀ l, ∀ x ∈ N', (H (l, 1)).val x = (α' l + mextDerivₗ I 1 (β' l)).val x)
    (hHP₀ : ∀ l ∈ P₀, H (l, 1) = α' l + mextDerivₗ I 1 (β' l))
    (hγV : ∀ l, ∀ x ∈ V, (γ l).val x = 0) (hβV : ∀ l, ∀ x ∈ V, (β' l).val x = (s.β l).val x) :
    ∃ s' : StageData I M P g b K P₀ αs, s'.τ = (fun l ↦ H (l, 1)) ∧ s'.α = α' ∧ s'.β = β' ∧
      ∀ l, ∀ x ∈ V, (s'.δ l + s'.β l).val x = (s.δ l + s.β l).val x :=
  ⟨{ τ := fun l ↦ H (l, 1), α := α', β := β', δ := fun l ↦ s.δ l + γ l, N := N',
      hαc := hα'c, hnd := hnd, hN := hN', haN := hbN', hτN := hHN', hτP₀ := hHP₀,
      hδ := fun l ↦ by rw [hγ, s.hδ, map_add, add_assoc] },
    rfl, rfl, rfl, fun l x hx ↦ by
      simp only [SmoothBundleForm.add_apply, hγV l x hx, hβV l x hx, add_zero]⟩

/-- The forms of the constant homotopy `(l, t) ↦ τ l` are closed in the class of `α₀` over `P₀`,
and also over `K` when `M` or `K` is empty. -/
private theorem closed_const_of_isEmpty {K P₀ : Set P} (hMK : IsEmpty M ∨ K = ∅)
    {τ α : P → SmoothTwoForm I M} (hαc : ∀ l, mextDerivₗ I 2 (α l) = 0)
    {α₀ : SmoothTwoForm I M} (hα₀ : ∀ l, α l - α₀ ∈ exactForms I M 2)
    (hP₀α : ∀ l ∈ P₀, α l = τ l) :
    (∀ l ∈ P₀, mextDerivₗ I 2 (τ l) = 0 ∧ τ l - α₀ ∈ exactForms I M 2) ∧
      ∀ l ∈ K, mextDerivₗ I 2 (τ l) = 0 ∧ τ l - α₀ ∈ exactForms I M 2 := by
  refine ⟨fun l hl ↦ by simpa only [← hP₀α l hl] using ⟨hαc l, hα₀ l⟩, fun l hl ↦ ?_⟩
  rcases hMK with hM | rfl
  · -- On an empty manifold every form is zero.
    rw [Subsingleton.elim (mextDerivₗ I 2 (τ l)) 0, Subsingleton.elim (τ l - α₀) 0]
    exact ⟨rfl, zero_mem _⟩
  · exact absurd hl (notMem_empty l)

/-- The recursion and the final argument of the relative h-principle, shared by its smooth and
continuous versions. The data of stage `k` lie in `D k` and give a `StageData` at the level
`e k`; `next` gives the data of the following stage and `Φ` the homotopy of the stage, which
changes neither the forms nor `δ + β` on `{g ≤ e k}`. Starting from `s₀`, the stages
`Φ n (seq n)` settle on the open cover by the sets `{g < e (n + 1)}`, and the form
`ε l := αs l + d θ l`, for the limit `θ l` of the one-forms `δ + β`, agrees there with the end of
stage `n`. Their infinite concatenation ending at `ε` is nondegenerate over `K`, runs through
closed forms in the class of `α₀` over `P₀`, and ends in such forms. -/
private theorem exists_seq_of_stages {g : M → ℝ} (hg : Continuous g) {e : ℕ → ℝ}
    (hemono : StrictMono e)
    (hetop : Tendsto e atTop atTop) {K P₀ : Set P} {αs : P → SmoothTwoForm I M}
    (hαsc : ∀ l, mextDerivₗ I 2 (αs l) = 0) {α₀ : SmoothTwoForm I M}
    (hα₀ : ∀ l, αs l - α₀ ∈ exactForms I M 2) {D : ℕ → Type*}
    (data : ∀ k, D k → StageData I M P g (e k) K P₀ αs) (next : ∀ k, D k → D (k + 1))
    (Φ : ∀ k, D k → P × unitInterval → SmoothTwoForm I M)
    (hΦ₀ : ∀ k s l, Φ k s (l, 0) = (data k s).τ l)
    (hΦ₁ : ∀ k s l, Φ k s (l, 1) = (data (k + 1) (next k s)).τ l)
    (hΦnd : ∀ k s, ∀ l ∈ K, ∀ t, (Φ k s (l, t)).IsNondegenerate)
    (hΦg : ∀ k s l t x, g x ≤ e k → (Φ k s (l, t)).val x = ((data k s).τ l).val x)
    (hθg : ∀ k s l x, g x ≤ e k →
      ((data (k + 1) (next k s)).δ l + (data (k + 1) (next k s)).β l).val x =
        ((data k s).δ l + (data k s).β l).val x)
    (hΦP₀ : ∀ k s, ∀ l ∈ P₀, ∀ t, mextDerivₗ I 2 (Φ k s (l, t)) = 0 ∧
      Φ k s (l, t) - (data k s).α l ∈ exactForms I M 2)
    (s₀ : D 0) :
    ∃ (seq : ∀ k, D k) (ε : P → SmoothTwoForm I M), seq 0 = s₀ ∧
      (∀ x, ∃ n, x ∈ {y | g y < e (n + 1)}) ∧
      (∀ n l, Φ (n + 1) (seq (n + 1)) (l, 0) = Φ n (seq n) (l, 1)) ∧
      (∀ n m, n < m → ∀ p, ∀ x ∈ {y | g y < e (n + 1)},
        (Φ m (seq m) p).val x = (Φ n (seq n) (p.1, 1)).val x) ∧
      (∀ n l, ∀ x ∈ {y | g y < e (n + 1)}, (ε l).val x = (Φ n (seq n) (l, 1)).val x) ∧
      (∀ l ∈ K, ∀ t,
        (infiniteConcat (fun n s ↦ Φ n (seq n) (l, s)) (ε l) t).IsNondegenerate) ∧
      (∀ l ∈ P₀, ∀ t,
        mextDerivₗ I 2 (infiniteConcat (fun n s ↦ Φ n (seq n) (l, s)) (ε l) t) = 0 ∧
        infiniteConcat (fun n s ↦ Φ n (seq n) (l, s)) (ε l) t - α₀ ∈ exactForms I M 2) ∧
      ∀ l, mextDerivₗ I 2 (ε l) = 0 ∧ ε l - α₀ ∈ exactForms I M 2 := by
  let seq : ∀ k, D k := fun k ↦ Nat.rec (motive := D) s₀ next k
  have hseq (k : ℕ) : seq (k + 1) = next k (seq k) := rfl
  -- The forms `τ` of the stages settle on `{g ≤ e k}`, and so do the one-forms `δ + β`.
  have hτset (l : P) {n m : ℕ} (hnm : n ≤ m) {x : M} (hx : g x ≤ e n) :
      ((data m (seq m)).τ l).val x = ((data n (seq n)).τ l).val x := by
    refine (Nat.rel_of_forall_rel_succ_of_le_of_le (· = ·)
      (f := fun k ↦ ((data k (seq k)).τ l).val x) (fun k hk ↦ ?_) le_rfl hnm).symm
    rw [hseq, ← hΦ₁ k (seq k) l]
    exact (hΦg k (seq k) l 1 x (hx.trans (hemono.monotone hk))).symm
  have hθset (l : P) {n m : ℕ} (hnm : n ≤ m) {x : M} (hx : g x ≤ e n) :
      ((data m (seq m)).δ l + (data m (seq m)).β l).val x =
        ((data n (seq n)).δ l + (data n (seq n)).β l).val x := by
    refine (Nat.rel_of_forall_rel_succ_of_le_of_le (· = ·)
      (f := fun k ↦ ((data k (seq k)).δ l + (data k (seq k)).β l).val x) (fun k hk ↦ ?_)
      le_rfl hnm).symm
    rw [hseq]
    exact (hθg k (seq k) l x (hx.trans (hemono.monotone hk))).symm
  -- The open cover by the sets `{g < e (n + 1)}`, on which the later stages no longer move.
  set U : ℕ → Set M := fun n ↦ {x | g x < e (n + 1)}
  have hUo (n : ℕ) : IsOpen (U n) := isOpen_lt hg continuous_const
  have hUcov (x : M) : ∃ n, x ∈ U n :=
    ((hetop.comp (tendsto_add_atTop_nat 1)).eventually_gt_atTop (g x)).exists
  -- The end is `αs l + d θ l`, for the limit `θ l` of the one-forms `δ + β` after each stage.
  have hlim (l : P) := SmoothForm.exists_eq_limit hUo hUcov
    (η := fun n ↦ (data (n + 1) (seq (n + 1))).δ l + (data (n + 1) (seq (n + 1))).β l)
    fun n m hnm x hx ↦
      hθset l (n := n + 1) (m := m + 1) (by omega) (show g x < e (n + 1) from hx).le
  choose θ hθ using hlim
  have hεU (n : ℕ) (l : P) (x : M) (hx : x ∈ U n) :
      (αs l + mextDerivₗ I 1 (θ l)).val x = (Φ n (seq n) (l, 1)).val x := by
    have hxN : x ∈ (data (n + 1) (seq (n + 1))).N :=
      (data (n + 1) (seq (n + 1))).haN (show g x ≤ e (n + 1) from hx.le)
    rw [hΦ₁, ← hseq, (data (n + 1) (seq (n + 1))).hτN l x hxN, (data (n + 1) (seq (n + 1))).hδ l,
      add_assoc, ← map_add, SmoothBundleForm.add_apply, SmoothBundleForm.add_apply,
      (hθ l n x hx).2]
  have hεc (l : P) : mextDerivₗ I 2 (αs l + mextDerivₗ I 1 (θ l)) = 0 ∧
      αs l + mextDerivₗ I 1 (θ l) - α₀ ∈ exactForms I M 2 := by
    refine ⟨?_, ?_⟩
    · rw [map_add, hαsc, zero_add]
      exact LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ I 1) (θ l)
    · rw [add_sub_right_comm]
      exact add_mem (hα₀ l) (by rw [exactForms_succ]; exact ⟨θ l, rfl⟩)
  refine ⟨seq, fun l ↦ αs l + mextDerivₗ I 1 (θ l), rfl, hUcov, fun n l ↦ ?_,
    fun n m hnm p x hx ↦ ?_, hεU, fun l hl t ↦ ?_, fun l hl t ↦ ?_, hεc⟩
  · rw [hΦ₀, hΦ₁, hseq]
  · have hxm : g x ≤ e m := (show g x < e (n + 1) from hx).le.trans (hemono.monotone hnm)
    rw [hΦg m (seq m) p.1 p.2 x hxm, hτset p.1 hnm hx.le, hΦ₁, ← hseq]
  · refine infiniteConcat_mem (s := {σ : SmoothTwoForm I M | σ.IsNondegenerate})
      (fun n t ↦ hΦnd n (seq n) l hl t) ?_ t
    -- Nondegeneracy is pointwise, and the end agrees near each point with the end of a stage.
    rw [mem_ofPred_eq, SmoothTwoForm.isNondegenerate_iff_forall_ker_bilinFormAt_eq_bot]
    intro x
    obtain ⟨n, hn⟩ := hUcov x
    have h := SmoothTwoForm.isNondegenerate_iff_forall_ker_bilinFormAt_eq_bot.1
      (hΦnd n (seq n) l hl 1) x
    rwa [SmoothForm.bilinFormAt_def, ← hεU n l x hn, ← SmoothForm.bilinFormAt_def] at h
  · refine infiniteConcat_mem
      (s := {σ : SmoothTwoForm I M | mextDerivₗ I 2 σ = 0 ∧ σ - α₀ ∈ exactForms I M 2})
      (fun n t ↦ ⟨(hΦP₀ n (seq n) l hl t).1, ?_⟩) (hεc l) t
    have h := add_mem (add_mem (hΦP₀ n (seq n) l hl t).2
      (show (data n (seq n)).α l - αs l ∈ exactForms I M 2 by
        rw [(data n (seq n)).hδ l, add_sub_cancel_left, exactForms_succ]; exact ⟨_, rfl⟩))
      (hα₀ l)
    simpa only [sub_add_sub_cancel] using h

end Stages

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]

/-- The levels of the stages. On a nonempty manifold none of whose connected components is
compact and that carries a nondegenerate two-form, there are a continuous `g : M → ℝ` and levels
`d k < e k < d (k + 1)`, with `e` strictly increasing, tending to infinity and below every value
of `g` at `0`, and band cores of `g` for `(d k, e k, e (k + 1))`. -/
private theorem exists_bandCore_levels [Nonempty M]
    (hM : ∀ x : M, ¬ IsCompact (connectedComponent x)) {σ : SmoothTwoForm I M}
    (hσ : σ.IsNondegenerate) :
    ∃ (g : M → ℝ) (d e : ℕ → ℝ), Continuous g ∧ StrictMono e ∧ Tendsto e atTop atTop ∧
      (∀ x, e 0 < g x) ∧ ∀ k, Nonempty (BandCore I g (d k) (e k) (e (k + 1))) := by
  -- A nondegenerate form at a point makes the dimension even.
  have hE : Module.finrank ℝ E ≠ 1 := by
    obtain ⟨n, hn⟩ := (hσ.symplecticFormAt (Classical.arbitrary M)).even_finrank
    -- The tangent space at a point is `E` by definition.
    change Module.finrank ℝ E = n + n at hn
    omega
  obtain ⟨g, d, e, -, -, he₀, hde, hd, hc⟩ := exists_isMorse_bandCore_seq (I := I) hE hM
  exact ⟨g, d, e, g.contMDiff.continuous,
    strictMono_nat_of_lt_succ fun k ↦ (hde k).2.trans (hde (k + 1)).1,
    tendsto_atTop_mono (fun k ↦ (hde k).1.le) hd, he₀, hc⟩


section Smooth

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

/-- The data of `StageData` for smooth families `τ`, `α`, `β` over `L`. -/
private structure SmoothStageData (I : ModelWithCorners ℝ E H) (M L : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [NormedAddCommGroup L] [NormedSpace ℝ L]
    (g : M → ℝ) (a : ℝ) (K P₀ : Set L) (αs : L → SmoothTwoForm I M)
    extends StageData I M L g a K P₀ αs where
  hτ : IsSmoothFamily 𝓘(ℝ, L) τ
  hα : IsSmoothFamily 𝓘(ℝ, L) α
  hβ : IsSmoothFamily 𝓘(ℝ, L) β

/-- One stage, on the data of `SmoothStageData`: from the data at the level `a`, the data at the
level `b` and the homotopy between them, which changes neither the forms nor `δ + β` on
`{g ≤ a}`. -/
private theorem SmoothStageData.exists_next {g : M → ℝ} {a₀ a b : ℝ} (c : BandCore I g a₀ a b)
    (hg : Continuous g) {K P₀ : Set L} (hK : IsCompact K) (hP₀ : IsClosed P₀)
    {αs : L → SmoothTwoForm I M} (s : SmoothStageData I M L g a K P₀ αs) :
    ∃ (s' : SmoothStageData I M L g b K P₀ αs) (H : L × unitInterval → SmoothTwoForm I M),
      IsSmoothFamily (𝓘(ℝ, L).prod (𝓡∂ 1)) H ∧ (∀ l, H (l, 0) = s.τ l) ∧
      (∀ l, H (l, 1) = s'.τ l) ∧ (∀ l ∈ K, ∀ t, (H (l, t)).IsNondegenerate) ∧
      (∀ l t x, g x ≤ a → (H (l, t)).val x = (s.τ l).val x) ∧
      (∀ l x, g x ≤ a → (s'.δ l + s'.β l).val x = (s.δ l + s.β l).val x) ∧
      ∀ l ∈ P₀, ∀ t, mextDerivₗ I 2 (H (l, t)) = 0 ∧ H (l, t) - s.α l ∈ exactForms I M 2 := by
  obtain ⟨H, α', β', V, N', hH, hα', hβ', hH₀, hHnd, hV, hHV, hα'c, hN', hbN', hHN', hHP₀⟩ :=
    c.exists_stage_family hg hK hP₀ s.hτ s.hα s.hαc s.hnd s.hβ s.hN s.haN s.hτN s.hτP₀
  choose hα'd γ hγ hγV using hα'c
  obtain ⟨s', hs'τ, hs'α, hs'β, hs'θ⟩ :=
    s.toStageData.exists_next hα'd hγ (fun l hl ↦ hHnd l hl 1) hN' hbN'
      hHN' (fun l hl ↦ (hHP₀ l hl).1) hγV fun l x hx ↦ (hHV l 0 x hx).2.2
  have h₁ : ContMDiff 𝓘(ℝ, L) (𝓘(ℝ, L).prod (𝓡∂ 1)) ∞ fun l : L ↦ (l, (1 : unitInterval)) :=
    contMDiff_id.prodMk contMDiff_const
  exact ⟨{ s' with hτ := hs'τ ▸ hH.comp _ h₁, hα := hs'α ▸ hα', hβ := hs'β ▸ hβ' },
    H, hH, hH₀, fun l ↦ (congrFun hs'τ l).symm, hHnd,
    fun l t x hx ↦ (hHV l t x (subset_of_mem_nhdsSet hV hx)).1,
    fun l x hx ↦ hs'θ l x (subset_of_mem_nhdsSet hV hx), fun l hl t ↦ (hHP₀ l hl).2 t⟩

/-- **The parametric relative h-principle for symplectic forms, smooth version.** Let `M` be a
manifold without boundary none of whose connected components is compact, `K ⊆ L` compact and
`P₀ ⊆ L` closed. Let `τ` be a smooth family over `L` of two-forms on `M`, nondegenerate for
`l ∈ K`, and `α` a smooth family of closed two-forms with every `α l - α₀` exact and `α l = τ l`
for `l ∈ P₀`. Then there is a smooth family `H` over `L × [0, 1]` with `H (l, 0) = τ l` such
that

* `H (l, t)` is nondegenerate for `l ∈ K`;
* `H (l, t)` is closed and `H (l, t) - α₀` is exact for `l ∈ P₀`;
* `H (l, 1)` is closed and `H (l, 1) - α₀` is exact for `l ∈ K`. -/
theorem exists_isSmoothFamily_homotopy_closed
    (hM : ∀ x : M, ¬ IsCompact (connectedComponent x)) {K P₀ : Set L} (hK : IsCompact K)
    (hP₀ : IsClosed P₀) {τ : L → SmoothTwoForm I M} (hτ : IsSmoothFamily 𝓘(ℝ, L) τ)
    (hnd : ∀ l ∈ K, (τ l).IsNondegenerate) {α : L → SmoothTwoForm I M}
    (hα : IsSmoothFamily 𝓘(ℝ, L) α) (hαc : ∀ l, mextDerivₗ I 2 (α l) = 0)
    {α₀ : SmoothTwoForm I M} (hα₀ : ∀ l, α l - α₀ ∈ exactForms I M 2)
    (hP₀α : ∀ l ∈ P₀, α l = τ l) :
    ∃ H : L × unitInterval → SmoothTwoForm I M, IsSmoothFamily (𝓘(ℝ, L).prod (𝓡∂ 1)) H ∧
      (∀ l, H (l, 0) = τ l) ∧ (∀ l ∈ K, ∀ t, (H (l, t)).IsNondegenerate) ∧
      (∀ l ∈ P₀, ∀ t, mextDerivₗ I 2 (H (l, t)) = 0 ∧ H (l, t) - α₀ ∈ exactForms I M 2) ∧
      ∀ l ∈ K, mextDerivₗ I 2 (H (l, 1)) = 0 ∧ H (l, 1) - α₀ ∈ exactForms I M 2 := by
  by_cases hMK : IsEmpty M ∨ K = ∅
  · obtain ⟨hP₀c, hKc⟩ := closed_const_of_isEmpty hMK hαc hα₀ hP₀α
    exact ⟨fun p ↦ τ p.1, hτ.comp _ contMDiff_fst, fun l ↦ rfl, fun l hl _ ↦ hnd l hl,
      fun l hl _ ↦ hP₀c l hl, hKc⟩
  obtain ⟨_, l₀, hl₀⟩ : Nonempty M ∧ K.Nonempty := by
    rw [not_or, not_isEmpty_iff, ← ne_eq, ne_empty_iff_nonempty] at hMK
    exact hMK
  obtain ⟨g, d, e, hg, hemono, hetop, he₀, hc⟩ := exists_bandCore_levels hM (hnd l₀ hl₀)
  -- The data of the stages, defined by recursion, and their composition.
  choose next Φ hΦ hΦ₀ hΦ₁ hΦnd hΦg hθg hΦP₀ using
    fun k (s : SmoothStageData I M L g (e k) K P₀ α) ↦ s.exists_next (hc k).some hg hK hP₀
  let s₀ : SmoothStageData I M L g (e 0) K P₀ α :=
    { StageData.init he₀ hαc hnd hP₀α with
      hτ := hτ, hα := hα, hβ := isSmoothFamily_const 0 }
  obtain ⟨seq, ε, hseq₀, hUcov, hseam, hΦU, hεU, hεnd, hεP₀, hε⟩ :=
    exists_seq_of_stages hg hemono hetop hαc hα₀ (fun _ s ↦ s.toStageData) next Φ hΦ₀ hΦ₁
      hΦnd hΦg hθg hΦP₀ s₀
  refine ⟨_, IsSmoothFamily.infiniteConcat (fun n ↦ hΦ n (seq n)) hseam
      (fun n ↦ isOpen_lt hg continuous_const) hUcov hΦU hεU, fun l ↦ ?_, hεnd, hεP₀,
    fun l _ ↦ by simpa only [infiniteConcat_one] using hε l⟩
  rw [infiniteConcat_zero, hΦ₀, hseq₀]
  rfl

/-- **The parametric relative h-principle for symplectic forms over `[0, 1]`.** Let `M` be a
manifold without boundary none of whose connected components is compact and `P₀ ⊆ [0, 1]` closed.
Let `τ : [0, 1] → SmoothTwoForm I M` be smooth with every `τ t` nondegenerate, and
`α : ℝ → SmoothTwoForm I M` smooth with every `α s` closed, every `α s - α₀` exact and
`α t = τ t` for `t ∈ P₀`. Then there is a smooth family `H` over `[0, 1] × [0, 1]` with
`H (t, 0) = τ t` such that

* every `H (t, u)` is nondegenerate;
* `H (t, u)` is closed and `H (t, u) - α₀` is exact for `t ∈ P₀`;
* `H (t, 1)` is closed and `H (t, 1) - α₀` is exact for every `t`.

The family `α` is asked over `ℝ`, where the uses build it explicitly: a smooth extension to `ℝ`
of a family of closed forms over `[0, 1]` need not be closed off `[0, 1]`. -/
theorem exists_isSmoothFamily_homotopy_closed_unitInterval
    (hM : ∀ x : M, ¬ IsCompact (connectedComponent x)) {P₀ : Set unitInterval}
    (hP₀ : IsClosed P₀) {τ : unitInterval → SmoothTwoForm I M} (hτ : IsSmoothFamily (𝓡∂ 1) τ)
    (hnd : ∀ t, (τ t).IsNondegenerate) {α : ℝ → SmoothTwoForm I M}
    (hα : IsSmoothFamily 𝓘(ℝ, ℝ) α) (hαc : ∀ s, mextDerivₗ I 2 (α s) = 0)
    {α₀ : SmoothTwoForm I M} (hα₀ : ∀ s, α s - α₀ ∈ exactForms I M 2)
    (hP₀α : ∀ t ∈ P₀, α t = τ t) :
    ∃ H : unitInterval × unitInterval → SmoothTwoForm I M,
      IsSmoothFamily ((𝓡∂ 1).prod (𝓡∂ 1)) H ∧ (∀ t, H (t, 0) = τ t) ∧
      (∀ t u, (H (t, u)).IsNondegenerate) ∧
      (∀ t ∈ P₀, ∀ u, mextDerivₗ I 2 (H (t, u)) = 0 ∧ H (t, u) - α₀ ∈ exactForms I M 2) ∧
      ∀ t, mextDerivₗ I 2 (H (t, 1)) = 0 ∧ H (t, 1) - α₀ ∈ exactForms I M 2 := by
  -- Extend `τ` to `ℝ`, apply the smooth version with `K = [0, 1]`, and restrict back.
  obtain ⟨τ', hτ', hτ'τ⟩ := hτ.exists_extend
  obtain ⟨H, hH, hH₀, hHnd, hHP₀, hH₁⟩ := exists_isSmoothFamily_homotopy_closed hM
    (K := Icc 0 1) isCompact_Icc (isClosed_Icc.isClosedMap_subtypeVal _ hP₀) hτ'
    (fun s hs ↦ by simpa only [hτ'τ ⟨s, hs⟩] using hnd ⟨s, hs⟩) hα hαc hα₀
    (by rintro _ ⟨t, ht, rfl⟩; rw [hP₀α t ht, hτ'τ])
  refine ⟨fun p ↦ H ((p.1 : ℝ), p.2),
    hH.comp _ ((contMDiff_subtypeVal_Icc (x := 0) (y := 1)).prodMap contMDiff_id),
    fun t ↦ (hH₀ t).trans (hτ'τ t), fun t u ↦ hHnd t t.property u,
    fun t ht u ↦ hHP₀ t ⟨t, ht, rfl⟩ u,
    fun t ↦ hH₁ t t.property⟩

/-- **The relative h-principle for a path of nondegenerate forms with closed ends.** Let `M` be
a manifold without boundary none of whose connected components is compact, and
`τ : [0, 1] → SmoothTwoForm I M` smooth with every `τ t` nondegenerate, whose ends `τ 0` and
`τ 1` are closed with `τ 0 - α₀` and `τ 1 - α₀` exact. Then there is a smooth family `H` over
`[0, 1] × [0, 1]` with `H (t, 0) = τ t` such that

* every `H (t, u)` is nondegenerate;
* `H (t, u)` is closed and `H (t, u) - α₀` is exact for `t = 0` and `t = 1`;
* `H (t, 1)` is closed and `H (t, 1) - α₀` is exact for every `t`.

This is `SymplecticGeometry.exists_isSmoothFamily_homotopy_closed_unitInterval` for
`P₀ = {0, 1}`, with the segment `s ↦ τ 0 + s • (τ 1 - τ 0)` as the family `α`. -/
theorem exists_isSmoothFamily_homotopy_closed_unitInterval_of_ends
    (hM : ∀ x : M, ¬ IsCompact (connectedComponent x)) {τ : unitInterval → SmoothTwoForm I M}
    (hτ : IsSmoothFamily (𝓡∂ 1) τ) (hnd : ∀ t, (τ t).IsNondegenerate)
    (h₀ : mextDerivₗ I 2 (τ 0) = 0) (h₁ : mextDerivₗ I 2 (τ 1) = 0) {α₀ : SmoothTwoForm I M}
    (h₀α : τ 0 - α₀ ∈ exactForms I M 2) (h₁α : τ 1 - α₀ ∈ exactForms I M 2) :
    ∃ H : unitInterval × unitInterval → SmoothTwoForm I M,
      IsSmoothFamily ((𝓡∂ 1).prod (𝓡∂ 1)) H ∧ (∀ t, H (t, 0) = τ t) ∧
      (∀ t u, (H (t, u)).IsNondegenerate) ∧
      (∀ t ∈ ({0, 1} : Set unitInterval), ∀ u,
        mextDerivₗ I 2 (H (t, u)) = 0 ∧ H (t, u) - α₀ ∈ exactForms I M 2) ∧
      ∀ t, mextDerivₗ I 2 (H (t, 1)) = 0 ∧ H (t, 1) - α₀ ∈ exactForms I M 2 := by
  refine exists_isSmoothFamily_homotopy_closed_unitInterval hM (Set.toFinite _).isClosed hτ hnd
    (isSmoothFamily_def.2 ⟨SmoothForm.lineMapFamily (τ 0) (τ 1) contDiff_id,
      SmoothForm.mpullback_prodMk_lineMapFamily (τ 0) (τ 1) contDiff_id⟩)
    (fun s ↦ ?_) (fun s ↦ ?_) ?_
  · simp [h₀, h₁]
  · convert add_mem h₀α (Submodule.smul_mem _ s (sub_mem h₁α h₀α)) using 1
    simp only [id]
    module
  · rintro t (rfl | rfl) <;> simp

end Smooth

section Continuous

open _root_.Bundle

variable {P : Type*} [TopologicalSpace P] [CompactSpace P] [T2Space P] {ι : Type*}
  (fr : ι → Trivialization (E [⋀^Fin 2]→L[ℝ] ℝ)
    (π (E [⋀^Fin 2]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x)))
  [∀ j, MemTrivializationAtlas (fr j)]
  (W : ι → TopologicalSpace.Opens M) (hW : ∀ j, (W j : Set M) ⊆ (fr j).baseSet)

/-- The data of `StageData`, for every parameter of `P` (`K = univ`), with `τ` and `α` continuous
into a topology `T` on the two-forms, and one-forms `β l = B (u l)` for a smooth family `B` over
`Fin m → ℝ` and a continuous `u`. -/
private structure ContinuousStageData (I : ModelWithCorners ℝ E H) (M P : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [TopologicalSpace P]
    (T : TopologicalSpace (Bundle.ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))))
    (g : M → ℝ) (a : ℝ) (P₀ : Set P) (αs : P → SmoothTwoForm I M)
    extends StageData I M P g a univ P₀ αs where
  m : ℕ
  B : (Fin m → ℝ) → SmoothForm I M ℝ 1
  u : P → Fin m → ℝ
  hτ : @Continuous _ _ _ T fun l ↦ Bundle.ContMDiffTwoForm.tangentEquiv.symm (τ l)
  hα : @Continuous _ _ _ T fun l ↦ Bundle.ContMDiffTwoForm.tangentEquiv.symm (α l)
  hB : IsSmoothFamily 𝓘(ℝ, Fin m → ℝ) B
  hu : Continuous u
  hβ : ∀ l, β l = B (u l)

/-- One stage, on the data of `ContinuousStageData` for the frame topology: from the data at the
level `a`, the data at the level `b` and the homotopy between them, which changes neither the
forms nor `δ + β` on `{g ≤ a}`. The parameter space `S × ∏ i, (Fin (n i) → ℝ)`
of the new one-forms of `BandCore.exists_stage_continuous_family` is identified with
`Fin m' → ℝ` for its dimension `m'`. -/
private theorem ContinuousStageData.exists_next {g : M → ℝ} {a₀ a b : ℝ}
    (c : BandCore I g a₀ a b) (hg : Continuous g) (hcover : ∀ x, ∃ j, x ∈ W j) {P₀ : Set P}
    (hP₀ : IsClosed P₀) {αs : P → SmoothTwoForm I M}
    (s : ContinuousStageData I M P
      (ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW)
      g a P₀ αs) :
    ∃ (s' : ContinuousStageData I M P
        (ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW)
        g b P₀ αs) (H : P × unitInterval → SmoothTwoForm I M),
      (@Continuous _ _ _
        (ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW)
        fun p ↦ Bundle.ContMDiffTwoForm.tangentEquiv.symm (H p)) ∧ (∀ l, H (l, 0) = s.τ l) ∧
      (∀ l, H (l, 1) = s'.τ l) ∧ (∀ l t, (H (l, t)).IsNondegenerate) ∧
      (∀ l t x, g x ≤ a → (H (l, t)).val x = (s.τ l).val x) ∧
      (∀ l x, g x ≤ a → (s'.δ l + s'.β l).val x = (s.δ l + s.β l).val x) ∧
      ∀ l ∈ P₀, ∀ t, mextDerivₗ I 2 (H (l, t)) = 0 ∧ H (l, t) - s.α l ∈ exactForms I M 2 := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
  obtain ⟨H, α', n, σ, B'', V, N', hH, hα', hσ, hB'', hH₀, hHnd, hV, hHV, hα'c, hN', hbN', hHN',
      hHP₀⟩ :=
    c.exists_stage_continuous_family fr W hW hg hcover hP₀ s.hτ s.hα s.hαc
      (fun l ↦ s.hnd l (mem_univ l)) s.hB s.hu s.hN s.haN
      (fun l x hx ↦ by rw [← s.hβ]; exact s.hτN l x hx)
      (fun l hl ↦ by rw [← s.hβ]; exact s.hτP₀ l hl)
  choose hα'd γ hγ hγV using hα'c
  obtain ⟨s', hs'τ, hs'α, hs'β, hs'θ⟩ :=
    s.toStageData.exists_next hα'd hγ (fun l _ ↦ hHnd l 1) hN' hbN'
      hHN' (fun l hl ↦ (hHP₀ l hl).1) hγV fun l x hx ↦ by rw [s.hβ]; exact (hHV l 0 x hx).2.2
  -- The parameters of the new one-forms, identified with `Fin m' → ℝ`.
  let φ : ((Fin s.m → ℝ) × ((i : c.ι) → Fin (n i) → ℝ)) ≃L[ℝ]
      (Fin (Module.finrank ℝ ((Fin s.m → ℝ) × ((i : c.ι) → Fin (n i) → ℝ))) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  exact ⟨{ s' with
      m := _, B := fun v ↦ B'' (φ.symm v), u := fun l ↦ φ (s.u l, fun i ↦ σ i l),
      hτ := hs'τ ▸ hH.comp (continuous_id.prodMk continuous_const), hα := hs'α ▸ hα',
      hB := hB''.comp _ φ.symm.contDiff.contMDiff,
      hu := φ.continuous.comp (s.hu.prodMk (continuous_pi hσ)),
      hβ := fun l ↦ by rw [hs'β, ContinuousLinearEquiv.symm_apply_apply] },
    H, hH, hH₀, fun l ↦ (congrFun hs'τ l).symm, hHnd,
    fun l t x hx ↦ (hHV l t x (subset_of_mem_nhdsSet hV hx)).1,
    fun l x hx ↦ hs'θ l x (subset_of_mem_nhdsSet hV hx), fun l hl t ↦ (hHP₀ l hl).2 t⟩

/-- **The parametric relative h-principle for symplectic forms, continuous version.** Let `M` be
a manifold without boundary none of whose connected components is compact, give the smooth
two-forms on its tangent bundle the frame topology of a covering frame system, let `P` be a
compact Hausdorff space and `P₀ ⊆ P` closed. Let `τ` be a continuous family over `P` of
nondegenerate two-forms, and `α` a family of closed two-forms, continuous into the frame
topology, with every `α l - α₀` exact and `α l = τ l` for `l ∈ P₀`. Then there is a continuous
family `H` over `P × [0, 1]` of nondegenerate two-forms with `H (l, 0) = τ l` such that

* `H (l, t)` is closed and `H (l, t) - α₀` is exact for `l ∈ P₀`;
* `H (l, 1)` is closed and `H (l, 1) - α₀` is exact for every `l`. -/
theorem exists_continuousMap_homotopy_closed
    (hM : ∀ x : M, ¬ IsCompact (connectedComponent x)) (hcover : ∀ x, ∃ j, x ∈ W j)
    {P₀ : Set P} (hP₀ : IsClosed P₀) :
    letI := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
    ∀ (τ : C(P,
        {σ : Bundle.ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M)) // σ.IsNondegenerate}))
      {α : P → SmoothTwoForm I M},
      Continuous (fun l ↦ Bundle.ContMDiffTwoForm.tangentEquiv.symm (α l)) →
      (∀ l, mextDerivₗ I 2 (α l) = 0) → ∀ {α₀ : SmoothTwoForm I M},
      (∀ l, α l - α₀ ∈ exactForms I M 2) →
      (∀ l ∈ P₀, α l = Bundle.ContMDiffTwoForm.tangentEquiv (τ l).val) →
      ∃ H : C(P × unitInterval,
          {σ : Bundle.ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M)) // σ.IsNondegenerate}),
        (∀ l, H (l, 0) = τ l) ∧
        (∀ l ∈ P₀, ∀ t, mextDerivₗ I 2 (Bundle.ContMDiffTwoForm.tangentEquiv (H (l, t)).val) = 0 ∧
          Bundle.ContMDiffTwoForm.tangentEquiv (H (l, t)).val - α₀ ∈ exactForms I M 2) ∧
        ∀ l, mextDerivₗ I 2 (Bundle.ContMDiffTwoForm.tangentEquiv (H (l, 1)).val) = 0 ∧
          Bundle.ContMDiffTwoForm.tangentEquiv (H (l, 1)).val - α₀ ∈ exactForms I M 2 := by
  intro τ α hα hαc α₀ hα₀ hP₀α
  let T := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
  -- Work with the forms `τ' l` of Tau Ceti, and package the homotopy at the end.
  set τ' : P → SmoothTwoForm I M := fun l ↦ Bundle.ContMDiffTwoForm.tangentEquiv (τ l).val
  have hτ' : Continuous fun l ↦ Bundle.ContMDiffTwoForm.tangentEquiv.symm (τ' l) := by
    simp only [τ', LinearEquiv.symm_apply_apply]
    exact continuous_subtypeVal.comp τ.continuous
  have hnd (l : P) : (τ' l).IsNondegenerate :=
    Bundle.ContMDiffTwoForm.isNondegenerate_tangentEquiv_iff.2 (τ l).property
  suffices h : ∃ H : P × unitInterval → SmoothTwoForm I M,
      Continuous (fun p ↦ Bundle.ContMDiffTwoForm.tangentEquiv.symm (H p)) ∧
      (∀ l, H (l, 0) = τ' l) ∧ (∀ p, (H p).IsNondegenerate) ∧
      (∀ l ∈ P₀, ∀ t, mextDerivₗ I 2 (H (l, t)) = 0 ∧ H (l, t) - α₀ ∈ exactForms I M 2) ∧
      ∀ l, mextDerivₗ I 2 (H (l, 1)) = 0 ∧ H (l, 1) - α₀ ∈ exactForms I M 2 by
    obtain ⟨H, hH, hH₀, hHnd, hHP₀, hH₁⟩ := h
    refine ⟨⟨fun p ↦ ⟨Bundle.ContMDiffTwoForm.tangentEquiv.symm (H p),
        Bundle.ContMDiffTwoForm.isNondegenerate_tangentEquiv_symm_iff.2 (hHnd p)⟩,
        hH.subtype_mk _⟩,
      fun l ↦ Subtype.ext ?_, fun l hl t ↦ ?_, fun l ↦ ?_⟩
    · simp only [ContinuousMap.coe_mk, hH₀, τ', LinearEquiv.symm_apply_apply]
    · simpa only [ContinuousMap.coe_mk, LinearEquiv.apply_symm_apply] using hHP₀ l hl t
    · simpa only [ContinuousMap.coe_mk, LinearEquiv.apply_symm_apply] using hH₁ l
  by_cases hMP : IsEmpty M ∨ IsEmpty P
  · -- The constant homotopy.
    obtain ⟨hP₀c, hc⟩ := closed_const_of_isEmpty (K := univ)
      (hMP.imp_right univ_eq_empty_iff.2) hαc hα₀ hP₀α
    exact ⟨fun p ↦ τ' p.1, hτ'.comp continuous_fst, fun l ↦ rfl, fun p ↦ hnd p.1,
      fun l hl _ ↦ hP₀c l hl, fun l ↦ hc l (mem_univ l)⟩
  obtain ⟨_, ⟨l₀⟩⟩ : Nonempty M ∧ Nonempty P := by
    rw [not_or, not_isEmpty_iff, not_isEmpty_iff] at hMP
    exact hMP
  obtain ⟨g, d, e, hg, hemono, hetop, he₀, hc⟩ := exists_bandCore_levels hM (hnd l₀)
  -- The data of the stages, defined by recursion, and their composition.
  choose next Φ hΦ hΦ₀ hΦ₁ hΦnd hΦg hθg hΦP₀ using
    fun k (s : ContinuousStageData I M P T g (e k) P₀ α) ↦
      s.exists_next fr W hW (hc k).some hg hcover hP₀
  let s₀ : ContinuousStageData I M P T g (e 0) P₀ α :=
    { StageData.init he₀ hαc (fun l _ ↦ hnd l) hP₀α with
      m := 0, B := fun _ ↦ 0, u := fun _ ↦ 0, hτ := hτ', hα := hα,
      hB := isSmoothFamily_const 0, hu := continuous_const, hβ := fun _ ↦ rfl }
  obtain ⟨seq, ε, hseq₀, hUcov, hseam, hΦU, hεU, hεnd, hεP₀, hε⟩ :=
    exists_seq_of_stages hg hemono hetop hαc hα₀ (fun _ s ↦ s.toStageData) next Φ hΦ₀ hΦ₁
      (fun k s l _ t ↦ hΦnd k s l t) hΦg hθg hΦP₀ s₀
  refine ⟨_, Bundle.ContMDiffTwoForm.continuous_tangentEquiv_symm_infiniteConcat fr W hW
      (fun n ↦ hΦ n (seq n)) hseam (fun n ↦ isOpen_lt hg continuous_const) hUcov hΦU hεU,
    fun l ↦ ?_, fun p ↦ hεnd p.1 (mem_univ _) p.2, hεP₀,
    fun l ↦ by simpa only [infiniteConcat_one] using hε l⟩
  rw [infiniteConcat_zero, hΦ₀, hseq₀]
  rfl

/-- **The relative h-principle for a continuous path of nondegenerate forms with closed ends.**
Let `M` be a manifold without boundary none of whose connected components is compact, give the
smooth two-forms on its tangent bundle the frame topology of a covering frame system, and let
`τ` be a continuous path of nondegenerate two-forms whose ends are closed with `τ 0 - α₀` and
`τ 1 - α₀` exact. Then there is a continuous family `H` over `[0, 1] × [0, 1]` of nondegenerate
two-forms with `H (t, 0) = τ t` such that

* `H (t, u)` is closed and `H (t, u) - α₀` is exact for `t = 0` and `t = 1`;
* `H (t, 1)` is closed and `H (t, 1) - α₀` is exact for every `t`.

This is `SymplecticGeometry.exists_continuousMap_homotopy_closed` for `P₀ = {0, 1}`, with the
segment `s ↦ τ 0 + s • (τ 1 - τ 0)` as the family `α`. -/
theorem exists_continuousMap_homotopy_closed_of_ends
    (hM : ∀ x : M, ¬ IsCompact (connectedComponent x)) (hcover : ∀ x, ∃ j, x ∈ W j) :
    letI := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
    ∀ (τ : C(unitInterval,
        {σ : Bundle.ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M)) // σ.IsNondegenerate}))
      {α₀ : SmoothTwoForm I M},
      mextDerivₗ I 2 (Bundle.ContMDiffTwoForm.tangentEquiv (τ 0).val) = 0 →
      mextDerivₗ I 2 (Bundle.ContMDiffTwoForm.tangentEquiv (τ 1).val) = 0 →
      Bundle.ContMDiffTwoForm.tangentEquiv (τ 0).val - α₀ ∈ exactForms I M 2 →
      Bundle.ContMDiffTwoForm.tangentEquiv (τ 1).val - α₀ ∈ exactForms I M 2 →
      ∃ H : C(unitInterval × unitInterval,
          {σ : Bundle.ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M)) // σ.IsNondegenerate}),
        (∀ t, H (t, 0) = τ t) ∧
        (∀ t ∈ ({0, 1} : Set unitInterval), ∀ u,
          mextDerivₗ I 2 (Bundle.ContMDiffTwoForm.tangentEquiv (H (t, u)).val) = 0 ∧
          Bundle.ContMDiffTwoForm.tangentEquiv (H (t, u)).val - α₀ ∈ exactForms I M 2) ∧
        ∀ t, mextDerivₗ I 2 (Bundle.ContMDiffTwoForm.tangentEquiv (H (t, 1)).val) = 0 ∧
          Bundle.ContMDiffTwoForm.tangentEquiv (H (t, 1)).val - α₀ ∈ exactForms I M 2 := by
  intro τ α₀ h₀ h₁ h₀α h₁α
  let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
  let _ := ContMDiffSection.isTopologicalAddGroup_frameTopology (I := I)
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
  let _ := ContMDiffSection.continuousSMul_frameTopology (𝕜 := ℝ) (I := I)
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
  set ω₀ := Bundle.ContMDiffTwoForm.tangentEquiv (τ 0).val
  set ω₁ := Bundle.ContMDiffTwoForm.tangentEquiv (τ 1).val
  refine exists_continuousMap_homotopy_closed fr W hW hM hcover (Set.toFinite _).isClosed τ
    (α := fun t : unitInterval ↦ ω₀ + (t : ℝ) • (ω₁ - ω₀)) ?_ (fun t ↦ ?_) (fun t ↦ ?_) ?_
  · simp only [map_add, map_smul, map_sub, LinearEquiv.symm_apply_apply, ω₀, ω₁]
    fun_prop
  · simp [h₀, h₁]
  · convert add_mem h₀α (Submodule.smul_mem _ (t : ℝ) (sub_mem h₁α h₀α)) using 1
    module
  · rintro t (rfl | rfl) <;> simp [ω₀, ω₁]

end Continuous

end SymplecticGeometry

end
