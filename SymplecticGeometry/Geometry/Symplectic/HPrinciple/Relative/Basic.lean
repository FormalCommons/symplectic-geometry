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
# The parametric relative h-principle for symplectic forms, smooth version

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

## Proof

`SymplecticGeometry.exists_isMorse_bandCore_seq` gives a proper Morse function `g` and levels
`d k < e k < d (k + 1)` tending to infinity, with band cores for `(d k, e k, e (k + 1))`. The data
carried from stage to stage are the families `τ`, `α`, `β` of the stages of `Relative/Stage.lean`,
the open set `N ⊇ {g ≤ e k}` on which `τ = α + d β`, and a one-form `δ` with `α = αs + d δ` for
the starting family `αs`. Stage `k` is `SymplecticGeometry.BandCore.exists_stage_family`; it
changes nothing near `{g ≤ e k}`. The stages, run on the times `[1 - 2⁻ᵏ, 1 - 2⁻ᵏ⁻¹]`, are
concatenated by `SymplecticGeometry.exists_isSmoothFamily_infiniteConcat` over the open cover by
the sets `{g < e (k + 1)}`. Its end agrees on `{g < e (k + 1)}` with the end of stage `k`, which
is `αs + d (δ + β)` there; the one-forms `δ + β` settle on that cover too, and their limit
(`TauCeti.SmoothForm.exists_eq_limit`) writes the end as `αs + d θ`. Over `P₀` every stage runs
through closed forms in the class.

When `M` is empty or `K` is empty, the constant homotopy works. Otherwise a nondegenerate form at
a point makes the dimension even (`TauCeti.SymplecticForm.even_finrank`), as
`SymplecticGeometry.exists_isMorse_bandCore_seq` requires.

## Main results

* `SymplecticGeometry.exists_isSmoothFamily_homotopy_closed`: the smooth version of the
  parametric relative h-principle.
* `SymplecticGeometry.exists_isSmoothFamily_homotopy_closed_unitInterval`: the same for a family
  over `[0, 1]`.
* `SymplecticGeometry.exists_isSmoothFamily_homotopy_closed_unitInterval_of_ends`: the case of a
  path whose ends are closed in the class of `α₀`, with `P₀ = {0, 1}`.

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
  [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
  {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

/-- The data carried from one stage of the relative h-principle to the next, at the level `a` of
`g`: smooth families `τ`, `α`, `β` over `L`, with `α l` closed and `τ l` nondegenerate for
`l ∈ K`, such that `τ l = α l + d (β l)` on an open `N ⊇ {g ≤ a}`, and everywhere for `l ∈ P₀`;
and one-forms `δ l` with `α l = αs l + d (δ l)` for the starting family `αs`. -/
private structure StageData (I : ModelWithCorners ℝ E H) (M L : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [NormedAddCommGroup L] [NormedSpace ℝ L]
    (g : M → ℝ) (a : ℝ) (K P₀ : Set L) (αs : L → SmoothTwoForm I M) where
  τ : L → SmoothTwoForm I M
  α : L → SmoothTwoForm I M
  β : L → SmoothForm I M ℝ 1
  δ : L → SmoothForm I M ℝ 1
  N : Set M
  hτ : IsSmoothFamily 𝓘(ℝ, L) τ
  hα : IsSmoothFamily 𝓘(ℝ, L) α
  hβ : IsSmoothFamily 𝓘(ℝ, L) β
  hαc : ∀ l, mextDerivₗ I 2 (α l) = 0
  hnd : ∀ l ∈ K, (τ l).IsNondegenerate
  hN : IsOpen N
  haN : {x | g x ≤ a} ⊆ N
  hτN : ∀ l, ∀ x ∈ N, (τ l).val x = (α l + mextDerivₗ I 1 (β l)).val x
  hτP₀ : ∀ l ∈ P₀, τ l = α l + mextDerivₗ I 1 (β l)
  hδ : ∀ l, α l = αs l + mextDerivₗ I 1 (δ l)

variable [I.Boundaryless]

/-- One stage, on the data of `StageData`: from the data at the level `a`, the data at the level
`b` and the homotopy between them, which changes neither the forms nor `δ + β` on a set
containing `{g ≤ a}`. -/
private theorem StageData.exists_next {g : M → ℝ} {a₀ a b : ℝ} (c : BandCore I g a₀ a b)
    (hg : Continuous g) {K P₀ : Set L} (hK : IsCompact K) (hP₀ : IsClosed P₀)
    {αs : L → SmoothTwoForm I M} (s : StageData I M L g a K P₀ αs) :
    ∃ (s' : StageData I M L g b K P₀ αs) (H : L × unitInterval → SmoothTwoForm I M) (V : Set M),
      IsSmoothFamily (𝓘(ℝ, L).prod (𝓡∂ 1)) H ∧ (∀ l, H (l, 0) = s.τ l) ∧
      (∀ l, H (l, 1) = s'.τ l) ∧ (∀ l ∈ K, ∀ t, (H (l, t)).IsNondegenerate) ∧
      {x | g x ≤ a} ⊆ V ∧
      (∀ l t, ∀ x ∈ V, (H (l, t)).val x = (s.τ l).val x ∧
        (s'.δ l + s'.β l).val x = (s.δ l + s.β l).val x) ∧
      ∀ l ∈ P₀, ∀ t, mextDerivₗ I 2 (H (l, t)) = 0 ∧ H (l, t) - s.α l ∈ exactForms I M 2 := by
  obtain ⟨H, α', β', V, N', hH, hα', hβ', hH₀, hHnd, hV, hHV, hα'c, hN', hbN', hHN', hHP₀⟩ :=
    c.exists_stage_family hg hK hP₀ s.hτ s.hα s.hαc s.hnd s.hβ s.hN s.haN s.hτN s.hτP₀
  choose hα'd γ hγ hγV using hα'c
  have h₁ : ContMDiff 𝓘(ℝ, L) (𝓘(ℝ, L).prod (𝓡∂ 1)) ∞ fun l : L ↦ (l, (1 : unitInterval)) :=
    contMDiff_id.prodMk contMDiff_const
  refine ⟨⟨fun l ↦ H (l, 1), α', β', fun l ↦ s.δ l + γ l, N', hH.comp _ h₁, hα', hβ', hα'd,
      fun l hl ↦ hHnd l hl 1, hN', hbN', hHN', fun l hl ↦ (hHP₀ l hl).1, fun l ↦ ?_⟩,
    H, V, hH, hH₀, fun l ↦ rfl, hHnd, subset_of_mem_nhdsSet hV, fun l t x hx ↦ ?_,
    fun l hl t ↦ (hHP₀ l hl).2 t⟩
  · rw [hγ, s.hδ, map_add, add_assoc]
  · obtain ⟨h₁, -, h₃⟩ := hHV l t x hx
    refine ⟨h₁, ?_⟩
    simp only [SmoothBundleForm.add_apply, hγV l x hx, h₃, add_zero]

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [FiniteDimensional ℝ L]
  [I.Boundaryless] in
/-- The constant homotopy, when `M` or `K` is empty. -/
private theorem exists_isSmoothFamily_homotopy_closed_of_isEmpty {K P₀ : Set L}
    (hMK : IsEmpty M ∨ K = ∅) {τ : L → SmoothTwoForm I M} (hτ : IsSmoothFamily 𝓘(ℝ, L) τ)
    (hnd : ∀ l ∈ K, (τ l).IsNondegenerate) {α : L → SmoothTwoForm I M}
    (hαc : ∀ l, mextDerivₗ I 2 (α l) = 0) {α₀ : SmoothTwoForm I M}
    (hα₀ : ∀ l, α l - α₀ ∈ exactForms I M 2) (hP₀α : ∀ l ∈ P₀, α l = τ l) :
    ∃ H : L × unitInterval → SmoothTwoForm I M, IsSmoothFamily (𝓘(ℝ, L).prod (𝓡∂ 1)) H ∧
      (∀ l, H (l, 0) = τ l) ∧ (∀ l ∈ K, ∀ t, (H (l, t)).IsNondegenerate) ∧
      (∀ l ∈ P₀, ∀ t, mextDerivₗ I 2 (H (l, t)) = 0 ∧ H (l, t) - α₀ ∈ exactForms I M 2) ∧
      ∀ l ∈ K, mextDerivₗ I 2 (H (l, 1)) = 0 ∧ H (l, 1) - α₀ ∈ exactForms I M 2 := by
  refine ⟨fun p ↦ τ p.1, hτ.comp _ contMDiff_fst, fun l ↦ rfl, fun l hl _ ↦ hnd l hl,
    fun l hl _ ↦ by simpa only [← hP₀α l hl] using ⟨hαc l, hα₀ l⟩, fun l hl ↦ ?_⟩
  rcases hMK with hM | rfl
  · -- On an empty manifold every form is zero.
    rw [Subsingleton.elim (mextDerivₗ I 2 (τ l)) 0, Subsingleton.elim (τ l - α₀) 0]
    exact ⟨rfl, zero_mem _⟩
  · exact absurd hl (notMem_empty l)

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
  · exact exists_isSmoothFamily_homotopy_closed_of_isEmpty hMK hτ hnd hαc hα₀ hP₀α
  obtain ⟨⟨x₀⟩, ⟨l₀, hl₀⟩⟩ : Nonempty M ∧ K.Nonempty := by
    rw [not_or, not_isEmpty_iff, ← ne_eq, ne_empty_iff_nonempty] at hMK
    exact hMK
  -- A nondegenerate form at a point makes the dimension even.
  have hE : Module.finrank ℝ E ≠ 1 := by
    obtain ⟨n, hn⟩ := ((hnd l₀ hl₀).symplecticFormAt x₀).even_finrank
    -- The tangent space at `x₀` is `E` by definition.
    change Module.finrank ℝ E = n + n at hn
    omega
  obtain ⟨g, d, e, -, -, he₀, hde, hd, hc⟩ := exists_isMorse_bandCore_seq (I := I) hE hM
  have hg : Continuous g := g.contMDiff.continuous
  have hemono : StrictMono e := strictMono_nat_of_lt_succ fun k ↦ (hde k).2.trans (hde (k + 1)).1
  have hetop : Tendsto e atTop atTop :=
    tendsto_atTop_mono (fun k ↦ (hde k).1.le) hd
  -- The data of the stages, defined by recursion.
  choose next Φ V hΦ hΦ₀ hΦ₁ hΦnd hV hΦV hΦP₀ using fun k (s : StageData I M L g (e k) K P₀ α) ↦
    s.exists_next (hc k).some hg hK hP₀
  let s₀ : StageData I M L g (e 0) K P₀ α :=
    { τ := τ, α := α, β := 0, δ := 0, N := ∅, hτ := hτ, hα := hα, hβ := isSmoothFamily_const 0,
      hαc := hαc, hnd := hnd, hN := isOpen_empty,
      haN := fun x hx ↦ absurd (show g x ≤ e 0 from hx) (he₀ x).not_ge,
      hτN := fun _ _ hx ↦ absurd hx (notMem_empty _),
      hτP₀ := fun l hl ↦ by simp [hP₀α l hl],
      hδ := fun l ↦ by simp }
  let seq : (k : ℕ) → StageData I M L g (e k) K P₀ α :=
    fun k ↦ Nat.rec (motive := fun k ↦ StageData I M L g (e k) K P₀ α) s₀
      (fun k s ↦ next k s) k
  have hseq (k : ℕ) : seq (k + 1) = next k (seq k) := rfl
  let Ψ : ℕ → L × unitInterval → SmoothTwoForm I M := fun k ↦ Φ k (seq k)
  have hΨ (k : ℕ) (p : L × unitInterval) : Ψ k p = Φ k (seq k) p := rfl
  -- The forms `τ` of the stages settle on `{g ≤ e k}`, and so do the one-forms `δ + β`.
  have hτset (l : L) {n m : ℕ} (hnm : n ≤ m) {x : M} (hx : g x ≤ e n) :
      ((seq m).τ l).val x = ((seq n).τ l).val x := by
    refine (Nat.rel_of_forall_rel_succ_of_le_of_le (· = ·) (f := fun k ↦ ((seq k).τ l).val x)
      (fun k hk ↦ ?_) le_rfl hnm).symm
    rw [hseq, ← hΦ₁ k (seq k) l]
    exact (hΦV k (seq k) l 1 x (hV k (seq k) (hx.trans (hemono.monotone hk)))).1.symm
  have hθset (l : L) {n m : ℕ} (hnm : n ≤ m) {x : M} (hx : g x ≤ e n) :
      ((seq m).δ l + (seq m).β l).val x = ((seq n).δ l + (seq n).β l).val x := by
    refine (Nat.rel_of_forall_rel_succ_of_le_of_le (· = ·)
      (f := fun k ↦ ((seq k).δ l + (seq k).β l).val x) (fun k hk ↦ ?_) le_rfl hnm).symm
    rw [hseq]
    exact (hΦV k (seq k) l 0 x (hV k (seq k) (hx.trans (hemono.monotone hk)))).2.symm
  -- The open cover by the sets `{g < e (n + 1)}`, on which the later stages no longer move.
  set U : ℕ → Set M := fun n ↦ {x | g x < e (n + 1)}
  have hUo (n : ℕ) : IsOpen (U n) := isOpen_lt hg continuous_const
  have hUcov (x : M) : ∃ n, x ∈ U n :=
    ((hetop.comp (tendsto_add_atTop_nat 1)).eventually_gt_atTop (g x)).exists
  have hseam (n : ℕ) (l : L) : Ψ (n + 1) (l, 0) = Ψ n (l, 1) := by
    simp only [hΨ, hΦ₀, hΦ₁, hseq]
  have hΨU (n m : ℕ) (hnm : n < m) (p : L × unitInterval) (x : M) (hx : x ∈ U n) :
      (Ψ m p).val x = (Ψ n (p.1, 1)).val x := by
    have hxm : g x ≤ e m := (show g x < e (n + 1) from hx).le.trans (hemono.monotone hnm)
    rw [hΨ, (hΦV m (seq m) p.1 p.2 x (hV m (seq m) hxm)).1, hτset p.1 hnm hx.le, hΨ, hΦ₁, ← hseq]
  obtain ⟨ε, hεU, hHs⟩ := exists_isSmoothFamily_infiniteConcat (fun n ↦ hΦ n (seq n)) hseam
    hUo hUcov hΨU
  -- The end is `α l + d θ l`, for the limit `θ l` of the one-forms `δ + β` after each stage.
  have hlim (l : L) := SmoothForm.exists_eq_limit hUo hUcov
    (η := fun n ↦ (seq (n + 1)).δ l + (seq (n + 1)).β l) fun n m hnm x hx ↦
      hθset l (n := n + 1) (m := m + 1) (by omega) (show g x < e (n + 1) from hx).le
  choose θ hθ using hlim
  have hε (l : L) : ε l = α l + mextDerivₗ I 1 (θ l) := Subtype.ext <| funext fun x ↦ by
    obtain ⟨n, hn⟩ := hUcov x
    have hxN : x ∈ (seq (n + 1)).N := (seq (n + 1)).haN (show g x ≤ e (n + 1) from hn.le)
    rw [(hεU n l x hn).1, hΦ₁, ← hseq, (seq (n + 1)).hτN l x hxN, (seq (n + 1)).hδ l,
      add_assoc, ← map_add, SmoothBundleForm.add_apply, SmoothBundleForm.add_apply,
      ← (hθ l n x hn).2]
  have hεc (l : L) : mextDerivₗ I 2 (ε l) = 0 ∧ ε l - α₀ ∈ exactForms I M 2 := by
    refine ⟨?_, ?_⟩
    · rw [hε, map_add, hαc, zero_add]
      exact LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ I 1) (θ l)
    · rw [hε, add_sub_right_comm]
      exact add_mem (hα₀ l) (by rw [exactForms_succ]; exact ⟨θ l, rfl⟩)
  refine ⟨_, hHs, fun l ↦ ?_, fun l hl t ↦ ?_, fun l hl t ↦ ?_, fun l _ ↦ ?_⟩
  · rw [infiniteConcat_zero]
    exact hΦ₀ 0 s₀ l
  · refine infiniteConcat_mem (s := {σ : SmoothTwoForm I M | σ.IsNondegenerate})
      (fun n t ↦ hΦnd n (seq n) l hl t) ?_ t
    -- Nondegeneracy is pointwise, and the end agrees near each point with the end of a stage.
    rw [mem_ofPred_eq, SmoothTwoForm.isNondegenerate_iff_forall_ker_bilinFormAt_eq_bot]
    intro x
    obtain ⟨n, hn⟩ := hUcov x
    have h := SmoothTwoForm.isNondegenerate_iff_forall_ker_bilinFormAt_eq_bot.1
      (hΦnd n (seq n) l hl 1) x
    rwa [SmoothForm.bilinFormAt_def, ← (hεU n l x hn).1, ← SmoothForm.bilinFormAt_def] at h
  · refine infiniteConcat_mem
      (s := {σ : SmoothTwoForm I M | mextDerivₗ I 2 σ = 0 ∧ σ - α₀ ∈ exactForms I M 2})
      (fun n t ↦ ⟨(hΦP₀ n (seq n) l hl t).1, ?_⟩) (hεc l) t
    have h := add_mem (add_mem (hΦP₀ n (seq n) l hl t).2
      (show (seq n).α l - α l ∈ exactForms I M 2 by
        rw [(seq n).hδ l, add_sub_cancel_left, exactForms_succ]; exact ⟨_, rfl⟩)) (hα₀ l)
    simpa only [sub_add_sub_cancel] using h
  · simpa only [infiniteConcat_one] using hεc l

/-- **The parametric relative h-principle for symplectic forms over `[0, 1]`.** Let `M` be a
manifold without boundary none of whose connected components is compact and `P₀ ⊆ [0, 1]` closed.
Let `τ : [0, 1] → SmoothTwoForm I M` be smooth with every `τ t` nondegenerate, and
`α : ℝ → SmoothTwoForm I M` smooth with every `α s` closed, every `α s - α₀` exact and
`α t = τ t` for `t ∈ P₀`. Then there is a smooth family `H` over `[0, 1] × [0, 1]` with `H (t, 0) = τ t` such that

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
`τ 1` are closed with `τ 0 - α₀` and `τ 1 - α₀` exact. Then there is a smooth family `H` over `[0, 1] × [0, 1]` with
`H (t, 0) = τ t` such that

* every `H (t, u)` is nondegenerate;
* `H (t, u)` is closed and `H (t, u) - α₀` is exact for `t = 0` and `t = 1`;
* `H (t, 1)` is closed and `H (t, 1) - α₀` is exact for every `t`.

This is `SymplecticGeometry.exists_isSmoothFamily_homotopy_closed_unitInterval` for
`P₀ = {0, 1}`, with the segment `s ↦ (1 - s) • τ 0 + s • τ 1` as the family `α`. -/
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
    (isSmoothFamily_one_sub_smul_add_smul (τ 0) (τ 1)) (fun s ↦ ?_) (fun s ↦ ?_) ?_
  · rw [map_add, map_smul, map_smul, h₀, h₁, smul_zero, smul_zero, add_zero]
  · convert add_mem (Submodule.smul_mem _ (1 - s) h₀α) (Submodule.smul_mem _ s h₁α) using 1
    module
  · rintro t (rfl | rfl) <;> simp

end SymplecticGeometry

end
