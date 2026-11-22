/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.DistributionalRegularity
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.LineDeriv
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Smoothness

/-!
# Interior regularity of elliptic systems with a scalar principal part

Let `T : ι → 𝓓'(Ω, ℂ)` be a finite family of complex distributions on an open set
`Ω ⊆ CoordinateSpace n`. Let `P = ∑ i ∈ t, c i g i ∂^(m i)` be a scalar differential operator of
order `M`, with smooth real coefficients, as in Tau Ceti's
`Distribution.IsLocallySobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp`. Let
`Q a b = ∑ j ∈ t', c' a b j h a b j ∂^(m' j)` be differential operators with smooth real
coefficients and orders `k' j < M`. This file proves interior regularity for the system

`P T a + ∑ b, Q a b (T b) = F a`,

whose principal part is `P` times the identity:

* `Distribution.IsLocallySobolevAt.of_ellipticSystem`: if `P` is elliptic at `x` and every `F a`
  is `H^s` near `x`, then every `T a` is `H^(s + M)` near `x`;
* `Distribution.singularSupport_eq_empty_of_ellipticSystem`: if `P` is elliptic at every point of
  `Ω` and every `F a` is smooth on `Ω`, then every `T a` is smooth on `Ω`.

The hypothesis `k' j < M` is needed: for `M = 0`, `P = 1` and `Q a a = -1`, every `F a` is zero
whatever `T` is.

The proof is a bootstrap. Every distribution is `H^r` near `x` for some `r`
(`Distribution.exists_forall_isLocallySobolevAt`). If every `T b` is `H^r` near `x`, the coupling
terms are `H^(r + 1 - M)` near `x`
(`Distribution.IsLocallySobolevAt.sum_smul_smulLeftCLM_iteratedLineDerivOp`), so every `P T a` is
`H^(min s (r + 1 - M))` near `x` and, by the scalar theorem, every `T a` is
`H^(min (s + M) (r + 1))` near `x`. Each step gains one order until `s + M` is reached.

## Main results

* `Distribution.IsLocallySobolevAt.sum`: a finite sum of distributions that are `H^s` near `x` is
  `H^s` near `x`.
* `Distribution.singularSupport_eq_empty_of_forall_isLocallySobolevAt`: a distribution that is,
  near every point, `M` orders more regular than a family of smooth distributions is smooth.
* `Distribution.IsLocallySobolevAt.of_ellipticSystem`,
  `Distribution.singularSupport_eq_empty_of_ellipticSystem`.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §6 (regularity of elliptic operators by bootstrapping).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

open TopologicalSpace TauCeti
open scoped ContDiff Distributions LineDeriv

namespace Distribution

section Sum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

/-- A finite sum of distributions that are `H^s` near a point `x ∈ Ω` is `H^s` near `x`. -/
theorem IsLocallySobolevAt.sum {ι : Type*} {u : Finset ι} {s : ℝ} {T : ι → 𝓓'(Ω, ℂ)} {x : E}
    (hx : x ∈ Ω) (h : ∀ i ∈ u, (T i).IsLocallySobolevAt s x) :
    (∑ i ∈ u, T i).IsLocallySobolevAt s x := by
  refine (notMem_sobolevSingularSupport_iff hx).1 fun hmem ↦ ?_
  obtain ⟨i, hi, hiT⟩ := Set.mem_iUnion₂.1 (sobolevSingularSupport_sum_subset s u T hmem)
  exact (notMem_sobolevSingularSupport_iff hx).2 (h i hi) hiT

/-- Let `T` and the `S b` be distributions on `Ω`, with every `S b` smooth on `Ω`. If, at every
`x ∈ Ω` and for every `s`, `T` is `H^(s + M)` near `x` whenever every `S b` is `H^s` near `x`,
then `T` is smooth on `Ω`. -/
theorem singularSupport_eq_empty_of_forall_isLocallySobolevAt {κ : Type*} {S : κ → 𝓓'(Ω, ℂ)}
    {T : 𝓓'(Ω, ℂ)} {M : ℝ} (hS : ∀ b, (S b).singularSupport = ∅)
    (h : ∀ x ∈ Ω, ∀ s, (∀ b, (S b).IsLocallySobolevAt s x) → T.IsLocallySobolevAt (s + M) x) :
    T.singularSupport = ∅ := by
  refine singularSupport_eq_empty_iff_forall_sobolevSingularSupport_eq_empty.2 fun s ↦
    Set.eq_empty_of_forall_notMem fun x hx ↦ ?_
  have hxΩ := (mem_sobolevSingularSupport_iff.1 hx).1
  refine (notMem_sobolevSingularSupport_iff hxΩ).2 ?_ hx
  have h := h x hxΩ (s - M) fun b ↦ (notMem_sobolevSingularSupport_iff hxΩ).1 <| by
    rw [singularSupport_eq_empty_iff_forall_sobolevSingularSupport_eq_empty.1 (hS b)]
    exact Set.notMem_empty x
  rwa [sub_add_cancel] at h

end Sum

variable {n : ℕ} {Ω : Opens (CoordinateSpace n)} {ι α β : Type*} [Fintype ι]
  {t : Finset α} {c : α → ℂ} {g : α → CoordinateSpace n → ℝ} {k : α → ℕ}
  {m : ∀ i, Fin (k i) → CoordinateSpace n}
  {t' : Finset β} {c' : ι → ι → β → ℂ} {h : ι → ι → β → CoordinateSpace n → ℝ} {k' : β → ℕ}
  {m' : ∀ j, Fin (k' j) → CoordinateSpace n}

/-- The coupling terms lose at most `M - 1` orders: if every `T b` is `H^r` near `x`, then
`∑ b, Q a b (T b)` is `H^(r + 1 - M)` near `x`. -/
private theorem isLocallySobolevAt_coupling (hh : ∀ a b j, ContDiff ℝ ∞ (h a b j)) {M : ℕ}
    (hk' : ∀ j ∈ t', k' j < M) {T : ι → 𝓓'(Ω, ℂ)} {x : CoordinateSpace n} (hx : x ∈ Ω) {r : ℝ}
    (hT : ∀ b, (T b).IsLocallySobolevAt r x) (a : ι) :
    IsLocallySobolevAt (r + 1 - M)
      (∑ b, ∑ j ∈ t', c' a b j • Distribution.smulLeftCLM (hh a b j) (∂^{m' j} (T b))) x := by
  refine IsLocallySobolevAt.sum hx fun b _ ↦ ?_
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · rw [Finset.sum_eq_zero fun j hj ↦ absurd (hk' j hj) (Nat.not_lt_zero _)]
    simpa using hx
  · have := (hT b).sum_smul_smulLeftCLM_iteratedLineDerivOp t' (c' a b) (hh a b) m'
      (k := M - 1) fun j hj ↦ Nat.le_sub_one_of_lt (hk' j hj)
    rwa [Nat.cast_pred hM, sub_sub_eq_add_sub] at this

/-- One step of the bootstrap: if every `T b` is `H^r` near `x`, every `T a` is
`H^(min s (r + 1 - M) + M)` near `x`. -/
private theorem isLocallySobolevAt_ellipticSystem_step (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (hh : ∀ a b j, ContDiff ℝ ∞ (h a b j)) {M : ℕ} (hk : ∀ i ∈ t, k i ≤ M)
    (hk' : ∀ j ∈ t', k' j < M) {T : ι → 𝓓'(Ω, ℂ)} {x : CoordinateSpace n} {s : ℝ}
    (hσ : ∀ ξ, ξ ≠ 0 → constCoeffPrincipalSymbol t (fun i ↦ c i * g i x) m M ξ ≠ 0)
    (hPT : ∀ a, IsLocallySobolevAt s
      (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} (T a)) +
        ∑ b, ∑ j ∈ t', c' a b j • Distribution.smulLeftCLM (hh a b j) (∂^{m' j} (T b))) x)
    {r : ℝ} (hT : ∀ b, (T b).IsLocallySobolevAt r x) (a : ι) :
    (T a).IsLocallySobolevAt (min s (r + 1 - M) + M) x := by
  refine IsLocallySobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp hg hk hσ ?_
  have hQ := isLocallySobolevAt_coupling (c' := c') (m' := m') hh hk' (hPT a).mem hT a
  simpa using ((hPT a).mono (min_le_left _ _)).sub (hQ.mono (min_le_right _ _))

/-- **Interior regularity of elliptic systems with a scalar principal part.** Let
`P = ∑ i ∈ t, c i g i ∂^(m i)` have smooth real coefficients and orders `k i ≤ M`, and be elliptic
at `x`. Let `Q a b = ∑ j ∈ t', c' a b j h a b j ∂^(m' j)` have smooth real coefficients and orders
`k' j < M`. If every `P T a + ∑ b, Q a b (T b)` is `H^s` near `x`, then every `T a` is
`H^(s + M)` near `x`. -/
theorem IsLocallySobolevAt.of_ellipticSystem (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (hh : ∀ a b j, ContDiff ℝ ∞ (h a b j)) {M : ℕ} (hk : ∀ i ∈ t, k i ≤ M)
    (hk' : ∀ j ∈ t', k' j < M) {T : ι → 𝓓'(Ω, ℂ)} {x : CoordinateSpace n} {s : ℝ}
    (hσ : ∀ ξ, ξ ≠ 0 → constCoeffPrincipalSymbol t (fun i ↦ c i * g i x) m M ξ ≠ 0)
    (hPT : ∀ a, IsLocallySobolevAt s
      (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} (T a)) +
        ∑ b, ∑ j ∈ t', c' a b j • Distribution.smulLeftCLM (hh a b j) (∂^{m' j} (T b))) x)
    (a : ι) : (T a).IsLocallySobolevAt (s + M) x := by
  -- A common finite order `r₀` of all components near `x`.
  choose r hr using fun b ↦ (T b).exists_forall_isLocallySobolevAt isCompact_singleton
    (Set.singleton_subset_iff.2 (hPT b).mem)
  obtain ⟨r₀, hr₀⟩ := Finite.exists_ge r
  -- After `N` steps, every component is `H^(min (s + M) (r₀ + N))` near `x`.
  have key (N : ℕ) (b : ι) : (T b).IsLocallySobolevAt (min (s + M) (r₀ + N)) x := by
    induction N generalizing b with
    | zero => exact (hr b x rfl).mono ((min_le_right _ _).trans (by simpa using hr₀ b))
    | succ N ih =>
      refine (isLocallySobolevAt_ellipticSystem_step hg hh hk hk' hσ hPT ih b).mono ?_
      rw [← min_add_add_right, sub_add_cancel, ← min_add_add_right, Nat.cast_succ]
      exact le_min (min_le_left _ _) (min_le_min (by linarith) (by linarith))
  refine (key ⌈s + M - r₀⌉₊ a).mono (le_min le_rfl ?_)
  linarith [Nat.le_ceil (s + M - r₀)]

/-- **Smoothness of solutions of elliptic systems with a scalar principal part.** Let
`P = ∑ i ∈ t, c i g i ∂^(m i)` have smooth real coefficients and orders `k i ≤ M`, and be elliptic
at every point of `Ω`. Let `Q a b = ∑ j ∈ t', c' a b j h a b j ∂^(m' j)` have smooth real
coefficients and orders `k' j < M`. If every `P T a + ∑ b, Q a b (T b)` is smooth on `Ω`, then
every `T a` is smooth on `Ω`. -/
theorem singularSupport_eq_empty_of_ellipticSystem (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (hh : ∀ a b j, ContDiff ℝ ∞ (h a b j)) {M : ℕ} (hk : ∀ i ∈ t, k i ≤ M)
    (hk' : ∀ j ∈ t', k' j < M) {T : ι → 𝓓'(Ω, ℂ)}
    (hσ : ∀ x ∈ Ω, ∀ ξ, ξ ≠ 0 → constCoeffPrincipalSymbol t (fun i ↦ c i * g i x) m M ξ ≠ 0)
    (hPT : ∀ a, singularSupport
      (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} (T a)) +
        ∑ b, ∑ j ∈ t', c' a b j • Distribution.smulLeftCLM (hh a b j) (∂^{m' j} (T b))) = ∅)
    (a : ι) : (T a).singularSupport = ∅ :=
  singularSupport_eq_empty_of_forall_isLocallySobolevAt hPT fun x hx _ hs ↦
    IsLocallySobolevAt.of_ellipticSystem hg hh hk hk' (hσ x hx) hs a

end Distribution

end
