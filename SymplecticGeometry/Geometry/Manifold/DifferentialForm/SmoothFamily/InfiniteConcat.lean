/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
public import SymplecticGeometry.Geometry.Manifold.Instances.Icc
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Exhaustion

/-!
# Infinite concatenation of smooth families of forms

Let `H n : N × [0, 1] → SmoothForm I M F k`, `n : ℕ`, be smooth families of forms over
`N × [0, 1]`, each starting where the previous one ends, `H (n + 1) (l, 0) = H n (l, 1)`, and let
`V n` be open sets covering `M` such that the later families no longer move on `V n`:
`H m (l, t) = H n (l, 1)` on `V n` for `m > n`. Run `H n` on the times `[1 - 2⁻ⁿ, 1 - 2⁻ⁿ⁻¹]`
and end at a form `E l` equal on each `V n` to `H n (l, 1)`; this is
`SymplecticGeometry.infiniteConcat` of `Geometry/Manifold/Instances/Icc.lean`. The result is a
smooth family over `N × [0, 1]` (`SymplecticGeometry.IsSmoothFamily.infiniteConcat`).

Before time `1` the concatenation is, near each time, one of the families `H n` reparametrized
by a smooth time step that is constant near the ends of its stage
(`SymplecticGeometry.infiniteConcat_of_mem_Ioo`), so it is smooth there. Near time `1` and a
point of `V n` it is constant in time, equal to `H n (l, 1)`
(`SymplecticGeometry.infiniteConcat_mem_of_le`). Smoothness of a family is local in the point,
by `SymplecticGeometry.isSmoothFamily_iff_contMDiff`.

The end forms exist, and have there the exterior derivatives of the `H n (l, 1)`, by
`TauCeti.SmoothForm.exists_eq_limit` (`DifferentialForm/Exhaustion.lean`); together this is
`SymplecticGeometry.exists_isSmoothFamily_infiniteConcat`.

## Main results

* `SymplecticGeometry.IsSmoothFamily.infiniteConcat`: the infinite concatenation of smooth
  families of forms that settle on the sets of an open cover, with a given end, is smooth.
* `SymplecticGeometry.exists_isSmoothFamily_infiniteConcat`: the end exists, and the
  concatenation with it is smooth.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14 (locality of the exterior derivative).
-/

public section

open TauCeti Bundle
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

variable {E H M EN HN N F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J 1 N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {Φ : ℕ → N × unitInterval → SmoothForm I M F k} {V : ℕ → Set M}

/-- **Infinite concatenation of smooth families of forms.** Let `Φ n` be smooth families of
forms over `N × [0, 1]` with `Φ (n + 1) (l, 0) = Φ n (l, 1)`, and `V n` open sets covering `M`
with `Φ m (l, t) = Φ n (l, 1)` on `V n` whenever `n < m`. Let `ε l` be a form equal on each
`V n` to `Φ n (l, 1)`. Then the infinite concatenation of the families `Φ n (l, ·)` ending at
`ε l` is a smooth family over `N × [0, 1]`. -/
protected theorem IsSmoothFamily.infiniteConcat {ε : N → SmoothForm I M F k}
    (hΦ : ∀ n, IsSmoothFamily (J.prod (𝓡∂ 1)) (Φ n))
    (hseam : ∀ n l, Φ (n + 1) (l, 0) = Φ n (l, 1))
    (hVo : ∀ n, IsOpen (V n)) (hV : ∀ x, ∃ n, x ∈ V n)
    (hΦV : ∀ n m, n < m → ∀ p, ∀ x ∈ V n, (Φ m p).val x = (Φ n (p.1, 1)).val x)
    (hε : ∀ n l, ∀ x ∈ V n, (ε l).val x = (Φ n (l, 1)).val x) :
    IsSmoothFamily (J.prod (𝓡∂ 1))
      (fun p : N × unitInterval ↦ infiniteConcat (fun n s ↦ Φ n (p.1, s)) (ε p.1) p.2) := by
  rw [isSmoothFamily_iff_contMDiff]
  rintro ⟨⟨l, t⟩, x⟩
  rcases lt_or_ge (t : ℝ) 1 with ht | ht
  · -- Before time `1`, near the stage `n` of `t`, the concatenation is `Φ n` reparametrized.
    obtain ⟨n, hn₀, hn₁⟩ := exists_mem_Ico_two_sub_two_pow_mul ht
    have hs : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ fun s : unitInterval ↦ 2 - 2 ^ (n + 1) * (1 - (s : ℝ)) :=
      (contDiff_const.sub (contDiff_const.mul (contDiff_const.sub contDiff_id))).contMDiff.comp
        contMDiff_subtypeVal_Icc
    have hG := (hΦ n).comp (fun p : N × unitInterval ↦
        (p.1, collaredSmoothTransitionUnit (2 - 2 ^ (n + 1) * (1 - (p.2 : ℝ)))))
      (contMDiff_fst.prodMk ((contMDiff_collaredSmoothTransitionUnit le_rfl).comp
        (hs.comp contMDiff_snd)))
    rw [isSmoothFamily_iff_contMDiff] at hG
    refine (hG _).congr_of_eventuallyEq ?_
    have hc : Continuous fun q : (N × unitInterval) × M ↦
        2 - 2 ^ (n + 1) * (1 - ((q.1.2 : unitInterval) : ℝ)) := by fun_prop
    have hopen : IsOpen {q : (N × unitInterval) × M |
        -1 / 8 < 2 - 2 ^ (n + 1) * (1 - ((q.1.2 : unitInterval) : ℝ)) ∧
          2 - 2 ^ (n + 1) * (1 - ((q.1.2 : unitInterval) : ℝ)) < 9 / 8} :=
      (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
    filter_upwards [hopen.mem_nhds ⟨by linarith, by linarith⟩] with q hq
    rw [sliceSection_apply, sliceSection_apply,
      infiniteConcat_of_mem_Ioo (fun m ↦ hseam m q.1.1) hq.1 hq.2]
  · -- Near time `1` and a point of `V n`, the concatenation is `Φ n (l, 1)` there.
    obtain ⟨n, hx⟩ := hV x
    have hG := (hΦ n).comp (fun p : N × unitInterval ↦ (p.1, (1 : unitInterval)))
      (contMDiff_fst.prodMk contMDiff_const : ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)) ∞ _)
    rw [isSmoothFamily_iff_contMDiff] at hG
    refine (hG _).congr_of_eventuallyEq ?_
    have hc : Continuous fun q : (N × unitInterval) × M ↦
        2 ^ (n + 1) * (1 - ((q.1.2 : unitInterval) : ℝ)) := by fun_prop
    have hopen : IsOpen {q : (N × unitInterval) × M |
        2 ^ (n + 1) * (1 - ((q.1.2 : unitInterval) : ℝ)) < 1 ∧ q.2 ∈ V n} :=
      (isOpen_lt hc continuous_const).inter ((hVo n).preimage continuous_snd)
    have h1 : (t : ℝ) = 1 := le_antisymm (unitInterval.le_one t) ht
    filter_upwards [hopen.mem_nhds ⟨by simp [h1], hx⟩] with q hq
    have hmem := infiniteConcat_mem_of_le (a := fun m s ↦ Φ m (q.1.1, s)) (e := ε q.1.1)
      (s := {η | η.val q.2 = (Φ n (q.1.1, 1)).val q.2}) (fun m hm s ↦ hΦV n m hm _ q.2 hq.2)
      (hε n q.1.1 q.2 hq.2) hq.1.le
    rw [sliceSection_apply, sliceSection_apply]
    exact congrArg _ hmem

/-- **Infinite concatenation of smooth families of forms, with its end.** Let `Φ n` be smooth
families of forms over `N × [0, 1]` with `Φ (n + 1) (l, 0) = Φ n (l, 1)`, and `V n` open sets
covering `M` with `Φ m (l, t) = Φ n (l, 1)` on `V n` whenever `n < m`. Then there are forms
`ε l`, equal on each `V n` to `Φ n (l, 1)` and with the same exterior derivative there, such that
the infinite concatenation of the families `Φ n (l, ·)` ending at `ε l` is a smooth family over
`N × [0, 1]`. -/
theorem exists_isSmoothFamily_infiniteConcat [IsManifold I 2 M]
    (hΦ : ∀ n, IsSmoothFamily (J.prod (𝓡∂ 1)) (Φ n))
    (hseam : ∀ n l, Φ (n + 1) (l, 0) = Φ n (l, 1))
    (hVo : ∀ n, IsOpen (V n)) (hV : ∀ x, ∃ n, x ∈ V n)
    (hΦV : ∀ n m, n < m → ∀ p, ∀ x ∈ V n, (Φ m p).val x = (Φ n (p.1, 1)).val x) :
    ∃ ε : N → SmoothForm I M F k,
      (∀ n l, ∀ x ∈ V n, (ε l).val x = (Φ n (l, 1)).val x ∧
        (mextDerivₗ I k (ε l)).val x = (mextDerivₗ I k (Φ n (l, 1))).val x) ∧
      IsSmoothFamily (J.prod (𝓡∂ 1))
        (fun p : N × unitInterval ↦ infiniteConcat (fun n s ↦ Φ n (p.1, s)) (ε p.1) p.2) := by
  have hlim : ∀ l : N, ∃ θ : SmoothForm I M F k, ∀ n, ∀ x ∈ V n,
      θ.val x = (Φ n (l, 1)).val x ∧
        (mextDerivₗ I k θ).val x = (mextDerivₗ I k (Φ n (l, 1))).val x := fun l ↦
    SmoothForm.exists_eq_limit hVo hV fun n m hnm x hx ↦ by
      rcases hnm.lt_or_eq with h | rfl
      exacts [hΦV n m h (l, 1) x hx, rfl]
  choose ε hε using hlim
  exact ⟨ε, fun n l x hx ↦ hε l n x hx, IsSmoothFamily.infiniteConcat hΦ hseam hVo hV hΦV
    fun n l x hx ↦ (hε l n x hx).1⟩

end SymplecticGeometry

end
