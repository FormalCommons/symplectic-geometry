/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Finite.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.SuccPred.LinearLocallyFinite

/-!
# Enumerating a set of reals with finite sublevels

A set `C` of reals whose part below each level is finite, and which lies strictly above `a`, is
contained in the range of a strictly increasing sequence that starts at `a` and tends to `+∞`
(`Real.exists_strictMono_tendsto_atTop_subset_range`).

The sequence enumerates `C ∪ {a + n | n : ℕ}` in increasing order: this set is a locally finite
linear order with a least element `a` and no greatest element, hence order isomorphic to `ℕ`
(`orderIsoNatOfLinearSuccPredArch`).
-/

public section

open Filter Set

namespace Real

/-- A set `C` of reals lying above `a`, whose part below each level is finite, is contained in
the range of a strictly increasing sequence `u` with `u 0 = a` that tends to `+∞`. -/
theorem exists_strictMono_tendsto_atTop_subset_range {C : Set ℝ} {a : ℝ}
    (hC : ∀ r, (C ∩ Iic r).Finite) (ha : ∀ x ∈ C, a < x) :
    ∃ u : ℕ → ℝ, StrictMono u ∧ Tendsto u atTop atTop ∧ u 0 = a ∧ C ⊆ range u := by
  set S : Set ℝ := C ∪ range fun n : ℕ ↦ a + n
  have haS : a ∈ S := Or.inr ⟨0, by simp⟩
  have hnS (n : ℕ) : a + n ∈ S := Or.inr ⟨n, rfl⟩
  have hle : ∀ x ∈ S, a ≤ x := by
    rintro x (hx | ⟨n, rfl⟩)
    · exact (ha x hx).le
    · simp
  have hfin (r : ℝ) : (S ∩ Iic r).Finite := by
    refine (hC r).union ((finite_Iic (⌈r - a⌉₊)).image fun n : ℕ ↦ a + n) |>.subset ?_
    rintro x ⟨hx | ⟨n, rfl⟩, hxr⟩
    · exact Or.inl ⟨hx, hxr⟩
    · refine Or.inr ⟨n, mem_Iic.2 ?_, rfl⟩
      exact Nat.cast_le.1 ((show (n : ℝ) ≤ r - a by linarith [mem_Iic.1 hxr]).trans (Nat.le_ceil _))
  let : LocallyFiniteOrder S := LocallyFiniteOrder.ofFiniteIcc fun x y ↦ by
    refine ((hfin y).preimage Subtype.val_injective.injOn).subset fun z hz ↦ ?_
    exact ⟨z.property, hz.2⟩
  let : OrderBot S := { bot := ⟨a, haS⟩, bot_le := fun x ↦ hle x x.property }
  have : NoMaxOrder S := ⟨fun x ↦ by
    obtain ⟨n, hn⟩ := exists_nat_gt (x - a : ℝ)
    exact ⟨⟨a + n, hnS n⟩, show (x : ℝ) < a + n by linarith⟩⟩
  let := LinearLocallyFiniteOrder.succOrder S
  let := LinearLocallyFiniteOrder.predOrder S
  set e : S ≃o ℕ := orderIsoNatOfLinearSuccPredArch
  refine ⟨fun n ↦ e.symm n, Subtype.strictMono_coe _ |>.comp e.symm.strictMono, ?_, ?_,
    fun x hx ↦ ⟨e ⟨x, Or.inl hx⟩, by simp⟩⟩
  · refine (Subtype.mono_coe _ |>.comp e.symm.monotone).tendsto_atTop_atTop fun r ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (r - a)
    refine ⟨e ⟨a + n, hnS n⟩, ?_⟩
    rw [Function.comp_apply, e.symm_apply_apply]
    linarith
  · -- `0` is `⊥` in `ℕ`, and `⊥` in `S` is `a` by the instance above.
    change ((e.symm ⊥ : S) : ℝ) = a
    rw [e.symm.map_bot]
    rfl

end Real
