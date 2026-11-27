/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.SuccPred.LinearLocallyFinite

/-!
# Enumerating a set with finite sublevels in an archimedean ring

In an archimedean linearly ordered ring, a set `C` whose part below each level is finite, and
which lies above `a`, is contained in the range of a strictly increasing sequence that starts at
`a` and tends to `+∞` (`exists_strictMono_tendsto_atTop_subset_range`).

The sequence enumerates `C ∪ {a + n | n : ℕ}` in increasing order: this set is a locally finite
linear order with a least element `a` and no greatest element, hence order isomorphic to `ℕ`
(`orderIsoNatOfLinearSuccPredArch`).
-/

public section

open Filter Set

variable {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Archimedean α]

/-- In an archimedean linearly ordered ring, a set `C` lying above `a`, whose part below each
level is finite, is contained in the range of a strictly increasing sequence `u` with `u 0 = a`
that tends to `+∞`. -/
theorem exists_strictMono_tendsto_atTop_subset_range {C : Set α} {a : α}
    (hC : ∀ r, (C ∩ Iic r).Finite) (ha : ∀ x ∈ C, a ≤ x) :
    ∃ u : ℕ → α, StrictMono u ∧ Tendsto u atTop atTop ∧ u 0 = a ∧ C ⊆ range u := by
  set S : Set α := C ∪ range fun n : ℕ ↦ a + n
  have haS : a ∈ S := Or.inr ⟨0, by simp⟩
  have hnS (n : ℕ) : a + n ∈ S := Or.inr ⟨n, rfl⟩
  have hle : ∀ x ∈ S, a ≤ x := by
    rintro x (hx | ⟨n, rfl⟩)
    · exact ha x hx
    · simp
  have hfin (r : α) : (S ∩ Iic r).Finite := by
    obtain ⟨N, hN⟩ := exists_nat_ge (r - a)
    refine (hC r).union ((finite_Iic N).image fun n : ℕ ↦ a + n) |>.subset ?_
    rintro x ⟨hx | ⟨n, rfl⟩, hxr⟩
    · exact Or.inl ⟨hx, hxr⟩
    · refine Or.inr ⟨n, mem_Iic.2 ?_, rfl⟩
      exact Nat.cast_le.1 ((le_sub_iff_add_le'.2 (mem_Iic.1 hxr)).trans hN)
  let : LocallyFiniteOrder S := LocallyFiniteOrder.ofFiniteIcc fun x y ↦ by
    refine ((hfin y).preimage Subtype.val_injective.injOn).subset fun z hz ↦ ?_
    exact ⟨z.property, hz.2⟩
  let : OrderBot S := { bot := ⟨a, haS⟩, bot_le := fun x ↦ hle x x.property }
  have : NoMaxOrder S := ⟨fun x ↦ by
    obtain ⟨n, hn⟩ := exists_nat_gt (x - a : α)
    exact ⟨⟨a + n, hnS n⟩, Subtype.mk_lt_mk.2 (sub_lt_iff_lt_add'.1 hn)⟩⟩
  let := LinearLocallyFiniteOrder.succOrder S
  let := LinearLocallyFiniteOrder.predOrder S
  set e : S ≃o ℕ := orderIsoNatOfLinearSuccPredArch
  refine ⟨fun n ↦ e.symm n, Subtype.strictMono_coe _ |>.comp e.symm.strictMono, ?_, ?_,
    fun x hx ↦ ⟨e ⟨x, Or.inl hx⟩, by simp⟩⟩
  · refine (Subtype.mono_coe _ |>.comp e.symm.monotone).tendsto_atTop_atTop fun r ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (r - a)
    refine ⟨e ⟨a + n, hnS n⟩, ?_⟩
    rw [Function.comp_apply, e.symm_apply_apply]
    exact sub_le_iff_le_add'.1 hn
  · -- `⊥` in `S` is `a` by the instance above.
    beta_reduce
    rw [← Nat.bot_eq_zero, e.symm.map_bot]
    rfl

end
