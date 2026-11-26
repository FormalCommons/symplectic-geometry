/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Data.Set.Prod

/-!
# Graphs of maps on a product

Supplements to `Mathlib/Data/Set/Prod.lean`.

## Main results

* `Set.injOn_fst_prod_iff`: the graph `(q, x) ↦ (q, g (q, x))` of a map `g` on a product is
  injective on `T ×ˢ A` exactly when every slice `g (q, ·)` with `q ∈ T` is injective on `A`.
-/

public section

namespace Set

/-- The graph `(q, x) ↦ (q, g (q, x))` of a map `g` on a product is injective on `T ×ˢ A`
exactly when every slice `g (q, ·)` with `q ∈ T` is injective on `A`. -/
theorem injOn_fst_prod_iff {α β γ : Type*} {g : α × β → γ} {T : Set α} {A : Set β} :
    InjOn (fun p ↦ (p.1, g p)) (T ×ˢ A) ↔ ∀ q ∈ T, InjOn (fun x ↦ g (q, x)) A := by
  refine ⟨fun h q hq x hx y hy hxy ↦
    (Prod.mk.inj (h (mk_mem_prod hq hx) (mk_mem_prod hq hy) (Prod.ext rfl hxy))).2, ?_⟩
  rintro h ⟨q, x⟩ ⟨hq, hx⟩ ⟨q', y⟩ ⟨-, hy⟩ hxy
  obtain ⟨rfl, hxy⟩ := Prod.mk.inj hxy
  exact congrArg (Prod.mk q) (h q hq hx hy hxy)

end Set

end
