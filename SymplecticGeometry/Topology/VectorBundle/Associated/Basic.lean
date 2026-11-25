/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Associated.Basic

/-!
# Scalar towers on the fibres of an associated bundle, and the preferred frames

Tau Ceti's `TauCeti.AssociatedBundle.instModule` gives each fibre of an associated bundle
`P ×_G F` the `𝕜`-module structure of the model fibre `F`, for every field `𝕜` over which the
action of `G` is linear. This file adds that when `F` is a scalar tower over two such fields, for
instance a complex vector space viewed also as a real one, so is each fibre. This is what lets a
complex associated bundle be used where both its real and its complex structures appear, such as
Tau Ceti's `complexEulerClass`.

It also reads the preferred trivialization of `P ×_G F` at `b'` on the classes `[σ b, v]`, where
`σ b` is the point of `P b` with coordinate `1` in the preferred trivialization of `P` at `b'`:
they have coordinate `v`.

## Main results

* `TauCeti.AssociatedBundle.instIsScalarTower`: the fibres of `P ×_G F` form a scalar tower
  `𝕜 → 𝕜' → AssociatedBundle G P F b` when `F` does.
* `TauCeti.AssociatedBundle.trivializationAt_mk_symm_one`,
  `TauCeti.AssociatedBundle.trivializationAt_symm_eq_mk`: the preferred trivialization of
  `P ×_G F` at `b'` and its inverse identify `[σ b, v]` with `v`.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, volume I, Chapter I, §5
  (associated bundles).
-/

public section

noncomputable section

open Bundle

namespace TauCeti.AssociatedBundle

variable {𝕜 𝕜' B G F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [SMul 𝕜 𝕜'] [TopologicalSpace B] [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  [DistribMulAction G F] [SMulCommClass G 𝕜 F] [SMulCommClass G 𝕜' F] [ContinuousSMul G F]

/-- The fibres of an associated bundle are scalar towers over the fields over which the model
fibre is one. -/
instance instIsScalarTower (b : B) : IsScalarTower 𝕜 𝕜' (AssociatedBundle G P F b) :=
  inferInstanceAs (IsScalarTower 𝕜 𝕜' F)

section PreferredSection

variable [∀ b, Nonempty (P b)]

/-- In the preferred trivialization of `P ×_G F` at `b'`, the class `[σ b, v]` has coordinate `v`,
where `σ b` is the point of `P b` with coordinate `1` in the preferred trivialization of `P` at
`b'`. -/
theorem trivializationAt_mk_symm_one {b' b : B} (hb : b ∈ (trivializationAt G P b').baseSet)
    (v : F) :
    trivializationAt F (AssociatedBundle G P F) b'
        ⟨b, mk G ((trivializationAt G P b').symm b 1) v⟩ = (b, v) := by
  rw [trivializationAt_mk hb, (trivializationAt G P b').apply_mk_symm hb, one_smul]

/-- The inverse of the preferred trivialization of `P ×_G F` at `b'` sends `v` over `b` to the
class `[σ b, v]`, where `σ b` is the point of `P b` with coordinate `1` in the preferred
trivialization of `P` at `b'`. -/
theorem trivializationAt_symm_eq_mk {b' b : B} (hb : b ∈ (trivializationAt G P b').baseSet)
    (v : F) :
    (trivializationAt F (AssociatedBundle G P F) b').symm b v =
      mk G ((trivializationAt G P b').symm b 1) v := by
  have hb' : b ∈ (trivializationAt F (AssociatedBundle G P F) b').baseSet := by
    rwa [baseSet_trivializationAt]
  have h := (trivializationAt F (AssociatedBundle G P F) b').symm_apply_apply_mk hb'
    (mk G ((trivializationAt G P b').symm b 1) v)
  rwa [trivializationAt_mk_symm_one hb] at h

end PreferredSection

end TauCeti.AssociatedBundle

end
