/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Associated.Basic

/-!
# Scalar towers and differences on the fibres of an associated bundle

Tau Ceti's `TauCeti.AssociatedBundle.instModule` gives each fibre of an associated bundle
`P ×_G F` the `𝕜`-module structure of the model fibre `F`, for every field `𝕜` over which the
action of `G` is linear. This file adds that when `F` is a scalar tower over two such fields, for
instance a complex vector space viewed also as a real one, so is each fibre. This is what lets a
complex associated bundle be used where both its real and its complex structures appear, such as
Tau Ceti's `complexEulerClass`.

The file also completes Tau Ceti's `TauCeti.AssociatedBundle.mk_add`,
`TauCeti.AssociatedBundle.mk_zero`, `TauCeti.AssociatedBundle.mk_neg`: in a fixed frame `p`, the
class map `v ↦ [p, v]` sends differences in the model fibre to those in the fibre.

## Main results

* `TauCeti.AssociatedBundle.instIsScalarTower`: the fibres of `P ×_G F` form a scalar tower
  `𝕜 → 𝕜' → AssociatedBundle G P F b` when `F` does.
* `TauCeti.AssociatedBundle.mk_sub`: `[p, v - w] = [p, v] - [p, w]`.

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

section Additive

variable {B G F : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [NormedAddCommGroup F] [DistribMulAction G F] [ContinuousSMul G F]

/-- Classes in a fixed principal frame respect subtraction. -/
@[simp]
theorem mk_sub {b : B} (p : P b) (v w : F) : mk G p (v - w) = mk G p v - mk G p w :=
  (AddMonoidHom.mk' (mk G p) (mk_add p)).map_sub v w

end Additive

end TauCeti.AssociatedBundle

end
