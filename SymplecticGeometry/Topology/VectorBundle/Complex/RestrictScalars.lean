/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.VectorBundle.RestrictScalars

/-!
# Complex vector bundles as real vector bundles

A complex topological vector bundle `V → B` with model fibre `G` is a real vector bundle with the
same trivializations, by Tau Ceti's `VectorBundle.restrictScalars ℝ ℂ`. This file makes that fact
the scoped instance `VectorBundle.ComplexToReal.vectorBundle`, available after
`open scoped VectorBundle.ComplexToReal`, so that files working with the real structure of a
complex bundle share one instance instead of each declaring its own.

The same scope has the instance `VectorBundle.ComplexToReal.continuousSMul`: where complex scalar
multiplication is continuous, as on a fibre of a complex bundle, so is any real scalar
multiplication compatible with it. This is Mathlib's `IsScalarTower.continuousSMul`, which cannot
be a global instance since its goal does not determine the intermediate field; here that field is
`ℂ`.

The scope is not `VectorBundle` itself: inside `namespace TauCeti`, `open scoped VectorBundle`
would open `TauCeti.VectorBundle` instead.

The instances are scoped rather than global so that the search for a real structure does not try
the complex one everywhere. Since `VectorBundle` and `ContinuousSMul` are propositions, the
instances create no diamond with any other real structure. Within the scope, `continuousSMul`
has low priority: it applies to every type, so the search tries the instances that a type has
directly first.

## Main definitions

* `VectorBundle.ComplexToReal.vectorBundle`: a complex vector bundle is a real vector bundle.
* `VectorBundle.ComplexToReal.continuousSMul`: continuous complex scalar multiplication makes a
  compatible real scalar multiplication continuous.
-/

public section

open Bundle

namespace VectorBundle.ComplexToReal

/-- If complex scalar multiplication on `X` is continuous, then so is a real scalar
multiplication on `X` that forms a scalar tower with it. -/
scoped instance (priority := low) continuousSMul {X : Type*} [MulAction ℂ X] [SMul ℝ X]
    [IsScalarTower ℝ ℂ X] [TopologicalSpace X] [ContinuousSMul ℂ X] : ContinuousSMul ℝ X :=
  IsScalarTower.continuousSMul ℂ

variable {B : Type*} [TopologicalSpace B] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedSpace ℝ G] [IsScalarTower ℝ ℂ G] {V : B → Type*} [∀ x, AddCommMonoid (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [TopologicalSpace (TotalSpace G V)] [∀ x, TopologicalSpace (V x)] [FiberBundle G V]

/-- A complex vector bundle is a real vector bundle, with the same trivializations. -/
scoped instance vectorBundle [VectorBundle ℂ G V] : VectorBundle ℝ G V :=
  VectorBundle.restrictScalars ℝ ℂ G V

end VectorBundle.ComplexToReal

end
