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

The scope is not `VectorBundle` itself: inside `namespace TauCeti`, `open scoped VectorBundle`
would open `TauCeti.VectorBundle` instead.

The instance is scoped rather than global so that the search for a real vector bundle structure
does not try the complex one everywhere. Since `VectorBundle` is a proposition, the instance
creates no diamond with any other real structure.

## Main definitions

* `VectorBundle.ComplexToReal.vectorBundle`: a complex vector bundle is a real vector bundle.
-/

public section

open Bundle

namespace VectorBundle.ComplexToReal

variable {B : Type*} [TopologicalSpace B] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedSpace ℝ G] [IsScalarTower ℝ ℂ G] {V : B → Type*} [∀ x, AddCommMonoid (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [TopologicalSpace (TotalSpace G V)] [∀ x, TopologicalSpace (V x)] [FiberBundle G V]

/-- A complex vector bundle is a real vector bundle, with the same trivializations. -/
scoped instance vectorBundle [VectorBundle ℂ G V] : VectorBundle ℝ G V :=
  VectorBundle.restrictScalars ℝ ℂ G V

end VectorBundle.ComplexToReal

end
