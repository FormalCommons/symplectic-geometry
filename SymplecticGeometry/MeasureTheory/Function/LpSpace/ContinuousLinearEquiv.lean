/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.MeasureTheory.Function.Lp.ContinuousLinearEquiv
import SymplecticGeometry.Analysis.InnerProductSpace.ContinuousLinearEquiv

/-!
# `Lᵖ` spaces under a continuous linear equivalence of the values

A continuous linear equivalence `e : E ≃L[𝕜] F` induces, by composition, Tau Ceti's continuous
linear equivalence `e.compLpL p μ : Lp E p μ ≃L[𝕜] Lp F p μ`, whose inverse is induced by
`e.symm`. This file states its values through `ContinuousLinearMap.compLp`.

As an application, `L²` with values in a finite-dimensional space is equivalent to `L²` with
values in a Euclidean space, and hence to a Hilbert space, although the norm of the values need
not come from an inner product.

## Main definitions and results

* `ContinuousLinearEquiv.compLpL_apply_eq_compLp`, `ContinuousLinearEquiv.compLpL_symm_apply`: the
  values of Tau Ceti's `ContinuousLinearEquiv.compLpL` and of its inverse.
* `MeasureTheory.Lp.exists_continuousLinearEquiv_innerProductSpace`: `L²` with values in a
  finite-dimensional normed space is continuously linearly equivalent to a Hilbert space.
-/

public section

noncomputable section

open MeasureTheory Module

universe u v w

namespace ContinuousLinearEquiv

variable {α : Type*} [MeasurableSpace α] {p : ENNReal} [Fact (1 ≤ p)] {μ : Measure α}
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- `e.compLpL p μ` composes with `e`. -/
theorem compLpL_apply_eq_compLp (e : E ≃L[𝕜] F) (f : Lp E p μ) :
    e.compLpL p μ f = (e : E →L[𝕜] F).compLp f := by
  rw [compLpL_apply]
  rfl

/-- The inverse of `e.compLpL p μ` composes with `e.symm`. -/
theorem compLpL_symm_apply (e : E ≃L[𝕜] F) (f : Lp F p μ) :
    (e.compLpL p μ).symm f = (e.symm : F →L[𝕜] E).compLp f := by
  rw [symm_compLpL, compLpL_apply_eq_compLp]

end ContinuousLinearEquiv

namespace MeasureTheory.Lp

variable {α : Type u} [MeasurableSpace α] (μ : Measure α) {𝕜 : Type w} [RCLike 𝕜]
  (G : Type v) [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]

/-- `L²` with values in a finite-dimensional normed space is continuously linearly equivalent to
a Hilbert space, `L²` with values in a Euclidean space of the same dimension. -/
theorem exists_continuousLinearEquiv_innerProductSpace :
    ∃ (K : Type (max u w)) (_ : NormedAddCommGroup K) (_ : InnerProductSpace 𝕜 K)
      (_ : CompleteSpace K),
      Nonempty (Lp G 2 μ ≃L[𝕜] K) :=
  ⟨Lp (EuclideanSpace 𝕜 (Fin (finrank 𝕜 G))) 2 μ, _, _, inferInstance,
    ⟨(ContinuousLinearEquiv.ofFinrankEq (E := G) (F := EuclideanSpace 𝕜 (Fin (finrank 𝕜 G)))
      finrank_euclideanSpace_fin.symm).compLpL 2 μ⟩⟩

end MeasureTheory.Lp

end
