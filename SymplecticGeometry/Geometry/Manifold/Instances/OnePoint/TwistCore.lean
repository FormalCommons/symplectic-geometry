/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.LineBundle
public import TauCeti.Geometry.Manifold.VectorBundle.RestrictScalars
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars

/-!
# The line bundles `𝒪(k)` on the Riemann sphere as real vector bundles

On the Riemann sphere `OnePoint ℂ`, Tau Ceti's `OnePoint.twistCore k` is the holomorphic line
bundle `𝒪(k)`, glued from trivial lines over the affine and the inverted chart along the
transition functions `OnePoint.twistTransition k`. This file records the structure it has as a
smooth real vector bundle over the underlying real surface, by restriction of scalars, for every
degree `k`:

* the instances `ContinuousSMul ℝ` on its fibres, `ContMDiffVectorBundle n ℂ _ 𝓘(ℝ, ℂ)` for
  every `n` (from Tau Ceti's `ContMDiffVectorBundle.restrictScalars_modelWithCornersSelf`), and
  `MemTrivializationAtlas` for its local trivializations `(twistCore k).localTriv y`;
* `OnePoint.twistCore_localTriv_symmL_apply`: over the chart at `y`, the real frame of the
  trivialization at `y` is multiplication by a transition function;
* `OnePoint.twistCore_localTriv_symmL_smul`: that frame commutes with complex scalars.

Files using the real structure `open scoped VectorBundle.ComplexToReal`.
-/

public section

open Bundle Set
open scoped Manifold ContDiff VectorBundle.ComplexToReal

noncomputable section

namespace OnePoint

variable {k : ℤ}

/-- The fibres of `𝒪(k)` on the Riemann sphere carry the topology of `ℂ`, for which multiplication
by real scalars is continuous. -/
instance (k : ℤ) (x : OnePoint ℂ) : ContinuousSMul ℝ ((twistCore (𝕜 := ℂ) k).Fiber x) :=
  inferInstanceAs (ContinuousSMul ℝ ℂ)

/-- `𝒪(k)` on the Riemann sphere is a `C^n` real vector bundle over the underlying real
surface, for every `n`. -/
instance (k : ℤ) {n : ℕ∞ω} : ContMDiffVectorBundle n ℂ (twistCore (𝕜 := ℂ) k).Fiber 𝓘(ℝ, ℂ) :=
  have : ContMDiffVectorBundle n ℂ (twistCore (𝕜 := ℂ) k).Fiber 𝓘(ℂ, ℂ) :=
    ContMDiffVectorBundle.of_le le_top
  ContMDiffVectorBundle.restrictScalars_modelWithCornersSelf ℝ this

/-- The local trivializations of `𝒪(k)` belong to its trivialization atlas. -/
instance (k : ℤ) (y : OnePoint ℂ) :
    MemTrivializationAtlas ((twistCore (𝕜 := ℂ) k).localTriv y) :=
  ⟨⟨y, rfl⟩⟩

/-- Over the chart at `y`, the frame of the trivialization of `𝒪(k)` at `y` is multiplication by
the transition function from the chart at `y` to the chart at the point. -/
theorem twistCore_localTriv_symmL_apply {y x : OnePoint ℂ} (hx : x ∈ (chartAt ℂ y).source)
    (v : ℂ) :
    ((twistCore (𝕜 := ℂ) k).localTriv y).symmL ℝ x v = twistTransition k y x x * v := by
  have hb : x ∈ ((twistCore (𝕜 := ℂ) k).localTriv y).baseSet := by simpa using hx
  rw [Trivialization.symmL_apply _ hb]
  have h := (twistCore (𝕜 := ℂ) k).localTriv_symm_apply y hb v
  rwa [twistCore_indexAt, twistCore_coordChange_apply] at h

/-- The real frame of a trivialization of `𝒪(k)` commutes with complex scalars. -/
theorem twistCore_localTriv_symmL_smul (y x : OnePoint ℂ) (c w : ℂ) :
    ((twistCore (𝕜 := ℂ) k).localTriv y).symmL ℝ x (c • w) =
      c • ((twistCore (𝕜 := ℂ) k).localTriv y).symmL ℝ x w := by
  by_cases hb : x ∈ ((twistCore (𝕜 := ℂ) k).localTriv y).baseSet
  · rw [Trivialization.symmL_apply _ hb, Trivialization.symmL_apply _ hb,
      ← Trivialization.symmL_apply (R := ℂ) _ hb, ← Trivialization.symmL_apply (R := ℂ) _ hb,
      map_smul]
  · simp [Trivialization.symmL_apply_of_notMem _ hb]

end OnePoint

end
