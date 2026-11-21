/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Linear independence of continuous sections is an open condition

Let `s₁, …, s_k` be sections of a topological vector bundle `E → B` that are continuous at a
point `x₀` of the base, as maps into the total space. If the vectors `sᵢ(x₀)` are linearly
independent, then so are the vectors `sᵢ(x)` for every `x` near `x₀`. Read in a local
trivialization, the sections become continuous maps into the model fibre, and the statement is
Mathlib's `LinearIndependent.eventually`.

The argument adapts the step of the proof of Tau Ceti's
`CovariantDerivative.exists_isLocalFrameOn_parallel_of_forall_exists` that shows that the
sections stay independent.

## Main results

* `Bundle.Trivialization.eventually_linearIndependent`: in a linear trivialization `e` whose
  base set contains `x₀`, sections continuous at `x₀` and independent at `x₀` stay independent
  near `x₀`.
-/

public section

open Bundle Topology Filter

namespace Bundle.Trivialization

variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]

/-- Let `e` be a linear trivialization whose base set contains `x₀`, and let `s₁, …, s_k` be
sections that are continuous at `x₀`, as maps into the total space. If the vectors `sᵢ(x₀)` are
linearly independent, then so are the vectors `sᵢ(x)` for all `x` near `x₀`. -/
theorem eventually_linearIndependent (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    {ι : Type*} [Finite ι] {s : ι → ∀ x, E x} {x₀ : B} (hx₀ : x₀ ∈ e.baseSet)
    (hs : ∀ i, ContinuousAt (fun x ↦ TotalSpace.mk' F x (s i x)) x₀)
    (hli : LinearIndependent 𝕜 fun i ↦ s i x₀) :
    ∀ᶠ x in 𝓝 x₀, LinearIndependent 𝕜 fun i ↦ s i x := by
  -- The coordinates of the sections in `e` are continuous at `x₀` and independent there.
  have hcont : ContinuousAt (fun x i ↦ (e ⟨x, s i x⟩).2) x₀ :=
    continuousAt_pi.2 fun i ↦
      ((e.toOpenPartialHomeomorph.continuousAt (e.mem_source.2 hx₀)).comp (hs i)).snd
  have hli₀ : LinearIndependent 𝕜 fun i ↦ (e ⟨x₀, s i x₀⟩).2 := by
    have h := hli.map' (e.linearEquivAt 𝕜 x₀ hx₀).toLinearMap (LinearEquiv.ker _)
    simpa [Function.comp_def, Trivialization.linearEquivAt_apply] using h
  filter_upwards [e.open_baseSet.mem_nhds hx₀, hcont.eventually hli₀.eventually] with x hx hli'
  refine LinearIndependent.of_comp (e.linearMapAt 𝕜 x) ?_
  simpa [Function.comp_def, e.coe_linearMapAt_of_mem hx] using hli'

end Bundle.Trivialization
