/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Pulling forms back along the local inverse of a local diffeomorphism

If a local diffeomorphism `f` at `x` pulls a form `ω` back to `η` at a point `Λ y`, where
`Λ = hf.localInverse` and `y` lies in the source of `Λ`, then `Λ` pulls `η` back to `ω` at `y`
(`IsLocalDiffeomorphAt.mpullback_localInverse_apply_eq`): the chain rule for `f ∘ Λ`, which is the
identity near `y`. The proof adapts the last step of the proof of Tau Ceti's
`IsLocalDiffeomorphAt.exists_partialDiffeomorph_mpullback_eq`. That theorem only gives some
partial diffeomorphism, a restriction of `Λ`; the pointwise form keeps `Λ` itself, so that it is
still known to invert `f`. The chain rule needs `f` to be differentiable at `Λ y`: it is a local
diffeomorphism there (`IsLocalDiffeomorphAt.isLocalDiffeomorphAt_localInverse_apply`).
-/

public section

open Set Filter
open scoped Manifold Topology

open TauCeti

variable {E H M E' H' M' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {k : ℕ} {n : WithTop ℕ∞} {f : M → M'} {x : M}

namespace IsLocalDiffeomorphAt

/-- A local diffeomorphism `f` at `x` is also a local diffeomorphism at `Λ y`, for `Λ` its local
inverse and `y` in the source of `Λ`. -/
theorem isLocalDiffeomorphAt_localInverse_apply (hf : IsLocalDiffeomorphAt I I' n f x) {y : M'}
    (hy : y ∈ hf.localInverse.source) : IsLocalDiffeomorphAt I I' n f (hf.localInverse y) := by
  -- `f` agrees with the inverse of `Λ` on the target of `Λ`, since `f ∘ Λ = id` on its source.
  refine isLocalDiffeomorphAt_of_eqOn (Φ := hf.localInverse.symm)
    (by simpa using hf.localInverse.map_source hy) fun x' hx' ↦ ?_
  have hx'' : x' ∈ hf.localInverse.target := by simpa using hx'
  have h := hf.localInverse_right_inv (hf.localInverse.map_target hx'')
  rw [hf.localInverse.right_inv hx''] at h
  simpa using h

/-- Let `f` be a `C^n` local diffeomorphism at `x`, `n ≠ 0`, with local inverse `Λ`, and let `y`
be in the source of `Λ`. If `f` pulls `ω` back to `η` at `Λ y`, then `Λ` pulls `η` back to `ω`
at `y`. -/
theorem mpullback_localInverse_apply_eq (hf : IsLocalDiffeomorphAt I I' n f x) (hn : n ≠ 0)
    {ω : RoughForm I' M' F k} {η : RoughForm I M F k} {y : M'} (hy : y ∈ hf.localInverse.source)
    (hfω : mpullback I I' f ω (hf.localInverse y) = η (hf.localInverse y)) :
    mpullback I' I hf.localInverse η y = ω y := by
  have hid : f ∘ hf.localInverse =ᶠ[𝓝 y] id :=
    eventually_of_mem (hf.localInverse.open_source.mem_nhds hy) hf.localInverse_eqOn_right
  calc mpullback I' I hf.localInverse η y
      = mpullback I' I hf.localInverse (mpullback I I' f ω) y :=
        ContinuousAlternatingMap.ext fun v ↦ by rw [mpullback_apply, mpullback_apply, hfω]
    _ = mpullback I' I' (f ∘ hf.localInverse) ω y :=
        (mpullback_comp_at (hf.localInverse.mdifferentiableAt hn hy)
          ((hf.isLocalDiffeomorphAt_localInverse_apply hy).mdifferentiableAt hn) ω).symm
    _ = ω y := by rw [hid.mpullback_eq, mpullback_id]

end IsLocalDiffeomorphAt

end
