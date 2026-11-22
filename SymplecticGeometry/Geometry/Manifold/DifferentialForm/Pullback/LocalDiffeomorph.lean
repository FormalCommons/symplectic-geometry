/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Pulling forms back along local diffeomorphisms

If a local diffeomorphism `f` at `x` pulls a form `ω` back to `η` at a point `Λ y`, where
`Λ = hf.localInverse` and `y` lies in the source of `Λ`, then `Λ` pulls `η` back to `ω` at `y`
(`IsLocalDiffeomorphAt.mpullback_localInverse_apply_eq`): the chain rule for `f ∘ Λ`, which is the
identity near `y`. The proof adapts the last step of the proof of Tau Ceti's
`IsLocalDiffeomorphAt.exists_partialDiffeomorph_mpullback_eq`. That theorem only gives some
partial diffeomorphism, a restriction of `Λ`; the pointwise form keeps `Λ` itself, so that it is
still known to invert `f`. The chain rule needs `f` to be differentiable at `Λ y`: it is a local
diffeomorphism there, as on the whole target of `Λ`
(`IsLocalDiffeomorphAt.isLocalDiffeomorphOn_localInverse_target`).

A `C^n` local diffeomorphism `f` with `2 ≤ n` also pulls a pair with `ι_Y dα = α` back to such a
pair, for the pulled-back field and form
(`IsLocalDiffeomorph.interior_mextDeriv_mpullback_of_interior_mextDeriv`). The proof combines Tau
Ceti's `TauCeti.mpullback_mextDeriv_at` and `TauCeti.mpullback_interior`; that the differential of
`f` sends the pulled-back field to `Y` comes from Mathlib's
`IsLocalDiffeomorphAt.isInvertible_mfderiv`.
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
          ((hf.isLocalDiffeomorphOn_localInverse_target
            ⟨_, hf.localInverse.map_source hy⟩).mdifferentiableAt hn) ω).symm
    _ = ω y := by rw [hid.mpullback_eq, mpullback_id]

end IsLocalDiffeomorphAt

namespace IsLocalDiffeomorph

variable [IsManifold I 2 M] [IsManifold I' 2 M']

/-- Let `f : M → M'` be a `C^n` local diffeomorphism with `2 ≤ n`. If the field `Y` on `M'`
satisfies `ι_Y dα = α` for a smooth form `α`, then the pulled-back field `f^* Y` satisfies
`ι_{f^* Y} d(f^* α) = f^* α`. -/
theorem interior_mextDeriv_mpullback_of_interior_mextDeriv (hf : IsLocalDiffeomorph I I' n f)
    (hn : 2 ≤ n) {Y : (y : M') → TangentSpace I' y} {α : SmoothForm I' M' F k}
    (hYα : (mextDeriv α.val).interior Y = α.val) :
    (mextDeriv (mpullback I I' f α.val)).interior (VectorField.mpullback I I' f Y) =
      mpullback I I' f α.val := by
  have hd : mextDeriv (mpullback I I' f α.val) = mpullback I I' f (mextDeriv α.val) :=
    funext fun x ↦ (mpullback_mextDeriv_at ((hf x).contMDiffAt.of_le hn)
      ((α.contMDiff (f x)).of_le (by simp))).symm
  have hY (x : M) : mfderiv I I' f x (VectorField.mpullback I I' f Y x) = Y (f x) := by
    rw [VectorField.mpullback_apply]
    exact ((hf x).isInvertible_mfderiv (lt_of_lt_of_le (by simp) hn).ne').self_apply_inverse _
  rw [hd, ← mpullback_interior _ _ _ _ hY, hYα]

end IsLocalDiffeomorph

end
