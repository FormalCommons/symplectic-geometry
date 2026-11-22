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
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Pulling forms back along local diffeomorphisms

For a `C^n` partial diffeomorphism `ψ` with `n ≠ 0`, pulling a form back along `ψ` and then
along `ψ.symm` returns it at each point of the target of `ψ`
(`PartialDiffeomorph.mpullback_symm_mpullback_apply`): by the chain rule, since `ψ ∘ ψ.symm`
is the identity near such a point. The proof is the pointwise form of the proof of Tau Ceti's
`TauCeti.mpullback_symm_mpullback` for diffeomorphisms, and adapts the last step of the proof of
Tau Ceti's `IsLocalDiffeomorphAt.exists_partialDiffeomorph_mpullback_eq`. Applied to `ψ.symm`,
it gives the other order, along `ψ.symm` and then along `ψ`, at each point of the source of `ψ`
(`PartialDiffeomorph.mpullback_mpullback_symm_apply`).

If a local diffeomorphism `f` at `x` pulls a form `ω` back to `η` at a point `Λ y`, where
`Λ = hf.localInverse` and `y` lies in the source of `Λ`, then `Λ` pulls `η` back to `ω` at `y`
(`IsLocalDiffeomorphAt.mpullback_localInverse_apply_eq`). Tau Ceti's
`IsLocalDiffeomorphAt.exists_partialDiffeomorph_mpullback_eq` only gives some partial
diffeomorphism, a restriction of `Λ`; the pointwise form keeps `Λ` itself, so that it is still
known to invert `f`. Near `Λ y`, `f` agrees with `Λ.symm`
(`IsLocalDiffeomorphAt.eqOn_localInverse_symm`), so this is
`PartialDiffeomorph.mpullback_mpullback_symm_apply` for `Λ`.

A `C^n` local diffeomorphism `f` with `2 ≤ n` also pulls a pair with `ι_Y dα = α` back to such a
pair, for the pulled-back field and form
(`IsLocalDiffeomorph.interior_mextDeriv_mpullback_of_interior_mextDeriv`). The proof combines Tau
Ceti's `TauCeti.mpullback_mextDeriv_at` and `TauCeti.mpullback_interior`; that the differential of
`f` sends the pulled-back field to `Y` comes from Mathlib's
`IsLocalDiffeomorphAt.isInvertible_mfderiv`.

For `f : M → M'` and a form `α` on `M`, `TauCeti.RoughForm.pushforwardAt I I' f α x z` is `α x`
read through the inverse of the differential of `f` at `x`, as an alternating map on the tangent
space at `z` (meant for `z = f x`). When that differential is invertible, a form on `M'` whose
value at `f x` is this one pulls back to `α x`
(`TauCeti.mpullback_apply_eq_of_apply_eq_pushforwardAt`). Reading a form through an inverse of a
differential is what Tau Ceti's `TauCeti.RoughForm.descendedForm` does through a right inverse.
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

/-- For a `C^n` partial diffeomorphism `ψ` with `n ≠ 0`, pulling a form `ω` back along `ψ` and
then along `ψ.symm` gives `ω` back at every point of the target of `ψ`. -/
theorem PartialDiffeomorph.mpullback_symm_mpullback_apply (ψ : PartialDiffeomorph I I' M M' n)
    (hn : n ≠ 0) (ω : RoughForm I' M' F k) {y : M'} (hy : y ∈ ψ.target) :
    mpullback I' I ψ.symm (mpullback I I' ψ ω) y = ω y := by
  have hid : ψ ∘ ψ.symm =ᶠ[𝓝 y] id :=
    eventually_of_mem (ψ.open_target.mem_nhds hy) fun z hz ↦ ψ.right_inv hz
  rw [← mpullback_comp_at (ψ.symm.mdifferentiableAt hn hy)
    (ψ.mdifferentiableAt hn (ψ.map_target hy)), hid.mpullback_eq, mpullback_id]

/-- For a `C^n` partial diffeomorphism `ψ` with `n ≠ 0`, pulling a form `ω` back along `ψ.symm`
and then along `ψ` gives `ω` back at every point of the source of `ψ`. -/
theorem PartialDiffeomorph.mpullback_mpullback_symm_apply (ψ : PartialDiffeomorph I I' M M' n)
    (hn : n ≠ 0) (ω : RoughForm I M F k) {x : M} (hx : x ∈ ψ.source) :
    mpullback I I' ψ (mpullback I' I ψ.symm ω) x = ω x :=
  ψ.symm.mpullback_symm_mpullback_apply hn ω hx

namespace TauCeti

variable (I I') in
/-- The value at `z` of the pushforward of a form `α` along `f : M → M'` from the point `x`:
`α x` read through the inverse of the differential of `f` at `x`, with the tangent space at `z`
identified with the one at `f x`. It is meant for `z = f x` and an invertible differential. -/
noncomputable def RoughForm.pushforwardAt (f : M → M') (α : RoughForm I M F k) (x : M) (z : M') :
    TangentSpace I' z [⋀^Fin k]→L[ℝ] F :=
  (α x).compContinuousLinearMap
    ((mfderiv I I' f x).inverse.comp (tangentSpaceCast I' z (f x) : TangentSpace I' z →L[ℝ] _))

theorem RoughForm.pushforwardAt_def (f : M → M') (α : RoughForm I M F k) (x : M) (z : M') :
    pushforwardAt I I' f α x z = (α x).compContinuousLinearMap
      ((mfderiv I I' f x).inverse.comp (tangentSpaceCast I' z (f x) : TangentSpace I' z →L[ℝ] _)) :=
  (rfl)

/-- If the differential of `f` at `x` is invertible, a form `β` whose value at `f x` is the
pushforward of `α` from `x` pulls back along `f` to `α` at `x`. -/
theorem mpullback_apply_eq_of_apply_eq_pushforwardAt {α : RoughForm I M F k}
    {β : RoughForm I' M' F k} (hf : (mfderiv I I' f x).IsInvertible)
    (hβ : β (f x) = RoughForm.pushforwardAt I I' f α x (f x)) :
    mpullback I I' f β x = α x := by
  ext v
  rw [mpullback_apply, hβ, RoughForm.pushforwardAt_def]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, tangentSpaceCast_self,
    hf.inverse_apply_self]

end TauCeti

namespace IsLocalDiffeomorphAt

/-- Let `f` be a `C^n` local diffeomorphism at `x`, `n ≠ 0`, with local inverse `Λ`, and let `y`
be in the source of `Λ`. If `f` pulls `ω` back to `η` at `Λ y`, then `Λ` pulls `η` back to `ω`
at `y`. -/
theorem mpullback_localInverse_apply_eq (hf : IsLocalDiffeomorphAt I I' n f x) (hn : n ≠ 0)
    {ω : RoughForm I' M' F k} {η : RoughForm I M F k} {y : M'} (hy : y ∈ hf.localInverse.source)
    (hfω : mpullback I I' f ω (hf.localInverse y) = η (hf.localInverse y)) :
    mpullback I' I hf.localInverse η y = ω y := by
  have hf' : f =ᶠ[𝓝 (hf.localInverse y)] hf.localInverse.symm :=
    eventually_of_mem (hf.localInverse.open_target.mem_nhds (hf.localInverse.map_source hy))
      hf.eqOn_localInverse_symm
  rw [← hf.localInverse.mpullback_mpullback_symm_apply hn ω hy]
  ext v
  rw [mpullback_apply, mpullback_apply, ← hfω, hf'.mpullback_eq]

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
