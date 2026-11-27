/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Analysis.Calculus.Jet.Equivalence

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Cancelling a local diffeomorphism from equal jets

Tau Ceti's `TauCeti.SameJetAt` says that two maps have the same derivatives through a given order
at a point. Tau Ceti cancels a continuous linear equivalence composed on the left
(`ContinuousLinearEquiv.comp_sameJetAt_iff`). This file cancels a nonlinear map `h` that is `C^n`
at the common value with an invertible derivative there: if `h ∘ f` and `h ∘ f'` have the same
jet of order `n` at `x`, and `f x = f' x`, then so do `f` and `f'`. Over `ℝ` or `ℂ` such an `h`
has a `C^n` local inverse by Mathlib's inverse function theorem
(`ContDiffAt.toOpenPartialHomeomorph`), and Tau Ceti's `TauCeti.SameJetAt.comp` composes it on
the left.

## Main results

* `TauCeti.SameJetAt.of_comp_left`: equal jets of `h ∘ f` and `h ∘ f'` give equal jets of `f`
  and `f'`, for `h` with invertible derivative at `f x = f' x`.
-/

public section

open scoped ContDiff Topology

namespace TauCeti

namespace SameJetAt

variable {𝕂 E F G : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
  [NormedAddCommGroup F] [NormedSpace 𝕂 F] [CompleteSpace F] [NormedAddCommGroup G]
  [NormedSpace 𝕂 G] {n : ℕ} {x : E} {f f' : E → F} {h : F → G}

/-- Let `f` and `f'` be `C^n` at `x` with `f x = f' x`, and let `h` be `C^n` at `f x` with
invertible derivative there. If `h ∘ f` and `h ∘ f'` have the same jet of order `n` at `x`, then
so do `f` and `f'`. -/
theorem of_comp_left (hjet : SameJetAt 𝕂 n x (h ∘ f) (h ∘ f'))
    (hh : ContDiffAt 𝕂 n h (f x)) (hinv : (_root_.fderiv 𝕂 h (f x)).IsInvertible)
    (hf : ContDiffAt 𝕂 n f x) (hf' : ContDiffAt 𝕂 n f' x) (hff' : f x = f' x) :
    SameJetAt 𝕂 n x f f' := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact sameJetAt_zero_iff.2 hff'
  obtain ⟨A, hA⟩ := hinv
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by exact_mod_cast hn.ne'
  have hd : HasFDerivAt h (A : F →L[𝕂] G) (f x) := hA ▸ (hh.differentiableAt hn0).hasFDerivAt
  -- `P`: the local diffeomorphism that `h` is near `f x`.
  set P := hh.toOpenPartialHomeomorph h hd hn0
  have hP : (P : F → G) = h := hh.toOpenPartialHomeomorph_coe hd hn0
  have hxP : f x ∈ P.source := hh.mem_toOpenPartialHomeomorph_source hd hn0
  have hPx : P.symm (h (f x)) = f x := by rw [← hP]; exact P.left_inv hxP
  have hsymm : ContDiffAt 𝕂 n P.symm (h (f x)) := by
    refine P.contDiffAt_symm (f₀' := A) (hh.image_mem_toOpenPartialHomeomorph_target hd hn0) ?_
      ?_ <;>
      rw [hP, hPx] <;> assumption
  have hback (g : E → F) (hg : ContinuousAt g x) (hgx : g x = f x) :
      P.symm ∘ h ∘ g =ᶠ[𝓝 x] g := by
    refine (hg.eventually (hgx ▸ P.eventually_left_inverse hxP)).mono fun y hy ↦ ?_
    rw [← hP]
    exact hy
  refine (hjet.comp (refl P.symm _) (hh.comp x hf) ((hff' ▸ hh).comp x hf') ?_ ?_).congr
    (hback f hf.continuousAt rfl) (hback f' hf'.continuousAt hff'.symm)
  · exact hsymm
  · simpa [← hff'] using hsymm

end SameJetAt

end TauCeti

end
