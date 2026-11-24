/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Homotopy
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.OrderedFlow
public import SymplecticGeometry.Geometry.Manifold.Flow.Ordered
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Loops of ordered flows are homotopic to the constant diffeotopy

Let `v 0, …, v (k - 1)` be complete `C^n` vector fields, `1 ≤ n`, and `A i` be `C^n` time
functions with `A i 0 = 0` and `A i 1 = 0`. Tau Ceti's ordered diffeotopy
`TauCeti.orderedGlobalFlowDiffeotopy`, with motion `ψ^(v 0)_(A 0 t) ∘ ⋯ ∘ ψ^(v (k-1))_(A (k-1) t)`,
is then a loop, and Tau Ceti's `TauCeti.Diffeotopy.exists_homotopy_orderedGlobalFlowDiffeotopy`
contracts it to the constant diffeotopy by scaling the times by `1 - s`. This file upgrades that
contraction to a homotopy in the sense of `TauCeti.Diffeotopy.Homotopic`, which also asks for a
jointly `C^n` inverse in the space variable. The inverse is the ordered flow of the fields in the
reverse order for the negated, reversed times (`TauCeti.orderedFlowOf_rev_neg_orderedFlowOf`,
`TauCeti.orderedFlowOf_orderedFlowOf_rev_neg`), which is jointly `C^n` by Tau Ceti's
`TauCeti.contMDiff_orderedFlowOf_uncurry`. The proof of its smoothness follows that of
`TauCeti.Diffeotopy.exists_homotopy_orderedGlobalFlowDiffeotopy`.

## Main results

* `TauCeti.Diffeotopy.orderedGlobalFlowDiffeotopy_homotopic_refl`: if every time function
  vanishes at `0` and at `1`, the ordered diffeotopy is homotopic to the constant diffeotopy.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §10.2
  (the proof of Theorem 10.2.5).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

namespace Diffeotopy

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [IsManifold I 1 M]
  {n : ℕ∞} [IsManifold I n M]

/-- **Loops of ordered flows are homotopic to the constant diffeotopy.** For complete `C^n`
vector fields `v i`, `1 ≤ n`, and `C^n` time functions `A i` vanishing at `0` and at `1`, the
ordered diffeotopy `t ↦ ψ^(v 0)_(A 0 t) ∘ ⋯ ∘ ψ^(v (k-1))_(A (k-1) t)` is homotopic, relative to
both time ends, to the constant diffeotopy. -/
theorem orderedGlobalFlowDiffeotopy_homotopic_refl (hn : 1 ≤ n) {k : ℕ}
    {v : Fin k → (x : M) → TangentSpace I x}
    (hv : ∀ i, CMDiff n (fun y ↦ (⟨y, v i y⟩ : TangentBundle I M)))
    (hc : ∀ i, IsCompleteVectorField (v i)) {A : Fin k → ℝ → ℝ} (hA : ∀ i, ContDiff ℝ n (A i))
    (hA₀ : ∀ i, A i 0 = 0) (h₁ : ∀ i, A i 1 = 0) :
    (orderedGlobalFlowDiffeotopy hn v hv hc A hA hA₀).Homotopic (refl I n M) := by
  obtain ⟨G, hG, hG₀, hG₁, hGt₀, hGt₁, hGs⟩ :=
    exists_homotopy_orderedGlobalFlowDiffeotopy hn v hv hc A hA hA₀ h₁
  have hv₁ : ∀ i, CMDiff 1 (fun y ↦ (⟨y, v i y⟩ : TangentBundle I M)) := fun i ↦
    (hv i).of_le (by exact_mod_cast hn)
  -- `G` at `((x, t), s)` is the ordered flow of `x` for the times `(1 - s) A i t`.
  have hG' : ∀ x t s, G ((x, t), s) = orderedFlowOf v (fun i ↦ (1 - (s : ℝ)) * A i t) x :=
    fun x t s ↦ congrFun (hGs t s) x
  refine homotopic_iff.2 ⟨G, fun q ↦ orderedFlowOf (fun i ↦ v i.rev)
    (fun i ↦ -((1 - (q.2 : ℝ)) * A i.rev q.1.2)) q.1.1, hG, hG₀, fun p ↦ ?_, hGt₀,
    fun x s ↦ ?_, ?_, fun x t s ↦ ?_, fun x t s ↦ ?_⟩
  · rw [hG₁, cylinderMap_apply, refl_apply]
  · rw [hGt₁, final_orderedGlobalFlowDiffeotopy_eq_refl hn v hv hc A hA hA₀ h₁,
      Diffeomorph.coe_refl, id_eq]
  · -- The negated, reversed times depend smoothly on `((x, t), s)`.
    have htimes : ContMDiff ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) 𝓘(ℝ, Fin k → ℝ) n
        fun q : (M × unitInterval) × unitInterval ↦
          fun i : Fin k ↦ -((1 - (q.2 : ℝ)) * A i.rev q.1.2) :=
      contMDiff_pi_module_iff.2 fun i ↦
        (((contDiff_const.sub contDiff_id).contMDiff.comp
          (contMDiff_subtypeVal_Icc.comp contMDiff_snd)).mul
          ((hA i.rev).contMDiff.comp
            (contMDiff_subtypeVal_Icc.comp (contMDiff_snd.comp contMDiff_fst)))).neg
    exact (contMDiff_orderedFlowOf_uncurry hn (fun i ↦ hv i.rev) fun i ↦ hc i.rev).comp
      (htimes.prodMk (contMDiff_fst.comp contMDiff_fst))
  · rw [hG']
    exact orderedFlowOf_rev_neg_orderedFlowOf hv₁ hc (fun i ↦ (1 - (s : ℝ)) * A i t) x
  · rw [hG']
    exact orderedFlowOf_orderedFlowOf_rev_neg hv₁ hc (fun i ↦ (1 - (s : ℝ)) * A i t) x

end Diffeotopy

end TauCeti

end
