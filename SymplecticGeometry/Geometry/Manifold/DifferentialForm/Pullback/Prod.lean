/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Support
import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Append

/-!
# Pullbacks of rough forms along the projections of a product

For rough forms, with no smoothness of the forms and no manifold or boundary hypotheses on the
factors, this file evaluates the pullbacks of forms along the two projections of a product
`M × M'`:

* `TauCeti.RoughForm.mpullback_fst_apply` and `TauCeti.RoughForm.mpullback_snd_apply`: the
  pullback along `Prod.fst` (resp. `Prod.snd`) reads the first (resp. second) components of the
  tangent vectors;
* `TauCeti.RoughForm.wedge_mpullback_fst_snd_apply_append`: on a frame whose first `k` vectors
  `(u i, 0)` are tangent to the first factor and whose last `l` vectors `(0, w j)` are tangent to
  the second, `pr₁^* α ∧ pr₂^* β` takes the value `α u * β w`;
* `TauCeti.RoughForm.tsupport_wedge_mpullback_fst_snd_subset`: the support of
  `pr₁^* α ∧ pr₂^* β` lies in the product of the supports of `α` and `β`, so it is compact when
  both supports are (`TauCeti.RoughForm.isCompact_tsupport_wedge_mpullback_fst_snd`).

The first three are the rough-form versions of Tau Ceti's `TauCeti.SmoothForm.mpullback_fst_apply`,
`TauCeti.SmoothForm.mpullback_snd_apply` and
`TauCeti.SmoothForm.wedge_mpullback_fst_snd_apply_append`
(`TauCeti/Geometry/Manifold/DifferentialForm/Pullback/Smooth.lean`), and their proofs adapt
those of Tau Ceti to rough forms.
-/

public section

open Set
open scoped Manifold

namespace TauCeti

namespace RoughForm

variable {E E' H H' M M' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H' M']
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] {k l : ℕ}

/-- The pullback of a rough form along the first projection of a product, evaluated on tangent
vectors, is the form evaluated on their first components. -/
theorem mpullback_fst_apply (φ : RoughForm I M F k) (p : M × M')
    (v : Fin k → TangentSpace (I.prod I') p) :
    mpullback (I.prod I') I Prod.fst φ p v =
      φ p.1 (fun i ↦ (Manifold.tangentSpaceProdEquiv p (v i)).1) := by
  rw [mpullback_apply, mfderiv_fst]
  simp only [Manifold.tangentSpaceProdEquiv_apply]
  -- `ContinuousLinearMap.fst` is the projection of the product.
  rfl

/-- The pullback of a rough form along the second projection of a product, evaluated on tangent
vectors, is the form evaluated on their second components. -/
theorem mpullback_snd_apply (φ : RoughForm I' M' F k) (p : M × M')
    (v : Fin k → TangentSpace (I.prod I') p) :
    mpullback (I.prod I') I' Prod.snd φ p v =
      φ p.2 (fun i ↦ (Manifold.tangentSpaceProdEquiv p (v i)).2) := by
  rw [mpullback_apply, mfderiv_snd]
  simp only [Manifold.tangentSpaceProdEquiv_apply]
  -- `ContinuousLinearMap.snd` is the projection of the product.
  rfl

/-- **The wedge of pullbacks from the two factors on a block frame.** On a tangent frame of
`M × M'` whose first `k` vectors `(u i, 0)` are tangent to the first factor and whose last `l`
vectors `(0, w j)` are tangent to the second, `pr₁^* α ∧ pr₂^* β` takes the value `α u * β w`. -/
theorem wedge_mpullback_fst_snd_apply_append (α : RoughForm I M ℝ k) (β : RoughForm I' M' ℝ l)
    (q : M × M') (u : Fin k → TangentSpace I q.1) (w : Fin l → TangentSpace I' q.2) :
    RoughForm.wedge (mpullback (I.prod I') I Prod.fst α) (mpullback (I.prod I') I' Prod.snd β) q
      (Fin.append (fun i ↦ ((u i, 0) : E × E')) fun j ↦ ((0, w j) : E × E')) =
      α q.1 u * β q.2 w := by
  rw [RoughForm.wedge_def, RoughForm.wedgeWith_apply']
  refine (ContinuousAlternatingMap.pairedWedge_apply_append_of_forall _ _ _ _ _ _
    fun y i j ↦ ?_).trans ?_
  · -- The second factor vanishes on a frame containing a vector tangent to the first factor.
    exact (mpullback_snd_apply _ q _).trans
      (ContinuousAlternatingMap.map_coord_zero _ j
        ((congrArg Prod.snd (Manifold.tangentSpaceProdEquiv_apply q _)).trans
          (congrArg Prod.snd (Function.update_self j _ y))))
  · rw [ContinuousLinearMap.mul_apply']
    refine (congrArg₂ (· * ·) (mpullback_fst_apply _ q _) (mpullback_snd_apply _ q _)).trans ?_
    exact congrArg₂ (fun u w ↦ α q.1 u * β q.2 w)
      (funext fun i ↦ congrArg Prod.fst (Manifold.tangentSpaceProdEquiv_apply q _))
      (funext fun j ↦ congrArg Prod.snd (Manifold.tangentSpaceProdEquiv_apply q _))

/-- The support of `pr₁^* α ∧ pr₂^* β` lies in the product of the supports of `α` and `β`. -/
theorem tsupport_wedge_mpullback_fst_snd_subset (α : RoughForm I M ℝ k)
    (β : RoughForm I' M' ℝ l) :
    _root_.tsupport (α := (E × E') [⋀^Fin (k + l)]→L[ℝ] ℝ)
        (RoughForm.wedge (mpullback (I.prod I') I Prod.fst α)
          (mpullback (I.prod I') I' Prod.snd β)) ⊆
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) α ×ˢ
        _root_.tsupport (α := E' [⋀^Fin l]→L[ℝ] ℝ) β := by
  rw [RoughForm.wedge_def]
  exact subset_inter
    ((RoughForm.tsupport_wedgeWith_subset_left _ _ _).trans
      (RoughForm.tsupport_mpullback_subset_preimage continuous_fst α))
    ((RoughForm.tsupport_wedgeWith_subset_right _ _ _).trans
      (RoughForm.tsupport_mpullback_subset_preimage continuous_snd β))

/-- If `α` and `β` have compact support, so does `pr₁^* α ∧ pr₂^* β`. -/
theorem isCompact_tsupport_wedge_mpullback_fst_snd {α : RoughForm I M ℝ k}
    {β : RoughForm I' M' ℝ l} (hα : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) α))
    (hβ : IsCompact (_root_.tsupport (α := E' [⋀^Fin l]→L[ℝ] ℝ) β)) :
    IsCompact (_root_.tsupport (α := (E × E') [⋀^Fin (k + l)]→L[ℝ] ℝ)
      (RoughForm.wedge (mpullback (I.prod I') I Prod.fst α)
        (mpullback (I.prod I') I' Prod.snd β))) :=
  (hα.prod hβ).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_wedge_mpullback_fst_snd_subset α β)

end RoughForm

end TauCeti

end
