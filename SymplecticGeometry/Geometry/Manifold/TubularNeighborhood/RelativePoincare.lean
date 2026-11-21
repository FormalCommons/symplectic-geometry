/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.TubularNeighborhood.RelativePoincare

/-!
# A primitive of the difference of two closed forms on a tube

Let `f : Q → M` be an embedding into a boundaryless Hausdorff second-countable manifold, and let
`η₀`, `η₁` be closed smooth `(k + 1)`-forms on `M` with the same pullback to `Q`. Then on a tube
`W` around `f(Q)`, inside any given open set containing `f(Q)`, there is a smooth `k`-form `β`
with `dβ = η₁ - η₀` on `W` that vanishes along `f(Q)`. Its coordinate expressions have zero
derivative at each point `f q` at which `η₁` and `η₀` agree as forms on `T_{f q} M`.

This is the first step of the relative Moser theorems ([McDuffSalamon2017], Lemma 3.2.1 and
Exercise 3.2.6; [CannasdaSilva2001], Theorem 7.4). It applies Tau Ceti's relative Poincaré lemma
`TauCeti.SmoothEmbedding.exists_isSmoothForm_relative_primitive` to `η₁ - η₀` and bundles the
primitive as a smooth form on the tube, as Tau Ceti's
`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_embedding_eventually_mpullback_eq` does inside its
proof.

## Main results

* `TauCeti.SmoothEmbedding.exists_smoothForm_relative_primitive_sub`: the primitive of `η₁ - η₀`
  on a tube around `f(Q)`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
* [A. Cannas da Silva, *Lectures on Symplectic Geometry*][CannasdaSilva2001]
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M]
  {E' H' Q : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

open TopologicalSpace in
/-- **A relative primitive of a difference of closed forms on a tube.** Let `f : Q → M` be a
smooth embedding and let `η₀`, `η₁` be closed smooth `(k + 1)`-forms on `M` with
`f^* η₁ = f^* η₀`. For every open set `O ⊇ f(Q)` there are an open set `W` with
`f(Q) ⊆ W ⊆ O` and a smooth `k`-form `β` on `W` with `dβ = η₁|_W - η₀|_W`, such that `β`
vanishes at every point `f q`, and the chart expression of `β` at `f q` has zero derivative
whenever `η₁` and `η₀` agree at `f q`. -/
theorem exists_smoothForm_relative_primitive_sub (f : SmoothEmbedding J I ∞ Q M) {k : ℕ}
    {η₀ η₁ : SmoothForm I M F (k + 1)} (h₀ : η₀.IsClosed) (h₁ : η₁.IsClosed)
    (hf : SmoothForm.mpullback f f.contMDiff η₁ = SmoothForm.mpullback f f.contMDiff η₀)
    {O : Set M} (hO : IsOpen O) (hfO : range f ⊆ O) :
    ∃ (W : Opens M) (_ : (W : Set M) ⊆ O) (hfW : range f ⊆ W) (β : SmoothForm I W F k),
      mextDeriv β.val =
        (SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal η₁ -
          SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal η₀).val ∧
      (∀ q, β.val ⟨f q, hfW (mem_range_self q)⟩ = 0) ∧
      ∀ q, η₁.val (f q) = η₀.val (f q) →
        HasFDerivAt (RoughForm.inChartAt β.val ⟨f q, hfW (mem_range_self q)⟩)
          (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F)
          (extChartAt I (⟨f q, hfW (mem_range_self q)⟩ : W) ⟨f q, hfW (mem_range_self q)⟩) := by
  have hf0 : mpullback (F := F) J I f (η₁ - η₀).val = 0 := by
    have h := congrArg Subtype.val (sub_eq_zero.2 hf)
    rwa [← map_sub, SmoothForm.coe_mpullback] at h
  obtain ⟨W, hWO, hfW, hprim⟩ := f.exists_isSmoothForm_relative_primitive (F := F) hO hfO
  obtain ⟨β, hβ, hdβ, hβ0, hβ1⟩ := hprim (r := ⊤) le_top (η₁ - η₀).isSmoothForm
    ((SmoothForm.isClosed_def _).1 (h₁.sub h₀)) hf0
  refine ⟨W, hWO, hfW, ⟨β, hβ.mem_smoothBundleForms⟩, ?_, hβ0, fun q hq ↦ hβ1 q ?_⟩
  · rw [hdβ, ← map_sub]
    exact (SmoothForm.coe_mpullback _ _ _).symm
  · rw [AddSubgroupClass.coe_sub, Pi.sub_apply, hq, sub_self]

end TauCeti.SmoothEmbedding

end
