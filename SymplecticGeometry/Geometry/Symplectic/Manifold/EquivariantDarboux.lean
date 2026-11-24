/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.EquivariantDarboux
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Equivariant Darboux parametrizations at a fixed point

Let a compact Lie group `G` act smoothly on a boundaryless finite-dimensional manifold `M`,
preserving a symplectic form `σ`, and let `p` be a point fixed by every element of `G`. Then `G`
acts linearly on `T_p M = E` through the derivatives `ρ g = d(g • ·)_p`, and this theorem gives a
smooth partial diffeomorphism `Φ` from `E` to `M` with

* an open source `U` containing `0`, invariant under every `ρ g`, and an open target `V`
  containing `p`, invariant under `G`;
* `Φ 0 = p` and `Φ (ρ g u) = g • Φ u` for `u ∈ U`;
* `Φ^* σ = σ_p` on `U`: for `u ∈ U`, `σ_{Φ u} (dΦ_u v, dΦ_u w) = σ_p (v, w)`.

So `Φ` is a `G`-equivariant symplectomorphism from `(U, σ_p)` onto `(V, σ)`.

Tau Ceti's `TauCeti.SmoothTwoForm.IsSymplectic.exists_equivariant_darbouxChart` gives a chart
from `M` to `E` with these properties; the theorem here is its inverse, read off with the chain
rule for the derivative of the inverse of a partial diffeomorphism
(`PartialDiffeomorph.mfderiv_apply_mfderiv_symm_apply`).

## Main results

* `TauCeti.SmoothTwoForm.IsSymplectic.exists_equivariant_symplectomorphism_tangentSpace`: the
  equivariant Darboux theorem at a fixed point, as an equivariant symplectomorphism from an
  invariant open neighbourhood of `0` in `(T_p M, σ_p)` onto an invariant open neighbourhood of
  `p`.

## References

* [A. Cannas da Silva, *Symplectic Toric Manifolds*][CannasdaSilva2001], Theorem 3.1.1.
* [V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*][GuilleminSternberg1990],
  Theorem 22.1.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {EG HG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} [IG.Boundaryless] [TopologicalSpace G] [ChartedSpace HG G]
  [IsManifold IG ∞ G] [Group G] [IsTopologicalGroup G] [CompactSpace G] [MulAction G M]
  [ContMDiffSMul IG I ∞ G M]

/-- **The equivariant Darboux theorem at a fixed point.** Let a compact Lie group `G` act smoothly
on a boundaryless finite-dimensional manifold `M`, preserving a symplectic form `form`, and let
`p` be fixed by `G`. Let `G` act on `T_p M` through its derivative representation
`g ↦ d(g • ·)_p`. Then there is a smooth partial diffeomorphism `Φ` from `T_p M` to `M`, whose
source is an open neighbourhood of `0` invariant under the derivative representation and whose
target is a `G`-invariant open neighbourhood of `p`, with `Φ 0 = p`, which is `G`-equivariant and
pulls `form` back to the constant form `form_p`.

Milestone: *Equivariant Darboux theorem and quadratic local moment maps*. -/
theorem IsSymplectic.exists_equivariant_symplectomorphism_tangentSpace
    {form : SmoothTwoForm I M} (hform : form.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun y : M ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) g) form = form)
    {p : M} (hp : ∀ g : G, g • p = p) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞,
      (0 : E) ∈ Φ.source ∧ Φ 0 = p ∧
      (∀ g : G, ∀ u ∈ Φ.source,
        mfderiv I I (g • ·) p u ∈ Φ.source ∧ Φ (mfderiv I I (g • ·) p u) = g • Φ u) ∧
      (∀ g : G, ∀ x ∈ Φ.target, g • x ∈ Φ.target) ∧
      ∀ u ∈ Φ.source, ∀ v w : E,
        form.eval₂ (Φ u) (mfderiv 𝓘(ℝ, E) I Φ u v) (mfderiv 𝓘(ℝ, E) I Φ u w) =
          hform.isNondegenerate.symplecticFormAt p v w := by
  obtain ⟨chart, hpc, hc0, hequiv, hform', -⟩ :=
    hform.exists_equivariant_darbouxChart (IG := IG) hG hp
  have h0 : (0 : E) ∈ chart.target := hc0 ▸ chart.map_source hpc
  have hsymm0 : chart.symm 0 = p := by rw [← hc0]; exact chart.left_inv hpc
  refine ⟨chart.symm, h0, hsymm0, fun g u hu ↦ ?_, fun g x hx ↦ (hequiv g x hx).1,
    fun u hu v w ↦ ?_⟩
  · have hx : chart.symm u ∈ chart.source := chart.map_target hu
    have hu' : chart (chart.symm u) = u := chart.right_inv hu
    obtain ⟨hgx, hcg⟩ := hequiv g _ hx
    rw [hu'] at hcg
    rw [← hcg]
    exact ⟨chart.map_source hgx, chart.left_inv hgx⟩
  · have hdiff (a : E) :
        mvfderiv I chart (chart.symm u) (mfderiv 𝓘(ℝ, E) I chart.symm u a) = a := by
      rw [mvfderiv_apply_eq_mfderiv_apply]
      exact chart.mfderiv_apply_mfderiv_symm_apply (by simp) hu a
    refine (hform' (chart.symm u) (chart.map_target hu) _ _).trans ?_
    rw [hdiff, hdiff]

end SmoothTwoForm

end TauCeti

end
