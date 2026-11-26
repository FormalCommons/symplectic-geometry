/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic
import SymplecticGeometry.Geometry.Manifold.ContMDiff.NullHomotopy
import SymplecticGeometry.Geometry.Symplectic.Flux.CompactSupport
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Comp
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Isotopy
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.PointParametric

/-!
# Families of symplectic balls with a fixed centre

Let `M` be a simply connected symplectic manifold, and `e` a smooth family over `[0, 1]` of
symplectic embeddings of the closed ball `B(r)`, `0 < r`, whose two ends `e (0, ·)` and
`e (1, ·)` are centred at the same point `p₀`. This file replaces `e` by a family `e'` with the
same two ends whose centre `e' (t, 0)` is `p₀` at every time
(`SymplecticGeometry.exists_based_family_of_family`). This is the first proof of Lemma 7.1.25
of [McDuffSalamon2017].

The proof follows theirs. The centres `t ↦ e (t, 0)` form a smooth loop based at `p₀`. Since `M`
is simply connected, the loop bounds a smooth map `H` on the square with `H (t, 0) = e (t, 0)`,
equal to `p₀` on the three other edges (`ContMDiff.exists_contMDiff_nullhomotopy`). Near
`B(r)` the family `e` is a smooth isotopy
(`SymplecticGeometry.IsSymplecticBallFamily.exists_smoothIsotopy`), so there are compactly
supported Hamiltonian diffeotopies `Φ_t`, jointly smooth in `t`, with
`Φ_t (s, H (t, 0)) = H (t, s)`, and equal to the identity for `t = 0` and `t = 1`, where `H (t, ·)`
is constant (`SymplecticGeometry.exists_isCompactlySupportedHamiltonian_param_apply_mk_zero_eq`).
The family `e' (t, z) = Φ_t (1, e (t, z))` has centre `H (t, 1) = p₀`, the ends of `e`, and
symplectic slices (`SymplecticGeometry.IsSymplecticBallEmbedding.diffeotopy_comp`).

## Main results

* `SymplecticGeometry.exists_based_family_of_family`: in a simply connected manifold, a family of
  symplectic balls whose ends share their centre can be replaced by one with the same ends and a
  fixed centre.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Lemma 7.1.25.
-/

public section

open Set Function Metric
open scoped ContDiff Manifold

namespace SymplecticGeometry

open TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {σ : SmoothTwoForm I M}

/-- **Based families of symplectic balls.** Let `σ` be a symplectic form on a simply connected,
Hausdorff, σ-compact, boundaryless manifold `M` of dimension `2n`, and let `e` be a smooth family
over `[0, 1]` of symplectic embeddings of the closed ball `B(r)` of `StdSpace (Fin n)`, `0 < r`,
with `e (0, 0) = e (1, 0) = p₀`. Then there is a smooth family `e'` of symplectic embeddings of
`B(r)` with `e' (0, ·) = e (0, ·)`, `e' (1, ·) = e (1, ·)` and `e' (t, 0) = p₀` for every `t`. -/
theorem exists_based_family_of_family [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [SimplyConnectedSpace M] (hσ : σ.IsSymplectic)
    (hdim : Module.finrank ℝ E = 2 * n) {r : ℝ} (hr : 0 < r)
    {e : unitInterval × StdSpace (Fin n) → M} (he : IsSymplecticBallFamily σ r e) {p₀ : M}
    (he₀ : e (0, 0) = p₀) (he₁ : e (1, 0) = p₀) :
    ∃ e' : unitInterval × StdSpace (Fin n) → M, IsSymplecticBallFamily σ r e' ∧
      (∀ z, e' (0, z) = e (0, z)) ∧ (∀ z, e' (1, z) = e (1, z)) ∧ ∀ t, e' (t, 0) = p₀ := by
  -- Near `B(r)`, the family `e` is a smooth isotopy `k`.
  obtain ⟨V, hrV, f₀, f₁, k, hk⟩ := he.exists_smoothIsotopy hr
  let x₀ : V := ⟨0, hrV (mem_closedBall_self hr.le)⟩
  -- The loop of centres and a smooth null-homotopy `H` of it.
  have hc : ContMDiff (𝓡∂ 1) I ∞ fun t ↦ e (t, 0) := by
    convert k.contMDiff.comp (contMDiff_id.prodMk (contMDiff_const (c := x₀))) using 1
    funext t
    exact (hk (t, x₀)).symm
  obtain ⟨G, hG, hG₀, hG₁, hGl, hGr⟩ := hc.exists_contMDiff_nullhomotopy he₀ he₁
  -- Hamiltonian diffeotopies `Φ t` moving `G (t, 0)` along `s ↦ G (t, s)`.
  have hd : Module.finrank ℝ (StdSpace (Fin n)) = Module.finrank ℝ E := by
    simp [hdim, two_mul]
  obtain ⟨Φ, -, -, -, hΦ, hΦs, -, hΦG, hΦid⟩ :=
    exists_isCompactlySupportedHamiltonian_param_apply_mk_zero_eq hσ hd hG
      (e := fun p : unitInterval × V ↦ k p) k.contMDiff
      (fun t ↦ by simpa only [SmoothIsotopy.toContMDiffMap_apply] using k.isSmoothEmbedding t)
      (x₀ := x₀) (fun t ↦ (hk _).trans (hG₀ t).symm) isOpen_univ fun _ _ ↦ mem_univ _
  have hid (t : unitInterval) (hGt : ∀ s, G (t, s) = p₀) (z : StdSpace (Fin n)) :
      Φ t (1, e (t, z)) = e (t, z) :=
    hΦid t (fun s ↦ by rw [hGt, hGt]) 1 _
  refine ⟨fun p ↦ Φ p.1 (1, e p), (isSymplecticBallFamily_def _ _ _).2 ⟨?_, fun t ↦ ?_⟩,
    hid 0 hGl, hid 1 hGr, fun t ↦ ?_⟩
  · obtain ⟨U, hU, hrU, heU⟩ := he.exists_contMDiffOn
    exact ⟨U, hU, hrU, hΦs.comp_contMDiffOn
      ((contMDiffOn_fst.prodMk contMDiffOn_const).prodMk heU)⟩
  · exact (he.isSymplecticBallEmbedding t).diffeotopy_comp
      ((Diffeotopy.isCompactlySupportedHamiltonian_iff.1 (hΦ t)).1 1)
  · exact (congrArg (fun y ↦ Φ t (1, y)) (hG₀ t).symm).trans ((hΦG t 1).trans (hG₁ t))

end SymplecticGeometry

end
