/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.GroupAction.CompactCutoff
public import TauCeti.Geometry.Manifold.Flow.Complete
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.Invariant

/-!
# Invariant vector fields translating an invariant function

Let a compact Lie group `G` act smoothly on a boundaryless, Hausdorff, σ-compact manifold `M`
with a finite-dimensional model, and let `f : M → ℝ` be a smooth `G`-invariant function whose
differential does not vanish on a compact set `K`. This file builds a smooth vector field `Y` on
`M` that

* is `G`-invariant: the differential of each `g • ·` carries `Y` at `x` to `Y` at `g • x`;
* vanishes outside a compact set, so it is complete;
* satisfies `df(Y) = 1` on a `G`-invariant open neighbourhood `W` of `K`.

The field is Milnor's cut-off normalized gradient `Y = (ρ / |∇f|²) ∇f` [Milnor, Thm 3.1], made
equivariant: `∇f` is the gradient for a `G`-invariant metric (Tau Ceti's
`TauCeti.of_forall_riemannianBundle_inner_mfderiv`), and `ρ` is a `G`-invariant cutoff, equal to
`1` near `K` and with compact support in the open set where `∇f ≠ 0`
(`SymplecticGeometry.exists_invariant_contMDiff_eq_one_of_isCompact`). Since each `g • ·` is an
isometry, it carries `∇f` to itself. In fact `df(Y) = ρ` everywhere. The construction follows the
non-equivariant one of Tau Ceti's `TauCeti.exists_vectorField_eq_inv_smul_of_mvfderiv_lt_zero`
and `TauCeti.exists_flow_apply_eq_sub_of_mvfderiv_lt_zero`.

The flow of such a field commutes with the action (`TauCeti.smul_flowOf`), and `f` increases at
unit speed along every piece of trajectory inside `W` (`TauCeti.apply_flowOf_eq_add`); both are
in `SymplecticGeometry.Geometry.Manifold.Flow.Basic`.

## Main results

* `SymplecticGeometry.exists_invariant_vectorField_mfderiv_eq_one`: the invariant complete field
  with `df(Y) = 1` near `K`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press
  (1963), Theorem 3.1 (the cut-off normalized gradient field).
* G. E. Bredon, *Introduction to Compact Transformation Groups*, Academic Press (1972),
  Chapter VI (averaging over a compact group).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 9
  (flows of compactly supported vector fields).
-/

public section

noncomputable section

open Bundle Function Manifold Set TauCeti TauCeti.Manifold Topology
open scoped ContDiff Manifold

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [ChartedSpace H' G] [IsManifold J ∞ G] [MulAction G M] [ContMDiffSMul J I ∞ G M]

include J

/-- **An invariant complete vector field translating an invariant function.** Let a compact Lie
group `G` act smoothly on a boundaryless, Hausdorff, σ-compact manifold `M` with a
finite-dimensional model, and let `f : M → ℝ` be smooth and `G`-invariant, with nonzero
differential at every point of a compact set `K`. Then there is a smooth vector field `Y` on `M`,
invariant under the action, vanishing outside a compact set (hence complete), and a `G`-invariant
open neighbourhood `W` of `K` on which `df(Y) = 1`. -/
theorem exists_invariant_vectorField_mfderiv_eq_one {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hfinv : ∀ (g : G) (x : M), f (g • x) = f x) {K : Set M} (hK : IsCompact K)
    (hKf : ∀ x ∈ K, mfderiv I 𝓘(ℝ) f x ≠ 0) :
    ∃ (Y : (x : M) → TangentSpace I x) (W : Set M),
      ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)) ∧
      (∃ D : Set M, IsCompact D ∧ ∀ x ∉ D, Y x = 0) ∧ IsCompleteVectorField Y ∧
      (∀ (g : G) (x : M), mfderiv I I (g • ·) x (Y x) = Y (g • x)) ∧
      IsOpen W ∧ K ⊆ W ∧ (∀ (g : G) (x : M), x ∈ W → g • x ∈ W) ∧
      ∀ x ∈ W, mfderiv I 𝓘(ℝ) f x (Y x) = 1 := by
  refine of_forall_riemannianBundle_inner_mfderiv (I := I) (M := M) J G fun hg ↦ ?_
  have : ContMDiffConstSMul I ∞ G M := ContMDiffSMul.contMDiffConstSMul J
  -- Each `g • ·` is a Riemannian isometry, and `f ∘ (g • ·) = f`.
  have hiso (g : G) : IsLocalRiemannianIsometry I I (g • · : M → M) := by
    simpa using (RiemannianIsometry.constSMul g (hg g)).isLocalRiemannianIsometry
  have hfg (g : G) : f ∘ (g • · : M → M) = f := funext (hfinv g)
  have hfd (x : M) : MDifferentiableAt I 𝓘(ℝ) f x := hf.mdifferentiableAt (by simp)
  set q : M → ℝ := fun x ↦ ‖mgradient I f x‖ ^ 2
  have : IsManifold I (∞ + 1) M := by simpa using ‹IsManifold I ∞ M›
  have hq : ContMDiff I 𝓘(ℝ) ∞ q := contMDiff_norm_sq_mgradient (n := ∞) (by simpa using hf)
  have hqinv (g : G) (x : M) : q (g • x) = q x := by
    simp only [q, ← (hiso g).norm_mgradient_comp (hfd _), hfg]
  have hdf (x : M) : mfderiv I 𝓘(ℝ) f x (mgradient I f x) = q x := by
    rw [← mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_mgradient, real_inner_self_eq_norm_sq]
  -- The open invariant set `U` where the differential does not vanish.
  set U := {x : M | q x ≠ 0}
  have hKU : K ⊆ U := fun x hx hqx ↦ hKf x hx <| by
    have h0 : mvfderiv I f x = 0 :=
      mgradient_eq_zero_iff.1 (by simpa [q] using hqx)
    ext v
    rw [← mvfderiv_apply_eq_mfderiv_apply, h0]
    rfl
  obtain ⟨ρ, W, hρ, hρinv, hW, hKW, hWinv, hρW, hρc, hρU⟩ :=
    exists_invariant_contMDiff_eq_one_of_isCompact (I := I) J (G := G) hK
      (isOpen_ne_fun hq.continuous continuous_const) hKU
      (fun g x hx ↦ by simpa [U, hqinv] using hx)
  have hρ0 (x : M) (hx : x ∉ tsupport ρ) : ρ x = 0 := image_eq_zero_of_notMem_tsupport hx
  set c : M → ℝ := fun x ↦ ρ x * (q x)⁻¹
  have hc : ContMDiff I 𝓘(ℝ) ∞ c := by
    refine contMDiff_of_tsupport fun x hx ↦ ?_
    exact hρ.contMDiffAt.mul (hq.contMDiffAt.inv₀ (hρU (tsupport_mul_subset_left hx)))
  have hρq (x : M) : c x * q x = ρ x := by
    by_cases hx : q x = 0
    · have : ρ x = 0 := hρ0 x fun h ↦ hρU h hx
      simp [c, hx, this]
    · simp [c, hx]
  set Y : (x : M) → TangentSpace I x := fun x ↦ c x • mgradient I f x
  have hYs : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)) :=
    fun x ↦ hc.contMDiffAt.smul_section (contMDiff_mgradient_infty hf x)
  have hY0 (x : M) (hx : x ∉ tsupport ρ) : Y x = 0 := by simp [Y, c, hρ0 x hx]
  refine ⟨Y, W, hYs, ⟨tsupport ρ, hρc.isCompact, hY0⟩,
    isCompleteVectorField_of_isCompact_of_eq_zero_off (hYs.of_le (by simp)) hρc.isCompact hY0,
    fun g x ↦ ?_, hW, hKW, hWinv, fun x hx ↦ ?_⟩
  · have hcg : c (g • x) = c x := by simp [c, hρinv, hqinv]
    simp only [Y, map_smul, hcg]
    rw [← (hiso g).mfderiv_mgradient_comp (hfd _), hfg]
  · simp only [Y, map_smul, hdf]
    exact (hρq x).trans (hρW x hx)

end SymplecticGeometry

end
