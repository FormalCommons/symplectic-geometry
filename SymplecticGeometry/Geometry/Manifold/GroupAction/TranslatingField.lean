/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral
public import TauCeti.Geometry.Manifold.Flow.Related
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.Invariant
public import TauCeti.RepresentationTheory.Compact.Haar

/-!
# Invariant vector fields translating an invariant function

Let a compact Lie group `G` act smoothly on a boundaryless, Hausdorff, σ-compact manifold `M`
with a finite-dimensional model, and let `f : M → ℝ` be a smooth `G`-invariant function whose
differential does not vanish on a compact set `K`. This file builds a smooth vector field `Y` on
`M` that

* is `G`-invariant: the differential of each `g • ·` carries `Y` at `x` to `Y` at `g • x`;
* vanishes outside a compact set, so it is complete;
* satisfies `df(Y) = 1` on a `G`-invariant open neighbourhood `W` of `K`.

The field is `Y = (ρ / |∇f|²) ∇f`, for the gradient `∇f` of a `G`-invariant metric (Tau Ceti's
`TauCeti.of_forall_riemannianBundle_inner_mfderiv`) and a `G`-invariant cutoff `ρ`, equal to `1`
near `K` and supported in a compact part of the open set where `∇f ≠ 0`. The cutoff is the Haar
average `ρ(x) = ∫ χ(a • x) da` of any cutoff `χ` equal to `1` near the compact set `G • K`; it is
smooth by differentiation under the integral over the compact group
(`ContMDiff.parametric_integral`). In fact `df(Y) = ρ` everywhere.

For such a field the maximal flow commutes with the action
(`MDifferentiable.apply_flowOf`), and `f` increases at unit speed along every piece of trajectory
inside `W`.

## Main results

* `SymplecticGeometry.exists_invariant_vectorField_mfderiv_eq_one`: the invariant complete field
  with `df(Y) = 1` near `K`.
* `SymplecticGeometry.smul_flowOf`: the flow of an invariant complete `C¹` field commutes with the
  action.
* `SymplecticGeometry.apply_flowOf_eq_add`: `f (Φ_t x) = f x + t` while the trajectory stays in
  an open set where `df(Y) = 1`.

## References

* G. E. Bredon, *Introduction to Compact Transformation Groups*, Academic Press (1972),
  Chapter VI (averaging over a compact group).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 9
  (flows of compactly supported vector fields, and naturality of flows).
-/

public section

noncomputable section

open Bundle Function Manifold MeasureTheory Set TauCeti TauCeti.Manifold Topology
open scoped ContDiff Manifold

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section Flow

variable {G : Type*} [Group G] [MulAction G M] [ContMDiffConstSMul I 1 G M] [T2Space M]
  [IsManifold I 1 M] [BoundarylessManifold I M]

/-- The maximal flow of a complete `C¹` vector field `Y` that is invariant under a `C¹` group
action (the differential of each `g • ·` carries `Y x` to `Y (g • x)`) commutes with the
action. -/
theorem smul_flowOf {Y : (x : M) → TangentSpace I x}
    (hY : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)))
    (hYc : IsCompleteVectorField Y)
    (hinv : ∀ (g : G) (x : M), mfderiv I I (g • ·) x (Y x) = Y (g • x)) (g : G) (t : ℝ)
    (x : M) :
    g • flowOf Y t x = flowOf Y t (g • x) :=
  ((contMDiff_const_smul (I := I) (n := 1) g).mdifferentiable one_ne_zero).apply_flowOf hY
    (hinv g) (hYc.mem_flowDomain t x)

end Flow

/-- If a `C¹` vector field `Y` satisfies `df(Y) = 1` on a set `W` where `f` is differentiable,
then `f (Φ_t x) = f x + t` for the maximal flow `Φ` of `Y`, whenever `(t, x)` is in the flow
domain and the trajectory from time `0` to time `t` stays in `W`. -/
theorem apply_flowOf_eq_add [T2Space M] [BoundarylessManifold I M] [CompleteSpace E]
    [IsManifold I 1 M] {Y : (x : M) → TangentSpace I x}
    (hY : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)))
    {f : M → ℝ} {W : Set M} (hf : ∀ y ∈ W, MDifferentiableAt I 𝓘(ℝ) f y)
    (hfY : ∀ y ∈ W, mfderiv I 𝓘(ℝ) f y (Y y) = 1) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain Y) (htW : ∀ s ∈ uIcc 0 t, flowOf Y s x ∈ W) :
    f (flowOf Y t x) = f x + t := by
  have hderiv : ∀ s ∈ uIcc 0 t,
      HasDerivWithinAt (fun s ↦ f (flowOf Y s x) - s) 0 (uIcc 0 t) s := by
    intro s hs
    have hd := hasDerivAt_comp_flowOf hY (uIcc_subset_setOf_mem_flowDomain ht hs)
      (hf _ (htW s hs))
    rw [mvfderiv_apply_eq_mfderiv_apply, hfY _ (htW s hs)] at hd
    have hd' : HasDerivAt (fun s ↦ f (flowOf Y s x) - s) (1 - 1) s := hd.sub (hasDerivAt_id' s)
    rw [sub_self] at hd'
    exact hd'.hasDerivWithinAt
  have h := (convex_uIcc 0 t).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv
    (fun _ _ ↦ by simp : ∀ s ∈ uIcc 0 t, ‖(0 : ℝ)‖ ≤ 0) left_mem_uIcc right_mem_uIcc
  rw [zero_mul, norm_le_zero_iff, flowOf_zero] at h
  linarith

section Existence

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [ChartedSpace H' G] [IsManifold J ∞ G] [MulAction G M] [ContMDiffSMul J I ∞ G M]

include J

/-- A smooth `G`-invariant cutoff: for a compact group acting smoothly, a compact set `K` inside
a `G`-invariant open set `U` has a smooth `G`-invariant function `ρ` that is `1` on a
`G`-invariant open neighbourhood `W` of `K` and vanishes outside a compact subset `D` of `U`. -/
theorem exists_invariant_contMDiff_eq_one_of_isCompact {K U : Set M} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hUinv : ∀ (g : G) (x : M), x ∈ U → g • x ∈ U) :
    ∃ (ρ : M → ℝ) (W D : Set M), ContMDiff I 𝓘(ℝ) ∞ ρ ∧ (∀ (g : G) (x : M), ρ (g • x) = ρ x) ∧
      IsOpen W ∧ K ⊆ W ∧ (∀ (g : G) (x : M), x ∈ W → g • x ∈ W) ∧ (∀ x ∈ W, ρ x = 1) ∧
      IsCompact D ∧ D ⊆ U ∧ ∀ x ∉ D, ρ x = 0 := by
  have hsmul : Continuous (fun p : G × M ↦ p.1 • p.2) :=
    (contMDiff_smul (I := J) (I' := I) (n := ∞)).continuous
  -- The saturation `G • K` is compact and lies in `U`.
  set C := (fun p : G × M ↦ p.1 • p.2) '' (univ ×ˢ K)
  have hC : IsCompact C := (isCompact_univ.prod hK).image hsmul
  have hCU : C ⊆ U := by
    rintro _ ⟨⟨a, y⟩, ⟨-, hy⟩, rfl⟩
    exact hUinv a y (hKU hy)
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨L, hL, hCL, hLU⟩ := exists_compact_between hC hU hCU
  obtain ⟨χ, hχ1, hχ0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior I (n := (⊤ : ℕ∞))
    hC.isClosed hCL
  -- The open set where `χ = 1` contains `C`; `W` is the set of points whose orbit lies in it.
  set V := interior {x | χ x = 1}
  have hCV : C ⊆ V := subset_interior_iff_mem_nhdsSet.2 hχ1
  set W := {x : M | ∀ a : G, a • x ∈ V}
  have hW : IsOpen W := by
    have hcl : IsClosed {p : G × M | p.1 • p.2 ∈ Vᶜ} :=
      isOpen_interior.isClosed_compl.preimage hsmul
    have : Wᶜ = Prod.snd '' {p : G × M | p.1 • p.2 ∈ Vᶜ} := by
      ext x
      simp [W]
    rw [← isClosed_compl_iff, this]
    exact isClosedMap_snd_of_compactSpace _ hcl
  have hKW : K ⊆ W := fun y hy a ↦ hCV ⟨(a, y), ⟨mem_univ _, hy⟩, rfl⟩
  have hWinv (g : G) (x : M) (hx : x ∈ W) : g • x ∈ W := fun a ↦ by
    rw [smul_smul]
    exact hx (a * g)
  -- The saturation `D = G • L` is compact and lies in `U`.
  set D := (fun p : G × M ↦ p.1 • p.2) '' (univ ×ˢ L)
  have hD : IsCompact D := (isCompact_univ.prod hL).image hsmul
  have hDU : D ⊆ U := by
    rintro _ ⟨⟨a, y⟩, ⟨-, hy⟩, rfl⟩
    exact hUinv a y (hLU hy)
  borelize G
  set ρ : M → ℝ := fun x ↦ ∫ a, χ (a • x) ∂haarProb G
  refine ⟨ρ, W, D, ?_, fun g x ↦ ?_, hW, hKW, hWinv, fun x hx ↦ ?_, hD, hDU, fun x hx ↦ ?_⟩
  · exact ContMDiff.parametric_integral (J := J)
      (χ.contMDiff.comp ((contMDiff_smul (I := J) (I' := I)).comp
        (contMDiff_snd.prodMk contMDiff_fst)))
  · simp only [ρ, smul_smul]
    exact integral_mul_right_eq_self (fun a ↦ χ (a • x)) g
  · have : ∀ a : G, χ (a • x) = 1 := fun a ↦ interior_subset (hx a)
    simp [ρ, this]
  · have : ∀ a : G, χ (a • x) = 0 := fun a ↦ hχ0 _ fun ha ↦ hx
      ⟨(a⁻¹, a • x), ⟨mem_univ _, ha⟩, by simp [smul_smul]⟩
    simp [ρ, this]

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
  -- Each `g • ·` is a Riemannian isometry, and `f ∘ (g • ·) = f`.
  have hiso (g : G) : IsLocalRiemannianIsometry I I (g • · : M → M) :=
    ⟨ContMDiffSMul.contMDiff_const_smul (I := J) g,
      fun x ↦ (Diffeomorph.smul J I ∞ g).isInvertible_mfderiv (by simp) (x := x), hg g⟩
  have hfg (g : G) : f ∘ (g • · : M → M) = f := funext (hfinv g)
  have hfd (x : M) : MDifferentiableAt I 𝓘(ℝ) f x := hf.mdifferentiableAt (by simp)
  set q : M → ℝ := fun x ↦ ‖mgradient I f x‖ ^ 2
  have : IsManifold I (∞ + 1) M := ‹IsManifold I ∞ M›
  have hq : ContMDiff I 𝓘(ℝ) ∞ q := contMDiff_norm_sq_mgradient (n := ∞) hf
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
  obtain ⟨ρ, W, D, hρ, hρinv, hW, hKW, hWinv, hρW, hD, hDU, hρD⟩ :=
    exists_invariant_contMDiff_eq_one_of_isCompact (I := I) J (G := G) hK
      (isOpen_ne_fun hq.continuous continuous_const) hKU
      (fun g x hx ↦ by simpa [U, hqinv] using hx)
  set c : M → ℝ := fun x ↦ ρ x * (q x)⁻¹
  have hc : ContMDiff I 𝓘(ℝ) ∞ c := by
    refine contMDiff_of_tsupport fun x hx ↦ ?_
    have hxU : x ∈ U := hDU (closure_minimal (fun y (hy : y ∈ support ρ) ↦
      by_contra fun h ↦ (mem_support.1 hy) (hρD y h))
      hD.isClosed (tsupport_mul_subset_left hx))
    exact hρ.contMDiffAt.mul (hq.contMDiffAt.inv₀ hxU)
  have hρq (x : M) : c x * q x = ρ x := by
    by_cases hx : q x = 0
    · have : ρ x = 0 := hρD x fun h ↦ hDU h hx
      simp [c, hx, this]
    · simp [c, hx]
  set Y : (x : M) → TangentSpace I x := fun x ↦ c x • mgradient I f x
  have hYs : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)) :=
    fun x ↦ hc.contMDiffAt.smul_section (contMDiff_mgradient_infty hf x)
  have hY0 (x : M) (hx : x ∉ D) : Y x = 0 := by simp [Y, c, hρD x hx]
  refine ⟨Y, W, hYs, ⟨D, hD, hY0⟩,
    isCompleteVectorField_of_isCompact_of_eq_zero_off (hYs.of_le (by simp)) hD hY0,
    fun g x ↦ ?_, hW, hKW, hWinv, fun x hx ↦ ?_⟩
  · have hcg : c (g • x) = c x := by simp [c, hρinv, hqinv]
    simp only [Y, map_smul, hcg]
    rw [← (hiso g).mfderiv_mgradient_comp (hfd _), hfg]
  · simp only [Y, map_smul, hdf]
    exact (hρq x).trans (hρW x hx)

end Existence

end SymplecticGeometry

end
