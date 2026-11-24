/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.Sets.Opens
public import SymplecticGeometry.Topology.VectorBundle.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FiberScaling

import Mathlib.Analysis.Calculus.LineDeriv.Basic
import TauCeti.Topology.FiberBundle.Separation

/-!
# The rescaled family of a map near the zero section of a vector bundle

Let `V → B` be a real vector bundle with model fibre `F`, `U` an open set of its total space and
`ψ : U → V` a map. Its *rescaled family* `SymplecticGeometry.vectorBundleRescaledFamily ψ` is
the map `V × [0, 1] → V` given for `t > 0` by `m_{1/t} ∘ ψ ∘ m_t`, where `m_c` multiplies each
fibre by `c` (`TauCeti.vectorBundleFiberScaling`, `TauCeti.vectorBundleScalarDiffeomorph`), and at
`t = 0` by the limit of these maps as `t → 0⁺`. At `t = 1` it is `ψ`.

When `ψ` fixes the point `0_x` of the zero section, is continuous there, and its fibre
coordinate in a linear trivialization `e` over `x` has derivative `L` at `0` in the fibre
direction, the limit exists and is the image under `e⁻¹` of `(x, L w)`, where `w` is the fibre
coordinate of the point (`SymplecticGeometry.vectorBundleRescaledFamily_zero_eq`). So the slice
at `t = 0` is the fibre derivative of `ψ` along the zero section; being a limit, it does not depend
on the trivialization. If `ψ` fixes a point of the zero section, so does every slice.

This is the vector bundle version of Tau Ceti's `TauCeti.zeroSectionRescale`, which
rescales a map of a product `S × V` and takes the value at `t = 0` as an argument.

## Main definitions

* `SymplecticGeometry.vectorBundleRescaledFamily ψ`: the rescaled family of `ψ`.

## Main results

* `SymplecticGeometry.vectorBundleRescaledFamily_of_pos`: for `t > 0` it is `m_{1/t} ∘ ψ ∘ m_t`
  (`SymplecticGeometry.vectorBundleRescaledFamily_of_ne_zero` writes it out).
* `SymplecticGeometry.vectorBundleRescaledFamily_one`: at `t = 1` it is `ψ`.
* `SymplecticGeometry.tendsto_vectorBundleRescaledFamily_zero`,
  `SymplecticGeometry.vectorBundleRescaledFamily_zero_eq`: the slices tend to the fibre
  derivative of `ψ` as `t → 0⁺`, which is the slice at `t = 0`.
* `SymplecticGeometry.vectorBundleRescaledFamily_zeroSection`: the slices fix every point of the
  zero section that `ψ` fixes.

Along the way: fibre scaling read in a linear trivialization,
`TauCeti.vectorBundleFiberScaling_eq_trivialization_symm`.

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 4, §5.
* [P. Seidel, *Floer homology and the symplectic isotopy problem*][Seidel1997Thesis], Lemma 2.2.
-/

public section

noncomputable section

open Set Bundle Filter Topology TopologicalSpace TauCeti
open scoped Manifold ContDiff

namespace TauCeti

variable {B F : Type*} {V : B → Type*} [∀ b, AddCommMonoid (V b)] [∀ b, Module ℝ (V b)]
  [TopologicalSpace B] [TopologicalSpace F] [AddCommMonoid F] [Module ℝ F]
  [TopologicalSpace (TotalSpace F V)]

/-- Fibre scaling read in a linear trivialization `e`: over the base set of `e`, it multiplies the
fibre coordinate by the time. -/
theorem vectorBundleFiberScaling_eq_trivialization_symm (e : Trivialization F (π F V))
    [e.IsLinear ℝ] {z : TotalSpace F V} (hz : z.proj ∈ e.baseSet) (t : Icc (0 : ℝ) 1) :
    vectorBundleFiberScaling F V (z, t) = ⟨z.proj, e.symm z.proj ((t : ℝ) • (e z).2)⟩ := by
  rw [vectorBundleFiberScaling_apply, e.symm_smul_snd hz]

end TauCeti

namespace SymplecticGeometry

variable {B F : Type*} {V : B → Type*} [∀ b, AddCommMonoid (V b)] [∀ b, Module ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] {U : Opens (TotalSpace F V)}

open scoped Classical in
/-- The **rescaled family** of a map `ψ : U → V` defined on an open set of the total space of a
vector bundle. For `t > 0` it is `m_{1/t} ∘ ψ ∘ m_t`, where `m_c` multiplies the fibres by `c`
(the junk value `z` is taken at `(z, t)` when `m_t z ∉ U`); at `t = 0` it is the limit of these
maps as `t → 0⁺` (a junk value if there is none). At a point over `x`, that value is the fibre
derivative of `ψ` at `0_x` when `ψ` fixes `0_x`, is continuous there and is differentiable along
the fibre (`SymplecticGeometry.vectorBundleRescaledFamily_zero_eq`). -/
def vectorBundleRescaledFamily (ψ : U → TotalSpace F V) (p : TotalSpace F V × Icc (0 : ℝ) 1) :
    TotalSpace F V :=
  let f : Icc (0 : ℝ) 1 → TotalSpace F V := fun t ↦
    if hz : vectorBundleFiberScaling F V (p.1, t) ∈ U then
      ⟨(ψ ⟨_, hz⟩).proj, (t : ℝ)⁻¹ • (ψ ⟨_, hz⟩).snd⟩
    else p.1
  if (p.2 : ℝ) = 0 then @limUnder _ _ _ ⟨p.1⟩ (𝓝[>] 0) f else f p.2

/-- Away from `t = 0`, the rescaled family at `(z, t)` is the point over the base point of
`ψ (m_t z)` whose fibre part is that of `ψ (m_t z)` divided by `t`. -/
theorem vectorBundleRescaledFamily_of_ne_zero (ψ : U → TotalSpace F V)
    {t : Icc (0 : ℝ) 1} (ht : (t : ℝ) ≠ 0) (z : TotalSpace F V)
    (hz : vectorBundleFiberScaling F V (z, t) ∈ U) :
    vectorBundleRescaledFamily ψ (z, t) =
      ⟨(ψ ⟨_, hz⟩).proj, (t : ℝ)⁻¹ • (ψ ⟨_, hz⟩).snd⟩ := by
  simp only [vectorBundleRescaledFamily, ht, ite_false]
  split_ifs
  rfl

/-- At `t = 1` the rescaled family is `ψ`. -/
@[simp]
theorem vectorBundleRescaledFamily_one (ψ : U → TotalSpace F V) (z : U) :
    vectorBundleRescaledFamily ψ (z, 1) = ψ z := by
  have hz' : vectorBundleFiberScaling F V (z, 1) ∈ U := by
    rw [vectorBundleFiberScaling_one]
    exact z.property
  rw [vectorBundleRescaledFamily_of_ne_zero ψ (by simp) z hz']
  simp only [Icc.coe_one, inv_one, one_smul]
  congr 2 <;> simp

/-- The slice at `t = 0` of the rescaled family is the limit of the slices as `t → 0⁺`. -/
theorem vectorBundleRescaledFamily_zero_of_tendsto [T2Space (TotalSpace F V)]
    {ψ : U → TotalSpace F V} {z w : TotalSpace F V}
    (h : Tendsto (fun t ↦ vectorBundleRescaledFamily ψ (z, t)) (𝓝[>] 0) (𝓝 w)) :
    vectorBundleRescaledFamily ψ (z, 0) = w := by
  have : (𝓝[>] (0 : Icc (0 : ℝ) 1)).NeBot :=
    nhdsGT_neBot_of_exists_gt ⟨1, by simp⟩
  simp only [vectorBundleRescaledFamily, Icc.coe_zero, ite_true]
  refine Tendsto.limUnder_eq (h.congr' ((eventually_nhdsWithin_of_forall fun t ht ↦
    (Subtype.coe_lt_coe.2 ht).ne').mono fun (t : Icc (0 : ℝ) 1) (ht : (t : ℝ) ≠ 0) ↦ ?_))
  simp [vectorBundleRescaledFamily, ht]

/-- If `ψ` fixes the point `0_x` of the zero section, then so does every slice of its rescaled
family. -/
theorem vectorBundleRescaledFamily_zeroSection [T2Space (TotalSpace F V)]
    {ψ : U → TotalSpace F V} {x : B} (hx : zeroSection F V x ∈ U)
    (hψ0 : ψ ⟨_, hx⟩ = zeroSection F V x) (t : Icc (0 : ℝ) 1) :
    vectorBundleRescaledFamily ψ (zeroSection F V x, t) = zeroSection F V x := by
  have hpos : ∀ t : Icc (0 : ℝ) 1, (t : ℝ) ≠ 0 →
      vectorBundleRescaledFamily ψ (zeroSection F V x, t) = zeroSection F V x := by
    intro t ht
    have hz : vectorBundleFiberScaling F V (zeroSection F V x, t) ∈ U := by
      rwa [vectorBundleFiberScaling_zeroSection]
    have hzx : (⟨_, hz⟩ : U) = ⟨_, hx⟩ := Subtype.ext (vectorBundleFiberScaling_zeroSection x t)
    rw [vectorBundleRescaledFamily_of_ne_zero ψ ht _ hz, hzx, hψ0]
    simp only [zeroSection]
    exact congrArg _ (smul_zero _)
  rcases eq_or_ne (t : ℝ) 0 with ht | ht
  · obtain rfl : t = 0 := Subtype.ext ht
    refine vectorBundleRescaledFamily_zero_of_tendsto (tendsto_const_nhds.congr' ?_)
    exact eventually_nhdsWithin_of_forall fun t ht ↦ (hpos t (Subtype.coe_lt_coe.2 ht).ne').symm
  · exact hpos t ht

section Trivialization

variable [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [∀ b, TopologicalSpace (V b)] [FiberBundle F V]

/-- **The slices tend to the fibre derivative.** Let `e` be a linear trivialization over the base
point `x` of `z`, and let `ψ` fix `0_x` and be continuous there. Suppose that for `w` near `0`,
whenever the point over `x` with fibre coordinate `w` in `e` lies in `U`, the fibre coordinate in
`e` of its image under `ψ` is `g w`, for a map `g : F → F` with derivative `L` at `0`. Then as
`t → 0⁺` the rescaled family at `(z, t)` tends to the point over `x` with fibre coordinate `L w`
in `e`, where `w` is the fibre coordinate of `z` in `e`. -/
theorem tendsto_vectorBundleRescaledFamily_zero (e : Trivialization F (π F V)) [e.IsLinear ℝ]
    {ψ : U → TotalSpace F V} {z : TotalSpace F V} (hz : z.proj ∈ e.baseSet)
    (h0 : zeroSection F V z.proj ∈ U) (hψ0 : ψ ⟨_, h0⟩ = zeroSection F V z.proj)
    (hψ : ContinuousAt ψ ⟨_, h0⟩) {g : F → F} {L : F →L[ℝ] F} (hg : HasFDerivAt g L 0)
    (hgψ : ∀ᶠ w in 𝓝 0, ∀ hw : (⟨z.proj, e.symm z.proj w⟩ : TotalSpace F V) ∈ U,
      (e (ψ ⟨_, hw⟩)).2 = g w) :
    Tendsto (fun t ↦ vectorBundleRescaledFamily ψ (z, t)) (𝓝[>] 0)
      (𝓝 ⟨z.proj, e.symm z.proj (L (e z).2)⟩) := by
  classical
  set x := z.proj
  set w₀ := (e z).2
  -- the inverse of `e`, as a map of `B × F`, continuous on `e.baseSet × F`
  set G : B × F → TotalSpace F V := fun q ↦ ⟨q.1, e.symm q.1 q.2⟩ with hG
  have hGc : ∀ v, ContinuousAt G (x, v) := fun v ↦
    e.continuousOn_symm.continuousAt (prod_mem_nhds (e.open_baseSet.mem_nhds hz) univ_mem)
  have hG0 : G (x, 0) = zeroSection F V x := by
    simp [hG, zeroSection, ← Trivialization.symmₗ_apply (R := ℝ) _ hz]
  have hcoe : Tendsto (fun t : Icc (0 : ℝ) 1 ↦ (t : ℝ)) (𝓝[>] 0) (𝓝[>] 0) :=
    continuous_subtypeVal.continuousWithinAt.tendsto_nhdsWithin fun _ ↦ id
  have hsmall : Tendsto (fun t : Icc (0 : ℝ) 1 ↦ (t : ℝ) • w₀) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hcoe.mono_right nhdsWithin_le_nhds).smul_const w₀
  have hscale : ∀ t, vectorBundleFiberScaling F V (z, t) = G (x, (t : ℝ) • w₀) :=
    vectorBundleFiberScaling_eq_trivialization_symm e hz
  have hm : Tendsto (fun t ↦ vectorBundleFiberScaling F V (z, t)) (𝓝[>] 0)
      (𝓝 (zeroSection F V x)) := by
    simp_rw [hscale, ← hG0]
    exact (hGc 0).tendsto.comp (tendsto_const_nhds.prodMk_nhds hsmall)
  have hU : ∀ᶠ t in 𝓝[>] 0, vectorBundleFiberScaling F V (z, t) ∈ U :=
    hm (U.isOpen.mem_nhds h0)
  -- the points `m_t z` of `U`, with a junk value elsewhere
  set σ : Icc (0 : ℝ) 1 → U := fun t ↦
    if h : vectorBundleFiberScaling F V (z, t) ∈ U then ⟨_, h⟩ else ⟨_, h0⟩ with hσ_def
  have hσ : ∀ t (h : vectorBundleFiberScaling F V (z, t) ∈ U), σ t = ⟨_, h⟩ := fun t h ↦ by
    simp only [hσ_def]
    split_ifs
    rfl
  have hy : Tendsto (fun t ↦ ψ (σ t)) (𝓝[>] 0) (𝓝 (zeroSection F V x)) := by
    refine hψ0 ▸ hψ.tendsto.comp (tendsto_subtype_rng.2 ?_)
    exact hm.congr' (hU.mono fun t ht ↦ by simp [hσ t ht])
  have hbase : ∀ᶠ t in 𝓝[>] 0, (ψ (σ t)).proj ∈ e.baseSet :=
    (FiberBundle.continuous_proj F V).continuousAt.tendsto.comp hy (e.open_baseSet.mem_nhds hz)
  have hgw : ∀ᶠ t : Icc (0 : ℝ) 1 in 𝓝[>] 0, ∀ hw : G (x, (t : ℝ) • w₀) ∈ U,
      (e (ψ ⟨_, hw⟩)).2 = g ((t : ℝ) • w₀) := hsmall.eventually hgψ
  -- the fibre derivative, as a one-sided limit
  have hg0 : g 0 = 0 := by
    have hx0 : G (x, 0) ∈ U := hG0.symm ▸ h0
    have hzx : (⟨_, hx0⟩ : U) = ⟨_, h0⟩ := Subtype.ext hG0
    rw [← hgψ.self_of_nhds hx0, hzx, hψ0, ← hG0]
    simp [hG, e.apply_mk_symm hz]
  have hder : Tendsto (fun t : Icc (0 : ℝ) 1 ↦ (t : ℝ)⁻¹ • g ((t : ℝ) • w₀)) (𝓝[>] 0)
      (𝓝 (L w₀)) := by
    simpa [Function.comp_def, hg0] using (hg.hasLineDerivAt w₀).tendsto_slope_zero_right.comp hcoe
  refine ((hGc (L w₀)).tendsto.comp
    (((FiberBundle.continuous_proj F V).continuousAt.tendsto.comp hy).prodMk_nhds hder)).congr' ?_
  filter_upwards [self_mem_nhdsWithin, hU, hbase, hgw] with t ht htU htb htg
  replace ht : (t : ℝ) ≠ 0 := (Subtype.coe_lt_coe.2 ht).ne'
  rw [vectorBundleRescaledFamily_of_ne_zero ψ ht z htU]
  simp only [Function.comp_apply] at htb ⊢
  rw [hσ t htU] at htb ⊢
  have hw : G (x, (t : ℝ) • w₀) ∈ U := hscale t ▸ htU
  have hzw : (⟨_, hw⟩ : U) = ⟨_, htU⟩ := Subtype.ext (hscale t).symm
  rw [← htg hw, hzw]
  exact congrArg _ (e.symm_smul_snd htb _)

/-- **The slice at `t = 0` is the fibre derivative.** Under the hypotheses of
`SymplecticGeometry.tendsto_vectorBundleRescaledFamily_zero`, the rescaled family at `(z, 0)` is
the point over the base point `x` of `z` with fibre coordinate `L w` in `e`, where `w` is the
fibre coordinate of `z` in `e`. Since the left side does not mention `e`, the right side is the
same for every such trivialization. -/
theorem vectorBundleRescaledFamily_zero_eq [T2Space B] (e : Trivialization F (π F V))
    [e.IsLinear ℝ] {ψ : U → TotalSpace F V} {z : TotalSpace F V} (hz : z.proj ∈ e.baseSet)
    (h0 : zeroSection F V z.proj ∈ U) (hψ0 : ψ ⟨_, h0⟩ = zeroSection F V z.proj)
    (hψ : ContinuousAt ψ ⟨_, h0⟩) {g : F → F} {L : F →L[ℝ] F} (hg : HasFDerivAt g L 0)
    (hgψ : ∀ᶠ w in 𝓝 0, ∀ hw : (⟨z.proj, e.symm z.proj w⟩ : TotalSpace F V) ∈ U,
      (e (ψ ⟨_, hw⟩)).2 = g w) :
    vectorBundleRescaledFamily ψ (z, 0) = ⟨z.proj, e.symm z.proj (L (e z).2)⟩ :=
  vectorBundleRescaledFamily_zero_of_tendsto
    (tendsto_vectorBundleRescaledFamily_zero e hz h0 hψ0 hψ hg hgψ)

end Trivialization

section Manifold

variable {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [∀ b, TopologicalSpace (V b)] [FiberBundle F V]
  [VectorBundle ℝ F V]

/-- For `t > 0`, the rescaled family is `m_{1/t} ∘ ψ ∘ m_t`, with the fibre scaling `m_t` of
`TauCeti.vectorBundleFiberScaling` and the dilation `m_{1/t}` of
`TauCeti.vectorBundleScalarDiffeomorph`. -/
theorem vectorBundleRescaledFamily_of_pos (ψ : U → TotalSpace F V) {t : Icc (0 : ℝ) 1}
    (ht : 0 < (t : ℝ)) (z : TotalSpace F V) (hz : vectorBundleFiberScaling F V (z, t) ∈ U) :
    vectorBundleRescaledFamily ψ (z, t) =
      vectorBundleScalarDiffeomorph (I := IB) (n := ∞) (fun _ ↦ (t : ℝ)⁻¹) contMDiff_const
        (fun _ ↦ inv_ne_zero ht.ne') (ψ ⟨_, hz⟩) := by
  rw [vectorBundleRescaledFamily_of_ne_zero ψ ht.ne' z hz, vectorBundleScalarDiffeomorph_apply]

end Manifold

end SymplecticGeometry
