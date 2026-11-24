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
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import SymplecticGeometry.Analysis.Calculus.FiberRescale
import TauCeti.Geometry.Manifold.VectorBundle.Submersion
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

section Smooth

variable {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [∀ b, TopologicalSpace (V b)] [FiberBundle F V]
  [VectorBundle ℝ F V]

/-- Away from `t = 0` the rescaled family is smooth, as a fibrewise rescaling of `ψ ∘ m_t`. -/
private theorem contMDiffWithinAt_vectorBundleRescaledFamily_of_ne_zero
    {U' : Set (TotalSpace F V)} (hU' : U' ⊆ U)
    (hstar : ∀ z ∈ U', ∀ t, vectorBundleFiberScaling F V (z, t) ∈ U')
    (ψ : U → TotalSpace F V)
    {ψ' : TotalSpace F V → TotalSpace F V}
    (hψ' : ContMDiffOn (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) ∞ ψ' U)
    (hψψ' : ∀ z (hz : z ∈ U), ψ' z = ψ ⟨z, hz⟩)
    {z₀ : TotalSpace F V} (hz₀ : z₀ ∈ U') {t₀ : Icc (0 : ℝ) 1} (ht₀ : (t₀ : ℝ) ≠ 0) :
    ContMDiffWithinAt ((IB.prod 𝓘(ℝ, F)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, F)) ∞
      (vectorBundleRescaledFamily ψ) (U' ×ˢ univ) (z₀, t₀) := by
  have hm : ContMDiffAt ((IB.prod 𝓘(ℝ, F)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, F)) ∞
      (fun p ↦ ψ' (vectorBundleFiberScaling F V p)) (z₀, t₀) :=
    (hψ'.contMDiffAt (U.isOpen.mem_nhds (hU' (hstar z₀ hz₀ t₀)))).comp
      _ contMDiff_vectorBundleFiberScaling.contMDiffAt
  have ha : ContMDiffAt ((IB.prod 𝓘(ℝ, F)).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : TotalSpace F V × Icc (0 : ℝ) 1 ↦ ((p.2 : ℝ))⁻¹) (z₀, t₀) :=
    (contMDiff_subtypeVal_Icc.comp contMDiff_snd).contMDiffAt.inv₀ ht₀
  have heq : ∀ p : TotalSpace F V × Icc (0 : ℝ) 1, p.1 ∈ U' → (p.2 : ℝ) ≠ 0 →
      vectorBundleRescaledFamily ψ p = ⟨(ψ' (vectorBundleFiberScaling F V p)).proj,
        ((p.2 : ℝ))⁻¹ • (ψ' (vectorBundleFiberScaling F V p)).snd⟩ := by
    rintro ⟨z, t⟩ hz ht
    rw [vectorBundleRescaledFamily_of_ne_zero ψ ht z (hU' (hstar z hz t)),
      hψψ' _ (hU' (hstar z hz t))]
  refine (ha.smul_totalSpace hm).contMDiffWithinAt.congr_of_eventuallyEq ?_ (heq _ hz₀ ht₀)
  have hne : ∀ᶠ p in 𝓝 (z₀, t₀), ((p.2 : Icc (0 : ℝ) 1) : ℝ) ≠ 0 :=
    (continuous_subtypeVal.comp continuous_snd).continuousAt.eventually_ne ht₀
  filter_upwards [nhdsWithin_le_nhds hne, self_mem_nhdsWithin] with p hp hpU
  exact heq p hpU.1 hp

/-- Near `t = 0` the rescaled family is smooth: read in the preferred chart at `z₀`, it is the
rescaling `fiberRescale` of the fibre coordinate of `ψ`. -/
private theorem contMDiffWithinAt_vectorBundleRescaledFamily_zero [IsManifold IB ∞ B]
    [ContMDiffVectorBundle ∞ F V IB] [IB.Boundaryless]
    [CompleteSpace F] [T2Space B] {U' : Set (TotalSpace F V)} (hU' : U' ⊆ U)
    (hstar : ∀ z ∈ U', ∀ t, vectorBundleFiberScaling F V (z, t) ∈ U')
    {ψ : U → TotalSpace F V} (hψ : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) ∞ ψ)
    (hψ0 : ∀ x (hx : zeroSection F V x ∈ U), ψ ⟨_, hx⟩ = zeroSection F V x)
    {ψ' : TotalSpace F V → TotalSpace F V}
    (hψ' : ContMDiffOn (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) ∞ ψ' U)
    (hψψ' : ∀ z (hz : z ∈ U), ψ' z = ψ ⟨z, hz⟩)
    {z₀ : TotalSpace F V} (hz₀ : z₀ ∈ U') :
    ContMDiffWithinAt ((IB.prod 𝓘(ℝ, F)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, F)) ∞
      (vectorBundleRescaledFamily ψ) (U' ×ˢ univ) (z₀, 0) := by
  set e := trivializationAt F V z₀.proj
  set Φ := extChartAt (IB.prod 𝓘(ℝ, F)) z₀ with hΦ
  set φ := extChartAt IB z₀.proj with hφ
  have h0 : ∀ z ∈ U', zeroSection F V z.proj ∈ U := fun z hz ↦ by
    have := hU' (hstar z hz 0)
    rwa [vectorBundleFiberScaling_zero] at this
  have hψ'0 : ∀ z ∈ U', ψ' (zeroSection F V z.proj) = zeroSection F V z.proj := fun z hz ↦ by
    rw [hψψ' _ (h0 z hz), hψ0]
  -- the fibre coordinate of `ψ` in the chart, and the open set where it is smooth
  set W : Set (EB × F) := Φ.target ∩ Φ.symm ⁻¹' (U ∩ ψ' ⁻¹' e.source)
  have hW : IsOpen W := (contMDiffOn_extChartAt_symm (n := ∞) z₀).continuousOn.isOpen_inter_preimage
    (isOpen_extChartAt_target z₀) (hψ'.continuousOn.isOpen_inter_preimage U.isOpen e.open_source)
  set g : EB × F → F := fun y ↦ (e (ψ' (Φ.symm y))).2 with hg_def
  have hg : ContDiffOn ℝ ∞ g W := by
    refine ContMDiffOn.contDiffOn fun y hy ↦ ?_
    have : ContMDiffAt 𝓘(ℝ, EB × F) (IB.prod 𝓘(ℝ, F)) ∞ (fun y ↦ ψ' (Φ.symm y)) y :=
      (hψ'.contMDiffAt (U.isOpen.mem_nhds hy.2.1)).comp y
        ((contMDiffOn_extChartAt_symm (n := ∞) z₀).contMDiffAt
          ((isOpen_extChartAt_target z₀).mem_nhds hy.1))
    exact ((e.contMDiffAt_iff (f := fun y ↦ ψ' (Φ.symm y)) hy.2.2).1 this).2.contMDiffWithinAt
  -- points of the zero section in the chart
  have hsymm : ∀ {x : B}, x ∈ e.baseSet → x ∈ (chartAt HB z₀.proj).source → ∀ w,
      Φ.symm (φ x, w) = ⟨x, e.symm x w⟩ := fun hxb hxs w ↦
    Bundle.extChartAt_symm_apply_extChartAt_of_mem_baseSet z₀ hxb (by simpa using hxs) w
  have hsymm0 : ∀ {x : B}, x ∈ e.baseSet → e.symm x 0 = 0 := fun hxb ↦ by
    simp [← Trivialization.symmₗ_apply (R := ℝ) _ hxb]
  have hW0 : ∀ z ∈ U', z.proj ∈ e.baseSet → z.proj ∈ (chartAt HB z₀.proj).source →
      (φ z.proj, (0 : F)) ∈ W := by
    intro z hz hxb hxs
    have hmem : (φ z.proj, (0 : F)) ∈ Φ.target := by
      rw [hΦ, FiberBundle.extChartAt_target]
      refine ⟨⟨(extChartAt IB z₀.proj).map_source (by simpa using hxs), ?_⟩, mem_univ _⟩
      rwa [mem_preimage, (extChartAt IB z₀.proj).left_inv (by simpa using hxs)]
    have hz0 : Φ.symm (φ z.proj, 0) = zeroSection F V z.proj := by
      rw [hsymm hxb hxs, hsymm0 hxb]
      rfl
    refine ⟨hmem, ?_, ?_⟩
    · rw [hz0]
      exact h0 z hz
    · rw [hz0, mem_preimage, hψ'0 z hz, e.mem_source]
      exact hxb
  have hg0 : ∀ p, (p, (0 : F)) ∈ W → g (p, 0) = 0 := by
    intro p hp
    have hp' := hp.1
    rw [hΦ, FiberBundle.extChartAt_target] at hp'
    have hb : φ.symm p ∈ e.baseSet := hp'.1.2
    have hz0 : Φ.symm (p, 0) = zeroSection F V (φ.symm p) := by
      rw [hΦ, Bundle.extChartAt_symm_apply_of_mem_baseSet z₀ hb, ← hφ, hsymm0 hb]
      rfl
    have hU0 : zeroSection F V (φ.symm p) ∈ U := hz0 ▸ hp.2.1
    simp only [hg_def, hz0, hψψ' _ hU0, hψ0, e.zeroSection ℝ hb]
  -- the value at `t = 0`
  have hval : ∀ z ∈ U', z.proj ∈ e.baseSet → z.proj ∈ (chartAt HB z₀.proj).source →
      vectorBundleRescaledFamily ψ (z, 0) =
        ⟨z.proj, e.symm z.proj (fderiv ℝ (fun w ↦ g (φ z.proj, w)) 0 (e z).2)⟩ := by
    intro z hz hxb hxs
    have hdiff : DifferentiableAt ℝ (fun w ↦ g (φ z.proj, w)) 0 :=
      ((hg.differentiableOn (by simp)).differentiableAt
        (hW.mem_nhds (hW0 z hz hxb hxs))).comp (0 : F) (by fun_prop)
    refine vectorBundleRescaledFamily_zero_eq e hxb (h0 z hz) (hψ0 _ (h0 z hz))
      (hψ.continuous.continuousAt) hdiff.hasFDerivAt (Eventually.of_forall fun w hw ↦ ?_)
    simp only [hg_def, hsymm hxb hxs, hψψ' _ hw]
  -- the family near `(z₀, 0)`, read in the chart
  have hfst : ∀ z : TotalSpace F V, z.proj ∈ e.baseSet → Φ z = (φ z.proj, (e z).2) :=
    fun z hxb ↦ Bundle.extChartAt_apply_of_mem_baseSet z₀ hxb
  have hbaseEq : ∀ z ∈ U', z.proj ∈ e.baseSet → z.proj ∈ (chartAt HB z₀.proj).source →
      ∀ t : Icc (0 : ℝ) 1, (vectorBundleRescaledFamily ψ (z, t)).proj =
        (ψ' (vectorBundleFiberScaling F V (z, t))).proj := by
    intro z hz hxb hxs t
    rcases eq_or_ne (t : ℝ) 0 with ht | ht
    · obtain rfl : t = 0 := Subtype.ext ht
      rw [hval z hz hxb hxs, vectorBundleFiberScaling_zero, hψ'0 z hz]
      rfl
    · rw [vectorBundleRescaledFamily_of_ne_zero ψ ht z (hU' (hstar z hz t)),
        hψψ' _ (hU' (hstar z hz t))]
  have hfibEq : ∀ z ∈ U', z.proj ∈ e.baseSet → z.proj ∈ (chartAt HB z₀.proj).source →
      ∀ t : Icc (0 : ℝ) 1, (ψ' (vectorBundleFiberScaling F V (z, t))).proj ∈ e.baseSet →
      (e (vectorBundleRescaledFamily ψ (z, t))).2 = fiberRescale g (Φ z, (t : ℝ)) := by
    intro z hz hxb hxs t hb
    rw [hfst z hxb]
    rcases eq_or_ne (t : ℝ) 0 with ht | ht
    · obtain rfl : t = 0 := Subtype.ext ht
      rw [hval z hz hxb hxs, e.apply_mk_symm hxb]
      simp
    · have hzt := hU' (hstar z hz t)
      rw [vectorBundleRescaledFamily_of_ne_zero ψ ht z hzt, fiberRescale_of_ne_zero g ht]
      simp only [hg_def]
      rw [hsymm hxb hxs, ← vectorBundleFiberScaling_eq_trivialization_symm e hxb t, hψψ' _ hzt]
      rw [hψψ' _ hzt] at hb
      exact (e.linear ℝ hb).map_smul _ _
  have hb₀ : z₀.proj ∈ e.baseSet := mem_baseSet_trivializationAt F V z₀.proj
  have hs₀ : z₀.proj ∈ (chartAt HB z₀.proj).source := mem_chart_source HB z₀.proj
  have hm : ContMDiffAt ((IB.prod 𝓘(ℝ, F)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, F)) ∞
      (fun p ↦ ψ' (vectorBundleFiberScaling F V p)) (z₀, 0) :=
    (hψ'.contMDiffAt (U.isOpen.mem_nhds (hU' (hstar z₀ hz₀ 0)))).comp _
      contMDiff_vectorBundleFiberScaling.contMDiffAt
  have hproj₀ : (ψ' (vectorBundleFiberScaling F V (z₀, 0))).proj = z₀.proj := by
    rw [vectorBundleFiberScaling_zero, hψ'0 z₀ hz₀]
    rfl
  have hN : ∀ᶠ p in 𝓝[U' ×ˢ univ] (z₀, 0), p.1 ∈ U' ∧ p.1.proj ∈ e.baseSet ∧
      p.1.proj ∈ (chartAt HB z₀.proj).source ∧
      (ψ' (vectorBundleFiberScaling F V p)).proj ∈ e.baseSet := by
    have h1 : ∀ᶠ p : TotalSpace F V × Icc (0 : ℝ) 1 in 𝓝 (z₀, 0),
        p.1.proj ∈ e.baseSet ∩ (chartAt HB z₀.proj).source :=
      ((FiberBundle.continuous_proj F V).comp continuous_fst).continuousAt.preimage_mem_nhds
        ((e.open_baseSet.inter (chartAt HB z₀.proj).open_source).mem_nhds ⟨hb₀, hs₀⟩)
    have h2 : ∀ᶠ p in 𝓝 (z₀, 0), (ψ' (vectorBundleFiberScaling F V p)).proj ∈ e.baseSet :=
      ((FiberBundle.continuous_proj F V).continuousAt.comp hm.continuousAt).preimage_mem_nhds
        (by rw [Function.comp_apply, hproj₀]; exact e.open_baseSet.mem_nhds hb₀)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2]
      with p hp h1 h2
    exact ⟨hp.1, h1.1, h1.2, h2⟩
  have hval₀ : (vectorBundleRescaledFamily ψ (z₀, 0)).proj = z₀.proj := by
    rw [hval z₀ hz₀ hb₀ hs₀]
  rw [contMDiffWithinAt_totalSpace_iff, hval₀]
  constructor
  · refine ((contMDiff_proj (E := V) (IB := IB) (F := F) (n := ∞)).contMDiffAt.comp _
      hm).contMDiffWithinAt.congr_of_eventuallyEq ?_ (hbaseEq z₀ hz₀ hb₀ hs₀ 0)
    filter_upwards [hN] with p hp
    exact hbaseEq p.1 hp.1 hp.2.1 hp.2.2.1 p.2
  · set S : Set ((EB × F) × ℝ) := {q | ∀ s : unitInterval, (q.1.1, (s : ℝ) • q.2 • q.1.2) ∈ W}
      with hS_def
    have hS : IsOpen S := by
      have : S = (fun q : (EB × F) × ℝ ↦ (q.2, q.1)) ⁻¹' TauCeti.normalSegmentDomain W := by
        ext q
        simp [hS_def, Subtype.forall, unitInterval]
      rw [this]
      exact (TauCeti.isOpen_normalSegmentDomain hW).preimage (by fun_prop)
    have hfr : ContDiffOn ℝ ∞ (fiberRescale g) S :=
      contDiffOn_fiberRescale (n := ⊤) hW (by simpa using hg) hg0
    have hκ : ContMDiffAt ((IB.prod 𝓘(ℝ, F)).prod (𝓡∂ 1)) 𝓘(ℝ, (EB × F) × ℝ) ∞
        (fun p : TotalSpace F V × Icc (0 : ℝ) 1 ↦ (Φ p.1, (p.2 : ℝ))) (z₀, 0) :=
      ((contMDiffAt_extChartAt (I := IB.prod 𝓘(ℝ, F)) (x := z₀) (n := ∞)).comp
        (z₀, (0 : Icc (0 : ℝ) 1)) contMDiffAt_fst).prodMk_space
        (contMDiff_subtypeVal_Icc.comp contMDiff_snd).contMDiffAt
    have hκS : (Φ z₀, ((0 : Icc (0 : ℝ) 1) : ℝ)) ∈ S := by
      intro s
      simpa [hfst z₀ hb₀] using hW0 z₀ hz₀ hb₀ hs₀
    have hfib : ContMDiffAt ((IB.prod 𝓘(ℝ, F)).prod (𝓡∂ 1)) 𝓘(ℝ, F) ∞
        (fun p : TotalSpace F V × Icc (0 : ℝ) 1 ↦ fiberRescale g (Φ p.1, (p.2 : ℝ))) (z₀, 0) :=
      (hfr.contDiffAt (hS.mem_nhds hκS)).contMDiffAt.comp (z₀, 0) hκ
    refine hfib.contMDiffWithinAt.congr_of_eventuallyEq ?_
      (hfibEq z₀ hz₀ hb₀ hs₀ 0 (by rw [hproj₀]; exact hb₀))
    filter_upwards [hN] with p hp
    exact hfibEq p.1 hp.1 hp.2.1 hp.2.2.1 p.2 hp.2.2.2

/-- **Smoothness of the rescaled family.** Let `V → B` be a smooth real vector bundle with
complete model fibre over a manifold without boundary, `U` an open set of its total space and
`ψ : U → V` a smooth map that fixes each point of the zero section lying in `U`. If `U' ⊆ U` is
star-shaped in the fibres, that is `m_t z ∈ U'` for `z ∈ U'` and `t ∈ [0, 1]`, then the rescaled
family of `ψ` is smooth on `U' × [0, 1]`, including at `t = 0`. -/
theorem contMDiffOn_vectorBundleRescaledFamily [IsManifold IB ∞ B]
    [ContMDiffVectorBundle ∞ F V IB] [IB.Boundaryless] [CompleteSpace F] [T2Space B]
    {U' : Set (TotalSpace F V)} (hU' : U' ⊆ U)
    (hstar : ∀ z ∈ U', ∀ t, vectorBundleFiberScaling F V (z, t) ∈ U')
    {ψ : U → TotalSpace F V} (hψ : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) ∞ ψ)
    (hψ0 : ∀ x (hx : zeroSection F V x ∈ U), ψ ⟨_, hx⟩ = zeroSection F V x) :
    ContMDiffOn ((IB.prod 𝓘(ℝ, F)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, F)) ∞
      (vectorBundleRescaledFamily ψ) (U' ×ˢ univ) := by
  classical
  -- `ψ`, extended by the identity outside `U`
  set ψ' : TotalSpace F V → TotalSpace F V := fun z ↦ if h : z ∈ U then ψ ⟨z, h⟩ else z
  have hψψ' : ∀ z (hz : z ∈ U), ψ' z = ψ ⟨z, hz⟩ := fun z hz ↦ by simp [ψ', hz]
  have hψ' : ContMDiffOn (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) ∞ ψ' U := fun z hz ↦
    (contMDiffAt_subtype_iff (x := ⟨z, hz⟩).1 ((hψ ⟨z, hz⟩).congr_of_eventuallyEq
      (Eventually.of_forall fun y ↦ hψψ' y y.property))).contMDiffWithinAt
  rintro ⟨z, t⟩ ⟨hz, -⟩
  rcases eq_or_ne (t : ℝ) 0 with ht | ht
  · obtain rfl : t = 0 := Subtype.ext ht
    exact contMDiffWithinAt_vectorBundleRescaledFamily_zero hU' hstar hψ hψ0 hψ' hψψ' hz
  · exact contMDiffWithinAt_vectorBundleRescaledFamily_of_ne_zero hU' hstar ψ hψ' hψψ' hz ht

end Smooth

end SymplecticGeometry
