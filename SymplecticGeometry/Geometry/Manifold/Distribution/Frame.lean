/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.VectorBundle

/-!
# Brackets of fields tangent to a distribution, from a local frame

Let `X` be a `C^n` local frame, with `1 ≤ n`, of a distribution `D` on a neighbourhood of a point
`x`. If the Lie brackets at `x` of the members of the frame lie in `D x`, then so does the bracket
at `x` of any two vector fields that are differentiable at `x` and tangent to `D` near `x`. This
is the local frame criterion for involutivity.

Near `x` such fields are combinations of the frame with coefficients differentiable at `x`
(`TauCeti.IsDistributionFrameOn.exists_mdifferentiableAt_coeff`), and Tau Ceti's
`TauCeti.mlieBracket_sum_smul_mem` computes the bracket of two such combinations at `x`.

## Main results

* `TauCeti.IsDistributionFrameOn.mlieBracket_mem_of_forall_mlieBracket_mem`: if the brackets of
  a local frame of `D` at `x` lie in `D x`, the bracket at `x` of two fields tangent to `D` near
  `x` lies in `D x`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 19.
-/

public section

open Filter VectorField
open scoped Manifold ContDiff Topology

namespace TauCeti

namespace IsDistributionFrameOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {n : ℕ∞ω} {D : Π x : M, Submodule 𝕜 (TangentSpace I x)} {ι : Type*} [Finite ι]
  {X : ι → Π y : M, TangentSpace I y} {U : Set M} {x : M}

/-- **Local frame criterion for involutivity, at a point.** Let `X` be a `C^n` local frame of `D`,
with `1 ≤ n`, on a neighbourhood of `x`, whose Lie brackets at `x` lie in `D x`. Then the Lie
bracket at `x` of two vector fields that are differentiable at `x` and tangent to `D` near `x`
lies in `D x`. -/
theorem mlieBracket_mem_of_forall_mlieBracket_mem (hX : IsDistributionFrameOn I n D X U)
    (hn : 1 ≤ n) (hU : U ∈ 𝓝 x) (hXX : ∀ i j, mlieBracket I (X i) (X j) x ∈ D x)
    {V W : Π y : M, TangentSpace I y} (hV : MDiffAt (T% V) x) (hW : MDiffAt (T% W) x)
    (hVD : ∀ᶠ y in 𝓝 x, V y ∈ D y) (hWD : ∀ᶠ y in 𝓝 x, W y ∈ D y) :
    mlieBracket I V W x ∈ D x := by
  let := Fintype.ofFinite ι
  obtain ⟨c, hc, hVc⟩ := hX.exists_mdifferentiableAt_coeff hn hU hV hVD
  obtain ⟨d, hd, hWd⟩ := hX.exists_mdifferentiableAt_coeff hn hU hW hWD
  have hV' : V =ᶠ[𝓝 x] ∑ i, c i • X i := hVc.mono fun y hy ↦
    hy.trans (Finset.sum_apply y Finset.univ fun i ↦ c i • X i).symm
  have hW' : W =ᶠ[𝓝 x] ∑ i, d i • X i := hWd.mono fun y hy ↦
    hy.trans (Finset.sum_apply y Finset.univ fun i ↦ d i • X i).symm
  rw [hV'.mlieBracket_vectorField_eq hW']
  exact mlieBracket_sum_smul_mem
    (fun i _ ↦ ((hX.contMDiffOn i).contMDiffAt hU).mdifferentiableAt (zero_lt_one.trans_le hn).ne')
    (fun i _ ↦ hX.isSubbundleFrameOn.apply_mem i (mem_of_mem_nhds hU)) (fun i _ j _ ↦ hXX i j)
    (fun i _ ↦ hc i) (fun i _ ↦ hd i)

end IsDistributionFrameOn

end TauCeti

end
