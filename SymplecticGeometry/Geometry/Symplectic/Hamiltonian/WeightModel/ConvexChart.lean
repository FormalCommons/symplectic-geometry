/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Convex.LocalToGlobal
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Basic
import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Convexity

/-!
# Convexity charts of the weight model times a linear projection

Let `μ = TauCeti.weightMomentMap α` be the moment map of the weight model on `ℂ^ι`, for weights
`α : ι → 𝔨*`. Near a point with a nontrivial stabilizer, a moment map of a torus action takes, in
suitable coordinates `(u, w, z)`, the product form `(u, w, z) ↦ (μ z, u)`: the coordinates `u`
along the orbit are sent linearly onto a complement, the coordinates `w` are invisible, and the
coordinates `z` see the weight model of the stabilizer. This file shows that such a map, which has
no moment map in it, has convexity charts in the sense of `TauCeti.IsConvexChart` around every
point of a product `A ×ˢ B ×ˢ {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r}`, with `A` open and `B` open and
preconnected.

On such a product the map is open onto the convex set `range μ ×ˢ univ`, by
`TauCeti.image_mem_nhdsWithin_range_weightMomentMap`, and its fibres are products of a point (or
nothing), the set `B`, and a fibre of `μ` inside an invariant ball, preconnected by
`TauCeti.isPreconnected_preimage_weightMomentMap_inter`. Tau Ceti's
`TauCeti.exists_isConvexChart_inter_preimage_ball` then gives the charts. Composition with a
continuous linear equivalence of the target is `TauCeti.IsConvexChart.continuousLinearEquiv_comp`.

## Main results

* `TauCeti.exists_isConvexChart_weightMomentMap_prod`: every point of the product above lies in a
  convexity chart `U ∩ f ⁻¹' ball (f p) ε` of `f (u, w, z) = (μ z, u)`.

## References

* [C. Bjorndahl and Y. Karshon, *Revisiting Tietze–Nakajima: local and global convexity for
  maps*][BjorndahlKarshon2010]
-/

public section

open Metric Set Topology

namespace TauCeti

variable {ι : Type*} [Fintype ι] {𝔨 Q W : Type*} [NormedAddCommGroup 𝔨] [NormedSpace ℝ 𝔨]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [TopologicalSpace W]

/-- **Convexity charts of the weight model times a linear projection.** Let
`f (u, w, z) = (weightMomentMap α z, u)` on `Q × W × ℂ^ι`, and let
`U = A ×ˢ B ×ˢ {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r}` with `A ⊆ Q` open and `B ⊆ W` open and
preconnected. Every point `p ∈ U` lies in a convexity chart `U ∩ f ⁻¹' ball (f p) ε` of `f`, for
some `ε > 0`. -/
theorem exists_isConvexChart_weightMomentMap_prod (α : ι → StrongDual ℝ 𝔨) {A : Set Q}
    (hA : IsOpen A) {B : Set W} (hB : IsOpen B) (hB' : IsPreconnected B) (r : ℝ)
    {p : Q × W × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)}
    (hp : p ∈ A ×ˢ B ×ˢ {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r}) :
    ∃ ε > 0, IsConvexChart (fun q ↦ (weightMomentMap α q.2.2, q.1))
      ((A ×ˢ B ×ˢ {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r}) ∩
        (fun q ↦ (weightMomentMap α q.2.2, q.1)) ⁻¹'
          ball (weightMomentMap α p.2.2, p.1) ε) := by
  set Z := {z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r}
  have hZ : IsOpen Z := isOpen_lt (by fun_prop) continuous_const
  have hcont : Continuous fun q : Q × W × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
      (weightMomentMap α q.2.2, q.1) :=
    ((continuous_weightMomentMap α).comp (continuous_snd.comp continuous_snd)).prodMk
      continuous_fst
  refine exists_isConvexChart_inter_preimage_ball hcont (hA.prod (hB.prod hZ))
    ((convex_range_weightMomentMap α).prod convex_univ)
    (by rintro _ ⟨q, -, rfl⟩; exact ⟨mem_range_self _, mem_univ _⟩) (fun V _ hV q hq ↦ ?_)
    (fun v ↦ ?_) hp
  · -- An open set contains a product of neighbourhoods, whose image is a neighbourhood.
    obtain ⟨Nu, hNu, Nwz, hNwz, hN⟩ := mem_nhds_prod_iff.1 (hV.mem_nhds hq)
    obtain ⟨Nw, hNw, Nz, hNz, hN'⟩ := mem_nhds_prod_iff.1 hNwz
    refine Filter.mem_of_superset (nhdsWithin_prod
      (image_mem_nhdsWithin_range_weightMomentMap α q.2.2 hNz)
      (nhdsWithin_le_nhds (s := univ) hNu)) ?_
    rintro ⟨_, u⟩ ⟨⟨z, hz, rfl⟩, hu⟩
    exact ⟨(u, q.2.1, z), hN ⟨hu, hN' ⟨mem_of_mem_nhds hNw, hz⟩⟩, rfl⟩
  · -- A fibre is a product of at most one point, `B`, and a fibre of the weight model in `Z`.
    have hfib : (A ×ˢ B ×ˢ Z) ∩ (fun q : Q × W × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
        (weightMomentMap α q.2.2, q.1)) ⁻¹' {v} =
        (A ∩ {v.2}) ×ˢ B ×ˢ (weightMomentMap α ⁻¹' {v.1} ∩ Z) := by
      ext ⟨u, w, z⟩
      simp only [mem_inter_iff, mem_prod, mem_preimage, mem_singleton_iff, Prod.ext_iff]
      tauto
    rw [hfib]
    exact (subsingleton_singleton.anti inter_subset_right).isPreconnected.prod
      (hB'.prod (isPreconnected_preimage_weightMomentMap_inter α (convex_singleton _) r))

end TauCeti

end
