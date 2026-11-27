/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Sum.RationalEllipticSurface.Basic
import Mathlib.Analysis.Convex.Contractible
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.Prod.ComplDisc
import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.Lefschetz
import SymplecticGeometry.Geometry.Symplectic.Sum.RationalEllipticSurface.FibreNeighborhood
import TauCeti.AlgebraicTopology.NotSimplyConnected

/-!
# The complement of the fibre of `E(1)` is simply connected

This file proves that the complement of the fibre over `[1 : 0] ∈ ℂℙ¹` in the rational elliptic
surface, the complement of the image of the Fermat cubic under
`SymplecticGeometry.rationalEllipticSurface.fibreEmbedding`, is simply connected
(`SymplecticGeometry.rationalEllipticSurface.simplyConnectedSpace_compl_fibre`).

## Proof

Let `f : F × ball 0 ε → E(1)` be the product neighbourhood of the fibre given by
`SymplecticGeometry.rationalEllipticSurface.exists_isOpenEmbedding_prod_ball`, with `F` the
Fermat cubic, which is path connected
(`SymplecticGeometry.SmoothProjectiveHypersurface.pathConnectedSpace`). Since `E(1)` is simply
connected (`SymplecticGeometry.rationalEllipticSurface.simplyConnectedSpace`), removing the fibre
`f '' (F × {0})` leaves a simply connected space once a single meridian `t ↦ f (q, w t)`, with
`w t = z e^{2πit}`, is null-homotopic in the complement
(`FundamentalGroup.map_subtypeVal_compl_image_bijective`).

Fix the point `P = [0 : 1 : -1]` of the base locus of the pencil. The line `{P} × ℂℙ¹` lies in
`E(1)` and crosses the fibre only at `(P, [1 : 0])`. For `w` in a small disc around `0`, the point
`(P, [1 : w])` lies in the range of `f`, and since `f` keeps the affine coordinate it is
`f (g w, w)` for a continuous `g`. Contracting the loop `w` inside the disc, which is simply
connected, gives a homotopy from the meridian at `q = g z` to the loop `t ↦ f (g (w t), w t)`,
that is `t ↦ (P, [1 : w t]) = (P, [1 / w t : 1])`, all in the complement of the fibre. The last
loop is the image of a loop in `ℂ` under `u ↦ (P, [u : 1])`, so it is null-homotopic there.

## References

* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995].
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.2.
-/

public section

open Set Metric Topology Projectivization
open scoped LinearAlgebra.Projectivization

namespace SymplecticGeometry.rationalEllipticSurface

/-- Some meridian of the fibre in a product neighbourhood `f` adapted to the affine coordinate is
null-homotopic in the complement of the fibre. -/
private theorem exists_meridian_eq_one {ε : ℝ} (hε : 0 < ε)
    {f : SmoothProjectiveHypersurface.fermat 1 3 × ball (0 : ℂ) ε → rationalEllipticSurface}
    (hf : IsOpenEmbedding f) (hf0 : ∀ x, f (x, ⟨0, mem_ball_self hε⟩) = fibreEmbedding x)
    (haff : ∀ p, affineCoordinate (f p) = p.2)
    (hZ : f '' {p | (p.2 : ℂ) = 0} = range fibreEmbedding) :
    ∃ q z, hf.meridian q z = 1 := by
  set P := Projectivization.mk ℂ ![(0 : ℂ), 1, -1] (fun h ↦ one_ne_zero (congrFun h 1))
  have hP : P ∈ baseLocus := by
    rw [mk_mem_baseLocus_iff]
    norm_num
  -- The line `{P} × ℂℙ¹`, through the points `[1 : w]`.
  set s : ℂ → rationalEllipticSurface := fun w ↦
    ⟨(P, Projectivization.mk ℂ ![1, w] fun h ↦ one_ne_zero (congrFun h 0)),
      mk_mem_of_mem_baseLocus hP _⟩
  have hs : Continuous s :=
    (continuous_const.prodMk (continuous_mk (by fun_prop) _)).subtype_mk _
  have haffs (w : ℂ) : affineCoordinate (s w) = w := by
    rw [affineCoordinate_mk_snd _ rfl]
    simp
  -- Near `w = 0` the line runs through the range of `f`.
  have hs0 : s 0 ∈ range f := by
    obtain ⟨x, hx⟩ : s 0 ∈ range fibreEmbedding := by
      rw [range_fibreEmbedding]
      rfl
    exact ⟨_, (hf0 x).trans hx⟩
  obtain ⟨δ', hδ', hδ's⟩ := Metric.isOpen_iff.1 (hf.isOpen_range.preimage hs) 0 hs0
  set δ := min δ' ε
  have hδ : 0 < δ := lt_min hδ' hε
  have hδε : ball (0 : ℂ) δ ⊆ ball 0 ε := ball_subset_ball (min_le_right _ _)
  have hsδ (w : ball (0 : ℂ) δ) : s w ∈ range f :=
    hδ's (ball_subset_ball (min_le_left _ _) w.property)
  set e := hf.isEmbedding.toHomeomorph
  set k : ball (0 : ℂ) δ → SmoothProjectiveHypersurface.fermat 1 3 × ball (0 : ℂ) ε :=
    fun w ↦ e.symm ⟨s w, hsδ w⟩
  have hk : Continuous k :=
    e.symm.continuous.comp ((hs.comp continuous_subtypeVal).subtype_mk _)
  have hfk (w : ball (0 : ℂ) δ) : f (k w) = s w :=
    congrArg Subtype.val (e.apply_symm_apply ⟨s w, hsδ w⟩)
  have hk2 (w : ball (0 : ℂ) δ) : ((k w).2 : ℂ) = w := by
    rw [← haff, hfk, haffs]
  -- A loop around `0` in the small disc.
  have hz₀ : ((δ / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) δ \ {0} := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    · simpa using hδ.ne'
  set z₀ : ↥(ball (0 : ℂ) δ \ {0}) := ⟨_, hz₀⟩
  set ℓ := Complex.loopAround 0 z₀
  set i : C(↥(ball (0 : ℂ) δ \ {0}), ball (0 : ℂ) δ) :=
    ⟨inclusion sdiff_subset, continuous_inclusion _⟩
  set j : C(↥(ball (0 : ℂ) δ \ {0}), ↥(ball (0 : ℂ) ε \ {0})) :=
    ⟨inclusion (sdiff_subset_sdiff_left hδε), continuous_inclusion _⟩
  refine ⟨(k (i z₀)).1, j z₀, ?_⟩
  -- The meridian is the loop `t ↦ f (q, ℓ t)`.
  have hA : Complex.loopAround 0 (j z₀) = ℓ.map j.continuous :=
    Path.ext (funext fun t ↦ Subtype.ext (by simp [ℓ, j]))
  -- The line through `[u : 1]`, in the complement of the fibre.
  have hHmem (u : ℂ) : (⟨(P, Projectivization.mk ℂ ![u, 1] fun h ↦ one_ne_zero (congrFun h 1)),
      mk_mem_of_mem_baseLocus hP _⟩ : rationalEllipticSurface) ∉ f '' {p | (p.2 : ℂ) = 0} := by
    rw [hZ, range_fibreEmbedding, mem_ofPred_eq]
    intro h
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).1 h.symm
    have h0 := congrFun ha 0
    have h1 := congrFun ha 1
    simp at h0 h1
    simp [h1] at h0
  set H : ℂ → ↥(f '' {p | (p.2 : ℂ) = 0})ᶜ := fun u ↦ ⟨_, hHmem u⟩
  have hH : Continuous H :=
    ((continuous_const.prodMk (continuous_mk (by fun_prop) _)).subtype_mk _).subtype_mk _
  have hinv : Continuous fun w : ↥(ball (0 : ℂ) δ \ {0}) ↦ (w : ℂ)⁻¹ :=
    continuous_subtypeVal.inv₀ fun w ↦ w.property.2
  have hK1 : Continuous fun w ↦ (k w).1 := continuous_fst.comp hk
  have := (convex_ball (0 : ℂ) δ).contractibleSpace ⟨0, mem_ball_self hδ⟩
  -- Contract the first coordinate inside the disc.
  have hB : (((Path.refl (k (i z₀)).1).prod (ℓ.map j.continuous)).map
      hf.restrictPuncturedBall.continuous).Homotopic
      ((((ℓ.map i.continuous).map hK1).prod (ℓ.map j.continuous)).map
        hf.restrictPuncturedBall.continuous) :=
    Path.Homotopic.map ⟨Path.Homotopic.prodHomotopy
      ((SimplyConnectedSpace.paths_homotopic (Path.refl _) (ℓ.map i.continuous)).map
        ⟨_, hK1⟩).some (Path.Homotopy.refl _)⟩ _
  -- The loop `t ↦ f (g (ℓ t), ℓ t)` is the loop `t ↦ (P, [1 / ℓ t : 1])`, null-homotopic.
  have hC : ((ℓ.map hinv).map hH).Homotopic (Path.refl _) :=
    (SimplyConnectedSpace.paths_homotopic (ℓ.map hinv) (Path.refl _)).map ⟨H, hH⟩
  have hcast : ∀ {x y : ↥(f '' {p | (p.2 : ℂ) = 0})ᶜ} (γ : Path x x) (γ' : Path y y),
      (∀ t, γ t = γ' t) → γ'.Homotopic (Path.refl y) → γ.Homotopic (Path.refl x) := by
    intro x y γ γ' h h'
    obtain rfl : x = y := by simpa using h 0
    obtain rfl : γ = γ' := Path.ext (funext h)
    exact h'
  have hD : ((((ℓ.map i.continuous).map hK1).prod (ℓ.map j.continuous)).map
      hf.restrictPuncturedBall.continuous).Homotopic (Path.refl _) := by
    refine hcast _ _ (fun t ↦ Subtype.ext ?_) hC
    simp only [Path.map_coe, Function.comp_apply, Path.prod_coe,
      Topology.IsOpenEmbedding.coe_restrictPuncturedBall_apply]
    refine Eq.trans (congrArg f (?_ : _ = k (i (ℓ t)))) ?_
    · exact Prod.ext rfl (Subtype.ext (hk2 (i (ℓ t))).symm)
    rw [hfk]
    refine Subtype.ext (Prod.ext rfl ?_)
    have hw : ((ℓ t : ℂ)) ≠ 0 := (ℓ t).property.2
    refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨ℓ t, funext fun m ↦ ?_⟩
    fin_cases m <;> simp [i, hw]
  rw [Topology.IsOpenEmbedding.meridian_def, Topology.IsOpenEmbedding.meridianLoop_def, hA]
  exact congrArg FundamentalGroup.fromPath (Quotient.sound (hB.trans hD))

/-- **The complement of the fibre of `E(1)` is simply connected.** The complement in the rational
elliptic surface of its fibre over `[1 : 0] ∈ ℂℙ¹`, the image of the Fermat cubic under
`fibreEmbedding`, is simply connected. -/
instance simplyConnectedSpace_compl_range_fibreEmbedding :
    SimplyConnectedSpace ↥(range fibreEmbedding)ᶜ := by
  obtain ⟨ε, hε, f, hf, hf0, haff⟩ := exists_isOpenEmbedding_prod_ball
  have := (SmoothProjectiveHypersurface.fermat 1 3).pathConnectedSpace (by norm_num) one_ne_zero
  have := ChartedSpace.locallyPathConnectedSpace (Fin 2 → ℂ) rationalEllipticSurface
  have hZ : f '' {p | (p.2 : ℂ) = 0} = range fibreEmbedding := by
    refine Set.ext fun y ↦ ⟨?_, ?_⟩
    · rintro ⟨⟨x, w⟩, hw, rfl⟩
      obtain rfl : w = ⟨0, mem_ball_self hε⟩ := Subtype.ext hw
      exact ⟨x, (hf0 x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl, hf0 x⟩
  obtain ⟨q, z, hqz⟩ := exists_meridian_eq_one hε hf hf0 (fun p ↦ (haff p).1) hZ
  have hZc : IsClosed (f '' {p | (p.2 : ℂ) = 0}) := by
    rw [hZ, range_fibreEmbedding]
    exact isClosed_eq (continuous_snd.comp continuous_subtypeVal) continuous_const
  have : PathConnectedSpace ↥(f '' {p | (p.2 : ℂ) = 0})ᶜ :=
    isPathConnected_iff_pathConnectedSpace.1 (hf.isPathConnected_compl_image hZc hε)
  have : Subsingleton (FundamentalGroup ↥(f '' {p | (p.2 : ℂ) = 0})ᶜ
      (hf.restrictPuncturedBall (q, z))) :=
    (FundamentalGroup.map_subtypeVal_compl_image_bijective hf hZc q z hqz).1.subsingleton
  rw [← hZ]
  exact TauCeti.simplyConnectedSpace_iff_forall_subsingleton_fundamentalGroup.2
    ⟨inferInstance, fun y ↦
      (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected y
        (hf.restrictPuncturedBall (q, z))).injective.subsingleton⟩

/-- **The complement of the fibre of `E(1)` is simply connected.** The complement in the rational
elliptic surface of the set of points over `[1 : 0] ∈ ℂℙ¹` is simply connected. This is
`simplyConnectedSpace_compl_range_fibreEmbedding`, through `range_fibreEmbedding`. -/
instance simplyConnectedSpace_compl_fibre :
    SimplyConnectedSpace ↥{p : rationalEllipticSurface |
      (p : ℙ ℂ (Fin 3 → ℂ) × ℙ ℂ (Fin 2 → ℂ)).2 =
        Projectivization.mk ℂ ![(1 : ℂ), 0] (by simp)}ᶜ :=
  range_fibreEmbedding ▸ simplyConnectedSpace_compl_range_fibreEmbedding

end SymplecticGeometry.rationalEllipticSurface

end
