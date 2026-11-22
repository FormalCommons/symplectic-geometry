/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Geometry.Manifold.Boundary.Collar.Global
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Deformation

/-!
# The collar of a regular level set

Let `g : M → ℝ` be a smooth function on a compact boundaryless manifold, with `0` a regular value.
Then the level set `g⁻¹(0)` is collared in the sublevel set `{g ≤ 0}`: the inclusion
`g⁻¹(0) → {g ≤ 0}` is `TauCeti.IsCollared`, and the points of `{g ≤ 0}` off the level set are
those with `g < 0` (`SymplecticGeometry.isCollared_inclusion_levelSet`).

The proof builds no new flow. Since `0` is a regular value and `M` is compact, some band
`g⁻¹[-ε, 0]` with `ε > 0` has no critical point
(`TauCeti.exists_mem_Ioc_isCompact_forall_mfderiv_ne_zero`, applied to `-g`). Tau Ceti's
`TauCeti.exists_bandHomeomorph`, applied to `-g` on `[0, ε]`, identifies this band with
`g⁻¹(0) × [0, ε]`, with second coordinate `-g` and first coordinate the identity on the level.
The collar is `(y, t) ↦ e⁻¹ (y, ε t)` for `t ∈ [0, 1)`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.1 (the product structure of a band without critical points).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 9.25 (collars).
-/

public section

open Set TauCeti Topology
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [I.Boundaryless]
  [IsManifold I ∞ M] [CompactSpace M] {g : M → ℝ}

/-- **The collar of a regular level set.** On a compact boundaryless manifold, if `0` is a regular
value of the smooth function `g`, then the inclusion of the level set `g⁻¹(0)` into the sublevel
set `{g ≤ 0}` admits a collar, and the complement of its image is `{g < 0}`. -/
theorem isCollared_inclusion_levelSet (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (h0 : IsRegularValue I 𝓘(ℝ) g 0) :
    IsCollared (inclusion (preimage_mono (singleton_subset_iff.2 self_mem_Iic)) :
        g ⁻¹' {0} → g ⁻¹' Iic 0) ∧
      (range (inclusion (preimage_mono (singleton_subset_iff.2 self_mem_Iic)) :
        g ⁻¹' {0} → g ⁻¹' Iic 0))ᶜ = {x : g ⁻¹' Iic 0 | g x < 0} := by
  refine ⟨?_, ?_⟩
  swap
  · refine Set.ext fun x ↦ ?_
    simp only [range_inclusion, mem_compl_iff, mem_ofPred_eq]
    exact ⟨fun h ↦ x.property.out.lt_of_ne h, ne_of_lt⟩
  -- A band `(-g)⁻¹[0, ε]` without critical points, and its product structure.
  have hg' : ContMDiff I 𝓘(ℝ) ∞ (-g) := hg.neg
  obtain ⟨ε, ⟨hε, -⟩, hcpt, hreg⟩ := exists_mem_Ioc_isCompact_forall_mfderiv_ne_zero
    (hg'.of_le (by simp)) zero_lt_one (isClosed_Icc.preimage hg'.continuous).isCompact
    (by simpa using h0)
  obtain ⟨e, he₂, he₁⟩ := exists_bandHomeomorph hg' hcpt hreg
  have hlev : g ⁻¹' {0} ⊆ (-g) ⁻¹' {0} := fun x hx ↦ by simp_all
  have hband : (-g) ⁻¹' Icc 0 ε ⊆ g ⁻¹' Iic 0 := fun x hx ↦ by simpa using hx.1
  have hscale : MapsTo (ε * ·) (Ico (0 : ℝ) 1) (Icc 0 ε) := fun t ht ↦
    ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  -- The collar, `(y, t) ↦ e⁻¹ (y, ε t)`.
  let k : g ⁻¹' {0} × Ico (0 : ℝ) 1 → (-g) ⁻¹' {0} × Icc 0 ε :=
    Prod.map (inclusion hlev) (hscale.restrict _ _ _)
  have hk : IsEmbedding k := (IsEmbedding.inclusion hlev).prodMap
    ((Homeomorph.mulLeft₀ ε hε.ne').isEmbedding.restrict hscale)
  have hkp (p) : ((k p).2 : ℝ) = ε * p.2 := hscale.val_restrict_apply p.2
  refine IsCollar.isCollared (c := inclusion hband ∘ e.symm ∘ k)
    ⟨⟨(IsEmbedding.inclusion hband).comp (e.symm.isEmbedding.comp hk), ?_⟩, fun y ↦ ?_⟩
  · -- The image of the collar is `{-ε < g}` inside `{g ≤ 0}`.
    suffices h : range (inclusion hband ∘ e.symm ∘ k) = {x : g ⁻¹' Iic 0 | -ε < g x} from
      h ▸ isOpen_lt continuous_const (hg.continuous.comp continuous_subtypeVal)
    refine Set.ext fun x ↦ ?_
    simp only [mem_range, Function.comp_apply, mem_ofPred_eq]
    constructor
    · rintro ⟨p, rfl⟩
      have h := he₂ (e.symm (k p))
      rw [Homeomorph.apply_symm_apply, hkp] at h
      simp only [Pi.neg_apply] at h ⊢
      nlinarith [p.2.property.2]
    · intro hx
      have hx0 : g x ≤ 0 := x.property
      have hxb : (x : M) ∈ (-g) ⁻¹' Icc 0 ε := ⟨by simpa using hx0, by simp; linarith⟩
      have h2 : ((e ⟨x, hxb⟩).2 : ℝ) = -g x := he₂ _
      have hq1 : g (e ⟨x, hxb⟩).1 = 0 := neg_eq_zero.1 (e ⟨x, hxb⟩).1.property
      have hmem : ((e ⟨x, hxb⟩).2 : ℝ) / ε ∈ Ico (0 : ℝ) 1 := by
        rw [h2, mem_Ico, le_div_iff₀ hε, div_lt_one hε]
        constructor <;> linarith
      have hk : k (⟨(e ⟨x, hxb⟩).1, hq1⟩, ⟨_, hmem⟩) = e ⟨x, hxb⟩ :=
        Prod.ext (Subtype.ext (coe_inclusion hlev _)) (Subtype.ext (mul_div_cancel₀ _ hε.ne'))
      exact ⟨(⟨(e ⟨x, hxb⟩).1, hq1⟩, ⟨_, hmem⟩), Subtype.ext (by simp [hk])⟩
  · have hy0 : g y = 0 := y.property
    have hy : (y : M) ∈ (-g) ⁻¹' Icc 0 ε := by simp [hy0, hε.le]
    have hk : k (y, ⟨0, by norm_num⟩) = e ⟨y, hy⟩ :=
      Prod.ext (Subtype.ext (he₁ ⟨y, hy⟩ (by simp [hy0])).symm)
        (Subtype.ext ((hkp _).trans ((mul_zero ε).trans (by simp [he₂, hy0]))))
    ext
    simp only [Function.comp_apply, hk, Homeomorph.symm_apply_apply, coe_inclusion]

end SymplecticGeometry

end
