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
`g⁻¹(0) → {g ≤ 0}` is `TauCeti.IsCollared` (`SymplecticGeometry.isCollared_inclusion_levelSet`).

For a continuous `g`, `SymplecticGeometry.sublevelBoundary` is the complement in `{g ≤ 0}` of
the image of the open set `{g < 0}`. Its points are those with `g x = 0`
(`SymplecticGeometry.mem_sublevelBoundary_iff_eq_zero`), so it is the image of the level set
`g⁻¹(0)` (`SymplecticGeometry.sublevelBoundary_eq_range_inclusion`), and its points lie in
`{g ≥ 0}` (`SymplecticGeometry.mem_preimage_Ici_of_mem_sublevelBoundary`). When `0` is a regular
value, it is the boundary of `{g ≤ 0}` in the form that
`TauCeti.HomologicalOrientation.boundaryDegree` takes. The other data that the boundary degree
needs are named here too: on a compact `M` the sublevel set is compact
(`SymplecticGeometry.compactSpace_preimage_Iic`), the inclusion of `{g < 0}` into it is an open
embedding (`SymplecticGeometry.isOpenEmbedding_inclusion_preimage_Iio`), and its image is the
complement of the image of `g⁻¹(0)` (`SymplecticGeometry.range_inclusion_preimage_Iio`).

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

section Boundary

variable {M : Type*} [TopologicalSpace M] {g : M → ℝ}

/-- For a continuous `g : M → ℝ`, the points of the sublevel set `{g ≤ 0}` outside the image of
the open set `{g < 0}`, taken as a `TopologicalSpace.Opens M`; these are the points with
`g x = 0`. When `0` is a regular value of a smooth `g`, this is the boundary of `{g ≤ 0}`, in the
form that the boundary degree (`TauCeti.HomologicalOrientation.boundaryDegree`) takes. For
other `g` it need not be the frontier of `{g ≤ 0}`: for `g = 0` it is all of `M`. -/
abbrev sublevelBoundary (hg : Continuous g) : Set (g ⁻¹' Iic 0) :=
  (range (inclusion (s := ((⟨g ⁻¹' Iio 0, isOpen_Iio.preimage hg⟩ :
    TopologicalSpace.Opens M) : Set M)) (preimage_mono Iio_subset_Iic_self)))ᶜ

/-- A point `x` of `{g ≤ 0}` lies on the boundary `sublevelBoundary hg` if and only if
`0 ≤ g x`. -/
theorem mem_sublevelBoundary_iff {hg : Continuous g} {x : g ⁻¹' Iic 0} :
    x ∈ sublevelBoundary hg ↔ 0 ≤ g x := by
  simp [range_inclusion]

/-- A point `x` of `{g ≤ 0}` lies in `sublevelBoundary hg` if and only if `g x = 0`. -/
theorem mem_sublevelBoundary_iff_eq_zero {hg : Continuous g} {x : g ⁻¹' Iic 0} :
    x ∈ sublevelBoundary hg ↔ g x = 0 :=
  mem_sublevelBoundary_iff.trans ⟨x.property.out.antisymm, ge_of_eq⟩

/-- `sublevelBoundary hg` is the image of the inclusion of the level set `g⁻¹(0)` into
`{g ≤ 0}`. -/
theorem sublevelBoundary_eq_range_inclusion (hg : Continuous g) :
    sublevelBoundary hg = range (inclusion (preimage_mono (singleton_subset_iff.2 self_mem_Iic)) :
      g ⁻¹' {0} → g ⁻¹' Iic 0) := by
  ext x
  rw [mem_sublevelBoundary_iff_eq_zero, range_inclusion, mem_ofPred_eq, mem_preimage,
    mem_singleton_iff]

/-- The image of the open set `{g < 0}` in `{g ≤ 0}` is the complement of the image of the level
set `g⁻¹(0)`. -/
theorem range_inclusion_preimage_Iio (hg : Continuous g) :
    range (inclusion (s := ((⟨g ⁻¹' Iio 0, isOpen_Iio.preimage hg⟩ :
      TopologicalSpace.Opens M) : Set M)) (preimage_mono Iio_subset_Iic_self)) =
      (range (inclusion (preimage_mono (singleton_subset_iff.2 self_mem_Iic)) :
        g ⁻¹' {0} → g ⁻¹' Iic 0))ᶜ :=
  (compl_compl _).symm.trans (congrArg _ (sublevelBoundary_eq_range_inclusion hg))

/-- The inclusion of the open set `{g < 0}` into `{g ≤ 0}` is an open embedding. -/
theorem isOpenEmbedding_inclusion_preimage_Iio (hg : Continuous g) :
    IsOpenEmbedding (inclusion (s := ((⟨g ⁻¹' Iio 0, isOpen_Iio.preimage hg⟩ :
      TopologicalSpace.Opens M) : Set M)) (preimage_mono Iio_subset_Iic_self)) :=
  IsOpenEmbedding.inclusion _ ((isOpen_Iio.preimage hg).preimage continuous_subtypeVal)

/-- On a compact space, the sublevel set `{g ≤ 0}` of a continuous `g` is compact. -/
theorem compactSpace_preimage_Iic [CompactSpace M] (hg : Continuous g) :
    CompactSpace (g ⁻¹' Iic 0) :=
  isCompact_iff_compactSpace.1 (isClosed_Iic.preimage hg).isCompact

/-- A point of `sublevelBoundary hg` lies in `{g ≥ 0}`. -/
theorem mem_preimage_Ici_of_mem_sublevelBoundary {hg : Continuous g} {x : g ⁻¹' Iic 0}
    (hx : x ∈ sublevelBoundary hg) : (x : M) ∈ g ⁻¹' Ici 0 :=
  mem_preimage.2 (mem_Ici.2 (mem_sublevelBoundary_iff.1 hx))

end Boundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [I.Boundaryless]
  [IsManifold I ∞ M] [CompactSpace M] {g : M → ℝ}

/-- **The collar of a regular level set.** On a compact boundaryless manifold, if `0` is a regular
value of the smooth function `g`, then the inclusion of the level set `g⁻¹(0)` into the sublevel
set `{g ≤ 0}` admits a collar. -/
theorem isCollared_inclusion_levelSet (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (h0 : IsRegularValue I 𝓘(ℝ) g 0) :
    IsCollared (inclusion (preimage_mono (singleton_subset_iff.2 self_mem_Iic)) :
        g ⁻¹' {0} → g ⁻¹' Iic 0) := by
  -- A band `(-g)⁻¹[0, ε]` without critical points, and its product structure.
  have hg' : ContMDiff I 𝓘(ℝ) ∞ (-g) := hg.neg
  obtain ⟨ε, ⟨hε, -⟩, hcpt, hreg⟩ := exists_mem_Ioc_isCompact_forall_mfderiv_ne_zero
    (hg'.of_le (by simp)) zero_lt_one (isClosed_Icc.preimage hg'.continuous).isCompact
    (by simpa using h0)
  obtain ⟨e, he₂, he₁⟩ := exists_bandHomeomorph hg' hcpt hreg
  have hlev : g ⁻¹' {0} ⊆ (-g) ⁻¹' {0} := fun x hx ↦ by simp_all
  have hband : (-g) ⁻¹' Icc 0 ε ⊆ g ⁻¹' Iic 0 := fun x hx ↦ by simpa using hx.1
  -- The collar, `(y, t) ↦ e⁻¹ (y, ε t)`.
  let k : g ⁻¹' {0} × Ico (0 : ℝ) 1 → (-g) ⁻¹' {0} × Icc 0 ε :=
    Prod.map (inclusion hlev) (inclusion Ico_subset_Icc_self ∘ icoScale hε)
  have hk : IsEmbedding k := (IsEmbedding.inclusion hlev).prodMap
    ((IsEmbedding.inclusion _).comp (icoScale hε).isEmbedding)
  have hkp (p) : ((k p).2 : ℝ) = ε * p.2 :=
    (coe_inclusion Ico_subset_Icc_self _).trans (coe_icoScale hε p.2)
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
      have hxb : (x : M) ∈ (-g) ⁻¹' Icc 0 ε := ⟨by simpa using hx0, by rw [Pi.neg_apply]; linarith⟩
      have h2 : ((e ⟨x, hxb⟩).2 : ℝ) = -g x := he₂ _
      have hq1 : g (e ⟨x, hxb⟩).1 = 0 := neg_eq_zero.1 (e ⟨x, hxb⟩).1.property
      have hmem : ((e ⟨x, hxb⟩).2 : ℝ) ∈ Ico 0 ε := ⟨(e ⟨x, hxb⟩).2.property.1, by linarith⟩
      have hk : k (⟨(e ⟨x, hxb⟩).1, hq1⟩, (icoScale hε).symm ⟨_, hmem⟩) = e ⟨x, hxb⟩ :=
        Prod.ext (Subtype.ext (coe_inclusion hlev _))
          (Subtype.ext ((coe_inclusion Ico_subset_Icc_self _).trans
            (congrArg Subtype.val ((icoScale hε).apply_symm_apply _))))
      exact ⟨(⟨(e ⟨x, hxb⟩).1, hq1⟩, (icoScale hε).symm ⟨_, hmem⟩), Subtype.ext (by simp [hk])⟩
  · have hy0 : g y = 0 := y.property
    have hy : (y : M) ∈ (-g) ⁻¹' Icc 0 ε := by simp [hy0, hε.le]
    have hk : k (y, ⟨0, by norm_num⟩) = e ⟨y, hy⟩ :=
      Prod.ext (Subtype.ext (he₁ ⟨y, hy⟩ (by simp [hy0])).symm)
        (Subtype.ext ((hkp _).trans ((mul_zero ε).trans (by simp [he₂, hy0]))))
    ext
    simp only [Function.comp_apply, hk, Homeomorph.symm_apply_apply, coe_inclusion]

end SymplecticGeometry

end
