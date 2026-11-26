/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
public import TauCeti.Geometry.Symplectic.Darboux.Basis
import TauCeti.Geometry.Symplectic.Darboux.EuclideanBasis
import SymplecticGeometry.Geometry.Manifold.VectorBundle.LocalFrame
import SymplecticGeometry.LinearAlgebra.Symplectic.Darboux

/-!
# Local Darboux frames of a symplectic vector bundle

Let `ω` be a nondegenerate `Cⁿ` two-form on a real vector bundle `V → M` of finite rank. This file
shows that `ω` has local `Cⁿ` frames that are Darboux bases at every point, and deduces that the
structure group of `(V, ω)` reduces to the linear symplectic group.

## Main results

* `ContMDiffTwoForm.IsNondegenerate.exists_local_darboux_sections`: with no hypothesis on the
  base, every point has an open neighbourhood with `Cⁿ` sections `aᵢ`, `bᵢ` that satisfy the
  Darboux relations of `ω` at each of its points.
* `ContMDiffTwoForm.IsNondegenerate.exists_isLocalFrameOn_isDarbouxBasis`: with no hypothesis on
  the base, every point has an open neighbourhood with a `Cⁿ` local frame
  `(q₁, p₁, …, q_k, p_k)` that is a Darboux basis of `ω` at each of its points.
* `ContMDiffTwoForm.IsNondegenerate.exists_trivialization_isSymplectomorphism`: for a symplectic
  form `σ` on the model fibre, every point lies in the base set of a trivialization of the `Cⁿ`
  maximal atlas whose fibre maps carry `ω` to `σ`.
* `ContMDiffTwoForm.IsNondegenerate.isSymplectomorphism_coordChangeL`: the coordinate changes
  between two such trivializations preserve `σ`.
* `ContMDiffTwoForm.IsNondegenerate.exists_isSymplecticFrameOn`: for a symplectic form `σ` on a
  space `W` of the rank of `V`, every point has an open neighbourhood with a symplectic frame of
  `ω` for `σ`.

## Implementation notes

The local Darboux frames come from a symplectic Gram–Schmidt process run on sections, as in the
inductive proof of McDuff–Salamon, Theorem 2.1.3. A Darboux basis of the fibre at the given point
is extended to sections `aᵢ`, `bᵢ` that are constant in a trivialization. Where
`c = ω(a₁, b₁)` does not vanish, `a₁` and `c⁻¹ b₁` satisfy the Darboux relations, and the other
sections are projected to their `ω`-orthogonal complement by
`v ↦ v - ω(v, c⁻¹ b₁) a₁ + ω(v, a₁) c⁻¹ b₁` (Tau Ceti's
`LinearMap.BilinForm.IsAlt.sub_smul_add_smul_mem_orthogonal_span_pair`). This changes nothing
at the given point, and the process goes on with the projected sections. Each step uses only
sums, products with smooth functions and the inverse of a nonvanishing smooth function, so it
needs neither a bundle metric nor a partition of unity, and works over any base. The
trivializations are Tau Ceti's frame trivializations `IsLocalFrameOn.trivialization`. The
symplectic frames do not go through them: they come from the Darboux sections through
`ContMDiffTwoForm.exists_isSymplecticFrameOn_of_darboux`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 2.1.3, Exercise 2.6.2 and Theorem 2.6.3
-/

public section

noncomputable section

open _root_.Bundle Set Module
open scoped Manifold

namespace SymplecticGeometry.Bundle

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ∞}

namespace ContMDiffTwoForm

variable {ω : ContMDiffTwoForm I n F V}

/-! ### Coordinate changes of symplectic trivializations -/

/-- Let `e` and `e'` be linear trivializations whose maps on the fibre over `y` are both linear
symplectomorphisms from `ω_y` to a symplectic form `σ` on the model fibre. Then their coordinate
change at `y` is a linear symplectomorphism of `σ`. -/
theorem IsNondegenerate.isSymplectomorphism_coordChangeL (hω : ω.IsNondegenerate)
    {σ : TauCeti.SymplecticForm F} {e e' : Trivialization F (π F V)} [e.IsLinear ℝ]
    [e'.IsLinear ℝ] {y : M} (hy : y ∈ e.baseSet ∩ e'.baseSet)
    (he : (hω.symplecticFormAt y).IsSymplectomorphism σ (e.linearEquivAt ℝ y hy.1))
    (he' : (hω.symplecticFormAt y).IsSymplectomorphism σ (e'.linearEquivAt ℝ y hy.2)) :
    σ.IsSymplectomorphism σ (e.coordChangeL ℝ e' y).toLinearEquiv := by
  rw [Trivialization.coe_coordChangeL' e e' hy]
  exact he.symm.trans he'

/-! ### Symplectic Gram–Schmidt near a point -/

/-- **Symplectic Gram–Schmidt near a point.** Let `a i`, `b i` (`i : Fin k`) be sections that are
`Cⁿ` on an open set `W ∋ x₀` and satisfy the Darboux relations of `ω` at `x₀`. Then there is an
open `U ⊆ W` containing `x₀` with sections `a' i`, `b' i` that are `Cⁿ` on `U`, satisfy the Darboux
relations of `ω_y` at every `y ∈ U`, and are `ω_y`-orthogonal to every vector that is
`ω_y`-orthogonal to all `a i y` and `b i y`. -/
private theorem exists_darboux_sections (ω : ContMDiffTwoForm I n F V) {k : ℕ} {W : Set M}
    (hW : IsOpen W) {x₀ : M} (hx₀ : x₀ ∈ W) {a b : Fin k → ∀ y, V y}
    (ha : ∀ i, CMDiff[W] n (T% (a i))) (hb : ∀ i, CMDiff[W] n (T% (b i)))
    (haa : ∀ i j, ω.bilinFormAt x₀ (a i x₀) (a j x₀) = 0)
    (hbb : ∀ i j, ω.bilinFormAt x₀ (b i x₀) (b j x₀) = 0)
    (hab : ∀ i j, ω.bilinFormAt x₀ (a i x₀) (b j x₀) = if i = j then 1 else 0) :
    ∃ U ⊆ W, IsOpen U ∧ x₀ ∈ U ∧ ∃ a' b' : Fin k → ∀ y, V y,
      (∀ i, CMDiff[U] n (T% (a' i))) ∧ (∀ i, CMDiff[U] n (T% (b' i))) ∧ ∀ y ∈ U,
        (∀ i j, ω.bilinFormAt y (a' i y) (a' j y) = 0) ∧
        (∀ i j, ω.bilinFormAt y (b' i y) (b' j y) = 0) ∧
        (∀ i j, ω.bilinFormAt y (a' i y) (b' j y) = if i = j then 1 else 0) ∧
        ∀ w : V y, (∀ i, ω.bilinFormAt y w (a i y) = 0 ∧ ω.bilinFormAt y w (b i y) = 0) →
          ∀ i, ω.bilinFormAt y w (a' i y) = 0 ∧ ω.bilinFormAt y w (b' i y) = 0 := by
  induction k generalizing W with
  | zero =>
    exact ⟨W, subset_rfl, hW, hx₀, a, b, ha, hb, fun _ _ ↦
      ⟨finZeroElim, finZeroElim, finZeroElim, fun _ _ ↦ finZeroElim⟩⟩
  | succ k ih =>
    have hskew (y : M) (u v : V y) : ω.bilinFormAt y u v = -ω.bilinFormAt y v u :=
      (LinearMap.IsAlt.neg (ω.isAlt_bilinFormAt y) v u).symm
    have hself (y : M) (u : V y) : ω.bilinFormAt y u u = 0 := (ω.isAlt_bilinFormAt y).self_eq_zero u
    -- Normalize `b 0` against `a 0` where `c = ω(a 0, b 0)` does not vanish.
    set c : M → ℝ := fun y ↦ ω.bilinFormAt y (a 0 y) (b 0 y)
    have hc : CMDiff[W] n c := ω.contMDiffOn_bilinFormAt (ha 0) (hb 0)
    have hc₀ : c x₀ = 1 := by simpa only [↓reduceIte] using hab 0 0
    set W₀ := W ∩ c ⁻¹' {0}ᶜ
    have hW₀ : IsOpen W₀ := hc.continuousOn.isOpen_inter_preimage hW isOpen_compl_singleton
    have hx₀W₀ : x₀ ∈ W₀ := ⟨hx₀, by simp [hc₀]⟩
    have hW₀W : W₀ ⊆ W := inter_subset_left
    set β : ∀ y, V y := (fun y ↦ (c y)⁻¹) • b 0 with hβ_def
    have hβ : CMDiff[W₀] n (T% β) :=
      ((hc.mono hW₀W).inv₀ fun y hy ↦ hy.2).smul_section ((hb 0).mono hW₀W)
    have haβ (y : M) (hy : y ∈ W₀) : ω.bilinFormAt y (a 0 y) (β y) = 1 := by
      simp only [hβ_def, Pi.smul_apply', map_smul, smul_eq_mul]
      exact inv_mul_cancel₀ hy.2
    -- Project the other sections to the `ω`-orthogonal complement of `a 0`, `β`, by Tau Ceti's
    -- projection for the pair `β`, `a 0`.
    set P : (∀ y, V y) → ∀ y, V y := fun v y ↦
      v y - ω.bilinFormAt y (a 0 y) (v y) • β y + ω.bilinFormAt y (β y) (v y) • a 0 y with hP_def
    have hP (v : ∀ y, V y) (hv : CMDiff[W] n (T% v)) : CMDiff[W₀] n (T% (P v)) :=
      ((hv.mono hW₀W).sub_section ((ω.contMDiffOn_bilinFormAt ((ha 0).mono hW₀W)
        (hv.mono hW₀W)).smul_section hβ)).add_section
        ((ω.contMDiffOn_bilinFormAt hβ (hv.mono hW₀W)).smul_section ((ha 0).mono hW₀W))
    have hPmem (v : ∀ y, V y) (y : M) (hy : y ∈ W₀) :
        ω.bilinFormAt y (β y) (P v y) = 0 ∧ ω.bilinFormAt y (a 0 y) (P v y) = 0 :=
      LinearMap.BilinForm.mem_orthogonal_span_pair_iff.1
        ((ω.isAlt_bilinFormAt y).sub_smul_add_smul_mem_orthogonal_span_pair (haβ y hy) (v y))
    have hPa (v : ∀ y, V y) (y : M) (hy : y ∈ W₀) : ω.bilinFormAt y (P v y) (a 0 y) = 0 :=
      (ω.isAlt_bilinFormAt y).eq_iff.1 (hPmem v y hy).2
    have hPβ (v : ∀ y, V y) (y : M) (hy : y ∈ W₀) : ω.bilinFormAt y (P v y) (β y) = 0 :=
      (ω.isAlt_bilinFormAt y).eq_iff.1 (hPmem v y hy).1
    have hPorth (v : ∀ y, V y) (y : M) (w : V y) (hwa : ω.bilinFormAt y w (a 0 y) = 0)
        (hwb : ω.bilinFormAt y w (b 0 y) = 0) (hwv : ω.bilinFormAt y w (v y) = 0) :
        ω.bilinFormAt y w (P v y) = 0 := by
      simp [-bilinFormAt_apply, hP_def, hβ_def, hwa, hwb, hwv]
    have hPx₀ (v : ∀ y, V y) (hav : ω.bilinFormAt x₀ (a 0 x₀) (v x₀) = 0)
        (hbv : ω.bilinFormAt x₀ (b 0 x₀) (v x₀) = 0) : P v x₀ = v x₀ := by
      simp [-bilinFormAt_apply, hP_def, hβ_def, hav, hbv]
    -- At `x₀` the projection changes none of the remaining sections.
    have hPa₀ (i : Fin k) : P (a i.succ) x₀ = a i.succ x₀ := by
      refine hPx₀ _ (haa _ _) ?_
      rw [hskew, hab i.succ 0]
      simp [Fin.succ_ne_zero]
    have hPb₀ (i : Fin k) : P (b i.succ) x₀ = b i.succ x₀ :=
      hPx₀ _ (by simpa [(Fin.succ_ne_zero i).symm] using hab 0 i.succ) (hbb _ _)
    obtain ⟨U, hUW₀, hU, hx₀U, a'', b'', ha'', hb'', hrel⟩ :=
      ih hW₀ hx₀W₀ (a := fun i ↦ P (a i.succ)) (b := fun i ↦ P (b i.succ))
        (fun i ↦ hP _ (ha _)) (fun i ↦ hP _ (hb _))
        (fun i j ↦ by simpa [hPa₀] using haa i.succ j.succ)
        (fun i j ↦ by simpa [hPb₀] using hbb i.succ j.succ)
        (fun i j ↦ by simpa [hPa₀, hPb₀] using hab i.succ j.succ)
    refine ⟨U, hUW₀.trans hW₀W, hU, hx₀U, Fin.cons (a 0) a'', Fin.cons β b'', ?_, ?_,
      fun y hy ↦ ?_⟩
    · exact Fin.cases (by simpa using (ha 0).mono (hUW₀.trans hW₀W)) (by simpa using ha'')
    · exact Fin.cases (by simpa using hβ.mono hUW₀) (by simpa using hb'')
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hrel y hy
    have hyW₀ := hUW₀ hy
    -- `a 0` and `β` are orthogonal to the new sections.
    have hao := h₄ (a 0 y) fun i ↦ ⟨by rw [hskew, hPa _ _ hyW₀, neg_zero],
      by rw [hskew, hPa _ _ hyW₀, neg_zero]⟩
    have hβo := h₄ (β y) fun i ↦ ⟨by rw [hskew, hPβ _ _ hyW₀, neg_zero],
      by rw [hskew, hPβ _ _ hyW₀, neg_zero]⟩
    refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_, fun w hw i ↦ ?_⟩
    · cases i using Fin.cases <;> cases j using Fin.cases <;>
        simp [hself, h₁, (hao _).1, hskew y (a'' _ y) (a 0 y)]
    · cases i using Fin.cases <;> cases j using Fin.cases <;>
        simp [hself, h₂, (hβo _).2, hskew y (b'' _ y) (β y)]
    · cases i using Fin.cases <;> cases j using Fin.cases <;>
        simp [haβ y hyW₀, h₃, (hao _).2, hskew y (a'' _ y) (β y), (hβo _).1, Fin.succ_ne_zero,
          (Fin.succ_ne_zero _).symm]
    · cases i using Fin.cases with
      | zero => simp [hβ_def, (hw 0).1, (hw 0).2]
      | succ i =>
        simpa using h₄ w (fun j ↦ ⟨hPorth _ y w (hw 0).1 (hw 0).2 (hw j.succ).1,
          hPorth _ y w (hw 0).1 (hw 0).2 (hw j.succ).2⟩) i

/-! ### Local Darboux frames -/

variable [FiniteDimensional ℝ F] [ContMDiffVectorBundle n F V I]

/-- **Local Darboux sections.** For a nondegenerate `Cⁿ` two-form `ω` on a bundle of rank `2k`,
every point `x₀` has an open neighbourhood `U` with `k` pairs of sections `aᵢ`, `bᵢ` that are `Cⁿ`
on `U` and satisfy the Darboux relations `ω(aᵢ, aⱼ) = 0`, `ω(bᵢ, bⱼ) = 0` and `ω(aᵢ, bⱼ) = δᵢⱼ`
at every point of `U`. -/
theorem IsNondegenerate.exists_local_darboux_sections (hω : ω.IsNondegenerate) (x₀ : M) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ ∃ k : ℕ, finrank ℝ F = 2 * k ∧
      ∃ a b : Fin k → ∀ y, V y, (∀ i, CMDiff[U] n (T% (a i))) ∧ (∀ i, CMDiff[U] n (T% (b i))) ∧
        ∀ y ∈ U, (∀ i j, ω.bilinFormAt y (a i y) (a j y) = 0) ∧
          (∀ i j, ω.bilinFormAt y (b i y) (b j y) = 0) ∧
          ∀ i j, ω.bilinFormAt y (a i y) (b j y) = if i = j then 1 else 0 := by
  classical
  have hB (y : M) (u v : V y) : hω.symplecticFormAt y u v = ω.bilinFormAt y u v := by
    rw [symplecticFormAt_apply, bilinFormAt_apply]
  have := VectorBundle.finiteDimensional ℝ F V
  -- A Darboux basis `b₀` of the fibre at `x₀`, extended to sections `L` that are constant in a
  -- trivialization `e` at `x₀`.
  obtain ⟨k, b₀, hb₀⟩ := (hω.symplecticFormAt x₀).exists_isDarbouxBasis
  have hk : finrank ℝ F = 2 * k := by
    rw [← VectorBundle.finrank_eq ℝ F V x₀, finrank_eq_card_basis b₀]
    simp [mul_comm]
  set e := trivializationAt F V x₀
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  set L := e.localFrame (b₀.map (e.linearEquivAt ℝ x₀ hx₀))
  have hL := e.isLocalFrameOn_localFrame_baseSet I n (b₀.map (e.linearEquivAt ℝ x₀ hx₀))
  have hLx₀ (p : Fin k × Fin 2) : L p x₀ = b₀ p := by
    simp [L, e.localFrame_apply_of_mem_baseSet _ hx₀, Trivialization.basisAt,
      e.symm_apply_apply_mk hx₀]
  -- Symplectic Gram–Schmidt turns `L` into sections with the Darboux relations near `x₀`.
  obtain ⟨U, -, hU, hx₀U, a, b, ha, hb, hrel⟩ :=
    exists_darboux_sections ω e.open_baseSet hx₀ (a := fun i ↦ L (i, 0)) (b := fun i ↦ L (i, 1))
      (fun _ ↦ hL.contMDiffOn _) (fun _ ↦ hL.contMDiffOn _)
      (fun i j ↦ by simpa only [hLx₀, hB] using hb₀.apply_fst_fst i j)
      (fun i j ↦ by simpa only [hLx₀, hB] using hb₀.apply_snd_snd i j)
      (fun i j ↦ by simpa only [hLx₀, hB] using hb₀.apply_fst_snd i j)
  exact ⟨U, hU, hx₀U, k, hk, a, b, ha, hb, fun y hy ↦
    (hrel y hy).imp_right fun h ↦ h.imp_right And.left⟩

/-- **Local Darboux frames.** For a nondegenerate `Cⁿ` two-form `ω` on a bundle of finite rank,
every point `x₀` has an open neighbourhood `U` with a `Cⁿ` local frame
`s : Fin k × Fin 2 → ∀ y, V y` on `U` that is a Darboux basis of `ω_y` at every `y ∈ U`. -/
theorem IsNondegenerate.exists_isLocalFrameOn_isDarbouxBasis (hω : ω.IsNondegenerate) (x₀ : M) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ ∃ (k : ℕ) (s : Fin k × Fin 2 → ∀ y, V y)
      (hs : IsLocalFrameOn I F n s U), ∀ y (hy : y ∈ U),
        (hω.symplecticFormAt y).IsDarbouxBasis (hs.toBasisAt hy) := by
  classical
  have hB (y : M) (u v : V y) : hω.symplecticFormAt y u v = ω.bilinFormAt y u v := by
    rw [symplecticFormAt_apply, bilinFormAt_apply]
  obtain ⟨U, hU, hx₀U, k, hk, a, b, ha, hb, hrel⟩ := hω.exists_local_darboux_sections x₀
  let s : Fin k × Fin 2 → ∀ y, V y := fun p ↦ if p.2 = 0 then a p.1 else b p.1
  have hs₀ (i : Fin k) : s (i, 0) = a i := by simp [s]
  have hs₁ (i : Fin k) : s (i, 1) = b i := by simp [s]
  have hrel' (y : M) (hy : y ∈ U) :
      (∀ i j, hω.symplecticFormAt y (s (i, 0) y) (s (j, 0) y) = 0) ∧
      (∀ i j, hω.symplecticFormAt y (s (i, 1) y) (s (j, 1) y) = 0) ∧
      (∀ i j, hω.symplecticFormAt y (s (i, 0) y) (s (j, 1) y) = if i = j then 1 else 0) := by
    simpa only [hs₀, hs₁, hB] using hrel y hy
  have hli (y : M) (hy : y ∈ U) : LinearIndependent ℝ (fun p ↦ s p y) :=
    TauCeti.SymplecticForm.linearIndependent_of_apply_fst_snd (hrel' y hy).1 (hrel' y hy).2.1
      (hrel' y hy).2.2
  have hs : IsLocalFrameOn I F n s U :=
    .of_linearIndependent_of_card_eq_finrank (hli := hli) (by simp [hk, mul_comm]) fun ⟨i, j⟩ ↦ by
      by_cases hj : j = 0
      · simpa only [s, hj, ↓reduceIte] using ha i
      · simpa only [s, hj, ↓reduceIte] using hb i
  refine ⟨U, hU, hx₀U, k, s, hs, fun y hy ↦ ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := hrel' y hy
  exact ⟨by simpa only [hs.toBasisAt_coe] using h₁, by simpa only [hs.toBasisAt_coe] using h₂,
    by simpa only [hs.toBasisAt_coe] using h₃⟩

/-- **Local symplectic trivializations.** Let `ω` be a nondegenerate `Cⁿ` two-form on a bundle
with finite-dimensional model fibre `F`, and `σ` a symplectic form on `F`. Every point `x₀` lies
in the base set of a linear trivialization `e` of
the maximal atlas of `Cⁿ` trivializations whose map on each fibre over its base set is a linear
symplectomorphism from `ω_y` to `σ`. By `IsNondegenerate.isSymplectomorphism_coordChangeL`, the
coordinate changes of such trivializations are linear symplectomorphisms of `σ`.

Milestone: *Symplectic vector bundles are complex vector bundles*. -/
theorem IsNondegenerate.exists_trivialization_isSymplectomorphism (hω : ω.IsNondegenerate)
    (σ : TauCeti.SymplecticForm F) (x₀ : M) :
    ∃ (e : Trivialization F (π F V)) (_ : e.IsLinear ℝ),
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear M F I n).maximalAtlas (TotalSpace F V) ∧
      x₀ ∈ e.baseSet ∧ ∀ y (hy : y ∈ e.baseSet),
        (hω.symplecticFormAt y).IsSymplectomorphism σ (e.linearEquivAt ℝ y hy) := by
  obtain ⟨U, hU, hx₀, k, s, hs, hD⟩ := hω.exists_isLocalFrameOn_isDarbouxBasis x₀
  obtain ⟨c, hc⟩ := σ.exists_isDarbouxBasis_of_finrank_eq (n := k)
    (by rw [← hs.card_eq_finrank hx₀, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin])
  have hxe : x₀ ∈ (hs.trivialization hU c).baseSet := by
    rwa [IsLocalFrameOn.baseSet_trivialization]
  refine ⟨hs.trivialization hU c, inferInstance, hs.trivialization_mem_maximalAtlas hU c, hxe,
    fun y hy ↦ ?_⟩
  have hyU : y ∈ U := by rwa [IsLocalFrameOn.baseSet_trivialization] at hy
  -- The fibre map sends the Darboux basis `s · y` of `ω_y` to the Darboux basis `c` of `σ`.
  have he : (hs.trivialization hU c).linearEquivAt ℝ y hy =
      (hs.toBasisAt hyU).darbouxBasisEquiv.trans c.darbouxBasisEquiv.symm := by
    refine (hs.toBasisAt hyU).ext' fun p ↦ ?_
    rw [Trivialization.linearEquivAt_apply, LinearEquiv.trans_apply, LinearEquiv.eq_symm_apply]
    nth_rw 1 [IsLocalFrameOn.toBasisAt_coe hs hyU]
    rw [IsLocalFrameOn.trivialization_apply_frame hs hU c hyU]
    rcases p with ⟨i, a⟩
    fin_cases a <;> simp [-IsLocalFrameOn.toBasisAt_coe]
  rw [he]
  exact (hD y hyU).isSymplectomorphism_darbouxBasisEquiv.trans
    hc.isSymplectomorphism_darbouxBasisEquiv.symm

/-- **Local symplectic frames.** Let `ω` be a nondegenerate `Cⁿ` two-form on a bundle with
finite-dimensional model fibre `F`, and `σ` a symplectic form on a finite-dimensional normed space
`W` with `dim W = dim F`. Every point `x₀` has an open
neighbourhood `U` with a symplectic frame `Φ` of `ω` for `σ` over `U`. -/
theorem IsNondegenerate.exists_isSymplecticFrameOn (hω : ω.IsNondegenerate) {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (σ : TauCeti.SymplecticForm W) (hW : finrank ℝ W = finrank ℝ F) (x₀ : M) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ ∃ Φ : ∀ x, W ≃L[ℝ] V x, ω.IsSymplecticFrameOn σ U Φ := by
  classical
  -- Darboux sections near `x₀` give a symplectic frame for `stdForm (Fin k)`, which a linear
  -- symplectomorphism from `σ` to `stdForm (Fin k)` turns into one for `σ`.
  obtain ⟨U, hU, hx₀, k, hk, a, b, ha, hb, hrel⟩ := hω.exists_local_darboux_sections x₀
  obtain ⟨Ψ, hΨ, -⟩ := exists_isSymplecticFrameOn_of_darboux (by rw [hk, Fintype.card_fin]) ha hb
    (fun y hy ↦ (hrel y hy).1) (fun y hy ↦ (hrel y hy).2.1) (fun y hy ↦ (hrel y hy).2.2)
  obtain ⟨e, he⟩ := exists_isSymplectomorphism_stdForm σ (ι := Fin k)
    (by rw [hW, hk, Fintype.card_fin])
  refine ⟨U, hU, hx₀, _, hΨ.precomp e.symm.toContinuousLinearEquiv ?_⟩
  rw [LinearEquiv.toLinearEquiv_toContinuousLinearEquiv]
  exact he.symm

end ContMDiffTwoForm

end SymplecticGeometry.Bundle

end
