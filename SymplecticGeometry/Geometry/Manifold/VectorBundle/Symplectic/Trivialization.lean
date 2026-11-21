/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.ComplexStructure.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
public import TauCeti.Geometry.Symplectic.Darboux.Basis
import TauCeti.Geometry.Symplectic.Darboux.EuclideanBasis
import Mathlib.Analysis.Normed.Module.FiniteDimension
import SymplecticGeometry.Analysis.InnerProductSpace.GramSchmidtOrtho
import TauCeti.Geometry.Manifold.Riemannian.Section
import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt
import TauCeti.Geometry.Manifold.VectorBundle.MaximalAtlas
import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis

/-!
# Local Darboux frames of a symplectic vector bundle

Let `ω` be a nondegenerate `Cⁿ` two-form on a real vector bundle `V → M` of finite rank. This file
shows that `ω` has local `Cⁿ` frames that are Darboux bases at every point, and deduces that the
structure group of `(V, ω)` reduces to the linear symplectic group.

## Main results

* `ContMDiffTwoForm.Compatible.exists_isLocalFrameOn_isDarbouxBasis`: if `ω` is compatible with a
  `Cⁿ` complex structure `J`, every point has an open neighbourhood with a `Cⁿ` local frame
  `(q₁, p₁, …, q_k, p_k)` that is a Darboux basis of `ω` at each of its points.
* `ContMDiffTwoForm.IsNondegenerate.exists_isLocalFrameOn_isDarbouxBasis`: the same for a
  nondegenerate form over a Hausdorff σ-compact base, where compatible complex structures exist.
* `ContMDiffTwoForm.IsNondegenerate.exists_trivialization_isSymplectomorphism`: for a symplectic
  form `σ` on the model fibre, every point lies in the base set of a trivialization of the `Cⁿ`
  maximal atlas whose fibre maps carry `ω` to `σ`.
* `ContMDiffTwoForm.IsNondegenerate.isSymplectomorphism_coordChangeL`: the coordinate changes
  between two such trivializations preserve `σ`.
* `ContMDiffTwoForm.IsNondegenerate.exists_isSymplecticFrameOn`: for a symplectic form `σ` on a
  space `W` of the rank of `V`, every point has an open neighbourhood with a symplectic frame of
  `ω` for `σ`.

## Implementation notes

The frame is built as in McDuff–Salamon, §2.6. For `ω` compatible with `J`, the bilinear form
`g(u, v) = ω(u, J v)` is a `Cⁿ` bundle metric for which `J` is orthogonal, and
`ω(u, v) = g(J u, v)`. A `J`-adapted orthonormal basis `u₁, J u₁, …` of the fibre at the given
point (Tau Ceti's `TauCeti.AlmostComplexStructure.exists_adapted_orthonormalBasis`) is extended to
constant sections in a trivialization, and the sections `u₁, J u₁, u₂, J u₂, …` are
orthonormalized by Tau Ceti's smooth Gram–Schmidt (`ContMDiffWithinAt.gramSchmidtNormed_bundle`)
where they stay independent. Since `J` is skew-adjoint and orthogonal for `g`, the output has the
form `e₁, J e₁, e₂, J e₂, …` (`InnerProductSpace.gramSchmidtNormed_eq_apply_gramSchmidtNormed`),
and such an orthonormal family is a Darboux basis of `ω`; this last step follows the proof of
Tau Ceti's `TauCeti.AlmostComplexStructure.toBasis_orientation_eq_symplecticForm_orientation`.
The smooth Gram–Schmidt needs a linearly ordered index, so the frame is built on `Fin (2 * k)`
and reindexed to `Fin k × Fin 2`. The trivializations are Tau Ceti's frame trivializations
`IsLocalFrameOn.trivialization`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
-/

public section

noncomputable section

open _root_.Bundle Set Module InnerProductSpace Filter
open scoped Manifold RealInnerProductSpace Topology

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

variable {ω : ContMDiffTwoForm I n F V} {J : ContMDiffComplexStructure I n F V}

/-! ### The metric of a compatible pair -/

/-- The bilinear section `(u, v) ↦ -ω(J u, v)`, which for a compatible pair is `ω(u, J v)`. -/
private def compatibleMetricBilin (ω : ContMDiffTwoForm I n F V)
    (J : ContMDiffComplexStructure I n F V) : TauCeti.Manifold.BilinearSection I F V ℝ n :=
  -⟨fun x ↦ (ω.flat x).comp (J x), ω.contMDiff_flat.clm_bundle_comp J.toEndomorphism.contMDiff⟩

private theorem compatibleMetricBilin_apply (x : M) (u v : V x) :
    compatibleMetricBilin ω J x u v = -ω.bilinFormAt x (J x u) v := by
  simp [compatibleMetricBilin, flat_apply, bilinFormAt_apply]

section Metric

variable [FiniteDimensional ℝ F]

/-- The bundle metric `g(u, v) = -ω(J u, v) = ω(u, J v)` of a compatible pair. -/
private def compatibleMetric (hc : ω.Compatible J) : ContMDiffRiemannianMetric I n F V :=
  .ofPositiveDefiniteSection (compatibleMetricBilin ω J) <| by
    refine (TauCeti.Manifold.mem_positiveDefiniteBilinearSections _).2
      ⟨(TauCeti.Manifold.mem_symmetricBilinearSections _).2 fun x u v ↦ ?_,
      fun x v hv ↦ ?_⟩
    · rw [compatibleMetricBilin_apply, compatibleMetricBilin_apply,
        ← invariant_def.1 hc.invariant x (J x u) v,
        ContMDiffComplexStructure.apply_apply, map_neg, LinearMap.neg_apply,
        (ω.isAlt_bilinFormAt x).neg_eq]
    · rw [compatibleMetricBilin_apply x v v, (ω.isAlt_bilinFormAt x).neg_eq]
      exact tames_def.1 hc.tames x v hv

private theorem compatibleMetric_inner (hc : ω.Compatible J) (x : M) (u v : V x) :
    (compatibleMetric hc).inner x u v = -ω.bilinFormAt x (J x u) v :=
  (ContMDiffRiemannianMetric.ofPositiveDefiniteSection_inner _ _ x u v).trans
    (compatibleMetricBilin_apply x u v)

/-- A basis `(q₁, p₁, …)` of a fibre that is orthonormal for the metric of a compatible pair, with
`pᵢ = J qᵢ`, is a Darboux basis of `ω`. The proof follows the Darboux step in the proof of Tau
Ceti's `TauCeti.AlmostComplexStructure.toBasis_orientation_eq_symplecticForm_orientation`. -/
private theorem Compatible.isDarbouxBasis_of_inner (hc : ω.Compatible J) {y : M} {k : ℕ}
    (b : Basis (Fin k × Fin 2) ℝ (V y))
    (hon : ∀ p q, (compatibleMetric hc).inner y (b p) (b q) = if p = q then 1 else 0)
    (hJ : ∀ i, b (i, 1) = J y (b (i, 0))) :
    (hc.isNondegenerate.symplecticFormAt y).IsDarbouxBasis b := by
  have hform (u v : V y) :
      hc.isNondegenerate.symplecticFormAt y u v = (compatibleMetric hc).inner y (J y u) v := by
    rw [compatibleMetric_inner, J.apply_apply, map_neg, LinearMap.neg_apply, neg_neg,
      IsNondegenerate.symplecticFormAt_apply, bilinFormAt_apply]
  refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩
  · rw [hform, ← hJ, hon]
    simp
  · rw [hform, hJ, J.apply_apply, map_neg, neg_apply, hon]
    simp
  · rw [hform, ← hJ, hon]
    simp

end Metric

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

/-! ### Local Darboux frames -/

variable [FiniteDimensional ℝ F] [ContMDiffVectorBundle n F V I]

/-- **Local Darboux frames of a compatible pair.** If `ω` is compatible with a `Cⁿ` complex
structure `J`, every point `x₀` has an open neighbourhood `U` with a `Cⁿ` local frame
`s : Fin k × Fin 2 → ∀ y, V y` on `U` that is a Darboux basis of `ω_y` at every `y ∈ U`:
`ω(qᵢ, qⱼ) = ω(pᵢ, pⱼ) = 0` and `ω(qᵢ, pⱼ) = δᵢⱼ` for `qᵢ = s (i, 0)`, `pᵢ = s (i, 1)`. -/
theorem Compatible.exists_isLocalFrameOn_isDarbouxBasis (hc : ω.Compatible J) (x₀ : M) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ ∃ (k : ℕ) (s : Fin k × Fin 2 → ∀ y, V y)
      (hs : IsLocalFrameOn I F n s U), ∀ y (hy : y ∈ U),
        (hc.isNondegenerate.symplecticFormAt y).IsDarbouxBasis (hs.toBasisAt hy) := by
  classical
  set g := compatibleMetric hc
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle I n F V := _root_.Bundle.instIsContMDiffRiemannianBundle g
  have := VectorBundle.finiteDimensional ℝ F V
  have hinner (x : M) (u v : V x) : ⟪u, v⟫ = -ω.bilinFormAt x (J x u) v :=
    (g.inner_riemannianBundle x u v).trans (compatibleMetric_inner hc x u v)
  -- On each fibre, `ω(u, v) = ⟪J u, v⟫`, and `J` is skew-adjoint and orthogonal.
  have hω (x : M) (u v : V x) : ω.bilinFormAt x u v = ⟪J x u, v⟫ := by
    rw [hinner, J.apply_apply, map_neg, LinearMap.neg_apply, neg_neg]
  have hskew (x : M) (u v : V x) : ⟪J x u, v⟫ = -⟪u, J x v⟫ := by
    rw [← hω, hinner, invariant_def.1 hc.invariant, neg_neg]
  have hnorm (x : M) (v : V x) : ‖J x v‖ = ‖v‖ := by
    have h : ⟪J x v, J x v⟫ = ⟪v, v⟫ := by rw [hskew, J.apply_apply, inner_neg_right, neg_neg]
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, h]
  -- A `J`-adapted orthonormal basis `b` of the fibre at `x₀`.
  obtain ⟨k, b₀, -⟩ := (hc.isNondegenerate.symplecticFormAt x₀).exists_isDarbouxBasis
  have hk : finrank ℝ F = 2 * k := by
    rw [← VectorBundle.finrank_eq ℝ F V x₀, finrank_eq_card_basis b₀]
    simp [Nat.mul_comm]
  obtain ⟨b, hb⟩ := TauCeti.AlmostComplexStructure.exists_adapted_orthonormalBasis
    (J.almostComplexStructureAt x₀) (by simpa using hnorm x₀) k
    (by rw [VectorBundle.finrank_eq ℝ F V x₀, hk])
  simp only [ContMDiffComplexStructure.almostComplexStructureAt_apply] at hb
  -- Extend `b` to a local frame `L` that is constant in a trivialization `e` at `x₀`.
  set e := trivializationAt F V x₀
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  set L := e.localFrame (b.toBasis.map (e.linearEquivAt ℝ x₀ hx₀))
  have hL := e.isLocalFrameOn_localFrame_baseSet I n (b.toBasis.map (e.linearEquivAt ℝ x₀ hx₀))
  have hLx₀ (j : Fin (2 * k)) : L j x₀ = b j := by
    simp [L, e.localFrame_apply_of_mem_baseSet _ hx₀, Trivialization.basisAt,
      e.symm_apply_apply_mk hx₀]
  -- The sections `u₀, J u₀, u₁, J u₁, …`, with `uᵢ` the even members of `L`.
  let u (i : Fin k) (y : M) : V y := L ⟨2 * i, by omega⟩ y
  let w (j : Fin (2 * k)) (y : M) : V y :=
    if (j : ℕ) % 2 = 0 then u ⟨j / 2, by omega⟩ y else J y (u ⟨j / 2, by omega⟩ y)
  have hw (j : Fin (2 * k)) : CMDiff[e.baseSet] n (T% (w j)) := by
    by_cases h : (j : ℕ) % 2 = 0
    · simpa only [w, h, ↓reduceIte] using hL.contMDiffOn _
    · simpa only [w, h, ↓reduceIte] using
        J.toEndomorphism.contMDiff.contMDiffOn.clm_bundle_apply (hL.contMDiffOn _)
  have hwx₀ (j : Fin (2 * k)) : w j x₀ = b j := by
    by_cases h : (j : ℕ) % 2 = 0
    · have hj : (⟨2 * (j / 2 : ℕ), by omega⟩ : Fin (2 * k)) = j := Fin.ext (by simp only; omega)
      simp only [w, u, h, ↓reduceIte, hj, hLx₀]
    · have hj : j = ⟨2 * (j / 2 : ℕ) + 1, by omega⟩ := Fin.ext (by simp only; omega)
      simp only [w, u, h, ↓reduceIte, hLx₀]
      rw [← hb ⟨(j : ℕ) / 2, by omega⟩, ← hj]
  -- The sections `w` stay linearly independent on an open neighbourhood `U` of `x₀`.
  have hcont : ContinuousAt (fun y ↦ fun j ↦ (e ⟨y, w j y⟩).2) x₀ := by
    refine continuousAt_pi.2 fun j ↦ ?_
    have hc := (hw j).continuousOn.continuousAt (e.open_baseSet.mem_nhds hx₀)
    exact ((e.toOpenPartialHomeomorph.continuousAt (e.mem_source.2 hx₀)).comp hc).snd
  have hli₀ : LinearIndependent ℝ (fun j ↦ (e ⟨x₀, w j x₀⟩).2) := by
    have h := b.toBasis.linearIndependent.map' _ (e.linearEquivAt ℝ x₀ hx₀).ker
    convert h using 2 with j
    simp [hwx₀, Trivialization.linearEquivAt_apply]
  obtain ⟨U, hUS, hU, hx₀U⟩ := mem_nhds_iff.1
    (inter_mem (e.open_baseSet.mem_nhds hx₀)
    (hcont.eventually hli₀.eventually))
  have hUe : U ⊆ e.baseSet := fun y hy ↦ (hUS hy).1
  have hli (y : M) (hy : y ∈ U) : LinearIndependent ℝ (fun j ↦ w j y) := by
    refine LinearIndependent.of_comp (e.linearMapAt ℝ y) ?_
    convert (hUS hy).2 using 1
    rw [e.coe_linearMapAt_of_mem (hUe hy)]
    rfl
  -- Their Gram–Schmidt orthonormalization `f` has the form `e₀, J e₀, e₁, J e₁, …`.
  set f : ∀ y, Fin (2 * k) → V y := fun y ↦ gramSchmidtNormed ℝ (fun j ↦ w j y)
  have horth (y : M) (hy : y ∈ U) : Orthonormal ℝ (f y) :=
    gramSchmidtNormed_orthonormal (hli y hy)
  have hrel (y : M) (i : Fin k) :
      f y ⟨2 * i + 1, by omega⟩ = J y (f y ⟨2 * i, by omega⟩) :=
    gramSchmidtNormed_two_mul_add_one (J := (J y : V y →L[ℝ] V y).toLinearMap) (hskew y)
      (hnorm y) (fun i ↦ u i y) i
  -- Reindexed by `Fin k × Fin 2`, the family `f` is the required frame.
  let E : Fin k × Fin 2 ≃ Fin (2 * k) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm k 2))
  have hE0 (i : Fin k) : E (i, 0) = ⟨2 * i, by omega⟩ := by
    ext; simp [E, finProdFinEquiv]
  have hE1 (i : Fin k) : E (i, 1) = ⟨2 * i + 1, by omega⟩ := by
    ext; simp [E, finProdFinEquiv]; omega
  have hs : IsLocalFrameOn I F n (fun p y ↦ f y (E p)) U :=
    { linearIndependent := fun {y} hy ↦ (horth y hy).linearIndependent.comp E E.injective
      generating := fun {y} hy ↦ ((horth y hy).linearIndependent.comp E
        E.injective).span_eq_top_of_card_eq_finrank' (by
          simp [VectorBundle.finrank_eq ℝ F V y, hk, Nat.mul_comm]) |>.ge
      contMDiffOn := fun p y hy ↦ ContMDiffWithinAt.gramSchmidtNormed_bundle (E p)
        (fun j _ ↦ (hw j).mono hUe y hy) ((hli y hy).linearIndepOn _) }
  refine ⟨U, hU, hx₀U, k, _, hs, fun y hy ↦ ?_⟩
  have hval (p : Fin k × Fin 2) : hs.toBasisAt hy p = f y (E p) := hs.toBasisAt_coe hy p
  refine hc.isDarbouxBasis_of_inner _ (fun p q ↦ ?_) fun i ↦ ?_
  · rw [hval, hval, ← g.inner_riemannianBundle, orthonormal_iff_ite.1 (horth y hy)]
    exact if_congr E.injective.eq_iff rfl rfl
  · rw [hval, hval, hE0, hE1, hrel]

variable [FiniteDimensional ℝ EB] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **Local Darboux frames.** Over a Hausdorff σ-compact base, for a nondegenerate `Cⁿ` two-form
`ω` on a bundle of finite rank, every point `x₀` has an open neighbourhood `U` with a `Cⁿ` local
frame `s : Fin k × Fin 2 → ∀ y, V y` on `U` that is a Darboux basis of `ω_y` at every `y ∈ U`. -/
theorem IsNondegenerate.exists_isLocalFrameOn_isDarbouxBasis (hω : ω.IsNondegenerate) (x₀ : M) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ ∃ (k : ℕ) (s : Fin k × Fin 2 → ∀ y, V y)
      (hs : IsLocalFrameOn I F n s U), ∀ y (hy : y ∈ U),
        (hω.symplecticFormAt y).IsDarbouxBasis (hs.toBasisAt hy) := by
  obtain ⟨J, hc⟩ := hω.exists_compatible
  exact hc.exists_isLocalFrameOn_isDarbouxBasis x₀

/-- **Local symplectic trivializations.** Over a Hausdorff σ-compact base, let `ω` be a
nondegenerate `Cⁿ` two-form on a bundle with finite-dimensional model fibre `F`, and `σ` a
symplectic form on `F`. Every point `x₀` lies in the base set of a linear trivialization `e` of
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

/-- **Local symplectic frames.** Over a Hausdorff σ-compact base, let `ω` be a nondegenerate `Cⁿ`
two-form on a bundle with finite-dimensional model fibre `F`, and `σ` a symplectic form on a
finite-dimensional normed space `W` with `dim W = dim F`. Every point `x₀` has an open
neighbourhood `U` with a symplectic frame `Φ` of `ω` for `σ` over `U`. -/
theorem IsNondegenerate.exists_isSymplecticFrameOn (hω : ω.IsNondegenerate) {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (σ : TauCeti.SymplecticForm W) (hW : finrank ℝ W = finrank ℝ F) (x₀ : M) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ ∃ Φ : ∀ x, W ≃L[ℝ] V x, ω.IsSymplecticFrameOn σ U Φ := by
  classical
  -- Move `σ` to `F`, and take a trivialization `e` that carries `ω` to it.
  set L := ContinuousLinearEquiv.ofFinrankEq hW
  obtain ⟨e, _, he, hx₀, hsymp⟩ :=
    hω.exists_trivialization_isSymplectomorphism (σ.transport L.toLinearEquiv) x₀
  -- Off the base set of `e`, the values of the frame play no role.
  let Φ (x : M) : W ≃L[ℝ] V x :=
    if hx : x ∈ e.baseSet then L.trans (e.continuousLinearEquivAt ℝ x hx).symm
    else L.trans ((trivializationAt F V x).continuousLinearEquivAt ℝ x
      (FiberBundle.mem_baseSet_trivializationAt' x)).symm
  have hΦ (x : M) (hx : x ∈ e.baseSet) (v : W) : Φ x v = e.symm x (L v) := by
    simp [Φ, hx]
  refine ⟨e.baseSet, e.open_baseSet, hx₀, Φ, ⟨fun p hp ↦ ?_, fun x hx v w ↦ ?_⟩⟩
  · have hp₁ : p.1 ∈ e.baseSet := hp.1
    rw [Trivialization.contMDiffWithinAt_iff_of_mem_maximalAtlas he (e.mem_source.2 hp₁)]
    refine ⟨contMDiffWithinAt_fst, ?_⟩
    have hL : ContMDiffWithinAt (I.prod 𝓘(ℝ, W)) 𝓘(ℝ, F) n (fun q : M × W ↦ L q.2)
        (e.baseSet ×ˢ univ) p :=
      (L.contDiff.contMDiff.comp contMDiff_snd).contMDiffAt.contMDiffWithinAt
    refine hL.congr (fun q hq ↦ ?_) ?_
    · rw [hΦ q.1 hq.1, e.apply_mk_symm hq.1]
    · rw [hΦ p.1 hp₁, e.apply_mk_symm hp₁]
  · have h := (hsymp x hx).apply (e.symm x (L v)) (e.symm x (L w))
    rw [Trivialization.linearEquivAt_apply, Trivialization.linearEquivAt_apply, e.apply_mk_symm hx,
      e.apply_mk_symm hx, IsNondegenerate.symplecticFormAt_apply, ← bilinFormAt_apply] at h
    rw [hΦ x hx v, hΦ x hx w, ← h]
    exact σ.transport_apply_apply L.toLinearEquiv v w

end ContMDiffTwoForm

end SymplecticGeometry.Bundle

end
