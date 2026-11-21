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
import SymplecticGeometry.Analysis.InnerProductSpace.GramSchmidtOrtho
import SymplecticGeometry.LinearAlgebra.Symplectic.Compatible
import SymplecticGeometry.Topology.VectorBundle.LinearIndependent
import TauCeti.Geometry.Symplectic.CompatibleMetric
import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt
import TauCeti.Geometry.Manifold.VectorBundle.MaximalAtlas
import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis
import TauCeti.LinearAlgebra.Complex.Orientation

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

The frame is built as in McDuff–Salamon, §2.6. For `ω` compatible with `J`, the bundle metric
`g(u, v) = ω(u, J v)` (`ContMDiffTwoForm.Compatible.metric`) makes `J` skew-adjoint and orthogonal
on each fibre, by Tau Ceti's lemmas on `TauCeti.SymplecticForm` for an inner product of the form
`ω(·, J ·)`. A `J`-adapted orthonormal basis `u₁, J u₁, …` of the fibre at the given
point (Tau Ceti's `TauCeti.AlmostComplexStructure.exists_adapted_orthonormalBasis`) is extended to
constant sections in a trivialization, and the sections `u₁, J u₁, u₂, J u₂, …` are
orthonormalized by Tau Ceti's smooth Gram–Schmidt (`ContMDiffWithinAt.gramSchmidtNormed_bundle`)
where they stay independent (`Bundle.Trivialization.eventually_linearIndependent`). Since `J` is
skew-adjoint and orthogonal for `g`, the output has the form `e₁, J e₁, e₂, J e₂, …`
(`InnerProductSpace.gramSchmidtNormed_eq_apply_gramSchmidtNormed`), and such an orthonormal
family is a Darboux basis of `ω` (`TauCeti.SymplecticForm.isDarbouxBasis_iff_apply_apply_eq_ite`).
The smooth Gram–Schmidt needs a linearly ordered index, so the frame is built on `Fin (2 * k)`
and reindexed to `Fin k × Fin 2`. The trivializations are Tau Ceti's frame trivializations
`IsLocalFrameOn.trivialization`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6,
  Exercise 2.6.2 and Theorem 2.6.3
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
  let : RiemannianBundle V := ⟨hc.metric.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle I n F V :=
    _root_.Bundle.instIsContMDiffRiemannianBundle hc.metric
  have := VectorBundle.finiteDimensional ℝ F V
  -- On each fibre, the inner product is the metric `ω_x(·, J_x ·)` of a linear compatible pair, so
  -- `J` is skew-adjoint and orthogonal.
  have hg (x : M) (u v : V x) :
      hc.isNondegenerate.symplecticFormAt x u (J.almostComplexStructureAt x v) = ⟪u, v⟫ := by
    rw [hc.symplecticFormAt_apply_apply_eq_metric_inner, hc.metric.inner_riemannianBundle]
  have hskew (x : M) (u v : V x) : ⟪J x u, v⟫ = -⟪u, J x v⟫ := by
    simpa using TauCeti.SymplecticForm.inner_apply_left_eq_neg_of_apply_apply_eq_inner (hg x) u v
  have hnorm (x : M) (v : V x) : ‖J x v‖ = ‖v‖ := by
    simpa using TauCeti.SymplecticForm.norm_apply_eq_norm_of_apply_apply_self_eq_inner
      (fun v ↦ hg x v v) v
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
  have hli₀ : LinearIndependent ℝ (fun j ↦ w j x₀) := by
    simpa only [hwx₀] using b.orthonormal.linearIndependent
  obtain ⟨U, hUS, hU, hx₀U⟩ := mem_nhds_iff.1 (inter_mem (e.open_baseSet.mem_nhds hx₀)
    (e.eventually_linearIndependent hx₀
      (fun j ↦ (hw j).continuousOn.continuousAt (e.open_baseSet.mem_nhds hx₀)) hli₀))
  have hUe : U ⊆ e.baseSet := fun y hy ↦ (hUS hy).1
  have hli (y : M) (hy : y ∈ U) : LinearIndependent ℝ (fun j ↦ w j y) := (hUS hy).2
  -- Their Gram–Schmidt orthonormalization `f` has the form `e₀, J e₀, e₁, J e₁, …`.
  set f : ∀ y, Fin (2 * k) → V y := fun y ↦ gramSchmidtNormed ℝ (fun j ↦ w j y)
  have horth (y : M) (hy : y ∈ U) : Orthonormal ℝ (f y) :=
    gramSchmidtNormed_orthonormal (hli y hy)
  have hrel (y : M) (i : Fin k) :
      f y ⟨2 * i + 1, by omega⟩ = J y (f y ⟨2 * i, by omega⟩) :=
    gramSchmidtNormed_two_mul_add_one (J := (J y : V y →L[ℝ] V y).toLinearMap) (hskew y)
      (hnorm y) (fun i ↦ u i y) i
  -- Reindexed by `Fin k × Fin 2`, the family `f` is the required frame.
  let E := TauCeti.complexRealIndexEquiv k
  have hs : IsLocalFrameOn I F n (fun p y ↦ f y (E p)) U :=
    { linearIndependent := fun {y} hy ↦ (horth y hy).linearIndependent.comp E E.injective
      generating := fun {y} hy ↦ ((horth y hy).linearIndependent.comp E
        E.injective).span_eq_top_of_card_eq_finrank' (by
          simp [VectorBundle.finrank_eq ℝ F V y, hk, Nat.mul_comm]) |>.ge
      contMDiffOn := fun p y hy ↦ ContMDiffWithinAt.gramSchmidtNormed_bundle (E p)
        (fun j _ ↦ (hw j).mono hUe y hy) ((hli y hy).linearIndepOn _) }
  refine ⟨U, hU, hx₀U, k, _, hs, fun y hy ↦ ?_⟩
  have hval (p : Fin k × Fin 2) : hs.toBasisAt hy p = f y (E p) := hs.toBasisAt_coe hy p
  -- An orthonormal basis of the form `(e₀, J e₀, e₁, J e₁, …)` is a Darboux basis.
  refine (TauCeti.SymplecticForm.isDarbouxBasis_iff_apply_apply_eq_ite
    (J := J.almostComplexStructureAt y) fun i ↦ ?_).2 fun p q ↦ ?_
  · have h₀ : E (i, 0) = ⟨2 * i, by omega⟩ := Fin.ext (by simp [E])
    have h₁ : E (i, 1) = ⟨2 * i + 1, by omega⟩ := Fin.ext (by simp [E])
    rw [ContMDiffComplexStructure.almostComplexStructureAt_apply, hval, hval, h₀, h₁, hrel]
  · rw [hg, hval, hval, orthonormal_iff_ite.1 (horth y hy)]
    exact if_congr E.injective.eq_iff rfl rfl

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
