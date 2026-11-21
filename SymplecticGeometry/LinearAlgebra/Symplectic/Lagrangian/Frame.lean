/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import SymplecticGeometry.LinearAlgebra.Matrix.OfReal
public import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Basic
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Constructions
public import TauCeti.Geometry.Symplectic.Lagrangian.TotallyReal
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic

/-!
# Lagrangian frames and graphs in the standard model

This file describes Lagrangian subspaces of the standard model `(StdSpace ι, ω₀)`, `ℝ²ⁿ` with
`ω₀ = ∑ dxᵢ ∧ dyᵢ`, by matrices, following McDuff–Salamon §2.3.

A *frame* is a real `2n × n` matrix `Z = fromRows X Y`, whose columns span the subspace
`range Z`. The *graphs* of a real `n × n` matrix `A` are the subspaces
`graph A = {(x, A x)}` and `graphY A = {(A y, y)}`.

## Main definitions

* `SymplecticGeometry.StdSpace.graph A`: the graph `{(x, A x)}` over the `x`-coordinates.
* `SymplecticGeometry.StdSpace.graphY A`: the graph `{(A y, y)}` over the `y`-coordinates.
* `SymplecticGeometry.LagrangianGrassmannian.ofFrame X Y`: the Lagrangian subspace spanned by a
  Lagrangian frame `fromRows X Y`.

## Main results

* `SymplecticGeometry.StdSpace.isCompl_graph_ker_x`, `isCompl_graphY_ker_y`: each graph is
  complementary to the coordinate subspace it is a graph over, and conversely
  `exists_eq_graph_of_isCompl_ker_x`, `exists_eq_graphY_of_isCompl_ker_y`.
* `SymplecticGeometry.StdSpace.map_symJ_graph`: the matrix `J` of `TauCeti.GLSymplectic.symJ`
  sends `graph A` to `graphY (-A)`.
* `SymplecticGeometry.StdSpace.map_realSubspace`, `map_lagrangianChart`,
  `SymplecticGeometry.stdForm_apply_eq_im_inner`: through `StdSpace.complexEuclideanEquiv`,
  Tau Ceti's `ℝⁿ ⊆ ℂⁿ` is the horizontal subspace `{y = 0}`, its chart subspace
  `Matrix.lagrangianChart S` is `graphY S`, and `ω₀` is `Im ⟪·, ·⟫`.
* `SymplecticGeometry.isLagrangian_range_fromRows_iff`: `fromRows X Y` spans a Lagrangian
  subspace iff it has rank `n` and `Xᵀ Y = Yᵀ X`.
* `SymplecticGeometry.isLagrangian_graph_iff`, `isLagrangian_graphY_iff`: a graph is Lagrangian
  iff its matrix is symmetric.
* `SymplecticGeometry.det_ne_zero_of_isLagrangian_range_fromRows`: the complex frame `X + i Y` of
  a Lagrangian frame is invertible.
* `SymplecticGeometry.exists_eq_graph_of_isCompl`, `exists_eq_graphY_of_isCompl`: a Lagrangian
  subspace transverse to `{x = 0}` (resp. `{y = 0}`) is `graph S` (resp. `graphY S`) for a
  symmetric `S`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3.
-/

public section

namespace SymplecticGeometry

open Matrix TauCeti Module

variable {ι : Type*} [Fintype ι]

/-! ### The two kinds of graph -/

namespace StdSpace

/-- The graph `{(x, A x)}` of a real square matrix `A`, as a subspace of `StdSpace ι`. -/
noncomputable def graph (A : Matrix ι ι ℝ) : Submodule ℝ (StdSpace ι) :=
  A.mulVecLin.graph.map (equivProd ι).symm.toLinearMap

theorem graph_def (A : Matrix ι ι ℝ) :
    graph A = A.mulVecLin.graph.map (equivProd ι).symm.toLinearMap :=
  (rfl)

@[simp]
theorem mem_graph_iff {A : Matrix ι ι ℝ} {z : StdSpace ι} : z ∈ graph A ↔ z.y = A *ᵥ z.x := by
  rw [graph_def, Submodule.mem_map_equiv]
  simp

/-- The graph `{(A y, y)}` of a real square matrix `A` over the `y`-coordinates, as a subspace
of `StdSpace ι`. -/
noncomputable def graphY (A : Matrix ι ι ℝ) : Submodule ℝ (StdSpace ι) :=
  A.mulVecLin.graph.map
    ((LinearEquiv.prodComm ℝ (ι → ℝ) (ι → ℝ)).trans (equivProd ι).symm).toLinearMap

theorem graphY_def (A : Matrix ι ι ℝ) :
    graphY A = A.mulVecLin.graph.map
      ((LinearEquiv.prodComm ℝ (ι → ℝ) (ι → ℝ)).trans (equivProd ι).symm).toLinearMap :=
  (rfl)

@[simp]
theorem mem_graphY_iff {A : Matrix ι ι ℝ} {z : StdSpace ι} :
    z ∈ graphY A ↔ z.x = A *ᵥ z.y := by
  rw [graphY_def, Submodule.mem_map_equiv]
  simp

/-- A matrix is determined by its graph. -/
theorem graph_injective : Function.Injective (graph : Matrix ι ι ℝ → Submodule ℝ (StdSpace ι)) := by
  intro A B h
  refine mulVec_injective (funext fun v ↦ ?_)
  have hv : (equivProd ι).symm (v, A *ᵥ v) ∈ graph B := h ▸ mem_graph_iff.2 (by simp)
  simpa using mem_graph_iff.1 hv

/-- A matrix is determined by its graph over the `y`-coordinates. -/
theorem graphY_injective :
    Function.Injective (graphY : Matrix ι ι ℝ → Submodule ℝ (StdSpace ι)) := by
  intro A B h
  refine mulVec_injective (funext fun v ↦ ?_)
  have hv : (equivProd ι).symm (A *ᵥ v, v) ∈ graphY B := h ▸ mem_graphY_iff.2 (by simp)
  simpa using mem_graphY_iff.1 hv

/-- Every graph `{(x, A x)}` is complementary to the vertical subspace `{x = 0}`. -/
theorem isCompl_graph_ker_x (A : Matrix ι ι ℝ) : IsCompl (graph A) (LinearMap.ker x) := by
  refine ⟨Submodule.disjoint_def.2 fun z hz hx ↦ ?_, Submodule.codisjoint_iff_exists_add_eq.2
    fun z ↦ ⟨(equivProd ι).symm (z.x, A *ᵥ z.x), z - (equivProd ι).symm (z.x, A *ᵥ z.x),
      by simp, by simp, by abel⟩⟩
  rw [LinearMap.mem_ker] at hx
  rw [mem_graph_iff, hx, mulVec_zero] at hz
  exact StdSpace.ext (by simpa using hx) (by simpa using hz)

/-- Every graph `{(A y, y)}` is complementary to the horizontal subspace `{y = 0}`. -/
theorem isCompl_graphY_ker_y (A : Matrix ι ι ℝ) : IsCompl (graphY A) (LinearMap.ker y) := by
  refine ⟨Submodule.disjoint_def.2 fun z hz hy ↦ ?_, Submodule.codisjoint_iff_exists_add_eq.2
    fun z ↦ ⟨(equivProd ι).symm (A *ᵥ z.y, z.y), z - (equivProd ι).symm (A *ᵥ z.y, z.y),
      by simp, by simp, by abel⟩⟩
  rw [LinearMap.mem_ker] at hy
  rw [mem_graphY_iff, hy, mulVec_zero] at hz
  exact StdSpace.ext (by simpa using hz) (by simpa using hy)

/-- A subspace complementary to the kernel of the first coordinate of `e⁻¹` is the image under
`e` of a graph `{(v, A v)}`. -/
private theorem exists_eq_map_graph_of_isCompl (e : ((ι → ℝ) × (ι → ℝ)) ≃ₗ[ℝ] StdSpace ι)
    {L : Submodule ℝ (StdSpace ι)}
    (hL : IsCompl L (LinearMap.ker (LinearMap.fst ℝ (ι → ℝ) (ι → ℝ) ∘ₗ e.symm.toLinearMap))) :
    ∃ A : Matrix ι ι ℝ, L = A.mulVecLin.graph.map e.toLinearMap := by
  classical
  set p := LinearMap.fst ℝ (ι → ℝ) (ι → ℝ) ∘ₗ e.symm.toLinearMap
  -- the first coordinate is bijective from `L` onto `ι → ℝ`
  have hinj : Function.Injective (p ∘ₗ L.subtype) := by
    refine (injective_iff_map_eq_zero _).2 fun z hz ↦ Subtype.ext ?_
    exact Submodule.disjoint_def.1 hL.disjoint z z.property hz
  have hsurj : Function.Surjective (p ∘ₗ L.subtype) := fun a ↦ by
    obtain ⟨l, k, hl, hk, hlk⟩ := Submodule.codisjoint_iff_exists_add_eq.1 hL.codisjoint (e (a, 0))
    refine ⟨⟨l, hl⟩, ?_⟩
    have := congrArg p hlk
    rw [map_add, LinearMap.mem_ker.1 hk, add_zero] at this
    simpa [p] using this
  have hbij : Function.Bijective (Prod.fst ∘ (L.map e.symm.toLinearMap).subtype) := by
    rw [← Function.Bijective.of_comp_iff _ (e.symm.submoduleMap L).bijective]
    exact ⟨hinj, hsurj⟩
  obtain ⟨f, hf⟩ := Submodule.exists_eq_graph hbij
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
  exact ((Submodule.map_symm_eq_iff e).1 hf).symm

/-- A subspace complementary to the vertical subspace `{x = 0}` is a graph `{(x, A x)}`. -/
theorem exists_eq_graph_of_isCompl_ker_x {L : Submodule ℝ (StdSpace ι)}
    (hL : IsCompl L (LinearMap.ker x)) : ∃ A : Matrix ι ι ℝ, L = graph A :=
  exists_eq_map_graph_of_isCompl (equivProd ι).symm (by convert hL using 2; ext; simp)

/-- A subspace complementary to the horizontal subspace `{y = 0}` is a graph `{(A y, y)}`. -/
theorem exists_eq_graphY_of_isCompl_ker_y {L : Submodule ℝ (StdSpace ι)}
    (hL : IsCompl L (LinearMap.ker y)) : ∃ A : Matrix ι ι ℝ, L = graphY A :=
  exists_eq_map_graph_of_isCompl
    ((LinearEquiv.prodComm ℝ (ι → ℝ) (ι → ℝ)).trans (equivProd ι).symm)
    (by convert hL using 2; ext; simp)

/-- The matrix `J = !![0, -1; 1, 0]` of `TauCeti.GLSymplectic.symJ`, which maps `(x, y)` to
`(-y, x)`, sends the graph `{(x, A x)}` to the graph `{(-A y, y)}`. -/
theorem map_symJ_graph [DecidableEq ι] (A : Matrix ι ι ℝ) :
    (graph A).map
        (toEuclideanLin ((GLSymplectic.symJ ι ℝ : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)) =
      graphY (-A) := by
  rw [GLSymplectic.coe_symJ, ← stdComplexStructure_eq_toEuclideanLin_J]
  ext z
  simp only [Submodule.mem_map, mem_graph_iff, mem_graphY_iff, neg_mulVec]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simp [hw]
  · intro hz
    refine ⟨(equivProd ι).symm (y z, -x z), by simp [hz], StdSpace.ext ?_ ?_⟩ <;> simp

/-! ### Comparison with the complex picture -/

/-- The real subspace `ℝⁿ ⊆ ℂⁿ` is the horizontal subspace `{y = 0}` of `StdSpace ι`. -/
theorem map_realSubspace :
    (realSubspace ι).map (complexEuclideanEquiv ι : EuclideanSpace ℂ ι →ₗ[ℝ] StdSpace ι) =
      LinearMap.ker y :=
  (Submodule.map_symm_eq_iff (complexEuclideanEquiv ι).toLinearEquiv).1 (by
    rw [← Submodule.comap_equiv_eq_map_symm]
    ext v
    simp [funext_iff])

/-- Tau Ceti's chart subspace `{S y + i y}` of `ℂⁿ` is the graph `{(S y, y)}` in
`StdSpace ι`. -/
theorem map_lagrangianChart [DecidableEq ι] (S : Matrix ι ι ℝ) :
    S.lagrangianChart.map (complexEuclideanEquiv ι : EuclideanSpace ℂ ι →ₗ[ℝ] StdSpace ι) =
      graphY S :=
  (Submodule.map_symm_eq_iff (complexEuclideanEquiv ι).toLinearEquiv).1 (by
    rw [← Submodule.comap_equiv_eq_map_symm]
    ext v
    simp [funext_iff, mem_lagrangianChart, mulVec, dotProduct])

end StdSpace

open StdSpace

/-- Through `StdSpace.complexEuclideanEquiv`, the standard symplectic form is the imaginary part
of the Hermitian inner product of `ℂⁿ`: `ω₀(v, w) = Im ⟪v, w⟫`. -/
theorem stdForm_apply_eq_im_inner (v w : EuclideanSpace ℂ ι) :
    stdForm ι (complexEuclideanEquiv ι v) (complexEuclideanEquiv ι w) = (inner ℂ v w).im := by
  simp only [stdForm_apply, x_complexEuclideanEquiv, y_complexEuclideanEquiv]
  simp [PiLp.inner_apply, Complex.im_sum, mul_comm, sub_eq_add_neg, add_comm]

/-! ### Graphs are Lagrangian exactly for symmetric matrices -/

/-- A graph `{e (v, A v)}`, for a linear identification `e` under which `ω₀` is a nonzero
multiple of the standard pairing of `(ι → ℝ) × (ι → ℝ)`, is Lagrangian iff `A` is symmetric. -/
private theorem isLagrangian_map_graph_iff (e : ((ι → ℝ) × (ι → ℝ)) ≃ₗ[ℝ] StdSpace ι) {c : ℝ}
    (hc : c ≠ 0) (he : ∀ p q, stdForm ι (e p) (e q) = c * (q.2 ⬝ᵥ p.1 - p.2 ⬝ᵥ q.1))
    (A : Matrix ι ι ℝ) :
    (stdForm ι).IsLagrangian (A.mulVecLin.graph.map e.toLinearMap) ↔ A.IsSymm := by
  classical
  rw [← SymplecticForm.transport_transport_symm (stdForm ι) e,
    SymplecticForm.isLagrangian_map_transport_iff,
    SymplecticForm.isLagrangian_graph_iff_of_pairing _ (fun d v ↦ c * (d ⬝ᵥ v))
      (fun p q ↦ by simp [he, mul_sub]),
    ← isSymm_toBilin'_iff_isSymm, LinearMap.BilinForm.isSymm_def]
  simp only [mul_right_inj' hc, toBilin'_apply', mulVecLin_apply, dotProduct_comm (A *ᵥ _)]
  exact forall_comm

/-- The graph `{(x, A x)}` is Lagrangian iff `A` is symmetric. -/
theorem isLagrangian_graph_iff (A : Matrix ι ι ℝ) :
    (stdForm ι).IsLagrangian (graph A) ↔ A.IsSymm :=
  isLagrangian_map_graph_iff _ one_ne_zero (fun ⟨a, b⟩ ⟨a', b'⟩ ↦ by
    simp only [stdForm_apply, x_equivProd_symm, y_equivProd_symm]
    simp [dotProduct, ← Finset.sum_sub_distrib, mul_comm]) A

/-- The graph `{(A y, y)}` is Lagrangian iff `A` is symmetric. -/
theorem isLagrangian_graphY_iff (A : Matrix ι ι ℝ) :
    (stdForm ι).IsLagrangian (graphY A) ↔ A.IsSymm :=
  isLagrangian_map_graph_iff _ (neg_ne_zero.2 one_ne_zero) (fun ⟨a, b⟩ ⟨a', b'⟩ ↦ by
    simp [dotProduct, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib, mul_comm]) A

/-- A Lagrangian subspace transverse to the vertical subspace `{x = 0}` is the graph
`{(x, S x)}` of a symmetric matrix `S`. -/
theorem exists_eq_graph_of_isCompl {L : Submodule ℝ (StdSpace ι)}
    (hL : (stdForm ι).IsLagrangian L) (h : IsCompl L (LinearMap.ker x)) :
    ∃ S : Matrix ι ι ℝ, S.IsSymm ∧ L = graph S :=
  let ⟨S, hS⟩ := exists_eq_graph_of_isCompl_ker_x h
  ⟨S, (isLagrangian_graph_iff S).1 (hS ▸ hL), hS⟩

/-- A Lagrangian subspace transverse to the horizontal subspace `{y = 0}` is the graph
`{(S y, y)}` of a symmetric matrix `S`. -/
theorem exists_eq_graphY_of_isCompl {L : Submodule ℝ (StdSpace ι)}
    (hL : (stdForm ι).IsLagrangian L) (h : IsCompl L (LinearMap.ker y)) :
    ∃ S : Matrix ι ι ℝ, S.IsSymm ∧ L = graphY S :=
  let ⟨S, hS⟩ := exists_eq_graphY_of_isCompl_ker_y h
  ⟨S, (isLagrangian_graphY_iff S).1 (hS ▸ hL), hS⟩

/-! ### Lagrangian frames -/

section Frame

variable [DecidableEq ι]

/-- The `x`-coordinates of `fromRows X Y` applied to `u` are `X u`. -/
@[simp]
theorem StdSpace.x_toEuclideanLin_fromRows (X Y : Matrix ι ι ℝ) (u : EuclideanSpace ℝ ι) :
    x (toEuclideanLin (fromRows X Y) u) = X *ᵥ u := by
  ext i
  simp [fromRows_mulVec]

/-- The `y`-coordinates of `fromRows X Y` applied to `u` are `Y u`. -/
@[simp]
theorem StdSpace.y_toEuclideanLin_fromRows (X Y : Matrix ι ι ℝ) (u : EuclideanSpace ℝ ι) :
    y (toEuclideanLin (fromRows X Y) u) = Y *ᵥ u := by
  ext i
  simp [fromRows_mulVec]

/-- The standard form on the columns of a frame: `ω₀(Z u, Z v) = uᵀ (Xᵀ Y - Yᵀ X) v` for
`Z = fromRows X Y`. -/
theorem stdForm_toEuclideanLin_fromRows (X Y : Matrix ι ι ℝ) (u v : EuclideanSpace ℝ ι) :
    stdForm ι (toEuclideanLin (fromRows X Y) u) (toEuclideanLin (fromRows X Y) v) =
      u ⬝ᵥ ((Xᵀ * Y - Yᵀ * X) *ᵥ v) := by
  rw [stdForm_apply, Finset.sum_sub_distrib, sub_mulVec, dotProduct_sub,
    ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec _ Xᵀ, dotProduct_mulVec _ Yᵀ,
    vecMul_transpose, vecMul_transpose]
  simp [dotProduct]

/-- The span of a frame `fromRows X Y` is isotropic iff `Xᵀ Y = Yᵀ X`. -/
theorem isIsotropic_range_fromRows_iff (X Y : Matrix ι ι ℝ) :
    (stdForm ι).IsIsotropic (LinearMap.range (toEuclideanLin (fromRows X Y))) ↔
      Xᵀ * Y = Yᵀ * X := by
  rw [SymplecticForm.isIsotropic_iff]
  simp only [LinearMap.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
    stdForm_toEuclideanLin_fromRows]
  refine ⟨fun h ↦ ?_, fun h u v ↦ by simp [h]⟩
  rw [← sub_eq_zero]
  ext i j
  simpa using h (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

/-- **Lagrangian frames.** The columns of `Z = fromRows X Y` span a Lagrangian subspace of
`(StdSpace ι, ω₀)` iff `Z` has rank `n` and `Xᵀ Y = Yᵀ X`. -/
theorem isLagrangian_range_fromRows_iff (X Y : Matrix ι ι ℝ) :
    (stdForm ι).IsLagrangian (LinearMap.range (toEuclideanLin (fromRows X Y))) ↔
      (fromRows X Y).rank = Fintype.card ι ∧ Xᵀ * Y = Yᵀ * X := by
  rw [SymplecticForm.isLagrangian_iff_isIsotropic_and_two_mul_finrank_eq,
    isIsotropic_range_fromRows_iff, finrank_stdSpace, rank_eq_finrank_range_toEuclideanLin]
  exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨Nat.eq_of_mul_eq_mul_left two_pos h₂, h₁⟩,
    fun ⟨h₁, h₂⟩ ↦ ⟨h₂, congrArg (2 * ·) h₁⟩⟩

/-- The Lagrangian subspace spanned by the columns of a Lagrangian frame `fromRows X Y`, one of
rank `n` with `Xᵀ Y = Yᵀ X`. -/
noncomputable def LagrangianGrassmannian.ofFrame (X Y : Matrix ι ι ℝ)
    (hrank : (fromRows X Y).rank = Fintype.card ι) (hXY : Xᵀ * Y = Yᵀ * X) :
    LagrangianGrassmannian (stdForm ι) :=
  ⟨LinearMap.range (toEuclideanLin (fromRows X Y)),
    (isLagrangian_range_fromRows_iff X Y).2 ⟨hrank, hXY⟩⟩

@[simp]
theorem LagrangianGrassmannian.coe_ofFrame (X Y : Matrix ι ι ℝ)
    (hrank : (fromRows X Y).rank = Fintype.card ι) (hXY : Xᵀ * Y = Yᵀ * X) :
    (ofFrame X Y hrank hXY : Submodule ℝ (StdSpace ι)) =
      LinearMap.range (toEuclideanLin (fromRows X Y)) :=
  (rfl)

/-- The complex frame `X + i Y` of a Lagrangian frame `fromRows X Y` is invertible. -/
theorem det_ne_zero_of_isLagrangian_range_fromRows {X Y : Matrix ι ι ℝ}
    (h : (stdForm ι).IsLagrangian (LinearMap.range (toEuclideanLin (fromRows X Y)))) :
    (X.map Complex.ofReal + Complex.I • Y.map Complex.ofReal).det ≠ 0 := by
  set e := (complexEuclideanEquiv ι).toLinearEquiv with e_def
  have he : (stdComplexStructure ι).toLinearMap ∘ₗ e.toLinearMap =
      e.toLinearMap ∘ₗ (LinearMap.lsmul ℂ (EuclideanSpace ℂ ι) Complex.I).restrictScalars ℝ :=
    LinearMap.ext fun v ↦ stdComplexStructure_complexEuclideanEquiv v
  have hrange : LinearMap.range (toEuclideanLin (fromRows X Y)) =
      (X.map Complex.ofReal + Complex.I • Y.map Complex.ofReal).realImage.map e.toLinearMap := by
    rw [range_toEuclideanLin_fromRows, e_def, complexEuclideanEquiv_def,
      ContinuousLinearEquiv.trans_toLinearEquiv, LinearEquiv.coe_trans]
  have hJ := h.isMaximalTotallyReal_of_compatible stdForm_compatible
  rw [hrange, e.isMaximalTotallyReal_map_iff he] at hJ
  exact isMaximalTotallyReal_realImage_iff.1 hJ

end Frame

end SymplecticGeometry

end
