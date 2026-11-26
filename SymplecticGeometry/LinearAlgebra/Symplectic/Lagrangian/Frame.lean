/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Basic
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Constructions
public import TauCeti.Geometry.Symplectic.Lagrangian.TotallyReal
public import TauCeti.LinearAlgebra.Matrix.Rank
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic
public import TauCeti.LinearAlgebra.Prod
public import TauCeti.LinearAlgebra.TotallyReal.Euclidean
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import SymplecticGeometry.LinearAlgebra.Matrix.OfReal
import SymplecticGeometry.LinearAlgebra.Matrix.Rank
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Matrix
import SymplecticGeometry.LinearAlgebra.Symplectic.Subspace
import Mathlib.RingTheory.Flat.TorsionFree

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
* `SymplecticGeometry.LagrangianGrassmannian.ofFrame X Y h`: the Lagrangian subspace spanned by
  the Lagrangian frame `fromRows X Y`.

## Main results

* `SymplecticGeometry.StdSpace.range_toEuclideanLin_fromRows_eq_map_realImage`: the span of
  `fromRows X Y` is the real image of its complex frame `X + i Y`, carried to `StdSpace ι`;
  `map_realImage`: the real image of a complex matrix `A` is the image of `{y = 0}` under the
  realification of `A`.
* `SymplecticGeometry.StdSpace.graph_zero`, `graphY_zero`: the graphs of `0` are the coordinate
  subspaces `{y = 0}` and `{x = 0}`.
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
* `SymplecticGeometry.isLagrangian_map_swap_iff`: the coordinate swap preserves and reflects
  Lagrangian subspaces.
* `SymplecticGeometry.isLagrangian_graph_iff`, `isLagrangian_graphY_iff`: a graph is Lagrangian
  iff its matrix is symmetric; `isLagrangian_range_fromRows_one`: so `fromRows A 1` is a
  Lagrangian frame for symmetric `A`.
* `SymplecticGeometry.LagrangianGrassmannian.finrank_eq_card`: a Lagrangian subspace of
  `StdSpace ι` has dimension `Fintype.card ι`; `injective_toEuclideanLin_of_range_eq`: so a
  real matrix whose columns span a Lagrangian subspace is injective, and
  `isUnit_of_range_mul_eq`: if `Z * g` is such a matrix, then `g` is invertible.
* `SymplecticGeometry.det_ne_zero_of_isLagrangian_range_fromRows`: the complex frame `X + i Y` of
  a Lagrangian frame is invertible.
* `SymplecticGeometry.exists_eq_graph_of_isCompl`, `exists_eq_graphY_of_isCompl`: a Lagrangian
  subspace transverse to `{x = 0}` (resp. `{y = 0}`) is `graph S` (resp. `graphY S`) for a
  symmetric `S`.
* `SymplecticGeometry.StdSpace.range_toEuclideanLin_fromRows_one_eq_graph`,
  `range_toEuclideanLin_fromRows_one_eq_graphY`: `fromRows 1 A` spans `graph A`, and
  `fromRows A 1` spans `graphY A`; `map_swap_range_toEuclideanLin_fromRows`: the swap carries
  the span of `fromRows X Y` to that of `fromRows Y X`.
* `SymplecticGeometry.StdSpace.disjoint_range_toEuclideanLin_fromRows_ker_y_iff`,
  `range_toEuclideanLin_fromRows_eq_graphY`: a frame `fromRows X Y` of full rank spans a subspace
  transverse to `{y = 0}` iff `Y` is invertible, and then it spans `graphY (X Y⁻¹)`;
  `disjoint_range_toEuclideanLin_fromRows_ker_y_iff_of_isLagrangian`: the same for a Lagrangian
  frame; `disjoint_range_toEuclideanLin_fromRows_ker_x_iff_of_isLagrangian`: a Lagrangian frame
  spans a subspace transverse to `{x = 0}` iff `X` is invertible.
* `SymplecticGeometry.StdSpace.range_toEuclideanLin_fromRows_eq_graph`: if `X` is invertible,
  the frame `fromRows X Y` spans `graph (Y X⁻¹)`.

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
  (graph A).map (swap ι : StdSpace ι →ₗ[ℝ] StdSpace ι)

theorem graphY_def (A : Matrix ι ι ℝ) :
    graphY A = (graph A).map (swap ι : StdSpace ι →ₗ[ℝ] StdSpace ι) :=
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

/-- The graph `{(x, 0)}` of the zero matrix is the horizontal subspace `{y = 0}`. -/
@[simp]
theorem graph_zero : graph (0 : Matrix ι ι ℝ) = LinearMap.ker y := by
  ext z
  simp

/-- The graph `{(0, y)}` of the zero matrix over the `y`-coordinates is the vertical subspace
`{x = 0}`. -/
@[simp]
theorem graphY_zero : graphY (0 : Matrix ι ι ℝ) = LinearMap.ker x := by
  ext z
  simp

/-- Every graph `{(x, A x)}` is complementary to the vertical subspace `{x = 0}`. This is
`LinearMap.isCompl_graph_ker_fst` carried to `StdSpace ι` by `equivProd`. -/
theorem isCompl_graph_ker_x (A : Matrix ι ι ℝ) : IsCompl (graph A) (LinearMap.ker x) := by
  convert Submodule.isCompl_map (equivProd ι).symm (LinearMap.isCompl_graph_ker_fst A.mulVecLin)
    <;> ext z <;> simp [Submodule.mem_map_equiv]

/-- A matrix is determined by its graph over the `y`-coordinates. -/
theorem graphY_injective :
    Function.Injective (graphY : Matrix ι ι ℝ → Submodule ℝ (StdSpace ι)) := by
  simpa only [Function.comp_def, ← graphY_def] using
    (Submodule.map_injective_of_injective (swap ι).injective).comp graph_injective

/-- Every graph `{(A y, y)}` is complementary to the horizontal subspace `{y = 0}`. -/
theorem isCompl_graphY_ker_y (A : Matrix ι ι ℝ) : IsCompl (graphY A) (LinearMap.ker y) := by
  simpa [← graphY_def] using (Submodule.orderIsoMapComap (swap ι)).isCompl (isCompl_graph_ker_x A)

/-- A subspace complementary to the vertical subspace `{x = 0}` is a graph `{(x, A x)}`. -/
theorem exists_eq_graph_of_isCompl_ker_x {L : Submodule ℝ (StdSpace ι)}
    (hL : IsCompl L (LinearMap.ker x)) : ∃ A : Matrix ι ι ℝ, L = graph A := by
  classical
  -- the first coordinate is bijective from `L` onto `ι → ℝ`
  have hinj : Function.Injective (x ∘ₗ L.subtype) := by
    refine (injective_iff_map_eq_zero _).2 fun z hz ↦ Subtype.ext ?_
    exact Submodule.disjoint_def.1 hL.disjoint z z.property hz
  have hsurj : Function.Surjective (x ∘ₗ L.subtype) := fun a ↦ by
    obtain ⟨l, k, hl, hk, hlk⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.1 hL.codisjoint ((equivProd ι).symm (a, 0))
    refine ⟨⟨l, hl⟩, ?_⟩
    have := congrArg x hlk
    rw [map_add, LinearMap.mem_ker.1 hk, add_zero] at this
    simpa using this
  have hbij : Function.Bijective (Prod.fst ∘ (L.map (equivProd ι).toLinearMap).subtype) := by
    rw [← Function.Bijective.of_comp_iff _ ((equivProd ι).submoduleMap L).bijective]
    rw [x_def] at hinj hsurj
    exact ⟨hinj, hsurj⟩
  obtain ⟨f, hf⟩ := Submodule.exists_eq_graph hbij
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  rw [graph_def, ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
  exact ((Submodule.map_symm_eq_iff (equivProd ι).symm).1 hf).symm

/-- A subspace complementary to the horizontal subspace `{y = 0}` is a graph `{(A y, y)}`. -/
theorem exists_eq_graphY_of_isCompl_ker_y {L : Submodule ℝ (StdSpace ι)}
    (hL : IsCompl L (LinearMap.ker y)) : ∃ A : Matrix ι ι ℝ, L = graphY A := by
  obtain ⟨A, hA⟩ := exists_eq_graph_of_isCompl_ker_x
    (by simpa [map_swap_ker_y] using (Submodule.orderIsoMapComap (swap ι)).isCompl hL)
  exact ⟨A, by rw [graphY_def, ← symm_swap, eq_comm, Submodule.map_symm_eq_iff, hA]⟩

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

/-- The column space of a frame `fromRows X Y` is the real image `(X + i Y) ℝⁿ ⊆ ℂⁿ` of its
complex frame, carried to `StdSpace ι` by `StdSpace.complexEuclideanEquiv`. -/
theorem range_toEuclideanLin_fromRows_eq_map_realImage [DecidableEq ι] (X Y : Matrix ι ι ℝ) :
    LinearMap.range (toEuclideanLin (fromRows X Y)) =
      (X.map Complex.ofReal + Complex.I • Y.map Complex.ofReal).realImage.map
        (complexEuclideanEquiv ι : EuclideanSpace ℂ ι →ₗ[ℝ] StdSpace ι) := by
  rw [range_toEuclideanLin_fromRows, complexEuclideanEquiv_def,
    ContinuousLinearEquiv.trans_toLinearEquiv, LinearEquiv.coe_trans]

/-- Through `StdSpace.complexEuclideanEquiv`, the real image `A ℝⁿ` of a complex matrix is the
image of the horizontal subspace `{y = 0}` under its realification. -/
theorem map_realImage [DecidableEq ι] (A : Matrix ι ι ℂ) :
    A.realImage.map (complexEuclideanEquiv ι : EuclideanSpace ℂ ι →ₗ[ℝ] StdSpace ι) =
      (LinearMap.ker y).map (toEuclideanLin A.realify) := by
  ext z
  simp only [Submodule.mem_map, mem_realImage, ← map_realSubspace]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨_, ⟨w, hw, rfl⟩, (complexEuclideanEquiv_toEuclideanCLM A w).symm⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨_, ⟨w, hw, rfl⟩, complexEuclideanEquiv_toEuclideanCLM A w⟩


end StdSpace

open StdSpace

/-- Through `StdSpace.complexEuclideanEquiv`, the standard symplectic form is the imaginary part
of the Hermitian inner product of `ℂⁿ`: `ω₀(v, w) = Im ⟪v, w⟫`. -/
theorem stdForm_apply_eq_im_inner (v w : EuclideanSpace ℂ ι) :
    stdForm ι (complexEuclideanEquiv ι v) (complexEuclideanEquiv ι w) = (inner ℂ v w).im := by
  rw [← imInnerSymplecticForm_apply, imInnerSymplecticForm_euclideanSpace_apply]
  simp [complexEuclideanEquiv_def]

/-! ### Graphs are Lagrangian exactly for symmetric matrices -/

/-- The coordinate swap `(x, y) ↦ (y, x)` preserves and reflects Lagrangian subspaces of `ω₀`:
it carries `ω₀` to `-ω₀`, which has the same Lagrangian subspaces. -/
@[simp]
theorem isLagrangian_map_swap_iff {L : Submodule ℝ (StdSpace ι)} :
    (stdForm ι).IsLagrangian (L.map (swap ι : StdSpace ι →ₗ[ℝ] StdSpace ι)) ↔
      (stdForm ι).IsLagrangian L :=
  SymplecticForm.isLagrangian_map_iff_of_apply_eq_mul (swap ι) (c := -1) (by norm_num) fun z w ↦ by
    rw [stdForm_swap, neg_one_mul]

/-- The graph `{(x, A x)}` is Lagrangian iff `A` is symmetric. -/
theorem isLagrangian_graph_iff (A : Matrix ι ι ℝ) :
    (stdForm ι).IsLagrangian (graph A) ↔ A.IsSymm := by
  classical
  have he : ∀ p q : (ι → ℝ) × (ι → ℝ), stdForm ι ((equivProd ι).symm p) ((equivProd ι).symm q) =
      q.2 ⬝ᵥ p.1 - p.2 ⬝ᵥ q.1 := fun ⟨a, b⟩ ⟨a', b'⟩ ↦ by
    simp only [stdForm_apply, x_equivProd_symm, y_equivProd_symm]
    simp [dotProduct, ← Finset.sum_sub_distrib, mul_comm]
  rw [graph_def, ← SymplecticForm.transport_transport_symm (stdForm ι) (equivProd ι).symm,
    SymplecticForm.isLagrangian_map_transport_iff,
    SymplecticForm.isLagrangian_graph_iff_of_pairing _ (fun d v ↦ d ⬝ᵥ v)
      (fun p q ↦ by simp [he]),
    ← isSymm_toBilin'_iff_isSymm, LinearMap.BilinForm.isSymm_def]
  simp only [toBilin'_apply', mulVecLin_apply, dotProduct_comm (A *ᵥ _)]
  exact forall_comm

/-- The graph `{(A y, y)}` is Lagrangian iff `A` is symmetric. -/
theorem isLagrangian_graphY_iff (A : Matrix ι ι ℝ) :
    (stdForm ι).IsLagrangian (graphY A) ↔ A.IsSymm := by
  rw [graphY_def, isLagrangian_map_swap_iff, isLagrangian_graph_iff]

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

/-- A Lagrangian subspace of the standard model `StdSpace ι` has dimension `Fintype.card ι`, half
the dimension of `StdSpace ι`. -/
theorem LagrangianGrassmannian.finrank_eq_card (Λ : LagrangianGrassmannian (stdForm ι)) :
    finrank ℝ (Λ : Submodule ℝ (StdSpace ι)) = Fintype.card ι := by
  have h := Λ.isLagrangian.two_mul_finrank
  rw [finrank_stdSpace] at h
  omega

section Frame

variable [DecidableEq ι]

/-- A real `2n × n` matrix whose columns span a Lagrangian subspace is injective. -/
theorem LagrangianGrassmannian.injective_toEuclideanLin_of_range_eq
    {Λ : LagrangianGrassmannian (stdForm ι)} {Z : Matrix (ι ⊕ ι) ι ℝ}
    (hZ : LinearMap.range (toEuclideanLin Z) = Λ) : Function.Injective (toEuclideanLin Z) := by
  have h := LinearMap.finrank_range_add_finrank_ker (toEuclideanLin Z)
  rw [hZ, finrank_eq_card, finrank_euclideanSpace] at h
  exact LinearMap.ker_eq_bot.1 (Submodule.finrank_eq_zero.1 (by omega))

/-- A change of frame `g` that keeps `Z * g` a frame of a Lagrangian subspace is invertible. -/
theorem LagrangianGrassmannian.isUnit_of_range_mul_eq {Λ : LagrangianGrassmannian (stdForm ι)}
    {Z : Matrix (ι ⊕ ι) ι ℝ} {g : Matrix ι ι ℝ}
    (h : LinearMap.range (toEuclideanLin (Z * g)) = Λ) : IsUnit g := by
  have hinj := injective_toEuclideanLin_of_range_eq h
  rw [toLpLin_mul_same, LinearMap.coe_comp] at hinj
  refine mulVec_injective_iff_isUnit.1 fun u v huv ↦ ?_
  simpa using hinj.of_comp (a₁ := WithLp.toLp 2 u) (a₂ := WithLp.toLp 2 v)
    (by simp [toLpLin_apply, huv])

/-- Two real frames of one Lagrangian subspace differ by an invertible change of frame: if the
columns of `Z₁` and of `Z₂` both span `Λ`, then `Z₂ * g = Z₁` for some `g : GL ι ℝ`. The converse
is `Matrix.range_toLpLin_mul_of_isUnit`. -/
theorem LagrangianGrassmannian.exists_mul_eq_of_range_eq
    {Λ : LagrangianGrassmannian (stdForm ι)} {Z₁ Z₂ : Matrix (ι ⊕ ι) ι ℝ}
    (h₁ : LinearMap.range (toEuclideanLin Z₁) = Λ) (h₂ : LinearMap.range (toEuclideanLin Z₂) = Λ) :
    ∃ g : GL ι ℝ, Z₂ * (g : Matrix ι ι ℝ) = Z₁ := by
  obtain ⟨L, hL⟩ := (toEuclideanLin Z₂).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (injective_toEuclideanLin_of_range_eq h₂))
  set g : Matrix ι ι ℝ := toEuclideanLin.symm (L ∘ₗ toEuclideanLin Z₁)
  have hg : Z₂ * g = Z₁ := by
    refine toEuclideanLin.injective (LinearMap.ext fun u ↦ ?_)
    obtain ⟨v, hv⟩ : toEuclideanLin Z₁ u ∈ LinearMap.range (toEuclideanLin Z₂) := by
      rw [h₂, ← h₁]; exact ⟨u, rfl⟩
    rw [toLpLin_mul_same, LinearMap.comp_apply, LinearEquiv.apply_symm_apply,
      LinearMap.comp_apply, ← hv, ← LinearMap.comp_apply L, hL, LinearMap.id_apply]
  exact ⟨(isUnit_of_range_mul_eq (Z := Z₂) (hg ▸ h₁)).unit, hg⟩

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

/-- The column space of the frame `fromRows 1 A` is the graph `{(x, A x)}`. -/
theorem StdSpace.range_toEuclideanLin_fromRows_one_eq_graph (A : Matrix ι ι ℝ) :
    LinearMap.range (toEuclideanLin (fromRows 1 A)) = graph A := by
  ext z
  refine ⟨?_, fun hz ↦ ⟨WithLp.toLp 2 (x z), StdSpace.ext
    (by rw [x_toEuclideanLin_fromRows]; simp)
    (by rw [y_toEuclideanLin_fromRows]; simp [mem_graph_iff.1 hz])⟩⟩
  rintro ⟨u, rfl⟩
  simp

/-- Swapping the coordinates of a column combination of `fromRows X Y` gives the same
combination of `fromRows Y X`. -/
@[simp]
theorem StdSpace.swap_toEuclideanLin_fromRows (X Y : Matrix ι ι ℝ) (u : EuclideanSpace ℝ ι) :
    swap ι (toEuclideanLin (fromRows X Y) u) = toEuclideanLin (fromRows Y X) u :=
  StdSpace.ext (by simp) (by simp)

/-- The coordinate swap carries the column space of `fromRows X Y` to that of `fromRows Y X`. -/
@[simp]
theorem StdSpace.map_swap_range_toEuclideanLin_fromRows (X Y : Matrix ι ι ℝ) :
    (LinearMap.range (toEuclideanLin (fromRows X Y))).map
        (swap ι : StdSpace ι →ₗ[ℝ] StdSpace ι) =
      LinearMap.range (toEuclideanLin (fromRows Y X)) := by
  rw [← LinearMap.range_comp]
  congr 1
  ext u : 1
  exact swap_toEuclideanLin_fromRows X Y u

/-- The column space of the frame `fromRows A 1` is the graph `{(A y, y)}`. -/
theorem StdSpace.range_toEuclideanLin_fromRows_one_eq_graphY (A : Matrix ι ι ℝ) :
    LinearMap.range (toEuclideanLin (fromRows A 1)) = graphY A := by
  rw [graphY_def, ← range_toEuclideanLin_fromRows_one_eq_graph,
    map_swap_range_toEuclideanLin_fromRows]

/-- A frame `fromRows X Y` of full column rank spans a subspace meeting `{y = 0}` only in `0`
exactly when `Y` is invertible. -/
theorem StdSpace.disjoint_range_toEuclideanLin_fromRows_ker_y_iff {X Y : Matrix ι ι ℝ}
    (h : Function.Injective (fromRows X Y).mulVec) :
    Disjoint (LinearMap.range (toEuclideanLin (fromRows X Y))) (LinearMap.ker y) ↔
      IsUnit Y := by
  rw [← mulVec_injective_iff_isUnit, Submodule.disjoint_def]
  refine ⟨fun hd ↦ (injective_iff_map_eq_zero Y.mulVecLin).2 fun u hu ↦ h ?_,
    fun hY z hz hz' ↦ ?_⟩
  · have := hd _ (LinearMap.mem_range_self _ (WithLp.toLp 2 u))
      (by rw [LinearMap.mem_ker, y_toEuclideanLin_fromRows]; simpa using hu)
    simpa [toEuclideanLin] using congrArg WithLp.ofLp this
  · obtain ⟨u, rfl⟩ := hz
    rw [LinearMap.mem_ker, y_toEuclideanLin_fromRows] at hz'
    have hu : u = 0 := by
      simpa using congrArg (WithLp.toLp 2) (hY (hz'.trans (mulVec_zero _).symm))
    simp [hu]

/-- If `Y` is invertible, the frame `fromRows X Y` spans the graph `{(X Y⁻¹ y, y)}`. -/
theorem StdSpace.range_toEuclideanLin_fromRows_eq_graphY {X Y : Matrix ι ι ℝ} (hY : IsUnit Y) :
    LinearMap.range (toEuclideanLin (fromRows X Y)) = graphY (X * Y⁻¹) := by
  rw [← range_toEuclideanLin_fromRows_one_eq_graphY,
    ← range_toLpLin_mul_of_isUnit 2 (fromRows (X * Y⁻¹) 1) hY, fromRows_mul, Matrix.one_mul,
    nonsing_inv_mul_cancel_right _ _ ((isUnit_iff_isUnit_det Y).1 hY)]

/-- If `X` is invertible, the frame `fromRows X Y` spans the graph `{(x, Y X⁻¹ x)}`. -/
theorem StdSpace.range_toEuclideanLin_fromRows_eq_graph {X Y : Matrix ι ι ℝ} (hX : IsUnit X) :
    LinearMap.range (toEuclideanLin (fromRows X Y)) = graph (Y * X⁻¹) := by
  rw [← map_swap_range_toEuclideanLin_fromRows Y X, range_toEuclideanLin_fromRows_eq_graphY hX,
    graphY_def, ← symm_swap, Submodule.map_symm_eq_iff, symm_swap]

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

/-- For a symmetric matrix `A`, `fromRows A 1` is a Lagrangian frame: it spans `graphY A`. -/
theorem isLagrangian_range_fromRows_one {A : Matrix ι ι ℝ} (hA : A.IsSymm) :
    (stdForm ι).IsLagrangian (LinearMap.range (toEuclideanLin (fromRows A 1))) := by
  rw [StdSpace.range_toEuclideanLin_fromRows_one_eq_graphY]
  exact (isLagrangian_graphY_iff A).2 hA

/-- A Lagrangian frame `fromRows X Y` spans a subspace meeting `{y = 0}` only in `0` exactly when
`Y` is invertible. -/
theorem StdSpace.disjoint_range_toEuclideanLin_fromRows_ker_y_iff_of_isLagrangian
    {X Y : Matrix ι ι ℝ}
    (h : (stdForm ι).IsLagrangian (LinearMap.range (toEuclideanLin (fromRows X Y)))) :
    Disjoint (LinearMap.range (toEuclideanLin (fromRows X Y))) (LinearMap.ker y) ↔
      IsUnit Y :=
  disjoint_range_toEuclideanLin_fromRows_ker_y_iff
    ((rank_eq_card_iff_mulVec_injective _).1 ((isLagrangian_range_fromRows_iff _ _).1 h).1)

/-- A Lagrangian frame `fromRows X Y` spans a subspace meeting `{x = 0}` only in `0` exactly when
`X` is invertible. -/
theorem StdSpace.disjoint_range_toEuclideanLin_fromRows_ker_x_iff_of_isLagrangian
    {X Y : Matrix ι ι ℝ}
    (h : (stdForm ι).IsLagrangian (LinearMap.range (toEuclideanLin (fromRows X Y)))) :
    Disjoint (LinearMap.range (toEuclideanLin (fromRows X Y))) (LinearMap.ker x) ↔
      IsUnit X := by
  -- The coordinate swap exchanges `fromRows X Y` with `fromRows Y X`, and `{x = 0}` with
  -- `{y = 0}`.
  rw [← disjoint_map_orderIso_iff (Submodule.orderIsoMapComap (swap ι)),
    Submodule.orderIsoMapComap_apply, Submodule.orderIsoMapComap_apply,
    map_swap_range_toEuclideanLin_fromRows, map_swap_ker_x]
  refine disjoint_range_toEuclideanLin_fromRows_ker_y_iff_of_isLagrangian ?_
  rwa [← map_swap_range_toEuclideanLin_fromRows, isLagrangian_map_swap_iff]

/-- The Lagrangian subspace spanned by the columns of a Lagrangian frame `fromRows X Y`. By
`isLagrangian_range_fromRows_iff`, the hypothesis says that the frame has rank `n` and that
`Xᵀ Y = Yᵀ X`. -/
noncomputable def LagrangianGrassmannian.ofFrame (X Y : Matrix ι ι ℝ)
    (h : (stdForm ι).IsLagrangian (LinearMap.range (toEuclideanLin (fromRows X Y)))) :
    LagrangianGrassmannian (stdForm ι) :=
  ⟨_, h⟩

@[simp]
theorem LagrangianGrassmannian.coe_ofFrame (X Y : Matrix ι ι ℝ)
    (h : (stdForm ι).IsLagrangian (LinearMap.range (toEuclideanLin (fromRows X Y)))) :
    (ofFrame X Y h : Submodule ℝ (StdSpace ι)) =
      LinearMap.range (toEuclideanLin (fromRows X Y)) :=
  (rfl)

@[simp]
theorem LagrangianGrassmannian.mem_ofFrame_iff {X Y : Matrix ι ι ℝ}
    {h : (stdForm ι).IsLagrangian (LinearMap.range (toEuclideanLin (fromRows X Y)))}
    {z : StdSpace ι} :
    z ∈ ofFrame X Y h ↔ z ∈ LinearMap.range (toEuclideanLin (fromRows X Y)) :=
  Iff.rfl

/-- The complex frame `X + i Y` of a Lagrangian frame `fromRows X Y` is invertible. -/
theorem det_ne_zero_of_isLagrangian_range_fromRows {X Y : Matrix ι ι ℝ}
    (h : (stdForm ι).IsLagrangian (LinearMap.range (toEuclideanLin (fromRows X Y)))) :
    (X.map Complex.ofReal + Complex.I • Y.map Complex.ofReal).det ≠ 0 := by
  set e := (complexEuclideanEquiv ι).toLinearEquiv
  have he : (stdComplexStructure ι).toLinearMap ∘ₗ e.toLinearMap =
      e.toLinearMap ∘ₗ (LinearMap.lsmul ℂ (EuclideanSpace ℂ ι) Complex.I).restrictScalars ℝ :=
    LinearMap.ext fun v ↦ stdComplexStructure_complexEuclideanEquiv v
  have hJ := h.isMaximalTotallyReal_of_compatible stdForm_compatible
  rw [range_toEuclideanLin_fromRows_eq_map_realImage] at hJ
  exact isMaximalTotallyReal_realImage_iff.1 ((e.isMaximalTotallyReal_map_iff he).1 hJ)

end Frame

end SymplecticGeometry

end
