/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Hermitian
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hermitian.Frame
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Section.Nonvanishing

/-!
# Unitary frames over manifolds with boundary

Let `M` be a compact connected smooth manifold of dimension `n + 2` whose boundary is not empty,
and let `V` be a smooth complex vector bundle over `M` with a smooth Hermitian metric: a smooth
real bundle metric `g` that multiplication by `Complex.I` preserves, whose Hermitian products on
the fibres are Tau Ceti's `g.complexInnerProductSpace hI`. This file shows:

* `Bundle.ContMDiffRiemannianMetric.exists_orthonormal_contMDiffSection_of_boundary_nonempty_of_le`:
  if `V` has complex rank `k + r` and `n + 2 ≤ 2 (r + 1)`, then `V` has `k` smooth sections that
  are orthonormal at every point;
* `Bundle.ContMDiffRiemannianMetric.exists_orthonormal_contMDiffSection_of_boundary_nonempty`:
  over a surface (`n = 0`), a bundle of complex rank `k` has `k` such sections, a unitary basis
  of every fibre;
* `Bundle.ContMDiffRiemannianMetric.exists_unitary_trivialization_of_boundary_nonempty`: so, for
  any complex basis `b` of the model fibre, `V` has a global trivialization in its smooth maximal
  atlas that is, on every fibre and in the coordinates of `b`, a complex linear isometry onto
  `EuclideanSpace ℂ (Fin k)`.

No orientation of `M` is used.

The sections are built one at a time, by an induction adapted from Tau Ceti's proof of
`Bundle.ContMDiffRiemannianMetric.exists_orthonormal_contMDiffSection_of_finrank_lt`
(`TauCeti/Geometry/Manifold/VectorBundle/Riemannian/LineSplitting.lean`), which treats closed
manifolds. Once `j < k` orthonormal sections are chosen, their pointwise Hermitian orthogonal
complement is a smooth complex subbundle of complex rank `r + (k - j)` (Tau Ceti's
`Bundle.ContMDiffRiemannianMetric.hasLocalContMDiffSubbundleFrames_orthogonalSpanFamily`), so of
real rank at least `n + 2`. Over a manifold with nonempty boundary such a bundle has a smooth
nowhere-zero section
(`SymplecticGeometry.exists_contMDiffSection_forall_ne_zero_of_boundary_nonempty`), and
`Bundle.ContMDiffRiemannianMetric.contMDiff_and_orthonormal_vecCons_of_mem_orthogonalSpanFamily`
normalizes and appends it. This replaces the cutting of the surface into pieces in McDuff–Salamon.
The trivialization is then
`Bundle.ContMDiffRiemannianMetric.exists_unitary_trivialization_of_orthonormal`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 2.6.7
* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  proof of Theorem C.1.10
-/

public noncomputable section

open Bundle Module Set TauCeti
open scoped Manifold ContDiff

namespace Bundle.ContMDiffRiemannianMetric

section Boundary

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 2)) M]
  [IsManifold (𝓡∂ (n + 2)) ∞ M] [CompactSpace M] [ConnectedSpace M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]
  {V : M → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]

open scoped VectorBundle.ComplexToReal

variable [ContMDiffVectorBundle ∞ F V (𝓡∂ (n + 2))]

/-- Let `V` be a smooth complex vector bundle of complex rank `k + r` with a smooth Hermitian
metric `g` over a compact connected manifold `M` of dimension `n + 2 ≤ 2 (r + 1)` whose boundary
is not empty. Then `V` has `k` smooth sections that are orthonormal at every point. -/
theorem exists_orthonormal_contMDiffSection_of_boundary_nonempty_of_le
    (g : ContMDiffRiemannianMetric (𝓡∂ (n + 2)) ∞ F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
    (hM : ((𝓡∂ (n + 2)).boundary M).Nonempty) {k r : ℕ} (hk : finrank ℂ F = k + r)
    (hdim : n + 2 ≤ 2 * (r + 1)) :
    ∃ s : Fin k → ∀ x, V x,
      (∀ i, ContMDiff (𝓡∂ (n + 2)) ((𝓡∂ (n + 2)).prod 𝓘(ℝ, F)) ∞
        (fun x ↦ (⟨x, s i x⟩ : TotalSpace F V))) ∧
      letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
      letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
      ∀ x, Orthonormal ℂ fun i ↦ s i x := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  induction k generalizing r with
  | zero => exact ⟨Fin.elim0, fun i ↦ i.elim0, fun _ ↦ ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩⟩
  | succ k ih =>
    obtain ⟨s, hs, hon⟩ := ih (r := r + 1) (by rw [hk]; ring) (by omega)
    have hW := g.hasLocalContMDiffSubbundleFrames_orthogonalSpanFamily hI s hs hon (r := r + 1)
      (by rw [hk, Fintype.card_fin]; ring)
    let W := g.orthogonalSpanFamily hI s
    let := hW.fiberBundle
    let := hW.vectorBundle
    let := hW.contMDiffVectorBundle
    -- A nowhere-zero smooth section of the complement of the sections chosen so far.
    have hr : n + 2 ≤ finrank ℝ (Fin (r + 1) → ℂ) := by
      simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
      omega
    obtain ⟨t, ht⟩ := SymplecticGeometry.exists_contMDiffSection_forall_ne_zero_of_boundary_nonempty
      (V := fun x ↦ W x) (F := Fin (r + 1) → ℂ) hM hr
    have hu : ContMDiff (𝓡∂ (n + 2)) ((𝓡∂ (n + 2)).prod 𝓘(ℝ, F)) ∞
        (fun x ↦ (⟨x, (t x : V x)⟩ : TotalSpace F V)) :=
      hW.contMDiff_totalSpace_inclusion.comp t.contMDiff
    exact ⟨_, g.contMDiff_and_orthonormal_vecCons_of_mem_orthogonalSpanFamily hI hs hon hu
      (fun x ↦ by simpa using ht x) fun x ↦ (t x).property⟩

end Boundary

section Surface

variable {S : Type*} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S] [CompactSpace S] [ConnectedSpace S] [T2Space S]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {V : S → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]

open scoped VectorBundle.ComplexToReal

variable [ContMDiffVectorBundle ∞ F V (𝓡∂ 2)]

/-- Let `V` be a smooth complex vector bundle of complex rank `k` with a smooth Hermitian metric
`g` over a compact connected surface `S` whose boundary is not empty. Then `V` has `k` smooth
sections that form a unitary basis of every fibre. -/
theorem exists_orthonormal_contMDiffSection_of_boundary_nonempty [FiniteDimensional ℂ F]
    (g : ContMDiffRiemannianMetric (𝓡∂ 2) ∞ F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
    (hS : ((𝓡∂ 2).boundary S).Nonempty) {k : ℕ} (hk : finrank ℂ F = k) :
    ∃ s : Fin k → ∀ x, V x,
      (∀ i, ContMDiff (𝓡∂ 2) ((𝓡∂ 2).prod 𝓘(ℝ, F)) ∞
        (fun x ↦ (⟨x, s i x⟩ : TotalSpace F V))) ∧
      letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
      letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
      ∀ x, Orthonormal ℂ fun i ↦ s i x :=
  exists_orthonormal_contMDiffSection_of_boundary_nonempty_of_le (n := 0) g hI hS (r := 0) hk
    le_rfl

/-- Let `V` be a smooth complex vector bundle with model fibre `F` and a smooth Hermitian metric
`g` over a compact connected surface `S` whose boundary is not empty, and let `b` be a complex
basis of `F`. Then `V` has a global trivialization `e`, compatible with its smooth structure, whose
map on each fibre, read in the coordinates of `b`, is a complex linear isometry from `V x` onto
`EuclideanSpace ℂ (Fin k)`. That is, `e` is unitary for `g` and the Hermitian product on `F` in
which `b` is orthonormal.

Milestone: *Unitary trivializations over surfaces with boundary*. -/
theorem exists_unitary_trivialization_of_boundary_nonempty
    (g : ContMDiffRiemannianMetric (𝓡∂ 2) ∞ F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
    (hS : ((𝓡∂ 2).boundary S).Nonempty) {k : ℕ} (b : Basis (Fin k) ℂ F) :
    ∃ e : Trivialization F (π F V),
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear S F (𝓡∂ 2) ∞).maximalAtlas (TotalSpace F V) ∧
      e.baseSet = univ ∧
      letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
      letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
      ∀ x, ∃ L : V x ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin k),
        ∀ v, b.equivFun (e ⟨x, v⟩).2 = (L v).ofLp := by
  have : FiniteDimensional ℂ F := b.finiteDimensional_of_finite
  obtain ⟨s, hs, hon⟩ := g.exists_orthonormal_contMDiffSection_of_boundary_nonempty hI hS
    ((finrank_eq_card_basis b).trans (Fintype.card_fin k))
  obtain ⟨e, he, heU, hL⟩ := g.exists_unitary_trivialization_of_orthonormal hI isOpen_univ
    (fun i ↦ (hs i).contMDiffOn) (fun x _ ↦ hon x) b
  exact ⟨e, he, heU, fun x ↦ hL x (mem_univ x)⟩

end Surface

end Bundle.ContMDiffRiemannianMetric
