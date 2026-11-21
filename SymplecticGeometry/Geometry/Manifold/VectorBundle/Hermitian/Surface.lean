/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Hermitian
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.OrthogonalComplement
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Section.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Unitary frames over surfaces with boundary

Let `S` be a compact connected smooth surface whose boundary is not empty, and let `V` be a smooth
complex vector bundle over `S` of complex rank `k`, with a smooth Hermitian metric: a smooth real
bundle metric `g` that multiplication by `Complex.I` preserves, whose Hermitian products on the
fibres are Tau Ceti's `g.complexInnerProductSpace hI`. This file shows:

* `Bundle.ContMDiffRiemannianMetric.exists_orthonormal_contMDiffSection_of_boundary_nonempty`:
  `V` has `k` smooth sections that are orthonormal, hence a unitary basis, at every point;
* `Bundle.ContMDiffRiemannianMetric.exists_unitary_trivialization_of_boundary_nonempty`: for any
  complex basis `b` of the model fibre, `V` has a global trivialization in its smooth maximal atlas
  that is, on every fibre and in the coordinates of `b`, a complex linear isometry onto
  `EuclideanSpace ℂ (Fin k)`.

No orientation of `S` is used.

The sections are built one at a time, as in Tau Ceti's
`Bundle.ContMDiffRiemannianMetric.exists_orthonormal_contMDiffSection_of_finrank_lt` for closed
manifolds of low dimension. Once `j < k` orthonormal sections are chosen, their pointwise
Hermitian orthogonal complement is a smooth complex subbundle of positive complex rank
(Tau Ceti's
`Bundle.ContMDiffRiemannianMetric.hasLocalContMDiffSubbundleFrames_orthogonalSpanFamily`),
so of real rank at least two. Over a surface with boundary such a bundle has a smooth nowhere-zero
section (`SymplecticGeometry.exists_contMDiffSection_forall_ne_zero_of_boundary_nonempty`); it is
normalized and appended. This replaces the book's cutting of the surface into pieces.

The trivialization is Tau Ceti's frame trivialization `IsLocalFrameOn.trivialization` of the real
frame `(s j, i • s j)`, with the real basis `(b j, i • b j)` of the model fibre.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 2.6.7
-/

public noncomputable section

open Bundle Module Set TauCeti
open scoped Manifold ContDiff InnerProductSpace Topology

variable {S : Type*} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S] [CompactSpace S] [ConnectedSpace S] [T2Space S]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]
  {V : S → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealHermitianSurface : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V (𝓡∂ 2)]

namespace Bundle.ContMDiffRiemannianMetric

/-- The inductive step: `k` orthonormal smooth sections of a Hermitian bundle of complex rank
`k + r` over a compact connected surface `S` whose boundary is not empty. -/
private theorem exists_orthonormal_contMDiffSection_of_boundary_nonempty_aux
    (g : ContMDiffRiemannianMetric (𝓡∂ 2) ∞ F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
    (hS : ((𝓡∂ 2).boundary S).Nonempty) {k r : ℕ} (hk : finrank ℂ F = k + r) :
    ∃ s : Fin k → ∀ x, V x,
      (∀ i, ContMDiff (𝓡∂ 2) ((𝓡∂ 2).prod 𝓘(ℝ, F)) ∞
        (fun x ↦ (⟨x, s i x⟩ : TotalSpace F V))) ∧
      letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
      letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
      ∀ x, Orthonormal ℂ fun i ↦ s i x := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  induction k generalizing r with
  | zero => exact ⟨Fin.elim0, fun i ↦ i.elim0, fun _ ↦ ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩⟩
  | succ k ih =>
    obtain ⟨s, hs, hon⟩ := ih (r := r + 1) (by rw [hk]; ring)
    have hW := g.hasLocalContMDiffSubbundleFrames_orthogonalSpanFamily hI s hs hon (r := r + 1)
      (by rw [hk, Fintype.card_fin]; ring)
    let W := g.orthogonalSpanFamily hI s
    let := hW.fiberBundle
    let := hW.vectorBundle
    let := VectorBundle.restrictScalars ℝ ℂ (Fin (r + 1) → ℂ) fun x ↦ W x
    let := hW.contMDiffVectorBundle
    -- A nowhere-zero smooth section of the complement of the sections chosen so far.
    have hr : 0 + 2 ≤ finrank ℝ (Fin (r + 1) → ℂ) := by
      simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
    obtain ⟨t, ht⟩ := SymplecticGeometry.exists_contMDiffSection_forall_ne_zero_of_boundary_nonempty
      (n := 0) (V := fun x ↦ W x) (F := Fin (r + 1) → ℂ) hS hr
    let u : ∀ x, V x := fun x ↦ (t x : V x)
    have hu : ContMDiff (𝓡∂ 2) ((𝓡∂ 2).prod 𝓘(ℝ, F)) ∞
        (fun x ↦ (⟨x, u x⟩ : TotalSpace F V)) :=
      hW.contMDiff_totalSpace_inclusion.comp t.contMDiff
    have hu₀ (x : S) : u x ≠ 0 := by simpa [u] using ht x
    -- Normalize it.
    let c : S → ℂ := fun x ↦ ((‖u x‖⁻¹ : ℝ) : ℂ)
    have hc : ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞ c := by
      refine Complex.ofRealCLM.contMDiff.comp (f := fun x ↦ ‖u x‖⁻¹) fun x ↦ ?_
      have hd := hu.inner_bundle hu x
      have hne : Inner.inner ℝ (u x) (u x) ≠ 0 := inner_self_ne_zero.mpr (hu₀ x)
      refine (ContDiffAt.comp_contMDiffAt (f := fun y ↦ Inner.inner ℝ (u y) (u y))
        ((Real.contDiffAt_sqrt hne).inv (Real.sqrt_ne_zero'.mpr
        (lt_of_le_of_ne real_inner_self_nonneg hne.symm))) hd).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y ↦ ?_)
      simp only [Function.comp_apply, Pi.inv_apply, real_inner_self_eq_norm_sq,
        Real.sqrt_sq (norm_nonneg _)]
    let s' : Fin (k + 1) → ∀ x, V x := Matrix.vecCons (fun x ↦ c x • u x) s
    refine ⟨s', fun i ↦ ?_, fun x ↦ ?_⟩
    · induction i using Fin.cases with
      | zero => simpa [s'] using hc.smul_totalSpace hu
      | succ i => simpa [s'] using hs i
    · have hux : u x ∈ W x := (t x).property
      have horth (i : Fin k) : ⟪s i x, c x • u x⟫_ℂ = 0 := by
        rw [inner_smul_right, (g.mem_orthogonalSpanFamily_iff hI s).mp hux i, mul_zero]
      have hnorm : ‖c x • u x‖ = 1 := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hu₀ x))]
      have hs' : (fun i ↦ s' i x) = Matrix.vecCons (c x • u x) fun i ↦ s i x := by
        ext i
        induction i using Fin.cases <;> simp [s']
      rw [hs']
      exact orthonormal_vecCons_iff.mpr ⟨hnorm, fun i ↦ inner_eq_zero_symm.mp (horth i), hon x⟩


/-- Let `V` be a smooth complex vector bundle of complex rank `k` with a smooth Hermitian metric
`g` over a compact connected surface `S` whose boundary is not empty. Then `V` has `k` smooth
sections that form a unitary basis of every fibre. -/
theorem exists_orthonormal_contMDiffSection_of_boundary_nonempty
    (g : ContMDiffRiemannianMetric (𝓡∂ 2) ∞ F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
    (hS : ((𝓡∂ 2).boundary S).Nonempty) {k : ℕ} (hk : finrank ℂ F = k) :
    ∃ s : Fin k → ∀ x, V x,
      (∀ i, ContMDiff (𝓡∂ 2) ((𝓡∂ 2).prod 𝓘(ℝ, F)) ∞
        (fun x ↦ (⟨x, s i x⟩ : TotalSpace F V))) ∧
      letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
      letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
      ∀ x, Orthonormal ℂ fun i ↦ s i x :=
  exists_orthonormal_contMDiffSection_of_boundary_nonempty_aux g hI hS (r := 0) hk

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
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  obtain ⟨s, hs, hon⟩ := g.exists_orthonormal_contMDiffSection_of_boundary_nonempty hI hS
    ((finrank_eq_card_basis b).trans (Fintype.card_fin k))
  -- At each point the sections form a unitary basis of the fibre.
  have hfd (x : S) : FiniteDimensional ℂ (V x) ∧ finrank ℂ (V x) = k := by
    let ex := (trivializationAt F V x).continuousLinearEquivAt ℂ x
      (FiberBundle.mem_baseSet_trivializationAt' x)
    have : FiniteDimensional ℂ (V x) := ex.symm.toLinearEquiv.finiteDimensional
    exact ⟨this, by rw [ex.toLinearEquiv.finrank_eq, finrank_eq_card_basis b, Fintype.card_fin]⟩
  have := fun x ↦ (hfd x).1
  let ob (x : S) : OrthonormalBasis (Fin k) ℂ (V x) := OrthonormalBasis.mk (hon x)
    ((hon x).linearIndependent.span_eq_top_of_card_eq_finrank'
      (by rw [Fintype.card_fin, (hfd x).2])).ge
  have hob (x : S) (j : Fin k) : ob x j = s j x := by simp [ob]
  -- The real frame `(s j, i • s j)` and the real basis `(b j, i • b j)`.
  let t : Fin 2 × Fin k → ∀ x, V x := fun ij x ↦ Complex.basisOneI ij.1 • s ij.2 x
  let bR : Basis (Fin 2 × Fin k) ℝ F := Complex.basisOneI.smulTower b
  have htx (x : S) : (t · x) = ⇑(Complex.basisOneI.smulTower (ob x).toBasis) := by
    ext ij
    simp [t, Basis.smulTower_apply, hob]
  have ht : IsLocalFrameOn (𝓡∂ 2) F ∞ t univ :=
    { linearIndependent := fun {x} _ ↦ by rw [htx x]; exact Basis.linearIndependent _
      generating := fun {x} _ ↦ by rw [htx x]; exact (Basis.span_eq _).ge
      contMDiffOn := fun ij ↦ (contMDiff_const.smul_totalSpace (hs ij.2)).contMDiffOn }
  refine ⟨ht.trivialization isOpen_univ bR, ht.trivialization_mem_maximalAtlas isOpen_univ bR,
    ht.baseSet_trivialization isOpen_univ bR, fun x ↦ ⟨(ob x).repr, fun v ↦ ?_⟩⟩
  -- Both sides are real linear in `v` and agree on the real frame.
  let f₁ : V x →ₗ[ℝ] Fin k → ℂ := (b.equivFun.restrictScalars ℝ).toLinearMap ∘ₗ
    ((ht.toBasisAt (mem_univ x)).equiv bR (Equiv.refl _)).toLinearMap
  let f₂ : V x →ₗ[ℝ] Fin k → ℂ := ((WithLp.linearEquiv 2 ℂ (Fin k → ℂ)).restrictScalars ℝ ∘ₗ
    ((ob x).repr.toLinearEquiv.restrictScalars ℝ).toLinearMap : V x →ₗ[ℝ] Fin k → ℂ)
  have hf : f₁ = f₂ := by
    refine (ht.toBasisAt (mem_univ x)).ext fun ij ↦ ?_
    simp only [f₁, f₂, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      Basis.equiv_apply, Equiv.refl_apply]
    simp [bR, t, Basis.smulTower_apply, ← hob, Finsupp.single_eq_pi_single]
  have := LinearMap.congr_fun hf v
  simpa [f₁, f₂, ht.trivialization_apply isOpen_univ bR (mem_univ x)] using this

end Bundle.ContMDiffRiemannianMetric
