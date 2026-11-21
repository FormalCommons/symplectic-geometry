/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Hermitian
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.OrthogonalComplement
public import TauCeti.Geometry.Manifold.VectorBundle.TotallyReal.Trivialization
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.ContMDiff.Sqrt
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Unitary frames of Hermitian bundles

Let `V` be a smooth complex vector bundle over a manifold `B`, with a smooth Hermitian metric: a
smooth real bundle metric `g` that multiplication by `Complex.I` preserves, whose Hermitian
products on the fibres are Tau Ceti's `g.complexInnerProductSpace hI`. This file gives two general
facts about smooth families of sections that are orthonormal at every point.

* `Bundle.ContMDiffRiemannianMetric.contMDiff_and_orthonormal_vecCons_of_mem_orthogonalSpanFamily`:
  if `s` is a smooth pointwise orthonormal family and `u` a smooth nowhere-zero section of its
  Hermitian orthogonal complement (Tau Ceti's `orthogonalSpanFamily`), then `u / ‖u‖` followed by
  `s` is again a smooth pointwise orthonormal family. This is the step of the induction that
  builds unitary frames. The lemma and its proof are adapted from the append step of Tau Ceti's
  proof of `Bundle.ContMDiffRiemannianMetric.exists_orthonormal_contMDiffSection_of_finrank_lt`
  (`TauCeti/Geometry/Manifold/VectorBundle/Riemannian/LineSplitting.lean`); the normalization
  here is rewritten with Tau Ceti's `ContMDiff.sqrt`.
* `Bundle.ContMDiffRiemannianMetric.exists_unitary_trivialization_of_orthonormal`: a smooth
  family `s` that is a unitary basis of every fibre over an open set `U` gives, for any complex
  basis `b` of the model fibre, a trivialization over `U` in the smooth maximal atlas whose map on
  each fibre, read in the coordinates of `b`, is a complex linear isometry onto
  `EuclideanSpace ℂ ι`. It is Tau Ceti's frame trivialization of the doubled frame
  `TauCeti.complexDoubledFrame s`, which is complex-linear on fibres
  (`IsLocalFrameOn.isLinear_complex_trivialization_complexDoubledFrame`) and sends `s j x` to
  `b j` (`IsLocalFrameOn.trivialization_complexDoubledFrame_apply_frame`).

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  proof of Theorem C.1.10
-/

public noncomputable section

open Bundle Module Set TauCeti
open scoped Manifold ContDiff InnerProductSpace

variable {X H B F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace H] {IB : ModelWithCorners ℝ X H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]
  {n : ℕ∞ω}

local instance instVectorBundleRealHermitianFrame : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

namespace Bundle.ContMDiffRiemannianMetric

/-- Let `s` be `k` smooth sections of a smooth Hermitian bundle that are orthonormal at every
point, and `u` a smooth nowhere-zero section that is Hermitian orthogonal to all of them. Then
the `k + 1` sections `u / ‖u‖, s 0, …, s (k - 1)` are smooth and orthonormal at every point.

The statement and proof are adapted from the append step of Tau Ceti's proof of
`Bundle.ContMDiffRiemannianMetric.exists_orthonormal_contMDiffSection_of_finrank_lt`. -/
theorem contMDiff_and_orthonormal_vecCons_of_mem_orthogonalSpanFamily
    (g : ContMDiffRiemannianMetric IB n F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
    {k : ℕ} {s : Fin k → ∀ x, V x}
    (hs : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun x ↦ (⟨x, s i x⟩ : TotalSpace F V)))
    (hon : letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
      letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
      ∀ x, Orthonormal ℂ fun i ↦ s i x)
    {u : ∀ x, V x}
    (hu : ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun x ↦ (⟨x, u x⟩ : TotalSpace F V)))
    (hu₀ : ∀ x, u x ≠ 0) (huW : ∀ x, u x ∈ g.orthogonalSpanFamily hI s x) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    (∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun x ↦ (⟨x,
        Matrix.vecCons (fun x ↦ ((‖u x‖⁻¹ : ℝ) : ℂ) • u x) s i x⟩ : TotalSpace F V))) ∧
      ∀ x, Orthonormal ℂ fun i ↦ Matrix.vecCons (fun x ↦ ((‖u x‖⁻¹ : ℝ) : ℂ) • u x) s i x := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  have hne (x : B) : Inner.inner ℝ (u x) (u x) ≠ 0 := inner_self_ne_zero.mpr (hu₀ x)
  have hsqrt := (hu.inner_bundle hu).sqrt hne
  have hc : ContMDiff IB 𝓘(ℝ, ℂ) n fun x ↦ ((‖u x‖⁻¹ : ℝ) : ℂ) := by
    refine Complex.ofRealCLM.contMDiff.comp ((hsqrt.inv₀ fun x ↦ ?_).congr fun x ↦ ?_)
    · exact Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne real_inner_self_nonneg (hne x).symm)
    · simp only [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
      rfl
  refine ⟨fun i ↦ ?_, fun x ↦ ?_⟩
  · induction i using Fin.cases with
    | zero => simpa using hc.smul_totalSpace hu
    | succ i => simpa using hs i
  · have horth (i : Fin k) : ⟪s i x, ((‖u x‖⁻¹ : ℝ) : ℂ) • u x⟫_ℂ = 0 := by
      rw [inner_smul_right, (g.mem_orthogonalSpanFamily_iff hI s).mp (huW x) i, mul_zero]
    have hnorm : ‖((‖u x‖⁻¹ : ℝ) : ℂ) • u x‖ = 1 := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hu₀ x))]
    have hs' : (fun i ↦ Matrix.vecCons (fun x ↦ ((‖u x‖⁻¹ : ℝ) : ℂ) • u x) s i x) =
        Matrix.vecCons (((‖u x‖⁻¹ : ℝ) : ℂ) • u x) fun i ↦ s i x := by
      ext i
      induction i using Fin.cases <;> simp
    rw [hs']
    exact orthonormal_vecCons_iff.mpr ⟨hnorm, fun i ↦ inner_eq_zero_symm.mp (horth i), hon x⟩

variable [ContMDiffVectorBundle n F V IB]

/-- Let `s` be a smooth family of sections, indexed by a finite type `ι`, of a smooth Hermitian
bundle with model fibre `F`, that is orthonormal at every point of an open set `U`, and let `b` be
a complex basis of `F`. Then there is a trivialization `e` over `U`, compatible with the smooth
structure, whose map on each fibre over `U`, read in the coordinates of `b`, is a complex linear
isometry from `V x` onto `EuclideanSpace ℂ ι`. -/
theorem exists_unitary_trivialization_of_orthonormal
    (g : ContMDiffRiemannianMetric IB n F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
    {ι : Type*} [Fintype ι] {s : ι → ∀ x, V x} {U : Set B} (hU : IsOpen U)
    (hs : ∀ i, ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (fun x ↦ (⟨x, s i x⟩ : TotalSpace F V)) U)
    (hon : letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
      letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
      ∀ x ∈ U, Orthonormal ℂ fun i ↦ s i x)
    (b : Basis ι ℂ F) :
    ∃ e : Trivialization F (π F V),
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F V) ∧
      e.baseSet = U ∧
      letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
      letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
      ∀ x ∈ U, ∃ L : V x ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι,
        ∀ v, b.equivFun (e ⟨x, v⟩).2 = (L v).ofLp := by
  classical
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  have : FiniteDimensional ℂ F := b.finiteDimensional_of_finite
  have := VectorBundle.finiteDimensional ℂ F V
  -- Over `U` the sections form an orthonormal basis of each fibre.
  let ob (x : B) (hx : x ∈ U) : OrthonormalBasis ι ℂ (V x) := OrthonormalBasis.mk (hon x hx)
    ((hon x hx).linearIndependent.span_eq_top_of_card_eq_finrank'
      (by rw [VectorBundle.finrank_eq ℂ F V x, finrank_eq_card_basis b])).ge
  have hob (x : B) (hx : x ∈ U) (j : ι) : ob x hx j = s j x := by simp [ob]
  have htx (x : B) (hx : x ∈ U) :
      (complexDoubledFrame s · x) = ⇑(Complex.basisOneI.smulTower (ob x hx).toBasis) := by
    ext ij
    simp [complexDoubledFrame_apply, Basis.smulTower_apply, hob]
  have ht : IsLocalFrameOn IB F n (complexDoubledFrame s) U :=
    { linearIndependent := fun {x} hx ↦ by rw [htx x hx]; exact Basis.linearIndependent _
      generating := fun {x} hx ↦ by rw [htx x hx]; exact (Basis.span_eq _).ge
      contMDiffOn := fun ij ↦ (contMDiffOn_const.smul_totalSpace (hs ij.2)).congr
        fun x _ ↦ by rw [complexDoubledFrame_apply] }
  set e := ht.trivialization hU (Complex.basisOneI.smulTower b)
  refine ⟨e, ht.trivialization_mem_maximalAtlas hU _, ht.baseSet_trivialization hU _,
    fun x hx ↦ ⟨(ob x hx).repr, fun v ↦ ?_⟩⟩
  have hxe : x ∈ e.baseSet := by simpa [e] using hx
  -- Both sides are complex linear in `v` and agree on the basis `s · x`.
  have key : b.equivFun.toLinearMap ∘ₗ e.linearMapAt ℂ x =
      (WithLp.linearEquiv 2 ℂ (ι → ℂ)).toLinearMap ∘ₗ (ob x hx).repr.toLinearMap := by
    refine (ob x hx).toBasis.ext fun j ↦ ?_
    have hrep : (ob x hx).repr (s j x) = EuclideanSpace.single j 1 := by
      rw [← hob x hx j, OrthonormalBasis.repr_self]
    simp [e.coe_linearMapAt_of_mem hxe, e, hob, hrep, Finsupp.single_eq_pi_single,
      ht.trivialization_complexDoubledFrame_apply_frame hU b hx]
  simpa [e.coe_linearMapAt_of_mem hxe] using LinearMap.congr_fun key v

end Bundle.ContMDiffRiemannianMetric
