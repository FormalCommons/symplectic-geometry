/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Hermitian
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.OrthogonalComplement
public import TauCeti.Geometry.Manifold.VectorBundle.TotallyReal.Trivialization
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Basic
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import SymplecticGeometry.Geometry.Manifold.VectorBundle.LocalFrame
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Riemannian.Hermitian
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Riemannian.Norm
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Basic
import TauCeti.Geometry.Manifold.VectorBundle.MaximalAtlas
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Unitary frames of Hermitian bundles

Let `V` be a smooth complex vector bundle over a manifold `B`, with a smooth Hermitian metric: a
smooth real bundle metric `g` that multiplication by `Complex.I` preserves, whose Hermitian
products on the fibres are Tau Ceti's `g.complexInnerProductSpace hI`. This file gives general
facts about smooth families of sections that are orthonormal at every point, and ways to build
them.

* `Bundle.ContMDiffRiemannianMetric.contMDiff_and_orthonormal_vecCons_of_mem_orthogonalSpanFamily`:
  if `s` is a smooth pointwise orthonormal family and `u` a smooth nowhere-zero section of its
  Hermitian orthogonal complement (Tau Ceti's `orthogonalSpanFamily`), then `u / ‖u‖` followed by
  `s` is again a smooth pointwise orthonormal family. This is the step of the induction that
  builds unitary frames. The lemma and its proof are adapted from the append step of Tau Ceti's
  proof of `Bundle.ContMDiffRiemannianMetric.exists_orthonormal_contMDiffSection_of_finrank_lt`
  (`TauCeti/Geometry/Manifold/VectorBundle/Riemannian/LineSplitting.lean`); the norm `‖u‖`
  is made smooth by `ContMDiff.norm_bundle`.
* `Bundle.ContMDiffRiemannianMetric.exists_unitary_trivialization_of_orthonormal`: a smooth
  family `s` that is a unitary basis of every fibre over an open set `U` gives, for any complex
  basis `b` of the model fibre, a trivialization over `U` in the smooth maximal atlas whose map on
  each fibre, read in the coordinates of `b`, is a complex linear isometry onto
  `EuclideanSpace ℂ ι`. It is Tau Ceti's frame trivialization of the doubled frame
  `TauCeti.complexDoubledFrame s`, which is complex-linear on fibres
  (`IsLocalFrameOn.isLinear_complex_trivialization_complexDoubledFrame`) and sends `s j x` to
  `b j` (`IsLocalFrameOn.trivialization_complexDoubledFrame_apply_frame`).
* `Bundle.ContMDiffRiemannianMetric.contMDiffWithinAt_gramSchmidt` and
  `Bundle.ContMDiffRiemannianMetric.contMDiffWithinAt_gramSchmidtNormed`: Gram–Schmidt with
  respect to the Hermitian products, plain and normalized, keeps smoothness of sections along a
  map within a set at a point where they are complex linearly independent. They and their proofs
  are adapted from Tau Ceti's real `ContMDiffWithinAt.gramSchmidt_bundle` and
  `ContMDiffWithinAt.gramSchmidtNormed_bundle`
  (`TauCeti/Geometry/Manifold/VectorBundle/GramSchmidt.lean`), with the Hermitian products made
  smooth by `Bundle.ContMDiffRiemannianMetric.contMDiffWithinAt_hermitianPairing`. Their
  versions on a set, `Bundle.ContMDiffRiemannianMetric.contMDiffOn_gramSchmidt` and
  `Bundle.ContMDiffRiemannianMetric.contMDiffOn_gramSchmidtNormed`, follow.
* `Bundle.Trivialization.contMDiffOn_totalSpaceMk_orthonormalFrameAt_complex`: for a complex
  linear trivialization `e` in the smooth maximal atlas, every vector
  `y ↦ e.orthonormalFrameAt c b y w` of Tau Ceti's local unitary frame of `e` is a smooth section
  over the base set of `e`, in any rank. It and its proof
  are adapted from Tau Ceti's real
  `Bundle.Trivialization.contMDiffOn_orthonormalBasis_of_mem_maximalAtlas`
  (`TauCeti/Geometry/Manifold/VectorBundle/Riemannian/OrthonormalTrivialization.lean`).

The Gram–Schmidt lemmas, and the proof of
`Bundle.Trivialization.contMDiffOn_totalSpaceMk_orthonormalFrameAt_complex`, repeat Tau Ceti's
real ones almost word for word, with `ℂ` in place of `ℝ`. They would become unnecessary if Tau
Ceti's `GramSchmidt.lean`, and its `Bundle.Trivialization.isLocalFrameOn_symm_of_mem_maximalAtlas`
for a basis over a larger field of scalars, were stated for fibres with an inner product over any
`RCLike` field.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  proof of Theorem C.1.10
-/

public noncomputable section

open Bundle InnerProductSpace Module Set TauCeti
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

open scoped VectorBundle.ComplexToReal

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
  have hc : ContMDiff IB 𝓘(ℝ, ℂ) n fun x ↦ ((‖u x‖⁻¹ : ℝ) : ℂ) :=
    Complex.ofRealCLM.contMDiff.comp
      ((hu.norm_bundle hu₀).inv₀ fun x ↦ norm_ne_zero_iff.2 (hu₀ x))
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

section GramSchmidt

variable {XM HM M : Type*} [NormedAddCommGroup XM] [NormedSpace ℝ XM]
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ XM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] {b : M → B} {v : ι → ∀ m, V (b m)}
  {s : Set M} {x : M}

/-- For a smooth Hermitian metric `(g, hI)`, Gram–Schmidt with respect to the Hermitian products
`g.complexInnerProductSpace hI` keeps smoothness within a set at a point: if the sections `v i`
along a map `b` are `C^n` within `s` at `x` for `i ≤ j`, and the vectors `v i x` with `i < j` are
complex linearly independent, then the `j`-th Gram–Schmidt vector is `C^n` within `s` at `x`.

This is the complex counterpart of Tau Ceti's `ContMDiffWithinAt.gramSchmidt_bundle`. -/
theorem contMDiffWithinAt_gramSchmidt (g : ContMDiffRiemannianMetric IB n F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w) (j : ι)
    (hv : ∀ i ≤ j, ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n
      (fun m ↦ (⟨b m, v i m⟩ : TotalSpace F V)) s x)
    (hli : LinearIndepOn ℂ (fun i ↦ v i x) (Iio j)) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n
      (fun m ↦ (⟨b m, gramSchmidt ℂ (fun i ↦ v i m) j⟩ : TotalSpace F V)) s x := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have hg (i : ι) (hi : i < j) :=
      ih i hi (fun k hk ↦ hv k (hk.trans hi.le)) (hli.mono (Iio_subset_Iio hi.le))
    -- The coefficient of `gramSchmidt ℂ v i` in the formula for `gramSchmidt ℂ v j`, written
    -- with a real denominator.
    have hc (i : ι) (hi : i < j) : ContMDiffWithinAt IM 𝓘(ℝ, ℂ) n
        (fun m ↦ (‖gramSchmidt ℂ (fun k ↦ v k m) i‖ ^ 2)⁻¹ •
          ⟪gramSchmidt ℂ (fun k ↦ v k m) i, v j m⟫_ℂ) s x := by
      have hd : ContMDiffWithinAt IM 𝓘(ℝ) n
          (fun m ↦ (‖gramSchmidt ℂ (fun k ↦ v k m) i‖ ^ 2)⁻¹) s x := by
        refine (((hg i hi).inner_bundle (hg i hi)).congr (fun m _ ↦ ?_) ?_).inv₀ ?_
        · exact (real_inner_self_eq_norm_sq _).symm
        · exact (real_inner_self_eq_norm_sq _).symm
        · exact pow_ne_zero 2 (norm_ne_zero_iff.2 (gramSchmidt_ne_zero_coe i
            (hli.mono (Iic_subset_Iio.2 hi))))
      exact hd.smul (g.contMDiffWithinAt_hermitianPairing hI (hg i hi) (hv j le_rfl))
    have hb : ContMDiffWithinAt IM IB n b s x :=
      (contMDiff_proj V).contMDiffAt.comp_contMDiffWithinAt x (hv j le_rfl)
    have heq (m : M) : gramSchmidt ℂ (fun i ↦ v i m) j = v j m -
        ∑ i ∈ Finset.Iio j, ((‖gramSchmidt ℂ (fun k ↦ v k m) i‖ ^ 2)⁻¹ •
          ⟪gramSchmidt ℂ (fun k ↦ v k m) i, v j m⟫_ℂ) • gramSchmidt ℂ (fun k ↦ v k m) i := by
      refine eq_sub_of_add_eq (Eq.trans ?_ (gramSchmidt_def'' ℂ (fun i ↦ v i m) j).symm)
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Complex.real_smul, div_eq_inv_mul, Complex.ofReal_inv, Complex.ofReal_pow]
      -- The two sides differ only in how scalar multiplication by `ℂ` is found: through the
      -- bundle's `Module ℂ`, or through `g.complexInnerProductSpace hI`, which keeps that module
      -- (`complexInnerProductSpace_toModule`, which holds by `rfl`).
      rfl
    refine ((hv j le_rfl).sub_sectionAlong (ContMDiffWithinAt.sum_sectionAlong (Finset.Iio j)
      (fun i m ↦ ((‖gramSchmidt ℂ (fun k ↦ v k m) i‖ ^ 2)⁻¹ •
        ⟪gramSchmidt ℂ (fun k ↦ v k m) i, v j m⟫_ℂ) • gramSchmidt ℂ (fun k ↦ v k m) i) hb
      fun i hi ↦ (hc i (Finset.mem_Iio.1 hi)).smul_totalSpace (hg i (Finset.mem_Iio.1 hi)))).congr
      (fun m _ ↦ ?_) ?_ <;> exact congrArg (TotalSpace.mk (b _)) (heq _)

/-- For a smooth Hermitian metric `(g, hI)`, Gram–Schmidt with respect to the Hermitian products
`g.complexInnerProductSpace hI` keeps smoothness on a set: if the sections `v i` along a map `b`
are `C^n` on `s` for `i ≤ j`, and the vectors `v i m` with `i < j` are complex linearly
independent at every point `m` of `s`, then the `j`-th Gram–Schmidt vector is `C^n` on `s`. -/
theorem contMDiffOn_gramSchmidt (g : ContMDiffRiemannianMetric IB n F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w) (j : ι)
    (hv : ∀ i ≤ j, ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n
      (fun m ↦ (⟨b m, v i m⟩ : TotalSpace F V)) s)
    (hli : ∀ m ∈ s, LinearIndepOn ℂ (fun i ↦ v i m) (Iio j)) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n
      (fun m ↦ (⟨b m, gramSchmidt ℂ (fun i ↦ v i m) j⟩ : TotalSpace F V)) s :=
  fun m hm ↦ g.contMDiffWithinAt_gramSchmidt hI j (fun i hi ↦ hv i hi m hm) (hli m hm)

/-- For a smooth Hermitian metric `(g, hI)`, normalized Gram–Schmidt with respect to the
Hermitian products `g.complexInnerProductSpace hI` keeps smoothness within a set at a point: if
the sections `v i` along a map `b` are `C^n` within `s` at `x` for `i ≤ j`, and the vectors
`v i x` with `i ≤ j` are complex linearly independent, then the `j`-th normalized Gram–Schmidt
vector is `C^n` within `s` at `x`.

This is the complex counterpart of Tau Ceti's `ContMDiffWithinAt.gramSchmidtNormed_bundle`. -/
theorem contMDiffWithinAt_gramSchmidtNormed (g : ContMDiffRiemannianMetric IB n F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w) (j : ι)
    (hv : ∀ i ≤ j, ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n
      (fun m ↦ (⟨b m, v i m⟩ : TotalSpace F V)) s x)
    (hli : LinearIndepOn ℂ (fun i ↦ v i x) (Iic j)) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n
      (fun m ↦ (⟨b m, gramSchmidtNormed ℂ (fun i ↦ v i m) j⟩ : TotalSpace F V)) s x := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  have hg := g.contMDiffWithinAt_gramSchmidt hI j hv (hli.mono Iio_subset_Iic_self)
  have h0 : gramSchmidt ℂ (fun i ↦ v i x) j ≠ 0 := gramSchmidt_ne_zero_coe j hli
  have hc : ContMDiffWithinAt IM 𝓘(ℝ, ℂ) n
      (fun m ↦ ((‖gramSchmidt ℂ (fun i ↦ v i m) j‖⁻¹ : ℝ) : ℂ)) s x :=
    Complex.ofRealCLM.contMDiff.contMDiffAt.comp_contMDiffWithinAt x
      ((hg.norm_bundle h0).inv₀ (norm_ne_zero_iff.2 h0))
  have heq (m : M) : gramSchmidtNormed ℂ (fun i ↦ v i m) j =
      ((‖gramSchmidt ℂ (fun i ↦ v i m) j‖⁻¹ : ℝ) : ℂ) • gramSchmidt ℂ (fun i ↦ v i m) j := by
    rw [gramSchmidtNormed, Complex.ofReal_inv]
    -- As in `contMDiffWithinAt_gramSchmidt`, the two sides differ only in the path to
    -- `Module ℂ`.
    rfl
  refine (hc.smul_totalSpace hg).congr (fun m _ ↦ ?_) ?_ <;>
    exact congrArg (TotalSpace.mk (b _)) (heq _)

/-- For a smooth Hermitian metric `(g, hI)`, normalized Gram–Schmidt with respect to the
Hermitian products `g.complexInnerProductSpace hI` keeps smoothness on a set: if the sections
`v i` along a map `b` are `C^n` on `s` for `i ≤ j`, and complex linearly independent for
`i ≤ j` at every point of `s`, then the `j`-th normalized Gram–Schmidt vector is `C^n` on `s`. -/
theorem contMDiffOn_gramSchmidtNormed (g : ContMDiffRiemannianMetric IB n F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w) (j : ι)
    (hv : ∀ i ≤ j, ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n
      (fun m ↦ (⟨b m, v i m⟩ : TotalSpace F V)) s)
    (hli : ∀ m ∈ s, LinearIndepOn ℂ (fun i ↦ v i m) (Iic j)) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n
      (fun m ↦ (⟨b m, gramSchmidtNormed ℂ (fun i ↦ v i m) j⟩ : TotalSpace F V)) s :=
  fun m hm ↦ g.contMDiffWithinAt_gramSchmidtNormed hI j (fun i hi ↦ hv i hi m hm) (hli m hm)

end GramSchmidt

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
  choose ob hob' using fun x (hx : x ∈ U) ↦ (hon x hx).exists_orthonormalBasis_coe_eq
    (by rw [VectorBundle.finrank_eq ℂ F V x, finrank_eq_card_basis b])
  have hob (x : B) (hx : x ∈ U) (j : ι) : ob x hx j = s j x := congrFun (hob' x hx) j
  have htx (x : B) (hx : x ∈ U) :
      (complexDoubledFrame s · x) = ⇑(Complex.basisOneI.smulTower (ob x hx).toBasis) := by
    ext ij
    simp [complexDoubledFrame_apply, Basis.smulTower_apply, hob]
  have ht : IsLocalFrameOn IB F n (complexDoubledFrame s) U :=
    .of_forall_exists_basis (fun x hx ↦ ⟨_, (htx x hx).symm⟩) fun ij ↦
      (contMDiffOn_const.smul_totalSpace (hs ij.2)).congr fun x _ ↦ by
        rw [complexDoubledFrame_apply]
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

/-- For a smooth Hermitian metric `(g, hI)` on a smooth complex vector bundle, and a complex
linear trivialization `e` in the maximal atlas of `C^n` trivializations, each vector of the local
unitary frame `e.orthonormalFrameAt c b` is a `C^n` section over the base set of `e`: for every
`w`, the section `y ↦ e.orthonormalFrameAt c b y w` is `C^n` on `e.baseSet`.

This is the complex counterpart of Tau Ceti's
`Bundle.Trivialization.contMDiffOn_orthonormalBasis_of_mem_maximalAtlas`. -/
theorem _root_.Bundle.Trivialization.contMDiffOn_totalSpaceMk_orthonormalFrameAt_complex
    (g : ContMDiffRiemannianMetric IB n F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
    (e : Trivialization F (π F V)) [e.IsLinear ℂ]
    (he : e.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F V))
    {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι] (c : Basis ι ℂ F)
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (b : OrthonormalBasis ι ℂ W)
    (w : W) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n
      (fun y ↦ (⟨y, e.orthonormalFrameAt c b y w⟩ : TotalSpace F V)) e.baseSet := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  have hs (j : ι) : ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n
      (fun y ↦ (⟨y, e.symm y (c j)⟩ : TotalSpace F V)) e.baseSet :=
    (Trivialization.contMDiffOn_section_iff_of_mem_maximalAtlas he subset_rfl).2
      (contMDiffOn_const.congr fun y hy ↦ by rw [e.apply_mk_symm hy])
  have hli {y : B} (hy : y ∈ e.baseSet) : LinearIndependent ℂ fun j ↦ e.symm y (c j) := by
    convert (c.map (e.linearEquivAt ℂ y hy).symm).linearIndependent with j
    simp [e.linearEquivAt_symm_apply]
  have hσ (i : ι) : ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (fun y ↦ (⟨y,
      gramSchmidtNormed ℂ (fun j ↦ e.symm y (c j)) i⟩ : TotalSpace F V)) e.baseSet :=
    g.contMDiffOn_gramSchmidtNormed hI i (fun j _ ↦ hs j) fun y hy ↦ (hli hy).linearIndepOn _
  refine (ContMDiffOn.sum_sectionAlong Finset.univ
    (fun i y ↦ ⟪b i, w⟫_ℂ • gramSchmidtNormed ℂ (fun j ↦ e.symm y (c j)) i) contMDiffOn_id
    fun i _ ↦ contMDiffOn_const.smul_totalSpace (hσ i)).congr fun y hy ↦ ?_
  rw [e.orthonormalFrameAt_of_mem c b hy, e.orthonormalFrame_apply]
  simp only [e.orthonormalBasis_apply, e.symmL_apply (R := ℂ) hy]

end Bundle.ContMDiffRiemannianMetric
