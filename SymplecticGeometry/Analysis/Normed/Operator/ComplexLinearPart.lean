/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Instances.RealVectorSpace
import TauCeti.Analysis.Normed.Module.RCLike.Basic

/-!
# Complex-linear and complex-antilinear parts of an operator: bounds, scalars, smoothness

For a continuous real-linear operator `Ψ` between complex normed spaces, whose real structures may
be given separately from the complex ones as long as they are compatible with them, Tau Ceti's
`ContinuousLinearMap.complexLinearPart` and `ContinuousLinearMap.complexAntilinearPart` both have
operator norm at most `‖Ψ‖` (`ContinuousLinearMap.norm_complexLinearPart_le`,
`ContinuousLinearMap.norm_complexAntilinearPart_le`), with pointwise forms. Seen as a
real-linear operator by Tau Ceti's `ContinuousLinearMap.complexAntilinearPartL`, the
complex-antilinear part keeps its operator norm
(`ContinuousLinearMap.norm_complexAntilinearPartL_apply`), so `complexAntilinearPartL` itself has
operator norm at most `1` (`ContinuousLinearMap.norm_complexAntilinearPartL_le`). The bound on
the complex-antilinear part also makes it a continuous real-linear map into the
complex-antilinear operators, `ContinuousLinearMap.complexAntilinearPartCLM`, again of operator
norm at most `1` (`ContinuousLinearMap.norm_complexAntilinearPartCLM_le`).

For complex normed spaces with the real structure they restrict to, a continuous
complex-antilinear operator is also a continuous real-linear one, by Mathlib's
`AddMonoidHom.toRealLinearMap`, with the same operator norm. This gives a real-linear isometry
`ContinuousLinearMap.restrictScalarsₛₗLI` from the complex-antilinear operators into the
real-linear ones. Tau Ceti's
`ContinuousLinearMap.complexAntilinearPartL` is `ContinuousLinearMap.complexAntilinearPartCLM`
followed by this isometry
(`ContinuousLinearMap.restrictScalarsₛₗLI_comp_complexAntilinearPartCLM`), and a
complex-antilinear operator is its own complex-antilinear part
(`ContinuousLinearMap.complexAntilinearPart_restrictScalarsₛₗLI`).

Each value of either part is half the sum of two vectors of norm at most `‖Ψ‖ * ‖v‖`, so the
pointwise bounds follow from Tau Ceti's `TauCeti.norm_two_inv_smul_add_le`.

For topological complex modules whose real structure is compatible with the complex one, the
setting of Tau Ceti's versions for real scalars, both parts commute with complex scalars
(`ContinuousLinearMap.complexLinearPart_complex_smul`,
`ContinuousLinearMap.complexAntilinearPart_complex_smul`). In the normed compatible setting of
the first paragraph, their values at a fixed vector are as smooth as the operator
(`ContDiffOn.complexLinearPart_apply`, `ContDiffOn.complexAntilinearPart_apply`).

The last section is about forms with values in a complex line `L` whose norm comes from a real
inner product, such as a fibre of a Hermitian line bundle. Multiplication by `i` is an isometry,
so `i • u` is orthogonal to `u` (`real_inner_I_smul_self_eq_zero`), and the vectors orthogonal to
a nonzero `u` are the real multiples of `i • u`. For two of them, `a + i • b` and `a - i • b` have
the same norm (`norm_add_I_smul_eq_norm_sub_I_smul`). So if every value of a real-linear map `η`
is orthogonal to a nonzero `u`, its complex-linear and complex-antilinear parts have values of
equal norms: for Tau Ceti's algebraic parts `TauCeti.complexLinearPart` and
`TauCeti.complexAntilinearPart`, for any endomorphism `J` of the source
(`TauCeti.norm_complexLinearPart_apply_eq_norm_complexAntilinearPart_apply`), and for the
continuous parts of an operator on a complex normed space, with equal operator norms
(`ContinuousLinearMap.norm_complexLinearPart_eq_norm_complexAntilinearPart`). This is the
pointwise step of the bound on `|s|` at the critical points of `log |s|²` in [Donaldson1996].

## References

* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
-/

public section

namespace ContinuousLinearMap

section Module

variable {E F : Type*} [AddCommGroup E] [TopologicalSpace E] [Module ℝ E] [Module ℂ E]
  [IsScalarTower ℝ ℂ E] [ContinuousConstSMul ℂ E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module ℝ F] [Module ℂ F]
  [IsScalarTower ℝ ℂ F] [ContinuousConstSMul ℝ F] [ContinuousConstSMul ℂ F]

/-- The complex-linear part commutes with complex scalar multiplication. -/
@[simp]
theorem complexLinearPart_complex_smul (c : ℂ) (Ψ : E →L[ℝ] F) :
    (c • Ψ).complexLinearPart = c • Ψ.complexLinearPart := by
  ext v
  simp only [complexLinearPart_apply, smul_apply]
  rw [smul_comm Complex.I c]
  module

/-- The complex-antilinear part commutes with complex scalar multiplication. -/
@[simp]
theorem complexAntilinearPart_complex_smul (c : ℂ) (Ψ : E →L[ℝ] F) :
    (c • Ψ).complexAntilinearPart = c • Ψ.complexAntilinearPart := by
  ext v
  simp only [complexAntilinearPart_apply, smul_apply]
  rw [smul_comm Complex.I c]
  module

end Module

section CompatibleReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F]

/-- The value of the complex-linear part of a real-linear operator `Ψ` at `v` has norm at most
`‖Ψ‖ * ‖v‖`. -/
theorem norm_complexLinearPart_apply_le (Ψ : E →L[ℝ] F) (v : E) :
    ‖Ψ.complexLinearPart v‖ ≤ ‖Ψ‖ * ‖v‖ := by
  rw [complexLinearPart_apply, sub_eq_add_neg]
  exact TauCeti.norm_two_inv_smul_add_le (Ψ.le_opNorm v)
    (by simpa [norm_smul] using Ψ.le_opNorm (Complex.I • v))

/-- The value of the complex-antilinear part of a real-linear operator `Ψ` at `v` has norm at
most `‖Ψ‖ * ‖v‖`. -/
theorem norm_complexAntilinearPart_apply_le (Ψ : E →L[ℝ] F) (v : E) :
    ‖Ψ.complexAntilinearPart v‖ ≤ ‖Ψ‖ * ‖v‖ := by
  rw [complexAntilinearPart_apply]
  exact TauCeti.norm_two_inv_smul_add_le (Ψ.le_opNorm v)
    (by simpa [norm_smul] using Ψ.le_opNorm (Complex.I • v))

/-- The complex-linear part of a real-linear operator has norm at most that of the operator. -/
theorem norm_complexLinearPart_le (Ψ : E →L[ℝ] F) :
    ‖Ψ.complexLinearPart‖ ≤ ‖Ψ‖ :=
  opNorm_le_bound _ (norm_nonneg Ψ) Ψ.norm_complexLinearPart_apply_le

/-- The complex-antilinear part of a real-linear operator has norm at most that of the
operator. -/
theorem norm_complexAntilinearPart_le (Ψ : E →L[ℝ] F) :
    ‖Ψ.complexAntilinearPart‖ ≤ ‖Ψ‖ :=
  opNorm_le_bound _ (norm_nonneg Ψ) Ψ.norm_complexAntilinearPart_apply_le

/-- Tau Ceti's `ContinuousLinearMap.complexAntilinearPartL`, which sees the complex-antilinear part
of an operator as a real-linear operator, preserves its operator norm. -/
theorem norm_complexAntilinearPartL_apply (Ψ : E →L[ℝ] F) :
    ‖complexAntilinearPartL Ψ‖ = ‖Ψ.complexAntilinearPart‖ := by
  refine le_antisymm (opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_)
    (opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_)
  · rw [complexAntilinearPartL_apply_apply, ← complexAntilinearPart_apply]
    exact le_opNorm _ v
  · rw [complexAntilinearPart_apply, ← complexAntilinearPartL_apply_apply]
    exact le_opNorm _ v

/-- Tau Ceti's `ContinuousLinearMap.complexAntilinearPartL` has operator norm at most `1`. -/
theorem norm_complexAntilinearPartL_le :
    ‖(complexAntilinearPartL : (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F)‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun Ψ ↦ by
    rw [one_mul, norm_complexAntilinearPartL_apply]
    exact norm_complexAntilinearPart_le Ψ

/-- The complex-antilinear part, as a continuous real-linear map from the real-linear operators
to the complex-antilinear ones. Tau Ceti's `ContinuousLinearMap.complexAntilinearPartL` is the
same map, with values seen as real-linear operators. -/
noncomputable def complexAntilinearPartCLM : (E →L[ℝ] F) →L[ℝ] E →L⋆[ℂ] F :=
  LinearMap.mkContinuous
    { toFun := complexAntilinearPart
      map_add' := complexAntilinearPart_add
      map_smul' := complexAntilinearPart_smul }
    1 fun Ψ ↦ by simpa using norm_complexAntilinearPart_le Ψ

@[simp]
theorem complexAntilinearPartCLM_apply (Ψ : E →L[ℝ] F) :
    complexAntilinearPartCLM Ψ = Ψ.complexAntilinearPart :=
  (rfl)

/-- The complex-antilinear part, as a continuous real-linear map into the complex-antilinear
operators, has operator norm at most `1`. -/
theorem norm_complexAntilinearPartCLM_le :
    ‖(complexAntilinearPartCLM : (E →L[ℝ] F) →L[ℝ] E →L⋆[ℂ] F)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end CompatibleReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- The inclusion of the continuous complex-antilinear operators into the continuous real-linear
ones, as a real-linear isometry: a complex-antilinear operator, being additive and continuous, is
real-linear (`AddMonoidHom.toRealLinearMap`), with the same operator norm. -/
noncomputable def restrictScalarsₛₗLI : (E →L⋆[ℂ] F) →ₗᵢ[ℝ] E →L[ℝ] F where
  toFun f := (f : E →+ F).toRealLinearMap f.continuous
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

@[simp]
theorem coe_restrictScalarsₛₗLI (f : E →L⋆[ℂ] F) : ⇑(restrictScalarsₛₗLI f) = f :=
  (rfl)

theorem restrictScalarsₛₗLI_apply (f : E →L⋆[ℂ] F) (v : E) : restrictScalarsₛₗLI f v = f v :=
  (rfl)

/-- Tau Ceti's `ContinuousLinearMap.complexAntilinearPartL` is
`ContinuousLinearMap.complexAntilinearPartCLM` followed by the inclusion of the
complex-antilinear operators into the real-linear ones. -/
theorem restrictScalarsₛₗLI_comp_complexAntilinearPartCLM :
    (restrictScalarsₛₗLI.toContinuousLinearMap.comp complexAntilinearPartCLM :
      (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F) = complexAntilinearPartL := by
  ext Ψ v
  simp

/-- A complex-antilinear operator is its own complex-antilinear part. -/
@[simp]
theorem complexAntilinearPart_restrictScalarsₛₗLI (f : E →L⋆[ℂ] F) :
    (restrictScalarsₛₗLI f).complexAntilinearPart = f := by
  ext v
  simp only [complexAntilinearPart_apply, coe_restrictScalarsₛₗLI, map_smulₛₗ, Complex.conj_I,
    neg_smul, smul_neg, smul_smul, Complex.I_mul_I, neg_neg]
  module

end ContinuousLinearMap

variable {G E F : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {f : G → E →L[ℝ] F} {s : Set G} {n : WithTop ℕ∞}

/-- If a family of real-linear operators is `C^n` on `s`, so is the value of its complex-linear
part at any vector. -/
theorem ContDiffOn.complexLinearPart_apply (hf : ContDiffOn ℝ n f s) (v : E) :
    ContDiffOn ℝ n (fun x ↦ (f x).complexLinearPart v) s := by
  simp only [ContinuousLinearMap.complexLinearPart_apply]
  exact ((hf.clm_apply contDiffOn_const).sub
    ((hf.clm_apply contDiffOn_const).const_smul Complex.I)).const_smul _

/-- If a family of real-linear operators is `C^n` on `s`, so is the value of its
complex-antilinear part at any vector. -/
theorem ContDiffOn.complexAntilinearPart_apply (hf : ContDiffOn ℝ n f s) (v : E) :
    ContDiffOn ℝ n (fun x ↦ (f x).complexAntilinearPart v) s := by
  simp only [ContinuousLinearMap.complexAntilinearPart_apply]
  exact ((hf.clm_apply contDiffOn_const).add
    ((hf.clm_apply contDiffOn_const).const_smul Complex.I)).const_smul _

/-! ### Equal norms of the two parts of a form with values in a complex line -/

section ComplexLine

open scoped RealInnerProductSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [NormedSpace ℂ L]

/-- In a complex normed space whose norm comes from a real inner product, `i • u` is orthogonal
to `u`: multiplication by `i` is an isometry, so `‖i • u + u‖ = ‖i • u - u‖`. -/
theorem real_inner_I_smul_self_eq_zero (u : L) : ⟪Complex.I • u, u⟫ = 0 := by
  have h : ‖Complex.I • u + u‖ = ‖Complex.I • u - u‖ := by
    rw [show Complex.I • u + u = (Complex.I + 1) • u by rw [add_smul, one_smul],
      show Complex.I • u - u = (Complex.I - 1) • u by rw [sub_smul, one_smul], norm_smul,
      norm_smul, ← Complex.norm_conj (Complex.I + 1), map_add, Complex.conj_I, map_one, ← norm_neg]
    ring_nf
  have h₁ := real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
    (Complex.I • u) u
  have h₂ := real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two
    (Complex.I • u) u
  rw [h] at h₁
  linarith

variable [IsScalarTower ℝ ℂ L]

/-- In a complex normed space whose norm comes from a real inner product, the real inner product
of `c • u` with `u` is `re c * ‖u‖ ^ 2`. -/
theorem real_inner_complex_smul_self (c : ℂ) (u : L) : ⟪c • u, u⟫ = c.re * ‖u‖ ^ 2 := by
  have hr (r : ℝ) (w : L) : (r : ℂ) • w = r • w := by simpa using algebraMap_smul ℂ r w
  conv_lhs => rw [← Complex.re_add_im c, add_smul, mul_comm, ← smul_smul, smul_comm, hr, hr,
    inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_I_smul_self_eq_zero,
    real_inner_self_eq_norm_sq]
  simp

/-- Let `L` be a complex line whose norm comes from a real inner product. If `a` and `b` are both
orthogonal to a nonzero `u`, then `‖a + i • b‖ = ‖a - i • b‖`: both are imaginary multiples of
`u`, `a = i α • u` and `b = i β • u` with `α`, `β` real, and `|i α - β| = |i α + β|`. -/
theorem norm_add_I_smul_eq_norm_sub_I_smul (hL : Module.finrank ℂ L = 1) {u a b : L}
    (hu : u ≠ 0) (ha : ⟪a, u⟫ = 0) (hb : ⟪b, u⟫ = 0) :
    ‖a + Complex.I • b‖ = ‖a - Complex.I • b‖ := by
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' u hu).1 hL a
  obtain ⟨d, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' u hu).1 hL b
  have hu2 : ‖u‖ ^ 2 ≠ 0 := by positivity
  rw [real_inner_complex_smul_self, mul_eq_zero, or_iff_left hu2] at ha hb
  rw [smul_smul, ← add_smul, ← sub_smul, norm_smul, norm_smul, ← Complex.norm_conj,
    ← norm_neg (c - _)]
  congr 2
  apply Complex.ext <;> simp [ha, hb]

/-- Let `η` be a real-linear map from a real vector space `T` with an endomorphism `J` (in
practice a complex structure) to a complex line `L` whose norm comes from a real inner product.
If every value of `η` is orthogonal to a nonzero `u`, then `TauCeti.complexLinearPart` and
`TauCeti.complexAntilinearPart` of `η`, for `J` and multiplication by `i`, take values of equal
norms. -/
theorem TauCeti.norm_complexLinearPart_apply_eq_norm_complexAntilinearPart_apply {T : Type*}
    [AddCommGroup T] [Module ℝ T] (J : T →ₗ[ℝ] T) (hL : Module.finrank ℂ L = 1) {u : L}
    (hu : u ≠ 0) {η : T →ₗ[ℝ] L} (hη : ∀ v, ⟪η v, u⟫ = 0) (v : T) :
    ‖complexLinearPart J (DistribSMul.toLinearMap ℝ L Complex.I) η v‖ =
      ‖complexAntilinearPart J (DistribSMul.toLinearMap ℝ L Complex.I) η v‖ := by
  simp only [complexLinearPart_apply, complexAntilinearPart_apply, DistribSMul.toLinearMap_apply,
    norm_smul, norm_add_I_smul_eq_norm_sub_I_smul hL hu (hη v) (hη (J v))]

namespace ContinuousLinearMap

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace ℂ W]
  [IsScalarTower ℝ ℂ W]

/-- Let `Ψ` be a continuous real-linear operator from a complex normed space to a complex line
whose norm comes from a real inner product. If every value of `Ψ` is orthogonal to a nonzero `u`,
its complex-linear and complex-antilinear parts have values of equal norms. -/
theorem norm_complexLinearPart_apply_eq_norm_complexAntilinearPart_apply
    (hL : Module.finrank ℂ L = 1) {u : L} (hu : u ≠ 0) {Ψ : W →L[ℝ] L} (hΨ : ∀ v, ⟪Ψ v, u⟫ = 0)
    (v : W) : ‖Ψ.complexLinearPart v‖ = ‖Ψ.complexAntilinearPart v‖ := by
  rw [complexLinearPart_apply, complexAntilinearPart_apply, norm_smul, norm_smul,
    norm_add_I_smul_eq_norm_sub_I_smul hL hu (hΨ v) (hΨ _)]

/-- Let `Ψ` be a continuous real-linear operator from a complex normed space to a complex line
whose norm comes from a real inner product. If every value of `Ψ` is orthogonal to a nonzero `u`,
its complex-linear and complex-antilinear parts have equal operator norms. -/
theorem norm_complexLinearPart_eq_norm_complexAntilinearPart (hL : Module.finrank ℂ L = 1)
    {u : L} (hu : u ≠ 0) {Ψ : W →L[ℝ] L} (hΨ : ∀ v, ⟪Ψ v, u⟫ = 0) :
    ‖Ψ.complexLinearPart‖ = ‖Ψ.complexAntilinearPart‖ :=
  opNorm_ext _ _ (norm_complexLinearPart_apply_eq_norm_complexAntilinearPart_apply hL hu hΨ)

end ContinuousLinearMap

end ComplexLine

end
