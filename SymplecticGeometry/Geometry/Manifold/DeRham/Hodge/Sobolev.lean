/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DeRham.Hodge.L2
public import TauCeti.Geometry.Manifold.Riemannian.Codifferential

/-!
# The Hodge `H¹` space of differential forms

Let `M` be a closed oriented Riemannian manifold, `Δ = dδ + δd` its Hodge Laplacian on real
`k`-forms and `⟪α, β⟫ = ∫_M ⟨α, β⟩ dV` the `L²` inner product of smooth forms
(`TauCeti.SmoothForm.l2Inner`). Since `Δ` is symmetric and nonnegative for this inner product,
`⟪α, β⟫ + ⟪Δα, β⟫ = ⟪α, β⟫ + ⟪dα, dβ⟫ + ⟪δα, δβ⟫` is again an inner product on the smooth forms,
and it is definite because the `L²` part is. The Hilbert space `SymplecticGeometry.H1Form o hkl`
is the completion of the smooth `k`-forms for it.

Its norm dominates the `L²` norm, so the identity of smooth forms extends to a continuous linear
map `H1Form.toL2 : H1Form o hkl →L[ℝ] L2Form o k` of norm at most one. The
**Dirichlet form** `H1Form.dirichlet u v = ⟪u, v⟫ - ⟪toL2 u, toL2 v⟫` is a continuous bilinear
form on `H1Form o hkl` that extends `⟪Δα, β⟫`, so that `‖u‖ ^ 2 = dirichlet u u + ‖toL2 u‖ ^ 2`
(Gårding's identity) holds by definition. Against a smooth form it is the weak Laplacian:
`dirichlet u (ofSmooth φ) = ⟪toL2 u, Δφ⟫`, which gives Green's identity
`⟪u, ofSmooth φ⟫ = ⟪toL2 u, φ + Δφ⟫`. Hence an element `u` with `toL2 u = 0` is orthogonal to
every smooth form, and `toL2` is injective. The Dirichlet form is nonnegative, so it satisfies
the Cauchy–Schwarz inequality, which bounds `|⟪toL2 u, Δφ⟫|` by `‖u‖` times the `H¹` norm
`√(‖φ‖ ^ 2 + ⟪Δφ, φ⟫)` of `φ`.

## Main definitions and results

* `SymplecticGeometry.H1Form o hkl`: the Hilbert space, with `H1Form.ofSmooth`,
  `H1Form.inner_ofSmooth`, `H1Form.norm_ofSmooth_sq`, `H1Form.ofSmooth_injective`,
  `H1Form.denseRange_ofSmooth` and `H1Form.induction_on`.
* `SymplecticGeometry.H1Form.toL2`: the inclusion into `L2Form o k`, with `toL2_ofSmooth`,
  `norm_toL2_le`, `inner_ofSmooth_right` and `toL2_injective`.
* `SymplecticGeometry.H1Form.dirichlet`: the Dirichlet form, with `dirichlet_ofSmooth`,
  `dirichlet_comm`, `dirichlet_self_nonneg`, `norm_sq_eq_dirichlet_add`,
  `dirichlet_ofSmooth_right` and `abs_dirichlet_le`.
* `SymplecticGeometry.H1Form.abs_inner_toL2_ofSmooth_hodgeLaplacian_le`: the bound
  `|⟪toL2 u, Δφ⟫| ≤ ‖u‖ * √(‖φ‖ ^ 2 + ⟪Δφ, φ⟫)`, the hypothesis of
  `SymplecticGeometry.L2Form.isLocallySobolev_one_of_forall_inner`.

## Implementation notes

The construction of `H1Form` through the type synonym `SymplecticGeometry.PreH1Form`, and the
names and proofs of `ofSmooth`, `inner_ofSmooth`, `denseRange_ofSmooth`, `induction_on`,
`dirichlet`, `dirichlet_comm`, `dirichlet_self_nonneg`, `norm_sq_eq_dirichlet_add`,
`dirichlet_ofSmooth_right`, `inner_ofSmooth_right` and `toL2_injective`, adapt those of Tau
Ceti's `TauCeti.Manifold.SobolevH1` (`TauCeti/Geometry/Manifold/Riemannian/Sobolev/H1.lean`,
itself after Mathlib's `PreGNS`: `SobolevH1.ofSmooth`, `SobolevH1.dirichletForm`,
`SobolevH1.dirichletForm_comm`, `SobolevH1.dirichletForm_self_nonneg`,
`SobolevH1.norm_sq_eq_dirichletForm_add`, `SobolevH1.dirichletForm_ofSmooth_right`,
`SobolevH1.inner_ofSmooth_right` and `SobolevH1.toLp_injective`), with smooth `k`-forms and the
Hodge Laplacian in place of smooth functions and the gradient, and `L2Form` in place of
`Lp ℝ 2`. Since the `L²` part of the inner product is definite, the type synonym carries an
`InnerProductSpace.Core` rather than a `PreInnerProductSpace.Core`, as in `L2.lean`. As
`L2Form.localize` does, `toL2` is Mathlib's extension `LinearMap.extendOfNorm` of the
inclusion of smooth forms into `L2Form o k`, which is bounded by `norm_l2FormOfSmooth_le`.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer, 1983, Chapter 6.
* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §6.
-/

public section

open Bundle MeasureTheory
open scoped Manifold ContDiff InnerProductSpace

noncomputable section

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {m k l : ℕ}

namespace SymplecticGeometry

open TauCeti TauCeti.SmoothForm

variable [IsManifold I ∞ M]

/-- The smooth real `k`-forms, as the space on which the Hodge `H¹` inner product of the
orientation `o` and the splitting `hkl : k + l = m` is defined before completion. -/
@[nolint unusedArguments]
def PreH1Form (_o : Manifold.Orientation I M (Fin m)) (_hkl : k + l = m) : Type _ :=
  SmoothForm I M ℝ k

variable (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)

instance : AddCommGroup (PreH1Form o hkl) := inferInstanceAs (AddCommGroup (SmoothForm I M ℝ k))

instance : Module ℝ (PreH1Form o hkl) := inferInstanceAs (Module ℝ (SmoothForm I M ℝ k))

variable {o hkl}

namespace PreH1Form

/-- A smooth form, as an element of `PreH1Form`. -/
def toPreH1Form : SmoothForm I M ℝ k ≃ₗ[ℝ] PreH1Form o hkl := LinearEquiv.refl ℝ _

/-- An element of `PreH1Form`, as a smooth form. -/
def ofPreH1Form : PreH1Form o hkl ≃ₗ[ℝ] SmoothForm I M ℝ k := toPreH1Form.symm

@[simp]
theorem toPreH1Form_ofPreH1Form (u : PreH1Form o hkl) : toPreH1Form (ofPreH1Form u) = u :=
  (rfl)

@[simp]
theorem ofPreH1Form_toPreH1Form (α : SmoothForm I M ℝ k) :
    ofPreH1Form (toPreH1Form α : PreH1Form o hkl) = α :=
  (rfl)

variable [CompactSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [BoundarylessManifold I M] [T2Space M]

/-- The Hodge `H¹` inner product `⟪α, β⟫ + ⟪Δα, β⟫` on `PreH1Form o hkl`. -/
abbrev innerCore : InnerProductSpace.Core ℝ (PreH1Form o hkl) where
  inner u v := l2Inner o (ofPreH1Form u) (ofPreH1Form v) +
    l2Inner o (hodgeLaplacian o hkl (ofPreH1Form u)) (ofPreH1Form v)
  conj_inner_symm u v := by
    rw [conj_trivial, l2Inner_comm o (ofPreH1Form v),
      l2Inner_hodgeLaplacian_eq_l2Inner_hodgeLaplacian, l2Inner_comm o (ofPreH1Form v)]
  re_inner_nonneg u :=
    add_nonneg (l2Inner_self_nonneg o _) (l2Inner_hodgeLaplacian_self_nonneg o hkl _)
  add_left u v w := by
    simp only [map_add, l2Inner_add_left]
    ring
  smul_left u v r := by
    simp only [map_smul, l2Inner_smul_left, conj_trivial]
    ring
  definite u h := ofPreH1Form.injective <| by
    rw [map_zero]
    refine (l2Inner_self_eq_zero_iff o).1 (le_antisymm ?_ (l2Inner_self_nonneg o _))
    linarith [l2Inner_hodgeLaplacian_self_nonneg o hkl (ofPreH1Form u)]

instance : NormedAddCommGroup (PreH1Form o hkl) :=
  InnerProductSpace.Core.toNormedAddCommGroup (cd := innerCore)

instance : InnerProductSpace ℝ (PreH1Form o hkl) :=
  InnerProductSpace.ofCore innerCore.toCore

/-- The inner product of two smooth forms in `PreH1Form` is `⟪α, β⟫ + ⟪Δα, β⟫`. -/
theorem inner_toPreH1Form (α β : SmoothForm I M ℝ k) :
    ⟪(toPreH1Form α : PreH1Form o hkl), toPreH1Form β⟫_ℝ =
      l2Inner o α β + l2Inner o (hodgeLaplacian o hkl α) β :=
  (rfl)

end PreH1Form

open PreH1Form

variable [CompactSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [BoundarylessManifold I M] [T2Space M]

/-- The **Hodge `H¹` space** of `k`-forms on a closed oriented Riemannian manifold of dimension
`m = k + l`: the completion of the smooth real `k`-forms for the inner product
`⟪α, β⟫ + ⟪Δα, β⟫`, where `⟪·, ·⟫` is the `L²` inner product and `Δ` the Hodge Laplacian. -/
abbrev H1Form (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :=
  UniformSpace.Completion (PreH1Form o hkl)

namespace H1Form

/-- The inclusion of the smooth forms into `H1Form o hkl`. -/
def ofSmooth : SmoothForm I M ℝ k →ₗ[ℝ] H1Form o hkl :=
  UniformSpace.Completion.toComplL.toLinearMap ∘ₗ toPreH1Form.toLinearMap

/-- A smooth form in `H1Form o hkl` is the image of its copy in the pre-completion space. -/
theorem ofSmooth_apply (α : SmoothForm I M ℝ k) :
    (ofSmooth α : H1Form o hkl) = ((toPreH1Form α : PreH1Form o hkl) : H1Form o hkl) :=
  (rfl)

/-- The inner product of two smooth forms in `H1Form o hkl` is `⟪α, β⟫ + ⟪Δα, β⟫`. -/
@[simp]
theorem inner_ofSmooth (α β : SmoothForm I M ℝ k) :
    ⟪(ofSmooth α : H1Form o hkl), ofSmooth β⟫_ℝ =
      l2Inner o α β + l2Inner o (hodgeLaplacian o hkl α) β := by
  rw [ofSmooth_apply, ofSmooth_apply, UniformSpace.Completion.inner_coe, inner_toPreH1Form]

/-- The squared norm of a smooth form in `H1Form o hkl` is `⟪α, α⟫ + ⟪Δα, α⟫`. -/
theorem norm_ofSmooth_sq (α : SmoothForm I M ℝ k) :
    ‖(ofSmooth α : H1Form o hkl)‖ ^ 2 = l2Inner o α α + l2Inner o (hodgeLaplacian o hkl α) α := by
  rw [← real_inner_self_eq_norm_sq, inner_ofSmooth]

/-- The inclusion of the smooth forms into `H1Form o hkl` is injective. -/
theorem ofSmooth_injective :
    Function.Injective (ofSmooth : SmoothForm I M ℝ k → H1Form o hkl) :=
  UniformSpace.Completion.coe_injective _ |>.comp toPreH1Form.injective

/-- The smooth forms are dense in `H1Form o hkl`. -/
theorem denseRange_ofSmooth : DenseRange (ofSmooth : SmoothForm I M ℝ k → H1Form o hkl) :=
  UniformSpace.Completion.denseRange_coe.comp toPreH1Form.surjective.denseRange
    (UniformSpace.Completion.continuous_coe _)

/-- **Induction principle for `H1Form o hkl`.** A closed property of elements of `H1Form o hkl`
that holds for all smooth forms holds everywhere. -/
@[elab_as_elim]
theorem induction_on {p : H1Form o hkl → Prop} (u : H1Form o hkl) (hp : IsClosed {u | p u})
    (h : ∀ α : SmoothForm I M ℝ k, p (ofSmooth α)) : p u :=
  denseRange_ofSmooth.induction_on u hp h

/-! ### The inclusion into `L2Form` -/

/-- The `L²` norm of a smooth form is at most its `H¹` norm. -/
theorem norm_l2FormOfSmooth_le (α : SmoothForm I M ℝ k) :
    ‖(L2Form.ofSmooth α : L2Form o k)‖ ≤ 1 * ‖(ofSmooth α : H1Form o hkl)‖ := by
  rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), L2Form.norm_ofSmooth_sq,
    norm_ofSmooth_sq]
  exact le_add_of_nonneg_right (l2Inner_hodgeLaplacian_self_nonneg o hkl α)

/-- The inclusion `H1Form o hkl → L2Form o k`: the continuous extension of the identity of smooth
forms. -/
def toL2 : H1Form o hkl →L[ℝ] L2Form o k :=
  (L2Form.ofSmooth : SmoothForm I M ℝ k →ₗ[ℝ] L2Form o k).extendOfNorm ofSmooth

/-- On a smooth form, `toL2` is the inclusion of smooth forms into `L2Form o k`. -/
@[simp]
theorem toL2_ofSmooth (α : SmoothForm I M ℝ k) :
    toL2 (ofSmooth α : H1Form o hkl) = L2Form.ofSmooth α :=
  LinearMap.extendOfNorm_eq denseRange_ofSmooth ⟨1, norm_l2FormOfSmooth_le⟩ α

/-- The inclusion into `L2Form o k` does not increase norms. -/
theorem norm_toL2_le (u : H1Form o hkl) : ‖toL2 u‖ ≤ ‖u‖ := by
  simpa [toL2] using
    LinearMap.norm_extendOfNorm_apply_le denseRange_ofSmooth 1 norm_l2FormOfSmooth_le u

/-! ### The Dirichlet form -/

/-- The **Dirichlet form** `D(u, v) = ⟪u, v⟫ - ⟪toL2 u, toL2 v⟫` on `H1Form o hkl`, the
continuous extension of `⟪Δα, β⟫` from smooth forms (`H1Form.dirichlet_ofSmooth`). -/
def dirichlet : H1Form o hkl →L[ℝ] H1Form o hkl →L[ℝ] ℝ :=
  innerSL ℝ - (innerSL ℝ).bilinearComp toL2 toL2

/-- The Dirichlet form is the `H¹` inner product minus the `L²` inner product. -/
theorem dirichlet_apply (u v : H1Form o hkl) :
    dirichlet u v = ⟪u, v⟫_ℝ - ⟪toL2 u, toL2 v⟫_ℝ :=
  (rfl)

/-- The Dirichlet form of two smooth forms is `⟪Δα, β⟫`. -/
@[simp]
theorem dirichlet_ofSmooth (α β : SmoothForm I M ℝ k) :
    dirichlet (ofSmooth α : H1Form o hkl) (ofSmooth β) = l2Inner o (hodgeLaplacian o hkl α) β := by
  rw [dirichlet_apply, inner_ofSmooth, toL2_ofSmooth, toL2_ofSmooth, L2Form.inner_ofSmooth,
    add_sub_cancel_left]

/-- The Dirichlet form is symmetric. -/
theorem dirichlet_comm (u v : H1Form o hkl) : dirichlet u v = dirichlet v u := by
  rw [dirichlet_apply, dirichlet_apply, real_inner_comm, real_inner_comm (toL2 u)]

/-- The Dirichlet form is nonnegative on the diagonal. -/
theorem dirichlet_self_nonneg (u : H1Form o hkl) : 0 ≤ dirichlet u u := by
  induction u using induction_on with
  | hp => exact isClosed_le continuous_const (by fun_prop)
  | h α => exact (dirichlet_ofSmooth α α).ge.trans' (l2Inner_hodgeLaplacian_self_nonneg o hkl α)

/-- **Gårding's identity**: the squared `H¹` norm is the Dirichlet energy plus the squared `L²`
norm. -/
theorem norm_sq_eq_dirichlet_add (u : H1Form o hkl) :
    ‖u‖ ^ 2 = dirichlet u u + ‖toL2 u‖ ^ 2 := by
  rw [dirichlet_apply, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, sub_add_cancel]

/-- **The Dirichlet form against a smooth form** is the weak Laplacian:
`D(u, φ) = ⟪toL2 u, Δφ⟫`. -/
theorem dirichlet_ofSmooth_right (u : H1Form o hkl) (φ : SmoothForm I M ℝ k) :
    dirichlet u (ofSmooth φ) = ⟪toL2 u, L2Form.ofSmooth (hodgeLaplacian o hkl φ)⟫_ℝ := by
  induction u using induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | h α =>
    rw [dirichlet_ofSmooth, toL2_ofSmooth, L2Form.inner_ofSmooth,
      l2Inner_hodgeLaplacian_eq_l2Inner_hodgeLaplacian]

/-- **Green's identity in `H1Form`**: the `H¹` inner product of `u` with a smooth form `φ` is
`⟪toL2 u, φ + Δφ⟫`. -/
theorem inner_ofSmooth_right (u : H1Form o hkl) (φ : SmoothForm I M ℝ k) :
    ⟪u, ofSmooth φ⟫_ℝ = ⟪toL2 u, L2Form.ofSmooth (φ + hodgeLaplacian o hkl φ)⟫_ℝ := by
  rw [map_add, inner_add_right, ← dirichlet_ofSmooth_right, dirichlet_apply, toL2_ofSmooth,
    add_sub_cancel]

/-- **The inclusion into `L2Form` is injective**: an element of `H1Form o hkl` that vanishes in
`L2Form o k` is orthogonal to every smooth form, by `inner_ofSmooth_right`, hence zero. -/
theorem toL2_injective : Function.Injective (toL2 : H1Form o hkl → L2Form o k) := by
  refine (injective_iff_map_eq_zero toL2).2 fun u hu ↦ ?_
  refine denseRange_ofSmooth.eq_zero_of_inner_left ℝ fun φ ↦ ?_
  rw [inner_ofSmooth_right, hu, inner_zero_left]

/-- **Cauchy–Schwarz inequality for the Dirichlet form**: `|D(u, v)| ≤ ‖u‖ * ‖v‖`. -/
theorem abs_dirichlet_le (u v : H1Form o hkl) : |dirichlet u v| ≤ ‖u‖ * ‖v‖ := by
  have hD (w : H1Form o hkl) : dirichlet w w ≤ ‖w‖ ^ 2 := by
    rw [norm_sq_eq_dirichlet_add]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hcs : dirichlet u v * dirichlet v u ≤ dirichlet u u * dirichlet v v :=
    LinearMap.BilinForm.apply_mul_apply_le_of_forall_zero_le
      (dirichlet (o := o) (hkl := hkl)).toLinearMap₁₂ dirichlet_self_nonneg u v
  rw [dirichlet_comm v u] at hcs
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow]
  calc dirichlet u v ^ 2 ≤ dirichlet u u * dirichlet v v := by rwa [sq]
    _ ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 :=
      mul_le_mul (hD u) (hD v) (dirichlet_self_nonneg v) (sq_nonneg _)

/-- The pairing of an element of `H1Form o hkl` with the Laplacian of a smooth form `φ` is
bounded by its norm times the Hodge `H¹` norm `√(‖φ‖ ^ 2 + ⟪Δφ, φ⟫)` of `φ`, computed in
`L2Form o k`. This is the hypothesis of `L2Form.isLocallySobolev_one_of_forall_inner` for
`toL2 u`. -/
theorem abs_inner_toL2_ofSmooth_hodgeLaplacian_le (u : H1Form o hkl) (φ : SmoothForm I M ℝ k) :
    |⟪toL2 u, L2Form.ofSmooth (hodgeLaplacian o hkl φ)⟫_ℝ| ≤
      ‖u‖ * √(‖(L2Form.ofSmooth φ : L2Form o k)‖ ^ 2 +
        ⟪(L2Form.ofSmooth (hodgeLaplacian o hkl φ) : L2Form o k), L2Form.ofSmooth φ⟫_ℝ) := by
  rw [← dirichlet_ofSmooth_right, L2Form.norm_ofSmooth_sq, L2Form.inner_ofSmooth,
    ← norm_ofSmooth_sq (hkl := hkl), Real.sqrt_sq (norm_nonneg _)]
  exact abs_dirichlet_le u (ofSmooth φ)

end H1Form

end SymplecticGeometry

end
