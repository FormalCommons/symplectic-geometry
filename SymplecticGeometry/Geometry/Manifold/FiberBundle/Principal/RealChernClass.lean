/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.Connection.Circle
public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DeRham.Map
import SymplecticGeometry.Geometry.Manifold.DeRham.Basic
import SymplecticGeometry.Geometry.Manifold.GroupAction.Opens

/-!
# The real first Chern class of a principal circle bundle

Let `P` be a smooth principal `Circle`-bundle over a finite-dimensional, boundaryless, Hausdorff,
σ-compact manifold `B`. Its **real first Chern class** is the de Rham class
`-(2π)⁻¹ [F_α] ∈ H²_dR(B)` of Chern–Weil theory, where `F_α` is the curvature of a connection form
`α` on `P` (`SymplecticGeometry.IsCircleConnectionForm.curvature`). It is defined with the
connection form chosen by `SymplecticGeometry.exists_isCircleConnectionForm`, and does not depend
on that choice: two connection forms differ by the pull-back `π^* a` of a `1`-form on `B`, so
their curvatures differ by the exact form `d a`.

The connection forms of the library take the value `1` on the fundamental vector field of
`circleLieGenerator`, so `F_α` is the curvature of McDuff–Salamon divided by `i`, and the
normalization `-(2π)⁻¹` agrees with that of the first Chern number: when `P` is the bundle of
unitary frames of a Hermitian complex line bundle `V` over a closed oriented surface, the integral
of `-(2π)⁻¹ F_α` is the first Chern number of `V`
(`SymplecticGeometry.Bundle.chernNumber_eq_integral_curvature`).

## Main definitions and results

* `SymplecticGeometry.realFirstChernClass IB P`: the real first Chern class of `P`.
* `SymplecticGeometry.IsCircleConnectionForm.realFirstChernClass_eq`: the class is
  `-(2π)⁻¹` times the class of the curvature of any connection form.
* `SymplecticGeometry.IsCircleConnectionForm.mk_sub_mk_eq_smul_realFirstChernClass_iff`: two
  closed `2`-forms differ in cohomology by `c` times the class exactly when
  `ω₁ - ω₂ + c (2π)⁻¹ F_α` is exact.
* `SymplecticGeometry.IsCircleConnectionForm.exists_curvature_eq_of_sub_mem_exactForms`: if
  `σ - F_α` is exact, then `σ` is the curvature of the connection form `α + π^* a`, for a
  primitive `a` of `σ - F_α`.
* `SymplecticGeometry.exists_isCircleConnectionForm_curvature_eq_iff`: a closed `2`-form `σ` is
  the curvature of a connection form exactly when `-(2π)⁻¹ [σ]` is the real first Chern class.
* `SymplecticGeometry.IsCircleConnectionForm.mpullback`,
  `SymplecticGeometry.IsCircleConnectionForm.curvature_mpullback`: for a smooth equivariant map
  `Φ : Q → P` of principal `Circle`-bundles covering `f : B' → B`, the pull-back `Φ^* α` is a
  connection form on `Q`, with curvature `f^* F_α`.
* `SymplecticGeometry.realFirstChernClass_map`: the real first Chern class of `Q` is the pull-back
  along `f` of that of `P`.
* `SymplecticGeometry.realFirstChernClass_eq_of_map`: the case `f = id`, so that `Q` and `P`
  have the same class; in particular the class is invariant under isomorphisms of circle bundles.

That `dΦ` carries fundamental vector fields to fundamental vector fields is Tau Ceti's
`TauCeti.mfderiv_rightFundamentalVectorField_of_map_op_smul`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 2.7.4 (the curvature integral of a circle bundle over a surface) and
  Proposition 5.1.9 (where the real first Chern class of a circle bundle appears).
* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6 (the Euler
  class of a circle bundle as the class of the curvature of an angular form).
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter II, §6 (mappings of connections: the pull-back of a connection form along a
  homomorphism of principal bundles, and of its curvature).
-/

public section

noncomputable section

open Bundle Manifold MulOpposite TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  [IB.Boundaryless]
  {P : B → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P] [∀ b, MulAction Circleᵐᵒᵖ (P b)] [PrincipalBundle Circle P]
  [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)]
  {α : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1}

/-- The curvature of a connection form is a closed form, as an element of the submodule
`TauCeti.closedForms`. -/
theorem IsCircleConnectionForm.curvature_mem_closedForms (hα : IsCircleConnectionForm α) :
    hα.curvature ∈ closedForms IB B 2 :=
  hα.isClosed_curvature.mem_closedForms

/-- The de Rham class of the curvature of a connection form `α` does not depend on `α`. -/
theorem IsCircleConnectionForm.deRhamCohomology_mk_curvature_eq (hα : IsCircleConnectionForm α)
    {β : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1}
    (hβ : IsCircleConnectionForm β) :
    deRhamCohomology.mk IB 2 ⟨hβ.curvature, hβ.curvature_mem_closedForms⟩ =
      deRhamCohomology.mk IB 2 ⟨hα.curvature, hα.curvature_mem_closedForms⟩ := by
  obtain ⟨a, rfl, -⟩ := hα.existsUnique_eq_add_mpullback hβ
  -- `hβ` and `hα.add_mpullback a` are proofs of the same proposition.
  have h : hβ.curvature = hα.curvature + mextDerivₗ IB 1 a := hα.curvature_add_mpullback a
  rw [deRhamCohomology.mk_eq_mk_iff, Submodule.coe_mk, Submodule.coe_mk, h, add_sub_cancel_left,
    exactForms_succ]
  exact LinearMap.mem_range_self _ a

/-- If `σ - F_α` is exact for a connection form `α`, then `σ` is the curvature of a connection
form, namely of `α + π^* a` for a primitive `a` of `σ - F_α`. -/
theorem IsCircleConnectionForm.exists_curvature_eq_of_sub_mem_exactForms
    (hα : IsCircleConnectionForm α) {σ : SmoothForm IB B ℝ 2}
    (h : σ - hα.curvature ∈ exactForms IB B 2) :
    ∃ (β : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1)
      (hβ : IsCircleConnectionForm β), hβ.curvature = σ := by
  rw [exactForms_succ] at h
  obtain ⟨a, ha⟩ := h
  exact ⟨_, hα.add_mpullback a, by rw [hα.curvature_add_mpullback, ha, add_sub_cancel]⟩

variable [FiniteDimensional ℝ EB] [T2Space B] [SigmaCompactSpace B]

variable (IB P) in
/-- The **real first Chern class** of a smooth principal `Circle`-bundle `P` over `B`: the de Rham
class `-(2π)⁻¹ [F_α]` of the curvature `F_α` of a connection form `α` on `P`, here the one chosen
by `exists_isCircleConnectionForm`. By `IsCircleConnectionForm.realFirstChernClass_eq` every
connection form gives this class. -/
def realFirstChernClass : deRhamCohomology IB B 2 :=
  -(2 * Real.pi)⁻¹ • deRhamCohomology.mk IB 2
    ⟨_, (exists_isCircleConnectionForm (IB := IB) (P := P)).choose_spec.curvature_mem_closedForms⟩

variable (IB P) in
theorem realFirstChernClass_def :
    realFirstChernClass IB P = -(2 * Real.pi)⁻¹ • deRhamCohomology.mk IB 2
      ⟨_, IsCircleConnectionForm.curvature_mem_closedForms
        (exists_isCircleConnectionForm (IB := IB) (P := P)).choose_spec⟩ :=
  (rfl)

/-- The real first Chern class of `P` is `-(2π)⁻¹` times the de Rham class of the curvature of
any connection form on `P`. -/
theorem IsCircleConnectionForm.realFirstChernClass_eq (hα : IsCircleConnectionForm α) :
    realFirstChernClass IB P =
      -(2 * Real.pi)⁻¹ • deRhamCohomology.mk IB 2 ⟨hα.curvature, hα.curvature_mem_closedForms⟩ := by
  rw [realFirstChernClass_def, IsCircleConnectionForm.deRhamCohomology_mk_curvature_eq hα]

/-- The difference of the de Rham classes of two closed `2`-forms `ω₁` and `ω₂` on `B` is `c`
times the real first Chern class of `P` exactly when `ω₁ - ω₂ + c (2π)⁻¹ F_α` is exact, for the
curvature `F_α` of any connection form `α` on `P`. -/
theorem IsCircleConnectionForm.mk_sub_mk_eq_smul_realFirstChernClass_iff
    (hα : IsCircleConnectionForm α) {ω₁ ω₂ : SmoothForm IB B ℝ 2}
    (h₁ : ω₁ ∈ closedForms IB B 2) (h₂ : ω₂ ∈ closedForms IB B 2) (c : ℝ) :
    deRhamCohomology.mk IB 2 ⟨ω₁, h₁⟩ - deRhamCohomology.mk IB 2 ⟨ω₂, h₂⟩ =
        c • realFirstChernClass IB P ↔
      ω₁ - ω₂ + (c * (2 * Real.pi)⁻¹) • hα.curvature ∈ exactForms IB B 2 := by
  rw [← map_sub, hα.realFirstChernClass_eq, smul_smul, ← map_smul,
    deRhamCohomology.mk_eq_mk_iff, Submodule.coe_sub, Submodule.coe_smul, mul_neg, neg_smul,
    sub_neg_eq_add]

/-- A closed `2`-form `σ` on `B` is the curvature of a connection form on `P` exactly when
`-(2π)⁻¹ [σ]` is the real first Chern class of `P`. -/
theorem exists_isCircleConnectionForm_curvature_eq_iff {σ : SmoothForm IB B ℝ 2}
    (hσ : σ ∈ closedForms IB B 2) :
    (∃ (β : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1)
        (hβ : IsCircleConnectionForm β), hβ.curvature = σ) ↔
      -(2 * Real.pi)⁻¹ • deRhamCohomology.mk IB 2 ⟨σ, hσ⟩ = realFirstChernClass IB P := by
  refine ⟨fun ⟨β, hβ, h⟩ ↦ by subst h; exact hβ.realFirstChernClass_eq.symm, fun h ↦ ?_⟩
  obtain ⟨α, hα⟩ := exists_isCircleConnectionForm (IB := IB) (P := P)
  rw [hα.realFirstChernClass_eq] at h
  have hmk := smul_right_injective _ (by simp [Real.pi_ne_zero] : -(2 * Real.pi)⁻¹ ≠ 0) h
  rw [deRhamCohomology.mk_eq_mk_iff, Submodule.coe_mk, Submodule.coe_mk] at hmk
  exact hα.exists_curvature_eq_of_sub_mem_exactForms hmk

/-! ### Naturality under maps of principal bundles -/

section Naturality

variable {EB' HB' B' : Type*} [NormedAddCommGroup EB'] [NormedSpace ℝ EB'] [TopologicalSpace HB']
  {IB' : ModelWithCorners ℝ EB' HB'} [TopologicalSpace B'] [ChartedSpace HB' B']
  [IsManifold IB' ∞ B'] [IB'.Boundaryless]
  {Q : B' → Type*} [TopologicalSpace (TotalSpace Circle Q)] [∀ b, TopologicalSpace (Q b)]
  [FiberBundle Circle Q] [∀ b, MulAction Circleᵐᵒᵖ (Q b)] [PrincipalBundle Circle Q]
  [ContMDiffFiberBundle ∞ Circle Q IB' (𝓡 1)]
  {Φ : ManifoldTotalSpace Circle Q → ManifoldTotalSpace Circle P}

omit [IB.Boundaryless] [FiniteDimensional ℝ EB] [T2Space B] [SigmaCompactSpace B]
  [IB'.Boundaryless] in
/-- The pull-back `Φ^* α` of a connection form `α` on `P` along a smooth map `Φ` of total spaces
that commutes with the action of `Circle` is a connection form on `Q`. -/
theorem IsCircleConnectionForm.mpullback (hα : IsCircleConnectionForm α)
    (hΦ : ContMDiff (IB'.prod (𝓡 1)) (IB.prod (𝓡 1)) ∞ Φ)
    (hΦz : ∀ (z : Circle) (q : ManifoldTotalSpace Circle Q), Φ (op z • q) = op z • Φ q) :
    IsCircleConnectionForm (SmoothForm.mpullback Φ hΦ α) where
  mpullback_op_smul z := SmoothForm.mpullback_smul_mpullback hΦ (hΦz z) (hα.mpullback_op_smul z)
  apply_rightFundamentalVectorField q := by
    rw [SmoothForm.mpullback_apply_one,
      mfderiv_rightFundamentalVectorField_of_map_op_smul ((hΦ q).mdifferentiableAt (by simp))
        (PrincipalBundle.mdifferentiableAt_orbit (n := ∞) (by simp) q 1) (fun z ↦ hΦz z q),
      hα.apply_rightFundamentalVectorField]

variable {f : B' → B} (hf : ContMDiff IB' IB ∞ f)
  (hΦ : ContMDiff (IB'.prod (𝓡 1)) (IB.prod (𝓡 1)) ∞ Φ)
  (hΦz : ∀ (z : Circle) (q : ManifoldTotalSpace Circle Q), Φ (op z • q) = op z • Φ q)
  (hΦf : ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1) ∘ Φ =
    f ∘ ManifoldTotalSpace.projContMDiffMap ∞ Circle Q IB' (𝓡 1))

omit [FiniteDimensional ℝ EB] [T2Space B] [SigmaCompactSpace B] in
include hΦf in
/-- Let `Φ` be a smooth map of total spaces that commutes with the action of `Circle` and covers a
smooth map `f` of bases. The curvature of the pull-back `Φ^* α` of a connection form `α` is the
pull-back `f^* F_α` of the curvature of `α`. -/
theorem IsCircleConnectionForm.curvature_mpullback (hα : IsCircleConnectionForm α) :
    (hα.mpullback hΦ hΦz).curvature = SmoothForm.mpullback f hf hα.curvature := by
  rw [curvature_eq_iff, SmoothForm.mpullback_mpullback_of_comp_eq _ hf hΦ
    (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)).contMDiff hΦf.symm,
    mpullback_curvature, SmoothForm.mextDerivₗ_mpullback]

variable [FiniteDimensional ℝ EB'] [T2Space B'] [SigmaCompactSpace B']

include hΦ hΦz hΦf in
/-- **Naturality of the real first Chern class.** If a smooth map `Φ` of total spaces commutes with
the action of `Circle` and covers a smooth map `f : B' → B`, then the real first Chern class of
`Q` is the pull-back along `f` of that of `P`. -/
theorem realFirstChernClass_map :
    realFirstChernClass IB' Q = deRhamCohomology.map f hf 2 (realFirstChernClass IB P) := by
  have hα := (exists_isCircleConnectionForm (IB := IB) (P := P)).choose_spec
  rw [hα.realFirstChernClass_eq, (hα.mpullback hΦ hΦz).realFirstChernClass_eq, map_smul,
    deRhamCohomology.map_mk]
  congr 2
  exact Subtype.ext ((hα.curvature_mpullback hf hΦ hΦz hΦf).trans
    (closedForms.coe_mpullback f hf 2 ⟨_, hα.curvature_mem_closedForms⟩).symm)

/-- **Invariance of the real first Chern class under maps over the identity.** If a smooth map `Φ`
of total spaces of principal `Circle`-bundles over the same base `B` commutes with the action of
`Circle` and covers the identity of `B`, then `Q` and `P` have the same real first Chern class. -/
theorem realFirstChernClass_eq_of_map {Q : B → Type*} [TopologicalSpace (TotalSpace Circle Q)]
    [∀ b, TopologicalSpace (Q b)] [FiberBundle Circle Q] [∀ b, MulAction Circleᵐᵒᵖ (Q b)]
    [PrincipalBundle Circle Q] [ContMDiffFiberBundle ∞ Circle Q IB (𝓡 1)]
    {Φ : ManifoldTotalSpace Circle Q → ManifoldTotalSpace Circle P}
    (hΦ : ContMDiff (IB.prod (𝓡 1)) (IB.prod (𝓡 1)) ∞ Φ)
    (hΦz : ∀ (z : Circle) (q : ManifoldTotalSpace Circle Q), Φ (op z • q) = op z • Φ q)
    (hΦπ : ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1) ∘ Φ =
      ManifoldTotalSpace.projContMDiffMap ∞ Circle Q IB (𝓡 1)) :
    realFirstChernClass IB Q = realFirstChernClass IB P := by
  rw [realFirstChernClass_map contMDiff_id hΦ hΦz hΦπ, deRhamCohomology.map_id,
    LinearMap.id_apply]

end Naturality

end SymplecticGeometry
