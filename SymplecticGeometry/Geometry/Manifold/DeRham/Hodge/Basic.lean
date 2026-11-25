/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DeRham.Hodge.Sobolev
public import TauCeti.Geometry.Manifold.DeRham.Harmonic
import SymplecticGeometry.Geometry.Manifold.DeRham.Basic
import TauCeti.Analysis.InnerProductSpace.Variational.Compatibility

/-!
# The Hodge theorem

On a closed oriented Riemannian manifold `M` of dimension `m = k + l`, this file proves the
analytic half of the Hodge theorem, which Tau Ceti's `Geometry/Manifold/DeRham/Harmonic.lean`
leaves open, and its consequences for de Rham cohomology.

The Dirichlet form `LinearPMap.friedrichsForm` on the Hodge `H¹` space satisfies Gårding's
inequality with constants `1` and `1` (`H1Form.norm_sq_eq_friedrichsForm_add`), and the inclusion
`LinearPMap.friedrichsInclusion` into the `L²` forms is compact
(`H1Form.isCompactOperator_friedrichsInclusion`). Tau Ceti's Fredholm alternative for
Gårding forms then gives:

* the harmonic forms embed into the kernel of the Dirichlet form, which is finite dimensional;
* a smooth form `L²`-orthogonal to the harmonic forms is the right-hand side of a weak solution
  of `Δu = f`: the compatibility condition holds, because an element of the adjoint kernel is a
  weak solution of `Δu = 0` in `L²`, hence a harmonic form by elliptic regularity
  (`L2Form.exists_eq_ofSmooth_of_isWeakSolution`). Regularity again makes the solution smooth.

So every smooth form is a harmonic form plus the Laplacian of a smooth form. Since
`Δγ = dd*γ + d*dγ`, every form lies in `ℋ ⊔ B ⊔ B*`, and with the orthogonality results of Tau
Ceti a closed form `Δγ` is exact, so that every de Rham class has exactly one harmonic
representative.

## Main results

* `TauCeti.finiteDimensional_harmonicForms`: the harmonic forms are finite dimensional.
* `TauCeti.exists_mem_harmonicForms_add_hodgeLaplacian`: every smooth form is `h + Δγ` with `h`
  harmonic and `γ` smooth.
* `TauCeti.harmonicForms_sup_exactForms_sup_coexactForms`: `ℋ ⊔ B ⊔ B* = ⊤`.
* `TauCeti.mem_exactForms_of_hodgeLaplacian_mem_closedForms`: a closed form `Δβ` is exact.
* `TauCeti.harmonicForms.toDeRhamCohomology_bijective`: the Hodge theorem, every de Rham class
  has exactly one harmonic representative, and the equivalence
  `TauCeti.harmonicForms.deRhamCohomologyEquiv`.

The proof of `TauCeti.closedForms_inf_exactForms_sup_coexactForms` follows that of Tau Ceti's
`TauCeti.closedForms_inf_sup_coexactForms`, with the exact forms in place of `ℋ ⊔ B`.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §6.
* [J.-P. Demailly, *Complex Analytic and Differential Geometry*][Demailly2012], Chapter VI.
* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer, 1983, Chapter 6.
-/

public section

noncomputable section

open Bundle SymplecticGeometry
open scoped Manifold ContDiff InnerProductSpace

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {m k l : ℕ}

/-- The Hodge Laplacian of a form is the sum of an exact form and a coexact form:
`Δγ = dd*γ + d*dγ`. -/
theorem hodgeLaplacian_mem_exactForms_sup_coexactForms (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (γ : SmoothForm I M ℝ k) :
    SmoothForm.hodgeLaplacian o hkl γ ∈ exactForms I M k ⊔ coexactForms o hkl := by
  rcases k with _ | k <;> rcases l with _ | l
  · rw [SmoothForm.hodgeLaplacian_zero_zero]
    exact zero_mem _
  · rw [SmoothForm.hodgeLaplacian_zero_add_one o hkl (by omega)]
    exact Submodule.mem_sup_right ((mem_coexactForms_add_one o hkl _).2 ⟨_, rfl⟩)
  · rw [SmoothForm.hodgeLaplacian_add_one_zero]
    exact Submodule.mem_sup_left (by rw [exactForms_succ]; exact LinearMap.mem_range_self _ _)
  · rw [SmoothForm.hodgeLaplacian_add_one_add_one o hkl (by omega)]
    exact add_mem (Submodule.mem_sup_right ((mem_coexactForms_add_one o hkl _).2 ⟨_, rfl⟩))
      (Submodule.mem_sup_left (by rw [exactForms_succ]; exact LinearMap.mem_range_self _ _))

variable [BoundarylessManifold I M] [T2Space M] [CompactSpace M]

/-- **A closed form in `B ⊔ B*` is exact**: on a compact oriented boundaryless Riemannian
manifold, the closed forms in the sum of the exact and coexact forms are the exact forms. -/
theorem closedForms_inf_exactForms_sup_coexactForms (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) :
    closedForms I M k ⊓ (exactForms I M k ⊔ coexactForms o hkl) = exactForms I M k := by
  rw [inf_comm, sup_inf_assoc_of_le _ (exactForms_le_closedForms I k), inf_comm,
    (disjoint_closedForms_coexactForms o hkl).eq_bot, sup_bot_eq]

/-- **A closed Laplacian is exact**: on a compact oriented boundaryless Riemannian manifold, if
`Δβ` is closed then it is exact; indeed `Δβ = dd*β`, and `d*dβ` is closed and coexact, hence
zero. -/
theorem mem_exactForms_of_hodgeLaplacian_mem_closedForms (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) {β : SmoothForm I M ℝ k}
    (hβ : SmoothForm.hodgeLaplacian o hkl β ∈ closedForms I M k) :
    SmoothForm.hodgeLaplacian o hkl β ∈ exactForms I M k := by
  rw [← closedForms_inf_exactForms_sup_coexactForms o hkl]
  exact Submodule.mem_inf.2 ⟨hβ, hodgeLaplacian_mem_exactForms_sup_coexactForms o hkl β⟩

/-! ### The analytic half

The Dirichlet form on the Hodge `H¹` space is `LinearPMap.friedrichsForm` of the Hodge Laplacian
on `L2Form I M k`, and the inclusion into `L2Form I M k` is `LinearPMap.friedrichsInclusion`. -/

open _root_.LinearPMap in
/-- A harmonic form, in the Hodge `H¹` space, lies in the kernel of the Dirichlet form. -/
theorem _root_.SymplecticGeometry.H1Form.ofSmooth_mem_ker_friedrichsForm
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) {α : SmoothForm I M ℝ k}
    (hα : α ∈ harmonicForms o hkl) :
    (H1Form.ofSmooth α : H1Form o hkl) ∈
      (friedrichsForm (L2Form.isSymmetricBoundedBelow_hodgeLaplacian o hkl)).ker := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  ext v
  rw [friedrichsForm_eq_star, star_trivial, H1Form.friedrichsForm_ofSmooth_right,
    (mem_harmonicForms o hkl α).1 hα, _root_.map_zero, inner_zero_right,
    _root_.zero_apply]

open _root_.LinearPMap in
/-- **The harmonic forms are finite dimensional** on a closed oriented Riemannian manifold. They
embed into the kernel of the Dirichlet form, which is finite dimensional by the Fredholm
alternative, since the Dirichlet form satisfies Gårding's inequality relative to the compact
inclusion of `H¹` into `L²`. -/
instance finiteDimensional_harmonicForms (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) : FiniteDimensional ℝ (harmonicForms o hkl) := by
  have := (H1Form.isCompactOperator_friedrichsInclusion (o := o)
    (hkl := hkl)).finiteDimensional_ker_of_garding
    (C₀ := 1) (β := 1) one_pos fun w ↦ by
      rw [one_mul, one_mul, H1Form.norm_sq_eq_friedrichsForm_add]
  exact Module.Finite.of_injective
    (LinearMap.codRestrict _ (H1Form.ofSmooth ∘ₗ (harmonicForms o hkl).subtype)
      fun α ↦ H1Form.ofSmooth_mem_ker_friedrichsForm o hkl α.property)
    fun α β h ↦ Subtype.ext (H1Form.ofSmooth_injective (congrArg Subtype.val h))

open _root_.LinearPMap in
/-- An element of `H¹` in the kernel of the Dirichlet form is a harmonic form. -/
theorem _root_.SymplecticGeometry.H1Form.exists_mem_harmonicForms_eq_ofSmooth_of_mem_ker
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) {w : H1Form o hkl}
    (hw : w ∈ (friedrichsForm (L2Form.isSymmetricBoundedBelow_hodgeLaplacian o hkl)).ker) :
    ∃ β ∈ harmonicForms o hkl, w = H1Form.ofSmooth β := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hw
  have hweak : L2Form.IsWeakSolution o hkl
      (friedrichsInclusion (L2Form.isSymmetricBoundedBelow_hodgeLaplacian o hkl) w)
      (L2Form.ofSmooth 0) :=
    L2Form.isWeakSolution_iff.2 fun φ ↦ by
      rw [← H1Form.friedrichsForm_ofSmooth_right, hw, _root_.map_zero, inner_zero_left,
        _root_.zero_apply]
  obtain ⟨β, hβ, hΔ⟩ := L2Form.exists_eq_ofSmooth_of_isWeakSolution hweak
  exact ⟨β, (mem_harmonicForms o hkl β).2 hΔ,
    friedrichsInclusion_injective _ (by rw [hβ, H1Form.friedrichsInclusion_ofSmooth])⟩

open _root_.LinearPMap in
/-- **The kernel of the Dirichlet form** consists of the harmonic forms. -/
theorem _root_.SymplecticGeometry.H1Form.mem_ker_friedrichsForm_iff
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) {w : H1Form o hkl} :
    w ∈ (friedrichsForm (L2Form.isSymmetricBoundedBelow_hodgeLaplacian o hkl)).ker ↔
      ∃ β ∈ harmonicForms o hkl, w = H1Form.ofSmooth β :=
  ⟨H1Form.exists_mem_harmonicForms_eq_ofSmooth_of_mem_ker o hkl,
    fun ⟨_, hβ, hw⟩ ↦ hw ▸ H1Form.ofSmooth_mem_ker_friedrichsForm o hkl hβ⟩

open _root_.LinearPMap in
/-- **The Hodge decomposition of a smooth form**: on a closed oriented Riemannian manifold, every
smooth `k`-form is `h + Δγ` with `h` harmonic and `γ` smooth. -/
theorem exists_mem_harmonicForms_add_hodgeLaplacian (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (α : SmoothForm I M ℝ k) :
    ∃ h ∈ harmonicForms o hkl, ∃ γ : SmoothForm I M ℝ k,
      α = h + SmoothForm.hodgeLaplacian o hkl γ := by
  -- Project `α` in `L²` onto the finite-dimensional space of harmonic forms.
  set K : Submodule ℝ (SymplecticGeometry.L2Form I M k) :=
    (harmonicForms o hkl).map
      (L2Form.ofSmooth : SmoothForm I M ℝ k →ₗ[ℝ] SymplecticGeometry.L2Form I M k)
  obtain ⟨_, ⟨h, hh, rfl⟩, z, hz, hα⟩ := K.exists_add_mem_mem_orthogonal (L2Form.ofSmooth α)
  have hperp : L2Form.ofSmooth (α - h) ∈ Kᗮ := by rwa [_root_.map_sub, hα, add_sub_cancel_left]
  set hS := L2Form.isSymmetricBoundedBelow_hodgeLaplacian o hkl
  -- The functional `v ↦ ⟪α - h, v⟫` on `H¹` vanishes on the kernel of the Dirichlet form.
  have hgard (w : H1Form o hkl) :
      1 * ‖w‖ ^ 2 ≤ friedrichsForm hS w w + 1 * ‖friedrichsInclusion hS w‖ ^ 2 := by
    rw [one_mul, one_mul, H1Form.norm_sq_eq_friedrichsForm_add]
  obtain ⟨u, hu⟩ :=
    (H1Form.isCompactOperator_friedrichsInclusion.exists_forall_apply_eq_iff_of_garding one_pos
      hgard ((innerSL ℝ (L2Form.ofSmooth (α - h))).comp (friedrichsInclusion hS))).2
      fun w hw ↦ by
      obtain ⟨β, hβ, rfl⟩ := (H1Form.mem_ker_friedrichsForm_iff o hkl).1 <| by
        rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
        exact ContinuousLinearMap.ext fun v ↦ by
          rw [friedrichsForm_eq_star, star_trivial]; exact hw v
      rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, H1Form.friedrichsInclusion_ofSmooth]
      exact Submodule.inner_left_of_mem_orthogonal (Submodule.mem_map_of_mem hβ) hperp
  -- Its solution is a weak solution of `Δu = α - h`, hence smooth.
  have hweak : L2Form.IsWeakSolution o hkl (friedrichsInclusion hS u)
      (L2Form.ofSmooth (α - h)) :=
    L2Form.isWeakSolution_iff.2 fun φ ↦ by
      rw [← H1Form.friedrichsForm_ofSmooth_right, hu, ContinuousLinearMap.comp_apply,
        H1Form.friedrichsInclusion_ofSmooth, innerSL_apply_apply, real_inner_comm]
  obtain ⟨γ, -, hγ⟩ := L2Form.exists_eq_ofSmooth_of_isWeakSolution hweak
  exact ⟨h, hh, γ, by rw [hγ, add_sub_cancel]⟩

/-- **The Hodge decomposition**: on a closed oriented Riemannian manifold, every smooth form is
the sum of a harmonic, an exact and a coexact form. The sum is direct by
`TauCeti.disjoint_harmonicForms_exactForms` and
`TauCeti.disjoint_harmonicForms_sup_exactForms_coexactForms`. -/
theorem harmonicForms_sup_exactForms_sup_coexactForms (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) :
    harmonicForms o hkl ⊔ exactForms I M k ⊔ coexactForms o hkl = ⊤ := by
  refine eq_top_iff.2 fun α _ ↦ ?_
  obtain ⟨h, hh, γ, rfl⟩ := exists_mem_harmonicForms_add_hodgeLaplacian o hkl α
  rw [sup_assoc]
  exact add_mem (Submodule.mem_sup_left hh)
    (Submodule.mem_sup_right (hodgeLaplacian_mem_exactForms_sup_coexactForms o hkl γ))

/-- **Every closed form is harmonic plus exact**: on a closed oriented Riemannian manifold, for a
closed form `α` there is a harmonic form `h` with `α - h` exact. -/
theorem exists_mem_harmonicForms_sub_mem_exactForms (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) {α : SmoothForm I M ℝ k} (hα : α ∈ closedForms I M k) :
    ∃ h ∈ harmonicForms o hkl, α - h ∈ exactForms I M k := by
  obtain ⟨h, hh, γ, rfl⟩ := exists_mem_harmonicForms_add_hodgeLaplacian o hkl α
  have hγ := sub_mem hα (harmonicForms_le_closedForms o hkl hh)
  rw [add_sub_cancel_left] at hγ
  refine ⟨h, hh, ?_⟩
  rw [add_sub_cancel_left]
  exact mem_exactForms_of_hodgeLaplacian_mem_closedForms o hkl hγ

/-! ### Harmonic representatives of de Rham classes -/

/-- **The Hodge theorem**: on a closed oriented Riemannian manifold, every de Rham class has
exactly one harmonic representative. -/
theorem harmonicForms.toDeRhamCohomology_bijective (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) : Function.Bijective (harmonicForms.toDeRhamCohomology o hkl) := by
  refine ⟨harmonicForms.toDeRhamCohomology_injective o hkl, fun c ↦ ?_⟩
  obtain ⟨α, rfl⟩ := deRhamCohomology.mk_surjective I k c
  obtain ⟨h, hh, hαh⟩ := exists_mem_harmonicForms_sub_mem_exactForms o hkl α.property
  refine ⟨⟨h, hh⟩, ?_⟩
  rw [harmonicForms.toDeRhamCohomology_apply, eq_comm, deRhamCohomology.mk_eq_mk_iff]
  exact hαh

/-- **The Hodge isomorphism**: on a closed oriented Riemannian manifold, sending a harmonic form
to its de Rham class is a linear isomorphism onto de Rham cohomology. -/
def harmonicForms.deRhamCohomologyEquiv (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) : harmonicForms o hkl ≃ₗ[ℝ] deRhamCohomology I M k :=
  LinearEquiv.ofBijective (harmonicForms.toDeRhamCohomology o hkl)
    (harmonicForms.toDeRhamCohomology_bijective o hkl)

/-- The Hodge isomorphism sends a harmonic form to its de Rham class. -/
@[simp]
theorem harmonicForms.deRhamCohomologyEquiv_apply (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (α : harmonicForms o hkl) :
    harmonicForms.deRhamCohomologyEquiv o hkl α =
      harmonicForms.toDeRhamCohomology o hkl α :=
  (rfl)

/-- The inverse of the Hodge isomorphism sends the class of a closed form `α` to the harmonic form
`h` such that `α - h` is exact. -/
theorem harmonicForms.deRhamCohomologyEquiv_symm_mk (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (α : closedForms I M k) (h : harmonicForms o hkl)
    (hαh : α.val - h.val ∈ exactForms I M k) :
    (harmonicForms.deRhamCohomologyEquiv o hkl).symm (deRhamCohomology.mk I k α) = h := by
  rw [LinearEquiv.symm_apply_eq, deRhamCohomologyEquiv_apply, toDeRhamCohomology_apply,
    deRhamCohomology.mk_eq_mk_iff]
  exact hαh

/-- A closed form differs from the harmonic representative of its class by an exact form. -/
theorem harmonicForms.sub_deRhamCohomologyEquiv_symm_mk_mem_exactForms
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) (α : closedForms I M k) :
    α.val - ((harmonicForms.deRhamCohomologyEquiv o hkl).symm (deRhamCohomology.mk I k α)).val ∈
      exactForms I M k := by
  obtain ⟨h, hh, hαh⟩ := exists_mem_harmonicForms_sub_mem_exactForms o hkl α.property
  rwa [harmonicForms.deRhamCohomologyEquiv_symm_mk o hkl α ⟨h, hh⟩ hαh]

end TauCeti

end
