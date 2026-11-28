/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.HPrinciple.FormSpaces
public import SymplecticGeometry.Geometry.Symplectic.HPrinciple.Relative.Basic
import SymplecticGeometry.Geometry.Manifold.Instances.Icc

/-!
# The h-principle for symplectic forms on open manifolds: existence and paths

Let `M` be a manifold without boundary none of whose connected components is compact, and `α` a
closed two-form on `M`. This file proves the two assertions of Theorem 7.3.1 of McDuff–Salamon
about the class `[α]`:

* every nondegenerate two-form `τ` is joined to a symplectic form in the class of `α` by a
  smooth path of nondegenerate two-forms
  (`TauCeti.SmoothTwoForm.IsNondegenerate.exists_homotopy_isSymplectic`);
* two symplectic forms in the class of `α` that are joined by a smooth path of nondegenerate
  two-forms are also the ends of a smooth path that stays among symplectic forms of that class
  (`TauCeti.SmoothTwoForm.IsSymplectic.exists_isSmoothFamily_isSymplectic_of_homotopy`), and the
  same holds for paths that are only continuous for the frame topology of a covering frame
  system: two forms of `SymplecticGeometry.symplecticFormsInClass α` joined in
  `SymplecticGeometry.nondegenerateForms I M` are joined inside the first space
  (`SymplecticGeometry.joinedIn_symplecticFormsInClass_of_joined`).

A class `a` of degree two is given by a closed representative `α`: every class is
`TauCeti.deRhamCohomology.mk` of a closed form (`TauCeti.deRhamCohomology.mk_surjective`), and
a closed form `σ` lies in the class of `α` exactly when `σ - α` is exact
(`TauCeti.deRhamCohomology.mk_eq_zero_iff`).

## Proof

Both assertions are corollaries of the parametric relative h-principle of
`HPrinciple/Relative/Basic.lean`. For the first, the parameter space is a point: the constant
family `τ` over `[0, 1]`, with no parameter where `τ` is already closed, gives a homotopy whose
slice at the parameter `0` is the path. For the second, the given path `τ` is the family over
`[0, 1]`, already closed in the class at its two ends; the relative h-principle gives a homotopy
`H` of `τ` over `[0, 1] × [0, 1]` through forms that are closed in the class on the three sides
`{0} × [0, 1]`, `[0, 1] × {1}` and `{1} × [0, 1]` of the square. The path along these three
sides, concatenated by `SymplecticGeometry.collaredConcat` so that it stays smooth
(`unitInterval.exists_contMDiff_path_sq_boundary`), composed with `H`, joins `τ 0` to `τ 1`.
The continuous version runs the same argument with the continuous form of the relative
h-principle for a path with closed ends
(`SymplecticGeometry.exists_continuousMap_homotopy_closed_of_ends`).

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Theorem 7.3.1.
* [Y. Eliashberg and N. Mishachev, *Introduction to the h-principle*][EliashbergMishachev2002],
  Theorems 10.2.1 and 10.2.2.
-/

public section

open Set TauCeti SymplecticGeometry
open scoped Manifold ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

namespace TauCeti.SmoothTwoForm

/-- **Existence in the h-principle for symplectic forms on open manifolds.** Here `M` is a
manifold without boundary none of whose connected components is compact, and `α` a closed
two-form on `M`. Every nondegenerate two-form `τ` on `M` is joined by a smooth path `σ` of
nondegenerate two-forms to a symplectic form `σ 1` with `σ 1 - α` exact, that is, in the
de Rham class of `α`. Since every class of degree two is that of a closed form
(`TauCeti.deRhamCohomology.mk_surjective`, `TauCeti.deRhamCohomology.mk_eq_zero_iff`), this
holds for every class.

Milestone: *Gromov's h-principle for symplectic forms on open manifolds*. -/
theorem IsNondegenerate.exists_homotopy_isSymplectic
    (hM : ∀ x : M, ¬ IsCompact (connectedComponent x)) {α : SmoothTwoForm I M}
    (hα : α ∈ closedForms I M 2) {τ : SmoothTwoForm I M} (hτ : τ.IsNondegenerate) :
    ∃ σ : unitInterval → SmoothTwoForm I M, IsSmoothFamily (𝓡∂ 1) σ ∧ σ 0 = τ ∧
      (∀ t, (σ t).IsNondegenerate) ∧ (σ 1).IsSymplectic ∧ σ 1 - α ∈ exactForms I M 2 := by
  obtain ⟨H, hH, hH₀, hHnd, -, hH₁⟩ :=
    exists_isSmoothFamily_homotopy_closed_unitInterval hM (P₀ := ∅) isClosed_empty
      (isSmoothFamily_const τ) (fun _ ↦ hτ) (isSmoothFamily_const α)
      (fun _ ↦ (mem_closedForms_iff_mextDerivₗ_eq_zero I α).1 hα)
      (α₀ := α) (fun _ ↦ by simp) (fun _ h ↦ h.elim)
  exact ⟨fun u ↦ H (0, u), hH.comp _ (contMDiff_const.prodMk contMDiff_id), hH₀ 0,
    fun u ↦ hHnd 0 u, ⟨(SmoothForm.isClosed_iff_mextDerivₗ_eq_zero _).2 (hH₁ 0).1,
      hHnd 0 1⟩, (hH₁ 0).2⟩

/-- **Paths in the h-principle for symplectic forms on open manifolds.** Here `M` is a manifold
without boundary none of whose connected components is compact, and `α` a two-form on `M`. If
two symplectic forms `ω₀` and `ω₁` with `ω₀ - α` and `ω₁ - α` exact, that is, in the de Rham
class of `α` (which is then closed), are joined by a smooth path `τ` of nondegenerate two-forms,
then some smooth path `σ` from `ω₀` to `ω₁` stays among symplectic forms of that class. As every
class of degree two is that of a closed form (`TauCeti.deRhamCohomology.mk_surjective`,
`TauCeti.deRhamCohomology.mk_eq_zero_iff`), this holds for every class.

The path `τ` is smooth as a family over `[0, 1]`; for paths that are only continuous in the
frame topology, see `SymplecticGeometry.joinedIn_symplecticFormsInClass_of_joined`. -/
theorem IsSymplectic.exists_isSmoothFamily_isSymplectic_of_homotopy
    (hM : ∀ x : M, ¬ IsCompact (connectedComponent x)) {α : SmoothTwoForm I M}
    {ω₀ ω₁ : SmoothTwoForm I M}
    (h₀ : ω₀.IsSymplectic) (h₁ : ω₁.IsSymplectic)
    (h₀α : ω₀ - α ∈ exactForms I M 2) (h₁α : ω₁ - α ∈ exactForms I M 2)
    {τ : unitInterval → SmoothTwoForm I M} (hτ : IsSmoothFamily (𝓡∂ 1) τ)
    (hτ₀ : τ 0 = ω₀) (hτ₁ : τ 1 = ω₁) (hτnd : ∀ t, (τ t).IsNondegenerate) :
    ∃ σ : unitInterval → SmoothTwoForm I M, IsSmoothFamily (𝓡∂ 1) σ ∧
      σ 0 = ω₀ ∧ σ 1 = ω₁ ∧ ∀ t, (σ t).IsSymplectic ∧ σ t - α ∈ exactForms I M 2 := by
  have hc {ψ : SmoothTwoForm I M} (h : ψ.IsSymplectic) : mextDerivₗ I 2 ψ = 0 :=
    (SmoothForm.isClosed_iff_mextDerivₗ_eq_zero ψ).1 h.isClosed
  subst hτ₀ hτ₁
  obtain ⟨H, hH, hH₀, hHnd, hHP₀, hH₁⟩ :=
    exists_isSmoothFamily_homotopy_closed_unitInterval_of_ends hM hτ hτnd (hc h₀) (hc h₁) h₀α h₁α
  obtain ⟨γ, hγ, hγ₀, hγ₁, hγside⟩ := unitInterval.exists_contMDiff_path_sq_boundary
  refine ⟨fun t ↦ H (γ t), hH.comp _ hγ, by simp only [hγ₀, hH₀], by simp only [hγ₁, hH₀],
    fun t ↦ ?_⟩
  have hclosed : mextDerivₗ I 2 (H (γ t)) = 0 ∧ H (γ t) - α ∈ exactForms I M 2 := by
    obtain h | h := hγside t
    · exact hHP₀ _ h _
    · rw [← Prod.mk.eta (p := γ t), h]
      exact hH₁ _
  exact ⟨⟨(SmoothForm.isClosed_iff_mextDerivₗ_eq_zero _).2 hclosed.1,
    hHnd _ _⟩, hclosed.2⟩

end TauCeti.SmoothTwoForm

namespace SymplecticGeometry

open _root_.Bundle

variable {ι : Type*}
  (fr : ι → Trivialization (E [⋀^Fin 2]→L[ℝ] ℝ)
    (π (E [⋀^Fin 2]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x)))
  [∀ j, MemTrivializationAtlas (fr j)]
  (W : ι → TopologicalSpace.Opens M) (hW : ∀ j, (W j : Set M) ⊆ (fr j).baseSet)

/-- **Paths in the h-principle for symplectic forms on open manifolds, continuous version.** Here
`M` is a manifold without boundary none of whose connected components is compact, the space
`nondegenerateForms I M` carries the frame topology of a covering frame system, and `α` is a
two-form on `M`. Two forms `ω₀` and `ω₁` of `symplecticFormsInClass α` that are joined by a path
in `nondegenerateForms I M` are joined by a path in `nondegenerateForms I M` that stays in
`symplecticFormsInClass α`. -/
theorem joinedIn_symplecticFormsInClass_of_joined
    (hM : ∀ x : M, ¬ IsCompact (connectedComponent x)) (hcover : ∀ x, ∃ j, x ∈ W j)
    {α : SmoothTwoForm I M} :
    letI := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
    ∀ {ω₀ ω₁ : nondegenerateForms I M}, ω₀.val ∈ symplecticFormsInClass α →
      ω₁.val ∈ symplecticFormsInClass α → Joined ω₀ ω₁ →
      JoinedIn (Subtype.val ⁻¹' symplecticFormsInClass α) ω₀ ω₁ := by
  intro ω₀ ω₁ h₀ h₁ ⟨γ⟩
  let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
  rw [mem_symplecticFormsInClass] at h₀ h₁
  have hc {ψ : SmoothTwoForm I M} (h : ψ.IsSymplectic) : mextDerivₗ I 2 ψ = 0 :=
    (SmoothForm.isClosed_iff_mextDerivₗ_eq_zero ψ).1 h.isClosed
  -- The path `γ`, as a path in the subtype that the relative h-principle takes.
  let τ : C(unitInterval,
      {σ : Bundle.ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M)) // σ.IsNondegenerate}) :=
    ⟨fun t ↦ ⟨(γ t).val, mem_nondegenerateForms.1 (γ t).property⟩,
      (continuous_subtypeVal.comp γ.continuous).subtype_mk _⟩
  have hτ₀ : (τ 0).val = ω₀.val := congrArg Subtype.val γ.source
  have hτ₁ : (τ 1).val = ω₁.val := congrArg Subtype.val γ.target
  obtain ⟨H, hH₀, hHP₀, hH₁⟩ := exists_continuousMap_homotopy_closed_of_ends fr W hW hM hcover τ
    (hτ₀ ▸ hc h₀.1) (hτ₁ ▸ hc h₁.1) (hτ₀ ▸ h₀.2) (hτ₁ ▸ h₁.2)
  obtain ⟨c, hc', hc₀, hc₁, hcside⟩ := unitInterval.exists_contMDiff_path_sq_boundary
  refine ⟨{ toFun t := ⟨(H (c t)).val, mem_nondegenerateForms.2 (H (c t)).property⟩
            continuous_toFun := ((continuous_subtypeVal.comp H.continuous).comp
              hc'.continuous).subtype_mk _
            source' := Subtype.ext (by simp only [hc₀, hH₀, hτ₀])
            target' := Subtype.ext (by simp only [hc₁, hH₀, hτ₁]) }, fun t ↦ ?_⟩
  have hclosed : mextDerivₗ I 2 (Bundle.ContMDiffTwoForm.tangentEquiv (H (c t)).val) = 0 ∧
      Bundle.ContMDiffTwoForm.tangentEquiv (H (c t)).val - α ∈ exactForms I M 2 := by
    obtain h | h := hcside t
    · exact hHP₀ _ h _
    · rw [← Prod.mk.eta (p := c t), h]
      exact hH₁ _
  exact mem_symplecticFormsInClass.2 ⟨⟨(SmoothForm.isClosed_iff_mextDerivₗ_eq_zero _).2
    hclosed.1, Bundle.ContMDiffTwoForm.isNondegenerate_tangentEquiv_iff.2 (H (c t)).property⟩,
    hclosed.2⟩

end SymplecticGeometry

end
