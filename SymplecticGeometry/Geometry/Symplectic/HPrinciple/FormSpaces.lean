/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Basic
public import SymplecticGeometry.Geometry.Manifold.DeRham.Basic

/-!
# The spaces of nondegenerate and of symplectic forms

The h-principle for symplectic forms on open manifolds compares two spaces of smooth two-forms
on a manifold `M`: all nondegenerate ones, and the symplectic ones in a fixed de Rham class.
Both are subsets of the type `Bundle.ContMDiffTwoForm I ⊤ E (TangentSpace I)` of smooth two-forms
on the tangent bundle, which is given the frame topology (`ContMDiffSection.frameTopology`) of a
covering frame system where a topology is needed; closedness and the class are read
through the linear equivalence `Bundle.ContMDiffTwoForm.tangentEquiv` with Tau Ceti's
`TauCeti.SmoothTwoForm`.

## Main definitions and results

* `nondegenerateForms I M`: the smooth two-forms on the tangent bundle that are nondegenerate on
  every tangent space, with `mem_nondegenerateForms`.
* `symplecticFormsInClass α`: for a smooth two-form `α` on `M`, the two-forms `ω` such that the
  Tau Ceti form of `ω` is symplectic and differs from `α` by an exact form, with
  `mem_symplecticFormsInClass`.
* `symplecticFormsInClass_subset_nondegenerateForms`: the second space lies in the first.
* `symplecticFormsInClass_congr`: the space depends on `α` only through its class modulo exact
  forms; `symplecticFormsInClass_eq_of_mk_eq` states this for de Rham classes of closed forms.

## Implementation notes

The space of symplectic forms is indexed by a representative `α` of the class rather than by
the class itself, since it is defined by a condition on `tangentEquiv ω - α`; for `α` that is not
closed the space is empty, as an exact form is closed. Both spaces are sets, so as types they
are the subtypes `{ω // ω ∈ nondegenerateForms I M}` and so on, with the subspace topology.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.3.
* [Y. Eliashberg and N. Mishachev, *Introduction to the h-principle*][EliashbergMishachev2002],
  §10.2.
-/

public section

noncomputable section

open Bundle SymplecticGeometry.Bundle
open scoped Manifold

namespace SymplecticGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- The smooth two-forms on the tangent bundle of `M` that are nondegenerate on every tangent
space. -/
def nondegenerateForms : Set (ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))) :=
  {ω | ω.IsNondegenerate}

variable {I M}

@[simp]
theorem mem_nondegenerateForms {ω : ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))} :
    ω ∈ nondegenerateForms I M ↔ ω.IsNondegenerate :=
  Iff.rfl

/-- The smooth two-forms `ω` on the tangent bundle of `M` that are symplectic, as Tau Ceti forms
`tangentEquiv ω`, and lie in the class of `α` modulo exact forms, that is,
`tangentEquiv ω - α` is exact. -/
def symplecticFormsInClass (α : TauCeti.SmoothTwoForm I M) :
    Set (ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))) :=
  {ω | (ContMDiffTwoForm.tangentEquiv ω).IsSymplectic ∧
    ContMDiffTwoForm.tangentEquiv ω - α ∈ TauCeti.exactForms I M 2}

@[simp]
theorem mem_symplecticFormsInClass {α : TauCeti.SmoothTwoForm I M}
    {ω : ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))} :
    ω ∈ symplecticFormsInClass α ↔ (ContMDiffTwoForm.tangentEquiv ω).IsSymplectic ∧
      ContMDiffTwoForm.tangentEquiv ω - α ∈ TauCeti.exactForms I M 2 :=
  Iff.rfl

/-- A symplectic form in a class is nondegenerate. -/
theorem symplecticFormsInClass_subset_nondegenerateForms (α : TauCeti.SmoothTwoForm I M) :
    symplecticFormsInClass α ⊆ nondegenerateForms I M := fun _ hω ↦
  ContMDiffTwoForm.isNondegenerate_tangentEquiv_iff.mp hω.1.isNondegenerate

/-- The space of symplectic forms in the class of `α` depends on `α` only modulo exact forms. -/
theorem symplecticFormsInClass_congr {α β : TauCeti.SmoothTwoForm I M}
    (h : α - β ∈ TauCeti.exactForms I M 2) :
    symplecticFormsInClass α = symplecticFormsInClass β := by
  ext ω
  simp only [mem_symplecticFormsInClass, and_congr_right_iff]
  intro _
  constructor <;> intro hω
  · simpa using add_mem hω h
  · simpa using sub_mem hω h

/-- For closed forms `α` and `β` with the same de Rham class, the spaces of symplectic forms in
their classes agree. -/
theorem symplecticFormsInClass_eq_of_mk_eq {α β : TauCeti.closedForms I M 2}
    (h : TauCeti.deRhamCohomology.mk I 2 α = TauCeti.deRhamCohomology.mk I 2 β) :
    symplecticFormsInClass α.val = symplecticFormsInClass β.val :=
  symplecticFormsInClass_congr ((TauCeti.deRhamCohomology.mk_eq_mk_iff I 2 α β).mp h)

end SymplecticGeometry

end
