/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.RepresentationTheory.Dual
public import TauCeti.RepresentationTheory.Subrepresentation

/-!
# Extension by zero along an invariant splitting is coadjoint-equivariant

Let `K` be a subgroup of a Lie group `G`, and `S`, `T` complementary subrepresentations of the
adjoint representation of `K` on `𝔤`. A linear form on `S` extends by zero on `T` to a linear form
on `𝔤`: it is composed with the projection of `𝔤` onto `S` along `T`. This file shows that this
extension takes the dual of the adjoint representation of `K` on `S` to the coadjoint
representation of `K` on `𝔤*`.

The proof is the route that the module docstring of Tau Ceti's
`TauCeti/Geometry/Lie/Adjoint/Splitting.lean` describes: the projection intertwines
(`Subrepresentation.isIntertwiningMap_projectionOnto`), so its transpose does
(`Representation.IsIntertwiningMap.dualMap`), and the dual of the adjoint representation
restricted to `K` is the coadjoint representation restricted to `K`
(`Representation.dual_comp`, `TauCeti.Lie.coadjointRepresentation_def`).

## Main results

* `TauCeti.Lie.dualMap_projectionOnto_dual`: `(f ∘ Ad_{k⁻¹}|_S) ∘ pr_S = Ad*_k (f ∘ pr_S)`.

## References

* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985).
* [V. Guillemin and S. Sternberg][GuilleminSternberg1990]
-/

public section

namespace TauCeti.Lie

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I 1 G]

/-- For complementary subrepresentations `S` and `T` of the adjoint representation of a subgroup
`K`, the extension by zero on `T` of linear forms on `S`, the transpose of the projection onto `S`
along `T`, takes the dual of the adjoint representation of `K` on `S` to the coadjoint
representation: it sends `f ∘ Ad_{k⁻¹}` to `Ad*_k` of the extension of `f`. -/
theorem dualMap_projectionOnto_dual {K : Subgroup G}
    {S T : Subrepresentation ((adjointRepresentation 𝕜 I G).comp K.subtype)} (h : IsCompl S T)
    (k : K) (f : Module.Dual 𝕜 S.toSubmodule) :
    (S.toSubmodule.projectionOnto T.toSubmodule
        (Subrepresentation.isCompl_toSubmodule.2 h)).dualMap (S.toRepresentation.dual k f) =
      coadjointRepresentation 𝕜 I G k
        ((S.toSubmodule.projectionOnto T.toSubmodule
          (Subrepresentation.isCompl_toSubmodule.2 h)).dualMap f) := by
  have h' := (Subrepresentation.isIntertwiningMap_projectionOnto h).dualMap.isIntertwining k f
  rwa [Representation.dual_comp, MonoidHom.comp_apply, Subgroup.coe_subtype,
    ← coadjointRepresentation_def] at h'

end TauCeti.Lie

end
