/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Sets.Opens

/-!
# Open sets of an open subspace

Facts about open sets of `X` read as open sets of an open subspace `W` of `X`, that is, about
their preimages under the inclusion `W → X`:

* `TopologicalSpace.Opens.range_val_comp_val_comap`: for `U ≤ W`, the inclusion of `W` maps `U`,
  read as an open set of `W`, back onto `U`;
* `TopologicalSpace.Opens.comap_val_sup_comap_val_eq_top`: `U` and `V`, read as open sets of
  `U ⊔ V`, cover it;
* `TopologicalSpace.Opens.iSup_comap_val_eq_top`: a family of open sets of `X` with union `U`,
  read as open sets of `U`, covers `U`;
* `TopologicalSpace.Opens.image_val_iInf_comap_val`: for open sets `V i ≤ U`, the inclusion of `U`
  maps the intersection of a nonempty finite subfamily, read in `U`, onto its intersection in `X`.

For `U ≤ W`, the homeomorphism between `U` read as an open set of `W` and `U` itself is Mathlib's
`Topology.IsEmbedding.homeomorphOfSubsetRange`, applied to `Topology.IsEmbedding.subtypeVal`.
-/

public section

namespace TopologicalSpace.Opens

variable {X : Type*} [TopologicalSpace X]

/-- For open sets `U ≤ W` of `X`, the composite of the inclusions `U ∩ W → W → X`, where `U ∩ W`
is `U` read as an open set of `W`, has range `U`. -/
theorem range_val_comp_val_comap {U W : Opens X} (hUW : U ≤ W) :
    Set.range ((Subtype.val : W → X) ∘
      (Subtype.val : Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ U → W)) = U := by
  ext x
  simpa using fun hx ↦ hUW hx

/-- Two open sets `U` and `V` of `X`, read as open sets of the subspace `U ⊔ V` (their preimages
under the inclusion `U ⊔ V → X`), cover `U ⊔ V`. -/
theorem comap_val_sup_comap_val_eq_top (U V : Opens X) :
    Opens.comap (⟨Subtype.val, continuous_subtypeVal⟩ : C(↥(U ⊔ V), X)) U ⊔
      Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ V = ⊤ := by
  rw [← map_sup, eq_top_iff]
  exact fun x _ ↦ x.property

/-- A family `V` of open sets of `X` with union `U`, read as open sets of the subspace `U` (their
preimages under the inclusion `U → X`), covers `U`. -/
theorem iSup_comap_val_eq_top {ι : Sort*} {U : Opens X} {V : ι → Opens X} (hU : ⨆ i, V i = U) :
    ⨆ i, Opens.comap (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, X)) (V i) = ⊤ := by
  rw [← map_iSup, hU, eq_top_iff]
  exact fun x _ ↦ x.property

/-- Let `V` be a family of open sets of `X` contained in `U`, and `s` a nonempty finite set of
indices. The inclusion `U → X` maps the intersection over `s` of the `V i`, read as open sets of
`U`, onto `⋂ i ∈ s, V i`. -/
theorem image_val_iInf_comap_val {ι : Type*} {U : Opens X} {V : ι → Opens X}
    (hV : ∀ i, V i ≤ U) {s : Finset ι} (hs : s.Nonempty) :
    Subtype.val '' ((⨅ i ∈ s,
      Opens.comap (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, X)) (V i) : Opens U) : Set U) =
      ⋂ i ∈ s, (V i : Set X) := by
  obtain ⟨j, hj⟩ := hs
  ext z
  rw [← Finset.inf_eq_iInf, coe_finset_inf, Finset.inf_eq_iInf]
  simpa using fun h ↦ hV j (h j hj)

end TopologicalSpace.Opens

end
