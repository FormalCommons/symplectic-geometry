/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Topology
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# Corestriction of `C^n` maps to an open subset of the target

A `C^n` map `f : M → N` whose values lie in an open subset `W` of `N` is a `C^n` map into the
manifold `W` (`ContMDiffMap.codRestrict`). The charts of `W` are the restrictions of those of
`N`, so a compact derivative test of the weak Whitney topology on `C^n⟮I, M; J, W⟯` is the
preimage of the test with the same data on `C^n⟮I, M; J, N⟯`
(`ContMDiffMap.codRestrict_mem_chartJetSet_iff`). Hence corestriction is continuous for the weak
Whitney topologies (`ContMDiffMap.continuous_codRestrict_manifoldWeakWhitney`), with no
hypothesis on the models.

The weak Whitney topology is Tau Ceti's, following M. Hirsch, *Differential Topology*, GTM 33,
Chapter 2, §1.

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 2, §1
-/

public section

open Set TopologicalSpace
open scoped Manifold

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : WithTop ℕ∞}

/-- The corestriction of a `C^n` map to an open subset of the target containing its values. -/
def codRestrict (f : C^n⟮I, M; J, N⟯) (W : Opens N) (h : ∀ x, f x ∈ W) : C^n⟮I, M; J, W⟯ :=
  ⟨fun x ↦ ⟨f x, h x⟩, (TauCeti.ContMDiff.subtypeVal_comp_iff W _).mp f.contMDiff⟩

/-- The corestriction has the values of the map. -/
@[simp]
theorem coe_codRestrict_apply (f : C^n⟮I, M; J, N⟯) (W : Opens N) (h : ∀ x, f x ∈ W) (x : M) :
    (f.codRestrict W h x : N) = f x :=
  (rfl)

/-- Following the corestriction by the inclusion of `W` gives back the map. -/
@[simp]
theorem val_comp_codRestrict (f : C^n⟮I, M; J, N⟯) (W : Opens N) (h : ∀ x, f x ∈ W) :
    Subtype.val ∘ f.codRestrict W h = f :=
  (rfl)

/-- A compact derivative test on maps into an open subset `W` is the test with the same data on
maps into `N`: the charts of `W` restrict those of `N`. -/
theorem codRestrict_mem_chartJetSet_iff [IsManifold I n M] [IsManifold J n N]
    (f : C^n⟮I, M; J, N⟯) (W : Opens N) (h : ∀ x, f x ∈ W) (x : M) (y : W) (m : ℕ)
    (K : Set (extChartAt I x).target) (V : Set (E [×m]→L[𝕜] F)) :
    f.codRestrict W h ∈ chartJetSet x y m K V ↔ f ∈ chartJetSet x (y : N) m K V := by
  have hcomp : extChartAt J y ∘ f.codRestrict W h = extChartAt J (y : N) ∘ f := by
    funext z
    exact W.extChartAt_apply y _
  simp only [mem_chartJetSet, W.extChartAt_source_eq, coe_codRestrict_apply]
  rw [← Function.comp_assoc, hcomp, Function.comp_assoc]

attribute [local instance] manifoldWeakWhitneyTopology

/-- Corestriction to an open subset of the target is continuous for the weak Whitney
topologies. -/
theorem continuous_codRestrict_manifoldWeakWhitney [IsManifold I n M] [IsManifold J n N]
    (W : Opens N) :
    Continuous fun f : {f : C^n⟮I, M; J, N⟯ // ∀ x, f x ∈ W} ↦ f.val.codRestrict W f.property := by
  refine continuous_manifoldWeakWhitney_iff.mpr fun x y m hm K hK V hV ↦ ?_
  have h : (fun f : {f : C^n⟮I, M; J, N⟯ // ∀ x, f x ∈ W} ↦ f.val.codRestrict W f.property) ⁻¹'
      chartJetSet x y m K V = Subtype.val ⁻¹' chartJetSet x (y : N) m K V := by
    ext f
    exact codRestrict_mem_chartJetSet_iff f.val W f.property x y m K V
  rw [h]
  exact (isOpen_chartJetSet x (y : N) m hm hK hV).preimage continuous_subtypeVal

/-- A family of `C^n` maps into `N` with values in an open subset `W` that is continuous for the
weak Whitney topology stays continuous after corestriction to `W`. -/
theorem _root_.Continuous.codRestrict_manifoldWeakWhitney [IsManifold I n M] [IsManifold J n N]
    {P : Type*} [TopologicalSpace P] {g : P → C^n⟮I, M; J, N⟯} (hg : Continuous g) (W : Opens N)
    (h : ∀ p x, g p x ∈ W) :
    Continuous fun p ↦ (g p).codRestrict W (h p) :=
  (continuous_codRestrict_manifoldWeakWhitney W).comp (hg.subtype_mk h)

end ContMDiffMap

end
