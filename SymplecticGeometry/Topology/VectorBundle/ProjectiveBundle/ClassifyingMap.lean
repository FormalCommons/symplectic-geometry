/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.ProjectiveBundle.Tautological
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FiberwiseEquiv
public import TauCeti.Topology.VectorBundle.TrivialEmbedding

/-!
# Classifying maps of line bundles to projective spaces

A line bundle `E → B` that embeds fibrewise into a fixed topological vector space `V`, by linear
injections `j b : E b → V` that are continuous on the total space, is the pull-back of the
tautological line `Projectivization.Tautological 𝕜 V` of the library along the map sending `b` to
the line `j b (E b)`. Over a compact normal base, Tau Ceti's
`TauCeti.exists_continuous_injective_fin_of_compactSpace` gives such an embedding into some
`Fin N → 𝕜`, so every line bundle is pulled back from a finite projective space, and for a
complex line bundle the Euler class is the pull-back of the Euler class of the tautological line.

## Main results

* `SymplecticGeometry.Bundle.exists_fiberwise_tautological_of_injective`: a fibrewise injection
  `j` of a line bundle into `V`, continuous on the total space, gives a continuous map
  `g : B → ℙ 𝕜 V` and isomorphisms `E b ≃ Tautological 𝕜 V (g b)` that agree with `j b` and are
  continuous on total spaces.
* `SymplecticGeometry.Bundle.exists_fiberwise_tautological_fin`: over a compact normal base, every
  line bundle is the pull-back of the tautological line of some `ℙ 𝕜 (Fin N → 𝕜)`, in the form
  that `TauCeti.complexEulerClass_eq_singularCohomologyMap_of_fiberwise` takes.
* `SymplecticGeometry.Bundle.exists_complexEulerClass_eq_singularCohomologyMap_tautological`: the
  Euler class of a complex line bundle over a compact normal base is pulled back from that of the
  tautological line of some `ℙ ℂ (Fin N → ℂ)`.

## Proof

The line `j b (E b)` has dimension one, since `E b` is isomorphic to the model fibre. Near a point
`b₀`, a trivialization of `E` gives a nonvanishing local section `b ↦ e.symm b c`, and `g b` is the
class of the nonzero vector `j b (e.symm b c)`, which depends continuously on `b`. The isomorphism
`E b ≃ Tautological 𝕜 V (g b)` is `j b` with its codomain restricted, and it is continuous on total
spaces because the tautological line carries the topology of a subspace of `ℙ 𝕜 V × V`. This is
the argument of Milnor–Stasheff, §5, for the Gauss map, with a fixed target space.

The construction is that of Tau Ceti's `TauCeti.IsClassifyingCoordinates.classify` and
`TauCeti.IsClassifyingCoordinates.classifyTautologicalEquiv`, which send a point to the range of
classifying coordinates in `ℕ →₀ 𝕜` and land in the infinite Grassmannian, a direct limit; here
the target is the projective space of a fixed space `V`, on which the library's tautological line
and, for `V = Fin N → ℂ`, the cohomology ring of `ℙ ℂ V` are available.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press (1974), §5 (classifying maps of vector bundles).
-/

public section

noncomputable section

open Bundle Module Set Topology
open scoped LinearAlgebra.Projectivization

namespace SymplecticGeometry.Bundle

open Projectivization

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {B : Type*}
  [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  {V : Type*} [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V] [T2Space V]

/-- A fibrewise injective linear map `j b : E b → V` from a line bundle `E`, continuous on the
total space, classifies `E`: the map `g` sending `b` to the line `j b (E b)` is continuous, and
`j b`, corestricted to that line, is an isomorphism `E b ≃ Tautological 𝕜 V (g b)`, continuous
on total spaces. -/
theorem exists_fiberwise_tautological_of_injective (hF : finrank 𝕜 F = 1)
    (j : ∀ b, E b →ₗ[𝕜] V) (hjc : Continuous fun v : TotalSpace F E ↦ j v.proj v.snd)
    (hj : ∀ b, Function.Injective (j b)) :
    ∃ (g : C(B, ℙ 𝕜 V)) (φ : ∀ b, E b ≃L[𝕜] Tautological 𝕜 V (g b)),
      (∀ b v, (φ b v : V) = j b v) ∧
      Continuous fun v : TotalSpace F E ↦
        TotalSpace.mk' 𝕜 (E := Tautological 𝕜 V) (g v.proj) (φ v.proj v.snd) := by
  have : FiniteDimensional 𝕜 F := Module.finite_of_finrank_eq_succ hF
  -- The fibre over `b`, read in the trivialization at `b`.
  let e : ∀ b, E b ≃L[𝕜] F := VectorBundle.continuousLinearEquivAt 𝕜 F E
  have hrange : ∀ b, finrank 𝕜 (LinearMap.range (j b)) = 1 := fun b ↦
    (LinearEquiv.ofInjective (j b) (hj b)).finrank_eq.symm.trans
      ((e b).toLinearEquiv.finrank_eq.trans hF)
  let g₀ : B → ℙ 𝕜 V := fun b ↦ mk'' (LinearMap.range (j b)) (hrange b)
  -- The line `g₀ x` is spanned by the image of any nonzero vector of `E x`.
  have hg₀ : ∀ x (w : E x) (hw : w ≠ 0),
      g₀ x = mk 𝕜 (j x w) ((map_ne_zero_iff _ (hj x)).2 hw) := by
    intro x w hw
    exact (mem_submodule_iff.1
      (by rw [submodule_mk'']; exact LinearMap.mem_range_self _ _) _).symm
  have : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  obtain ⟨c, hc⟩ := exists_ne (0 : F)
  have hg₀c : Continuous g₀ := by
    refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
    let e' := trivializationAt F E x₀
    have hs : ContinuousOn (fun x ↦ (fun v : TotalSpace F E ↦ j v.proj v.snd)
        (e'.toOpenPartialHomeomorph.symm (x, c))) e'.baseSet :=
      hjc.comp_continuousOn e'.continuousOn_symm_prodMk_left
    have hon : ContinuousOn g₀ e'.baseSet := by
      have hw : ∀ x : e'.baseSet, (e'.continuousLinearEquivAt 𝕜 x x.property).symm c ≠ 0 := fun x ↦
        (map_ne_zero_iff _
          (e'.continuousLinearEquivAt 𝕜 x x.property).symm.injective).2 hc
      have hs' : Continuous fun x : e'.baseSet ↦
          j x ((e'.continuousLinearEquivAt 𝕜 x x.property).symm c) := by
        refine (continuousOn_iff_continuous_domRestrict.1 hs).congr fun x ↦ ?_
        rw [domRestrict_apply,
          e'.symm_apply_eq_mk_continuousLinearEquivAt_symm (R := 𝕜) x x.property]
      rw [continuousOn_iff_continuous_domRestrict]
      exact (continuous_mk hs' fun x ↦ (map_ne_zero_iff _ (hj x)).2 (hw x)).congr fun x ↦
        (hg₀ x _ (hw x)).symm
    exact hon.continuousAt (e'.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E x₀))
  let g : C(B, ℙ 𝕜 V) := ⟨g₀, hg₀c⟩
  let φ : ∀ b, E b ≃L[𝕜] Tautological 𝕜 V (g b) := fun b ↦ (e b).trans
    (LinearEquiv.toContinuousLinearEquiv ((e b).symm.toLinearEquiv.trans
      ((LinearEquiv.ofInjective (j b) (hj b)).trans
        (LinearEquiv.ofEq _ _ (submodule_mk'' _ (hrange b)).symm))))
  have hφ : ∀ b v, (φ b v : V) = j b v := fun b v ↦ by simp [φ]
  refine ⟨g, φ, hφ, Projectivization.continuous_totalSpace_tautological_iff.2
    ⟨hg₀c.comp (FiberBundle.continuous_proj F E), ?_⟩⟩
  simpa only [hφ] using hjc

end General

section Compact

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜] {B : Type*}
  [TopologicalSpace B] [CompactSpace B] [NormalSpace B] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- **Classifying maps of line bundles to finite projective spaces.** A line bundle `E` over a
compact normal (for instance compact Hausdorff) base `B` is the pull-back of the tautological line
of some `ℙ 𝕜 (Fin N → 𝕜)`: there are a continuous map `g : B → ℙ 𝕜 (Fin N → 𝕜)` and isomorphisms
`E b ≃ Tautological 𝕜 (Fin N → 𝕜) (g b)`, continuous on total spaces. -/
theorem exists_fiberwise_tautological_fin (hF : finrank 𝕜 F = 1) :
    ∃ (N : ℕ) (g : C(B, ℙ 𝕜 (Fin N → 𝕜)))
      (φ : ∀ b, E b ≃L[𝕜] Tautological 𝕜 (Fin N → 𝕜) (g b)),
      Continuous fun v : TotalSpace F E ↦
        TotalSpace.mk' 𝕜 (E := Tautological 𝕜 (Fin N → 𝕜)) (g v.proj) (φ v.proj v.snd) := by
  have : FiniteDimensional 𝕜 F := Module.finite_of_finrank_eq_succ hF
  obtain ⟨N, j, hjc, hj⟩ :=
    TauCeti.exists_continuous_injective_fin_of_compactSpace (𝕜 := 𝕜) (F := F) (E := E)
  obtain ⟨g, φ, -, hφ⟩ := exists_fiberwise_tautological_of_injective hF
    (fun b ↦ (j b).toLinearMap) hjc hj
  exact ⟨N, g, φ, hφ⟩

end Compact

section EulerClass

open TauCeti

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [NormalSpace B]
  {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
  [FiniteDimensional ℂ G]
  {E : B → Type} [TopologicalSpace (TotalSpace G E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, Module ℂ (E b)] [∀ b, IsScalarTower ℝ ℂ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle G E] [VectorBundle ℂ G E]

/-- The Euler class of a complex line bundle `E` over a compact normal base is the pull-back of
the Euler class of the tautological line of some `ℙ ℂ (Fin N → ℂ)`, along a continuous map. -/
theorem exists_complexEulerClass_eq_singularCohomologyMap_tautological
    (hG : finrank ℂ G = 1) :
    ∃ (N : ℕ) (g : C(B, ℙ ℂ (Fin N → ℂ))),
      complexEulerClass (r := 0) G E hG = TopCat.singularCohomologyMap (TopCat.ofHom g) 2
        (complexEulerClass (r := 0) ℂ (Tautological ℂ (Fin N → ℂ)) (finrank_self ℂ)) := by
  obtain ⟨N, g, φ, hφ⟩ := exists_fiberwise_tautological_fin (E := E) hG
  exact ⟨N, g, complexEulerClass_eq_singularCohomologyMap_of_fiberwise (finrank_self ℂ) hG hφ⟩

end EulerClass

end SymplecticGeometry.Bundle

end
