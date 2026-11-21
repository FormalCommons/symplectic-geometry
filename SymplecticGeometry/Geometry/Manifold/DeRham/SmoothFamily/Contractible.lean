/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.DegreeZero
public import SymplecticGeometry.Geometry.Manifold.DeRham.GoodCover.Basic
public import SymplecticGeometry.Geometry.Manifold.DeRham.SmoothFamily.Basic
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.HomotopyOperator

/-!
# Smooth cohomology splittings of smoothly contractible manifolds

A smoothly contractible manifold `N` has a smooth cohomology splitting
(`SymplecticGeometry.nonempty_smoothCohomologySplitting_of_isSmoothlyContractible`). Let
`Φ : N × [0, 1] → N` be a smooth contraction, from the constant map at `c` to the identity.

* In degree zero, the space of the splitting is the space of all closed `0`-forms, which is
  finite-dimensional since `N` is connected, and the projection is the identity.
* In positive degree, the space is `0` and the projection is `0`.
* The primitive of a closed `(k + 1)`-form `z` is `h (Φ^* z)`, the homotopy operator after
  pullback along the contraction. By the homotopy formula, `d (h (Φ^* z)) = z - c^* z`, and the
  pullback `c^* z` along the constant map vanishes in positive degree. The primitive takes smooth
  families to smooth families by
  `SymplecticGeometry.preservesSmoothFamilies_homotopyOperator_mpullback`.

This is the base case of the Mayer–Vietoris induction over a good cover, and the smooth
dependence on families of the Poincaré lemma in the form Weil gives it [Weil1952, §2].

## Main results

* `SymplecticGeometry.nonempty_smoothCohomologySplitting_of_isSmoothlyContractible`: a smoothly
  contractible manifold has a smooth cohomology splitting.
* `SymplecticGeometry.mextDerivₗ_homotopyOperator_mpullback_of_contraction`: for a contraction
  `Φ` and a closed form `z` of positive degree, `d (h (Φ^* z)) = z`.
* `SymplecticGeometry.IsSmoothlyContractible.finiteDimensional_closedForms_zero`: the closed
  `0`-forms of a smoothly contractible manifold form a finite-dimensional space.

## References

* [A. Weil, *Sur les théorèmes de de Rham*][Weil1952], §2 (the homotopy operator of a
  contraction).
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], proof of
  Theorem 3.2.4.
-/

public section

open Set
open scoped Manifold ContDiff

namespace SymplecticGeometry

open TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N]

/-- On a smoothly contractible manifold, the closed `0`-forms are a finite-dimensional space: they
are the constant functions, since the manifold is connected. -/
theorem IsSmoothlyContractible.finiteDimensional_closedForms_zero
    (h : IsSmoothlyContractible I N) : FiniteDimensional ℝ (closedForms I N 0) := by
  -- `N` is connected: the contraction joins every point to the centre `c`.
  obtain ⟨c, Φ, hΦ, h₀, h₁⟩ := isSmoothlyContractible_def.mp h
  have : ConnectedSpace N := by
    have : PreconnectedSpace N := ⟨isPreconnected_of_forall c fun y _ ↦
      ⟨range fun s ↦ Φ (y, s), subset_univ _, ⟨0, h₀ y⟩, ⟨1, h₁ y⟩,
        isPreconnected_range (hΦ.continuous.comp (continuous_const.prodMk continuous_id))⟩⟩
    exact ⟨⟨c⟩⟩
  have : FiniteDimensional ℝ (deRhamCohomology I N 0) :=
    Module.finite_of_finrank_eq_succ (finrank_deRhamCohomology_zero I N)
  exact ((closedFormsZeroEquiv I N).trans
    (deRhamCohomologyZeroEquiv I N).symm).symm.finiteDimensional

/-- Let `Φ : N × [0, 1] → N` be a smooth contraction of `N` to `c`, with `Φ (x, 0) = c` and
`Φ (x, 1) = x`. For a closed `(k + 1)`-form `z`, the form `h (Φ^* z)` is a primitive of `z`. -/
theorem mextDerivₗ_homotopyOperator_mpullback_of_contraction {c : N}
    {Φ : N × unitInterval → N} (hΦ : ContMDiff (I.prod (𝓡∂ 1)) I ∞ Φ) (h₀ : ∀ x, Φ (x, 0) = c)
    (h₁ : ∀ x, Φ (x, 1) = x) {k : ℕ} {z : SmoothForm I N ℝ (k + 1)}
    (hz : z ∈ closedForms I N (k + 1)) :
    mextDerivₗ I k (SmoothForm.homotopyOperator (SmoothForm.mpullback Φ hΦ z)) = z := by
  have hclosed : mextDerivₗ (I.prod (𝓡∂ 1)) (k + 1) (SmoothForm.mpullback Φ hΦ z) = 0 := by
    rw [SmoothForm.mextDerivₗ_mpullback, (mem_closedForms_iff_mextDerivₗ_eq_zero I z).mp hz,
      map_zero]
  rw [SmoothForm.mextDerivₗ_homotopyOperator hclosed, SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_mpullback]
  -- The end slices of the contraction are the identity and the constant map at `c`.
  have hid : Φ ∘ (fun x : N ↦ (x, (1 : unitInterval))) = id := funext h₁
  have hconst : Φ ∘ (fun x : N ↦ (x, (0 : unitInterval))) = fun _ ↦ c := funext h₀
  -- Pulling back along the constant map kills forms of positive degree.
  have hzero : ∀ (f : N → N) (hf : ContMDiff I I ∞ f), f = (fun _ ↦ c) →
      SmoothForm.mpullback f hf z = 0 := by
    rintro f hf rfl
    refine Subtype.ext (funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ ?_)
    rw [SmoothForm.coe_mpullback, TauCeti.mpullback_apply, mfderiv_const]
    exact (z.val c).map_coord_zero 0 rfl
  have hone : ∀ (f : N → N) (hf : ContMDiff I I ∞ f), f = id →
      SmoothForm.mpullback f hf z = z := by
    rintro f hf rfl
    rw [SmoothForm.mpullback_id, LinearMap.id_apply]
  rw [hone _ _ hid, hzero _ _ hconst, sub_zero]

variable (I) in
/-- **The splitting of a contractible manifold.** A smoothly contractible manifold `N` has a
smooth cohomology splitting: in degree zero its space is that of all closed `0`-forms, and in
positive degree it is `0`, with the primitive `z ↦ h (Φ^* z)` given by the homotopy operator
after pullback along a contraction `Φ`. -/
theorem nonempty_smoothCohomologySplitting_of_isSmoothlyContractible
    (h : IsSmoothlyContractible I N) : Nonempty (SmoothCohomologySplitting I N) := by
  have := h.finiteDimensional_closedForms_zero
  obtain ⟨c, Φ, hΦ, h₀, h₁⟩ := isSmoothlyContractible_def.mp h
  exact ⟨{
    space := fun
      | 0 => closedForms I N 0
      | _ + 1 => ⊥
    space_le_closedForms := fun
      | 0 => le_rfl
      | _ + 1 => bot_le
    finiteDimensional_space := fun
      | 0 => inferInstanceAs (FiniteDimensional ℝ (closedForms I N 0))
      | _ + 1 => inferInstanceAs (FiniteDimensional ℝ (⊥ : Submodule ℝ (SmoothForm I N ℝ _)))
    proj := fun
      | 0 => (closedForms I N 0).subtype
      | _ + 1 => 0
    proj_mem := fun
      | 0, z => z.property
      | _ + 1, _ => Submodule.zero_mem _
    proj_zero := fun _ ↦ rfl
    primitive := fun k ↦
      SmoothForm.homotopyOperator ∘ₗ SmoothForm.mpullback Φ hΦ ∘ₗ (closedForms I N (k + 1)).subtype
    mextDerivₗ_primitive := fun k z ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        mextDerivₗ_homotopyOperator_mpullback_of_contraction hΦ h₀ h₁ z.property,
        LinearMap.zero_apply, sub_zero]
    eq_zero_of_mem_exactForms := by
      rintro (_ | k) s hs hex
      · rwa [exactForms_zero, Submodule.mem_bot] at hex
      · exact (Submodule.mem_bot ℝ).mp hs
    preservesSmoothFamilies_proj := fun
      | 0 => preservesSmoothFamilies_subtype
      | _ + 1 => preservesSmoothFamilies_zero
    preservesSmoothFamilies_primitive := fun k ↦
      preservesSmoothFamilies_homotopyOperator_mpullback hΦ (closedForms I N (k + 1)) }⟩

end SymplecticGeometry
