/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg

/-!
# The cohomology class of a Lie algebra `2`-cocycle

Mathlib describes the Lie algebra `2`-cocycles of `L` with coefficients in `M` as the kernel
`LieModule.Cohomology.twoCocycle R L M` of `d₂₃` on alternating bilinear maps, without a second
cohomology group. Tau Ceti's Chevalley–Eilenberg complex has cohomology in every degree
(`TauCeti.LieModule.Cohomology.cohomology`), and identifies its degree-two cochains with Mathlib's
through `TauCeti.LieModule.Cohomology.twoCochainEquiv`. This file gives the `R`-linear map that
sends a Mathlib `2`-cocycle to its class in `TauCeti.LieModule.Cohomology.cohomology R L M 2`,
and shows that it is surjective, and that two cocycles have the same class exactly when they
differ by a coboundary `d₁₂ f` of a one-cochain `f`.

The class map is Tau Ceti's `HomologicalComplex.moduleCatHomologyClass` for the kernel of the
Chevalley–Eilenberg differential `d R L M 2`, precomposed with the restriction of
`(twoCochainEquiv R L M).symm` to the `2`-cocycles. Its source cannot be `twoCocycle R L M`
itself, since `moduleCatHomologyClass` needs an `AddCommGroup` on its source and that instance
does not synthesize on the submodule `twoCocycle R L M`.

## Main definitions

* `TauCeti.LieModule.Cohomology.twoCocycleClass`: the class of a `2`-cocycle, as a linear map
  `twoCocycle R L M →ₗ[R] cohomology R L M 2`.

## Main results

* `TauCeti.LieModule.Cohomology.d_two_eq_zero_iff`: a Chevalley–Eilenberg `2`-cochain is a cycle
  exactly when its Mathlib form is a `2`-cocycle. Its proof is the step of Tau Ceti's
  `TauCeti.LieModule.Cohomology.twoCochainEquiv_mem_continuousTwoCocycle_iff` that compares the
  two differentials, without the continuity conditions.
* `TauCeti.LieModule.Cohomology.twoCocycleClass_eq_iff`: two `2`-cocycles have the same class
  exactly when they differ by a coboundary `d₁₂ f`.
* `TauCeti.LieModule.Cohomology.twoCocycleClass_eq_zero_iff`: a `2`-cocycle has class zero exactly
  when it is a coboundary `d₁₂ f`, from Tau Ceti's
  `HomologicalComplex.moduleCatHomologyClass_eq_zero_iff`.
* `TauCeti.LieModule.Cohomology.twoCocycleClass_surjective`: every class is the class of a
  `2`-cocycle, from Tau Ceti's `HomologicalComplex.moduleCatHomologyClass_surjective`.

## References

* C. Chevalley and S. Eilenberg, *Cohomology theory of Lie groups and Lie algebras*,
  Trans. Amer. Math. Soc. 63 (1948), 85–124.
-/

public section

namespace TauCeti.LieModule.Cohomology

open _root_.LieModule.Cohomology

variable (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {R L M} in
/-- A Chevalley–Eilenberg `2`-cochain is a cycle exactly when its Mathlib form is a
`2`-cocycle. -/
theorem d_two_eq_zero_iff (ω : L [⋀^Fin 2]→ₗ[R] M) :
    d R L M 2 ω = 0 ↔ twoCochainEquiv R L M ω ∈ twoCocycle R L M := by
  rw [mem_twoCocycle_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext x y z
    rw [d₂₃_twoCochainEquiv, h, zero_apply, LinearMap.zero_apply,
      LinearMap.zero_apply, LinearMap.zero_apply]
  · ext v
    have hv : v = ![v 0, v 1, v 2] := by ext i; fin_cases i <;> rfl
    rw [hv, ← d₂₃_twoCochainEquiv, h, LinearMap.zero_apply, LinearMap.zero_apply,
      LinearMap.zero_apply, zero_apply]

variable {R L M} in
/-- An element of degree two of the Chevalley–Eilenberg complex is a cycle exactly when its
Mathlib form is a `2`-cocycle. -/
theorem cochainComplex_d_two_eq_zero_iff (ω : (cochainComplex R L M).X 2) :
    (cochainComplex R L M).d 2 3 ω = 0 ↔ twoCochainEquiv R L M ω ∈ twoCocycle R L M :=
  -- the differential of `cochainComplex` is `d R L M 2` by `cochainComplex_d_succ`, through
  -- `ModuleCat.ofHom`, which `rw` does not see through on `(cochainComplex R L M).X 2`
  d_two_eq_zero_iff ω

variable {R L M} in
/-- The differential of the Chevalley–Eilenberg complex, applied to an `n`-cochain. -/
theorem cochainComplex_d_succ_apply {n : ℕ} (ω : L [⋀^Fin n]→ₗ[R] M) :
    (cochainComplex R L M).d n (n + 1) ω = d R L M n ω := by
  rw [cochainComplex_d_succ]
  -- `ModuleCat.ofHom_apply` does not rewrite here, as the argument has type
  -- `L [⋀^Fin n]→ₗ[R] M` rather than `ModuleCat.of R _`
  rfl

/-- The **cohomology class** of a Lie algebra `2`-cocycle, as an `R`-linear map from Mathlib's
`2`-cocycles `twoCocycle R L M` to the second Chevalley–Eilenberg cohomology
`cohomology R L M 2`: a cocycle `c` goes to the class of the cycle
`(twoCochainEquiv R L M).symm c`. -/
noncomputable def twoCocycleClass : twoCocycle R L M →ₗ[R] cohomology R L M 2 :=
  (cochainComplex R L M).moduleCatHomologyClass (n := 2) (m := 3) (by simp)
      (LinearMap.ker (d R L M 2)).subtype
      (fun z ↦ (cochainComplex_d_succ_apply (n := 2) _).trans z.property) ∘ₗ
    ((twoCochainEquiv R L M).symm.toLinearMap ∘ₗ (twoCocycle R L M).subtype).codRestrict _
      fun c ↦ (d_two_eq_zero_iff _).2 (by simp)

variable {R L M} in
/-- The class map of `2`-cocycles is Tau Ceti's homology class map of the kernel of `d R L M 2`,
precomposed with the restriction of `(twoCochainEquiv R L M).symm`. -/
theorem twoCocycleClass_def :
    twoCocycleClass R L M =
      (cochainComplex R L M).moduleCatHomologyClass (n := 2) (m := 3) (by simp)
          (LinearMap.ker (d R L M 2)).subtype
          (fun z ↦ (cochainComplex_d_succ_apply (n := 2) _).trans z.property) ∘ₗ
        ((twoCochainEquiv R L M).symm.toLinearMap ∘ₗ (twoCocycle R L M).subtype).codRestrict _
          fun c ↦ (d_two_eq_zero_iff _).2 (by simp) :=
  (rfl)

variable {R L M}

/-- The class of a `2`-cocycle `c` is the homology class of the cycle
`(twoCochainEquiv R L M).symm c`. -/
theorem twoCocycleClass_apply (c : twoCocycle R L M) :
    twoCocycleClass R L M c =
      (cochainComplex R L M).homologyπ 2
        ((cochainComplex R L M).moduleCatCyclesMk
          ((twoCochainEquiv R L M).symm (c : twoCochain R L M)) 3 (by simp)
          ((cochainComplex_d_two_eq_zero_iff _).2 (by simp))) := by
  rw [twoCocycleClass_def, LinearMap.comp_apply]
  -- `rw` with `moduleCatHomologyClass_apply` fails: the codomain of the kernel's `subtype` is
  -- `L [⋀^Fin 2]→ₗ[R] M`, equal to `(cochainComplex R L M).X 2` only up to unfolding
  exact HomologicalComplex.moduleCatHomologyClass_apply _ _ _ _ _

/-- A `2`-cocycle has class zero exactly when it is the coboundary `d₁₂ f` of a one-cochain. -/
theorem twoCocycleClass_eq_zero_iff (c : twoCocycle R L M) :
    twoCocycleClass R L M c = 0 ↔ ∃ f : oneCochain R L M, d₁₂ R L M f = c := by
  rw [twoCocycleClass_def, LinearMap.comp_apply]
  refine (HomologicalComplex.moduleCatHomologyClass_eq_zero_iff _ _ _ _ (p := 1) (by simp)
    _).trans ⟨fun ⟨y, hy⟩ ↦ ⟨oneCochainEquiv R L M y, ?_⟩, fun ⟨f, hf⟩ ↦
      ⟨(oneCochainEquiv R L M).symm f, (cochainComplex_d_succ_apply (n := 1) _).trans ?_⟩⟩
  · have h : twoCochainEquiv R L M (d R L M 1 y) = c :=
      (twoCochainEquiv R L M).eq_symm_apply.1
        ((cochainComplex_d_succ_apply (n := 1) y).symm.trans hy)
    rwa [twoCochainEquiv_d_one y] at h
  · refine (twoCochainEquiv R L M).eq_symm_apply.2 ?_
    rw [twoCochainEquiv_d_one, LinearEquiv.apply_symm_apply, hf]
    exact ((twoCocycle R L M).subtype_apply c).symm

/-- Two `2`-cocycles have the same class exactly when they differ by the coboundary `d₁₂ f` of a
one-cochain `f`. -/
theorem twoCocycleClass_eq_iff (c c' : twoCocycle R L M) :
    twoCocycleClass R L M c = twoCocycleClass R L M c' ↔
      ∃ f : oneCochain R L M, (c : twoCochain R L M) = c' + d₁₂ R L M f := by
  -- as in `twoCocycleClass_apply`, `iCycles_moduleCatCyclesMk` applies only up to unfolding
  have hi : ∀ (c : twoCochain R L M) h, (cochainComplex R L M).iCycles 2
      ((cochainComplex R L M).moduleCatCyclesMk ((twoCochainEquiv R L M).symm c) 3 (by simp) h) =
        (twoCochainEquiv R L M).symm c :=
    fun _ _ ↦ HomologicalComplex.iCycles_moduleCatCyclesMk _ _ _ _ _ _
  rw [twoCocycleClass_apply, twoCocycleClass_apply,
    HomologicalComplex.moduleCat_homologyπ_eq_iff _ (m := 1) (by simp), hi, hi]
  refine ⟨fun ⟨y, hy⟩ ↦ ⟨oneCochainEquiv R L M y, ?_⟩, fun ⟨f, hf⟩ ↦
    ⟨(oneCochainEquiv R L M).symm f, (cochainComplex_d_succ_apply (n := 1) _).trans ?_⟩⟩
  · -- the subtraction in `hy` is that of `(cochainComplex R L M).X 2`
    have h : d R L M 1 y = (twoCochainEquiv R L M).symm ((c : twoCochain R L M) - c') :=
      (cochainComplex_d_succ_apply (n := 1) y).symm.trans
        (hy.trans (map_sub (twoCochainEquiv R L M).symm (c : twoCochain R L M) c').symm)
    have h' : twoCochainEquiv R L M (d R L M 1 y) = (c : twoCochain R L M) - c' :=
      (twoCochainEquiv R L M).eq_symm_apply.1 h
    rw [twoCochainEquiv_d_one y] at h'
    rw [h']
    exact (add_sub_cancel (c' : twoCochain R L M) c).symm
  · refine Eq.trans ?_ (map_sub (twoCochainEquiv R L M).symm (c : twoCochain R L M) c')
    exact (twoCochainEquiv R L M).eq_symm_apply.2 (by
      rw [twoCochainEquiv_d_one, LinearEquiv.apply_symm_apply, hf]
      exact (add_sub_cancel_left (c' : twoCochain R L M) _).symm)

/-- Every class in the second cohomology is the class of a `2`-cocycle. -/
theorem twoCocycleClass_surjective : Function.Surjective (twoCocycleClass R L M) := by
  rw [twoCocycleClass_def, LinearMap.coe_comp]
  refine (HomologicalComplex.moduleCatHomologyClass_surjective _ _ _ _
    fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩).comp fun z ↦ ?_
  refine ⟨⟨twoCochainEquiv R L M z, (d_two_eq_zero_iff _).1 z.property⟩, Subtype.ext ?_⟩
  exact LinearEquiv.symm_apply_apply _ _

end TauCeti.LieModule.Cohomology

end
