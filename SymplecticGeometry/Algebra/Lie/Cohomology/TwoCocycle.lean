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
through `TauCeti.LieModule.Cohomology.twoCochainEquiv`. This file sends a Mathlib `2`-cocycle to
its class in `TauCeti.LieModule.Cohomology.cohomology R L M 2`, and shows that every class arises
so, and that two cocycles have the same class exactly when they differ by a coboundary `d₁₂ f` of
a one-cochain `f`.

## Main definitions

* `TauCeti.LieModule.Cohomology.twoCocycleCycle`: the cycle `(twoCochainEquiv R L M).symm c` of
  the Chevalley–Eilenberg complex given by a `2`-cocycle `c`, built with Tau Ceti's
  `HomologicalComplex.moduleCatCyclesMk`.
* `TauCeti.LieModule.Cohomology.twoCocycleClass`: the class of a `2`-cocycle, the homology class
  of that cycle.

## Main results

* `TauCeti.LieModule.Cohomology.d_two_eq_zero_iff`: a Chevalley–Eilenberg `2`-cochain is a cycle
  exactly when its Mathlib form is a `2`-cocycle. Its proof is the step of Tau Ceti's
  `TauCeti.LieModule.Cohomology.twoCochainEquiv_mem_continuousTwoCocycle_iff` that compares the
  two differentials, without the continuity conditions.
* `TauCeti.LieModule.Cohomology.twoCocycleClass_eq_iff`: two `2`-cocycles have the same class
  exactly when they differ by a coboundary `d₁₂ f`.
* `TauCeti.LieModule.Cohomology.twoCocycleClass_eq_zero_iff`: a `2`-cocycle has class zero exactly
  when it is a coboundary `d₁₂ f`.
* `TauCeti.LieModule.Cohomology.exists_twoCocycleClass_eq`: every class is the class of a
  `2`-cocycle.

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

/-- The degree-two cycle of the Chevalley–Eilenberg complex given by a `2`-cocycle. -/
noncomputable def twoCocycleCycle (c : twoCochain R L M) (hc : c ∈ twoCocycle R L M) :
    (cochainComplex R L M).cycles 2 :=
  (cochainComplex R L M).moduleCatCyclesMk ((twoCochainEquiv R L M).symm c) 3 (by simp) <|
    (cochainComplex_d_two_eq_zero_iff _).2 (by rwa [LinearEquiv.apply_symm_apply])

/-- The **cohomology class** of a Lie algebra `2`-cocycle `c`, in the second Chevalley–Eilenberg
cohomology `cohomology R L M 2`: the class of the cycle `(twoCochainEquiv R L M).symm c`. -/
noncomputable def twoCocycleClass (c : twoCochain R L M) (hc : c ∈ twoCocycle R L M) :
    cohomology R L M 2 :=
  (cochainComplex R L M).homologyπ 2 (twoCocycleCycle R L M c hc)

variable {R L M}

/-- The cycle given by a `2`-cocycle `c` has underlying cochain `(twoCochainEquiv R L M).symm c`. -/
@[simp]
theorem iCycles_twoCocycleCycle (c : twoCochain R L M) (hc : c ∈ twoCocycle R L M) :
    (cochainComplex R L M).iCycles 2 (twoCocycleCycle R L M c hc) =
      (twoCochainEquiv R L M).symm c :=
  HomologicalComplex.iCycles_moduleCatCyclesMk _ _ _ _ _ _

/-- The class of a `2`-cocycle is the homology class of the cycle it gives. -/
theorem twoCocycleClass_def (c : twoCochain R L M) (hc : c ∈ twoCocycle R L M) :
    twoCocycleClass R L M c hc = (cochainComplex R L M).homologyπ 2 (twoCocycleCycle R L M c hc) :=
  (rfl)

/-- Two `2`-cocycles have the same class exactly when they differ by the coboundary `d₁₂ f` of a
one-cochain `f`. -/
theorem twoCocycleClass_eq_iff {c c' : twoCochain R L M} (hc : c ∈ twoCocycle R L M)
    (hc' : c' ∈ twoCocycle R L M) :
    twoCocycleClass R L M c hc = twoCocycleClass R L M c' hc' ↔
      ∃ f : oneCochain R L M, c = c' + d₁₂ R L M f := by
  rw [twoCocycleClass_def, twoCocycleClass_def,
    HomologicalComplex.moduleCat_homologyπ_eq_iff _ (m := 1) (by simp)]
  rw [iCycles_twoCocycleCycle, iCycles_twoCocycleCycle]
  refine ⟨fun ⟨y, hy⟩ ↦ ⟨oneCochainEquiv R L M y, ?_⟩, fun ⟨f, hf⟩ ↦
    ⟨(oneCochainEquiv R L M).symm f, (cochainComplex_d_succ_apply (n := 1) _).trans ?_⟩⟩
  · -- the subtraction in `hy` is that of `(cochainComplex R L M).X 2`
    have h : d R L M 1 y = (twoCochainEquiv R L M).symm (c - c') :=
      (cochainComplex_d_succ_apply (n := 1) y).symm.trans
        (hy.trans (map_sub (twoCochainEquiv R L M).symm c c').symm)
    have h' : twoCochainEquiv R L M (d R L M 1 y) = c - c' :=
      (twoCochainEquiv R L M).eq_symm_apply.1 h
    rw [twoCochainEquiv_d_one y] at h'
    rw [h']
    exact (add_sub_cancel c' c).symm
  · refine Eq.trans ?_ (map_sub (twoCochainEquiv R L M).symm c c')
    exact (twoCochainEquiv R L M).eq_symm_apply.2 (by
      rw [twoCochainEquiv_d_one, LinearEquiv.apply_symm_apply, hf]
      exact (add_sub_cancel_left c' _).symm)

/-- The zero cocycle has class zero. -/
@[simp]
theorem twoCocycleClass_zero : twoCocycleClass R L M 0 (zero_mem _) = 0 := by
  rw [twoCocycleClass_def, ← map_zero ((cochainComplex R L M).homologyπ 2).hom]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [iCycles_twoCocycleCycle, map_zero]
  exact (map_zero _).symm

/-- A `2`-cocycle has class zero exactly when it is the coboundary `d₁₂ f` of a one-cochain. -/
theorem twoCocycleClass_eq_zero_iff {c : twoCochain R L M} (hc : c ∈ twoCocycle R L M) :
    twoCocycleClass R L M c hc = 0 ↔ ∃ f : oneCochain R L M, d₁₂ R L M f = c := by
  rw [← twoCocycleClass_zero, twoCocycleClass_eq_iff]
  simp only [zero_add, eq_comm]

/-- Every class in the second cohomology is the class of a `2`-cocycle. -/
theorem exists_twoCocycleClass_eq (x : cohomology R L M 2) :
    ∃ (c : twoCochain R L M) (hc : c ∈ twoCocycle R L M), twoCocycleClass R L M c hc = x := by
  obtain ⟨z, rfl⟩ := (cochainComplex R L M).moduleCat_homologyπ_surjective 2 x
  have hz := (cochainComplex R L M).moduleCat_d_iCycles_apply 2 3 z
  rw [cochainComplex_d_two_eq_zero_iff] at hz
  refine ⟨_, hz, ?_⟩
  rw [twoCocycleClass_def]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [iCycles_twoCocycleCycle]
  exact LinearEquiv.symm_apply_apply _ _

end TauCeti.LieModule.Cohomology

end
