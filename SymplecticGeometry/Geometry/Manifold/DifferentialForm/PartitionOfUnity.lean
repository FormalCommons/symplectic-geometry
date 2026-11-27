/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Basic
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Semibasic

/-!
# Gluing forms on open sets with a partition of unity of a base

Let `proj : X → B` be a smooth map and `ρ` a smooth partition of unity on `B`. Given, for each
`i`, an open set `W i` of `X` containing the preimage of the topological support of `ρ i` (for
instance `proj ⁻¹' U i`, when `ρ` is subordinate to an open cover `U`) and a form `η i` on
`W i`, the glued form `ρ.glueForms proj W η` is `∑ᵢ (ρ i ∘ proj) • η i`, each term
extended by zero off `W i`; at each point only the finitely many indices of
`ρ.finsupport (proj x)` contribute.

## Main results

* `SmoothPartitionOfUnity.isSmoothForm_glueForms`: the glued form of `C^n` forms is `C^n`.
* `SmoothPartitionOfUnity.mextDeriv_glueForms_apply_of_mem_ker`: on tangent vectors in the kernel
  of the differential of `proj`, the exterior derivative of the glued form is
  `∑ᵢ ρ i (proj x) * dη i`. By the Leibniz rule, `d((ρ i ∘ proj) • η i)` is
  `d(ρ i ∘ proj) ∧ η i + (ρ i ∘ proj) • dη i`, and `d(ρ i ∘ proj)` vanishes on such vectors,
  being semibasic for `proj` (`TauCeti.RoughForm.isSemibasicAt_mextDeriv_ofFunction_comp`).

Each `η i` is extended to `X` by `TauCeti.RoughForm.extendByZeroOfOpens`. The smoothness proof
follows Tau Ceti's `TauCeti.isSmoothForm_sum_finsupport_smul_mpullback`. The derivative proof
follows the library's `TauCeti.mextDeriv_sum_finsupport_smul_mpullback_apply`: it reduces the
locally finite sum to the finite set `ρ.fintsupport (proj x)` near `x`, and applies the Leibniz
rule to each term.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 6.1.4.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Chapters 2 and 14.
-/

public section

open Set Filter TopologicalSpace Bundle
open scoped Manifold Topology ContDiff

variable {EX HX X EB HB B F : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

namespace SmoothPartitionOfUnity

open TauCeti TauCeti.RoughForm

variable {ι : Type*} {s : Set B} (ρ : SmoothPartitionOfUnity ι IB B s) (proj : X → B)
  (W : ι → Opens X)

/-- **Gluing forms on open sets with a partition of unity of a base.** For a partition of unity
`ρ` on `B`, a map `proj : X → B`, and forms `η i` on open sets `W i` of `X`, the form
`∑ᵢ (ρ i ∘ proj) • η i` on `X`, where each `η i` is extended by zero off `W i`. The sum at `x`
runs over the finite set `ρ.finsupport (proj x)` of indices whose weight does not vanish at
`proj x`. -/
noncomputable def glueForms (η : ∀ i, RoughForm IX (W i) F k) : RoughForm IX X F k :=
  fun x ↦ ∑ i ∈ ρ.finsupport (proj x), ρ i (proj x) • extendByZeroOfOpens (η i) x

/-- The value of the glued form `ρ.glueForms proj W η` at a point. -/
theorem glueForms_apply (η : ∀ i, RoughForm IX (W i) F k) (x : X) :
    ρ.glueForms proj W η x =
      ∑ i ∈ ρ.finsupport (proj x), ρ i (proj x) • extendByZeroOfOpens (η i) x :=
  (rfl)

variable {ρ proj W}

private theorem isSmoothForm_smul_extendByZeroOfOpens [IsManifold IX 1 X] {n : ℕ∞}
    (hproj : ContMDiff IX IB n proj) (hW : ∀ i, proj ⁻¹' tsupport (ρ i) ⊆ W i)
    {η : ∀ i, RoughForm IX (W i) F k} (hη : ∀ i, IsSmoothForm IX n (η i)) (i : ι) :
    IsSmoothForm IX n (fun y ↦ ρ i (proj y) • extendByZeroOfOpens (η i) y) :=
  isSmoothForm_fun_smul_of_mpullback_subtype_val (f := ρ i ∘ proj)
    (((ρ i).contMDiff.of_le (by exact_mod_cast le_top)).comp hproj)
    ((tsupport_comp_subset_preimage _ hproj.continuous).trans (hW i))
    (by rw [mpullback_subtype_val_extendByZeroOfOpens]; exact hη i)

/-- **The glued form is smooth.** Let `ρ` be a smooth partition of unity on `B`, `proj : X → B`
a `C^n` map, and `η i` a `C^n` form on an open set `W i` of `X` that contains the preimage of the
topological support of `ρ i`. Then `ρ.glueForms proj W η` is a `C^n` form on `X`. -/
theorem isSmoothForm_glueForms [IsManifold IX 1 X] {n : ℕ∞} (hproj : ContMDiff IX IB n proj)
    (hW : ∀ i, proj ⁻¹' tsupport (ρ i) ⊆ W i) {η : ∀ i, RoughForm IX (W i) F k}
    (hη : ∀ i, IsSmoothForm IX n (η i)) : IsSmoothForm IX n (ρ.glueForms proj W η) := by
  rw [isSmoothForm_def]
  have hsum : ∀ x, ρ.glueForms proj W η x =
      ∑ᶠ i, ρ i (proj x) • extendByZeroOfOpens (η i) x := fun x ↦
    (glueForms_apply ρ proj W η x).trans (ρ.sum_finsupport_smul_eq_finsum (x₀ := proj x)
      (φ := fun i _ ↦ extendByZeroOfOpens (η i) x))
  simp_rw [hsum]
  refine ContMDiff.finsum_section_of_locallyFinite
    (t := fun i y ↦ ρ i (proj y) • extendByZeroOfOpens (η i) y) ?_ fun i x ↦ ?_
  · refine (ρ.locallyFinite.preimage_continuous hproj.continuous).subset fun i x hx ↦ ?_
    exact left_ne_zero_of_smul hx
  · exact (isSmoothForm_smul_extendByZeroOfOpens hproj hW hη i).contMDiff x

/-- The derivative of one term `(ρ i ∘ proj) • η i` of the glued form, at a point of `W i`, on
tangent vectors in the kernel of the differential of `proj`. -/
private theorem mextDeriv_smul_extendByZeroOfOpens_apply_of_mem_ker [IsManifold IX 1 X]
    (hproj : ContMDiff IX IB 1 proj)
    {η : ∀ i, RoughForm IX (W i) ℝ k} (hη : ∀ i, IsSmoothForm IX 1 (η i)) (i : ι) {x : X}
    (hx : x ∈ W i) {v : Fin (k + 1) → TangentSpace IX x}
    (hv : ∀ j, v j ∈ (mfderiv IX IB proj x).ker) :
    mextDeriv (fun y ↦ ρ i (proj y) • extendByZeroOfOpens (η i) y) x v =
      ρ i (proj x) * mextDeriv (η i) ⟨x, hx⟩ v := by
  have hρi : MDifferentiableAt IB 𝓘(ℝ) (ρ i) (proj x) :=
    (ρ i).contMDiff.mdifferentiableAt (by simp)
  have hprojx : MDifferentiableAt IX IB proj x := hproj.mdifferentiableAt (by simp)
  have hμ := ((contMDiffAt_mpullback_subtype_val_iff (extendByZeroOfOpens (η i)) ⟨x, hx⟩).1
    (by rw [mpullback_subtype_val_extendByZeroOfOpens]; exact (hη i).contMDiff _))
      |>.mdifferentiableAt (by simp)
  -- The term is the pointwise product `(ρ i ∘ proj) • extendByZeroOfOpens (η i)` of the Leibniz
  -- rule.
  have hleib : mextDeriv (fun y ↦ ρ i (proj y) • extendByZeroOfOpens (η i) y) x v = _ :=
    mextDeriv_fun_smul (f := ρ i ∘ proj) (hρi.comp x hprojx) hμ v
  -- `d(ρ i ∘ proj)` is semibasic for `proj`, so it vanishes on vertical vectors.
  have hdf := isSemibasicAt_mextDeriv_ofFunction_comp hρi hprojx
  have hd : mextDeriv (extendByZeroOfOpens (η i)) x = mextDeriv (η i) ⟨x, hx⟩ := by
    have h := congrFun (mpullback_subtype_val_mextDeriv (U := W i)
      (extendByZeroOfOpens (η i))) ⟨x, hx⟩
    rwa [mpullback_subtype_val_apply, mpullback_subtype_val_extendByZeroOfOpens] at h
  rw [hleib, RoughForm.wedge_apply, Finset.sum_eq_zero fun σ _ ↦ by
      rw [hdf.apply_eq_zero (fun j ↦ (v ∘ Fin.cast _) (σ (Fin.castAdd k j))) 0 (hv _), zero_mul,
        smul_zero],
    smul_zero, zero_add, Function.comp_apply, hd]
  -- Both sides apply the same form to `v`, read in `TangentSpace IX x` and in the tangent space
  -- of `W i` at `x`, which are the same model space.
  rfl

/-- **The derivative of the glued form on vertical vectors.** Let `ρ` be a smooth partition of
unity on `B`, `proj : X → B` a `C^1` map, and `η i` a `C^1` real form on an open set `W i` of
`X` that contains the preimage of the topological support of `ρ i`. At `x : X`, on tangent
vectors in the kernel of the differential of `proj`, the exterior derivative of
`ρ.glueForms proj W η` is `∑ᵢ ρ i (proj x) * dη i`, over the indices `i` with `proj x` in the
topological support of `ρ i`, at each of which `x` lies in `W i`. -/
theorem mextDeriv_glueForms_apply_of_mem_ker [IsManifold IX 1 X]
    (hproj : ContMDiff IX IB 1 proj) (hW : ∀ i, proj ⁻¹' tsupport (ρ i) ⊆ W i)
    {η : ∀ i, RoughForm IX (W i) ℝ k} (hη : ∀ i, IsSmoothForm IX 1 (η i)) (x : X)
    {v : Fin (k + 1) → TangentSpace IX x} (hv : ∀ j, v j ∈ (mfderiv IX IB proj x).ker) :
    mextDeriv (ρ.glueForms proj W η) x v =
      ∑ i ∈ (ρ.fintsupport (proj x)).attach, ρ i (proj x) *
        mextDeriv (η i) ⟨x, hW i ((ρ.mem_fintsupport_iff (proj x) i).mp i.property)⟩ v := by
  set S := ρ.fintsupport (proj x)
  let θ : ι → RoughForm IX X ℝ k := fun i y ↦ ρ i (proj y) • extendByZeroOfOpens (η i) y
  have hgerm : ∀ᶠ y in 𝓝 x, ρ.glueForms proj W η y = (∑ i ∈ S, θ i) y := by
    filter_upwards [hproj.continuous.continuousAt.eventually
      (ρ.eventually_finsupport_subset (proj x))] with y hy
    rw [glueForms_apply, Finset.sum_apply]
    refine Finset.sum_subset hy fun i _ hi ↦ ?_
    simp [show ρ i (proj y) = 0 by simpa [ρ.mem_finsupport] using hi]
  rw [mextDeriv_congr_of_eventuallyEq hgerm,
    mextDeriv_sum θ S fun i _ ↦ isSmoothForm_smul_extendByZeroOfOpens hproj hW hη i,
    Finset.sum_apply, ContinuousAlternatingMap.sum_apply, ← Finset.sum_attach S]
  exact Finset.sum_congr rfl fun i _ ↦
    mextDeriv_smul_extendByZeroOfOpens_apply_of_mem_ker hproj hη i _ hv

end SmoothPartitionOfUnity

end
