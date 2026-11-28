/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Semibasic

/-!
# Gluing forms on open sets with a partition of unity of a base

Let `proj : X → B` be a smooth map and `ρ` a smooth partition of unity on a set `s` of `B`.
Given, for each `i`, an open set `W i` of `X` containing the preimage of the topological support
of `ρ i` (for instance `proj ⁻¹' U i`, when `ρ` is subordinate to an open cover `U`) and a form
`η i` on `W i`, the glued form `ρ.glueForms proj W η` is `∑ᵢ (ρ i ∘ proj) • η i`, each term
extended by zero off `W i`; at each point only the finitely many indices of
`ρ.finsupport (proj x)` contribute.

The smoothness and the exterior derivative of such a sum are first proved for any family of forms
`θ i` on `X` weighted by `ρ i ∘ b`; the glued forms here, and the glued pullbacks of
`Pullback/PartitionOfUnity.lean`, are cases of it.

## Main results

* `SmoothPartitionOfUnity.isSmoothForm_sum_finsupport_smul`: for forms `θ i` on `X` and a
  continuous `b : X → B`, the form `y ↦ ∑ i ∈ ρ.finsupport (b y), ρ i (b y) • θ i y` is `C^n`
  when each term `(ρ i ∘ b) • θ i` is.
* `SmoothPartitionOfUnity.mextDeriv_sum_finsupport_smul`: its exterior derivative at `x` is the
  sum of those of the terms over the finite set `ρ.fintsupport (b x)`, when these terms are `C^1`.
* `SmoothPartitionOfUnity.isSmoothForm_glueForms`: the glued form of `C^n` forms is `C^n`.
* `SmoothPartitionOfUnity.mextDeriv_glueForms_apply_of_mem_ker`: on tangent vectors in the kernel
  of the differential of `proj`, the exterior derivative of the glued form is
  `∑ᵢ ρ i (proj x) * dη i`. By the Leibniz rule, `d((ρ i ∘ proj) • η i)` is
  `d(ρ i ∘ proj) ∧ η i + (ρ i ∘ proj) • dη i`, and `d(ρ i ∘ proj)` vanishes on such vectors,
  being semibasic for `proj` (`TauCeti.RoughForm.mextDeriv_fun_smul_comp_apply_of_mem_ker`).

Each `η i` is extended to `X` by `TauCeti.RoughForm.extendByZeroOfOpens`. The proof of
`SmoothPartitionOfUnity.isSmoothForm_sum_finsupport_smul` is that of Tau Ceti's
`TauCeti.isSmoothForm_sum_finsupport_smul_mpullback`, for any family of terms in place of pullbacks
of one form. That of `SmoothPartitionOfUnity.mextDeriv_sum_finsupport_smul`, which reduces the
locally finite sum to the finite set `ρ.fintsupport (b x)` near `x`, follows the proof of Tau
Ceti's `SmoothPartitionOfUnity.mvfderiv_finsum_smul_pos`.

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

variable {ι : Type*} {s : Set B}

section Sum

variable {ρ : SmoothPartitionOfUnity ι IB B s} {b : X → B} {θ : ι → RoughForm IX X F k}

/-- **A locally finite sum of forms weighted by a partition of unity is smooth.** Let `ρ` be a
smooth partition of unity on `s ⊆ B`, read on `X` through a continuous map `b : X → B`, and `θ i`
forms on `X` such that each `(ρ i ∘ b) • θ i` is `C^n`. Then the form
`y ↦ ∑ i ∈ ρ.finsupport (b y), ρ i (b y) • θ i y` is `C^n`. -/
theorem isSmoothForm_sum_finsupport_smul [IsManifold IX 1 X] {n : WithTop ℕ∞}
    (hb : Continuous b) (hθ : ∀ i, IsSmoothForm IX n (fun y ↦ ρ i (b y) • θ i y)) :
    IsSmoothForm IX n (fun y ↦ ∑ i ∈ ρ.finsupport (b y), ρ i (b y) • θ i y) := by
  rw [isSmoothForm_def]
  simp_rw [fun y ↦ ρ.sum_finsupport_smul_eq_finsum (x₀ := b y) (φ := fun i _ ↦ θ i y)]
  refine ContMDiff.finsum_section_of_locallyFinite
    (t := fun i y ↦ ρ i (b y) • θ i y) ?_ fun i ↦ (hθ i).contMDiff
  exact (ρ.locallyFinite.preimage_continuous hb).subset fun i x hx ↦ left_ne_zero_of_smul hx

/-- **The exterior derivative of a sum of forms weighted by a partition of unity.** Let `ρ` be a
smooth partition of unity on `s ⊆ B`, read on `X` through a map `b : X → B` continuous at
`x : X`, and `θ i` forms on `X`. If `(ρ i ∘ b) • θ i` is `C^1` for each index `i` with `b x` in
the topological support of `ρ i`, then the exterior derivative of
`y ↦ ∑ i ∈ ρ.finsupport (b y), ρ i (b y) • θ i y` at `x` is the sum of those of the
`(ρ i ∘ b) • θ i` over these indices. -/
theorem mextDeriv_sum_finsupport_smul [IsManifold IX 1 X] {x : X} (hb : ContinuousAt b x)
    (hθ : ∀ i ∈ ρ.fintsupport (b x), IsSmoothForm IX 1 (fun y ↦ ρ i (b y) • θ i y)) :
    mextDeriv (fun y ↦ ∑ i ∈ ρ.finsupport (b y), ρ i (b y) • θ i y) x =
      ∑ i ∈ ρ.fintsupport (b x), mextDeriv (fun y ↦ ρ i (b y) • θ i y) x := by
  have hgerm : ∀ᶠ y in 𝓝 x, ∑ i ∈ ρ.finsupport (b y), ρ i (b y) • θ i y =
      (∑ i ∈ ρ.fintsupport (b x), fun y ↦ ρ i (b y) • θ i y) y := by
    filter_upwards [hb.eventually (ρ.eventually_finsupport_subset (b x))] with y hy
    rw [Finset.sum_apply]
    refine Finset.sum_subset hy fun i _ hi ↦ ?_
    simp [show ρ i (b y) = 0 by simpa [ρ.mem_finsupport] using hi]
  rw [mextDeriv_congr_of_eventuallyEq hgerm, mextDeriv_sum _ _ hθ, Finset.sum_apply]

end Sum

variable (ρ : SmoothPartitionOfUnity ι IB B s) (proj : X → B) (W : ι → Opens X)

/-- **Gluing forms on open sets with a partition of unity of a base.** For a partition of unity
`ρ` on a set `s` of `B`, a map `proj : X → B`, and forms `η i` on open sets `W i` of `X`, the
form `∑ᵢ (ρ i ∘ proj) • η i` on `X`, where each `η i` is extended by zero off `W i`. The sum at
`x` runs over the finite set `ρ.finsupport (proj x)` of indices whose weight does not vanish at
`proj x`. -/
noncomputable def glueForms (η : ∀ i, RoughForm IX (W i) F k) : RoughForm IX X F k :=
  fun x ↦ ∑ i ∈ ρ.finsupport (proj x), ρ i (proj x) • extendByZeroOfOpens (η i) x

/-- The value of the glued form `ρ.glueForms proj W η` at a point. -/
theorem glueForms_apply (η : ∀ i, RoughForm IX (W i) F k) (x : X) :
    ρ.glueForms proj W η x =
      ∑ i ∈ ρ.finsupport (proj x), ρ i (proj x) • extendByZeroOfOpens (η i) x :=
  (rfl)

variable {ρ proj W}

/-- **One term of the glued form is smooth.** For a `C^n` map `proj : X → B` and a `C^n` form
`η i` on an open set `W i` of `X` that contains the preimage of the topological support of `ρ i`,
the form `(ρ i ∘ proj) • η i`, with `η i` extended by zero off `W i`, is `C^n` on `X`. -/
theorem isSmoothForm_smul_extendByZeroOfOpens [IsManifold IX 1 X] {n : ℕ∞}
    (hproj : ContMDiff IX IB n proj) (hW : ∀ i, proj ⁻¹' tsupport (ρ i) ⊆ W i)
    {η : ∀ i, RoughForm IX (W i) F k} (hη : ∀ i, IsSmoothForm IX n (η i)) (i : ι) :
    IsSmoothForm IX n (fun y ↦ ρ i (proj y) • extendByZeroOfOpens (η i) y) :=
  (hη i).fun_smul_extendByZeroOfOpens (f := ρ i ∘ proj)
    (((ρ i).contMDiff.of_le (by exact_mod_cast le_top)).comp hproj)
    ((tsupport_comp_subset_preimage _ hproj.continuous).trans (hW i))

/-- **The glued form is smooth.** Let `ρ` be a smooth partition of unity on `s ⊆ B`,
`proj : X → B` a `C^n` map, and `η i` a `C^n` form on an open set `W i` of `X` that contains the
preimage of the topological support of `ρ i`. Then `ρ.glueForms proj W η` is a `C^n` form on `X`. -/
theorem isSmoothForm_glueForms [IsManifold IX 1 X] {n : ℕ∞} (hproj : ContMDiff IX IB n proj)
    (hW : ∀ i, proj ⁻¹' tsupport (ρ i) ⊆ W i) {η : ∀ i, RoughForm IX (W i) F k}
    (hη : ∀ i, IsSmoothForm IX n (η i)) : IsSmoothForm IX n (ρ.glueForms proj W η) :=
  isSmoothForm_sum_finsupport_smul hproj.continuous
    (isSmoothForm_smul_extendByZeroOfOpens hproj hW hη)

/-- **The derivative of the glued form on vertical vectors.** Let `ρ` be a smooth partition of
unity on `s ⊆ B`, `proj : X → B` a `C^1` map, and `η i` a `C^1` real form on an open set `W i` of
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
  rw [show ρ.glueForms proj W η = _ from funext (glueForms_apply ρ proj W η),
    mextDeriv_sum_finsupport_smul hproj.continuous.continuousAt fun i _ ↦
      isSmoothForm_smul_extendByZeroOfOpens hproj hW hη i,
    ContinuousAlternatingMap.sum_apply, ← Finset.sum_attach]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hx : x ∈ W i := hW i ((ρ.mem_fintsupport_iff (proj x) i).mp i.property)
  have hμ := ((contMDiffAt_mpullback_subtypeVal_iff (extendByZeroOfOpens (η i)) ⟨x, hx⟩).1
    (by rw [mpullback_subtypeVal_extendByZeroOfOpens]; exact (hη i).contMDiff _))
      |>.mdifferentiableAt (by simp)
  rw [mextDeriv_fun_smul_comp_apply_of_mem_ker ((ρ i).contMDiff.mdifferentiableAt (by simp))
    (hproj.mdifferentiableAt (by simp)) hμ hv, mextDeriv_extendByZeroOfOpens_coe (η i) ⟨x, hx⟩]
  -- Both sides apply the same form to `v`, read in `TangentSpace IX x` and in the tangent space
  -- of `W i` at `x`, which are the same model space.
  rfl

end SmoothPartitionOfUnity

end
