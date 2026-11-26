/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.PartitionOfUnity
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# The exterior derivative of pullbacks glued by a partition of unity

Let `ρ` be a smooth partition of unity on `M` subordinate to an open cover `U`, read on `X`
through a smooth map `b : X → M`, and let `g i : X → Z` be smooth over `b ⁻¹' U i`. Tau Ceti's
`TauCeti.isSmoothForm_sum_finsupport_smul_mpullback` shows that the glued form
`τ = ∑ᵢ (ρᵢ ∘ b) • (g i)^* φ` is smooth for a smooth form `φ` on `Z`. This file computes its
exterior derivative when `φ` is closed: by the Leibniz rule, and since each `(g i)^* φ` is closed
where it is smooth, only the differentials of the weights contribute,
`dτ = ∑ᵢ d(ρᵢ ∘ b) ∧ (g i)^* φ`, the sum running over the finite set `ρ.fintsupport (b x)`
(`TauCeti.mextDeriv_sum_finsupport_smul_mpullback_apply`). Moreover the differentials of the
weights sum to zero there (`SmoothPartitionOfUnity.sum_fintsupport_mextDeriv_ofFunction_comp`),
because the weights sum to one near `x`. Each term `(ρᵢ ∘ b) • (g i)^* φ` is smooth by
`TauCeti.isSmoothForm_fun_smul_mpullback`.

## Main results

* `TauCeti.mextDeriv_sum_finsupport_smul_mpullback_apply`: the exterior derivative of the glued
  form of a closed form.
* `SmoothPartitionOfUnity.sum_fintsupport_mextDeriv_ofFunction_comp`: the differentials of the
  weights of a partition of unity sum to zero.

The reduction to the fixed finite set `ρ.fintsupport (b x)` near `x` follows the proof of Tau
Ceti's
`SmoothPartitionOfUnity.mvfderiv_finsum_smul_pos`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Exercise 6.3.6.
* [V. Guillemin, E. Lerman and S. Sternberg, *Symplectic Fibrations and Multiplicity
  Diagrams*][GuilleminLermanSternberg1996], Theorem 1.2.5.
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff

variable {EX HX X EZ HZ Z EM HM M F : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
  [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
  {IZ : ModelWithCorners ℝ EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {ι : Type*} {ρ : SmoothPartitionOfUnity ι IM M univ} {b : X → M}

namespace TauCeti

/-- **The exterior derivative of pullbacks of a closed form glued by a partition of unity.** Let
`ρ` be a smooth partition of unity on `M` subordinate to an open cover `U`, read on `X` through a
smooth map `b : X → M`, let each `g i : X → Z` be smooth at every point of `b ⁻¹' U i`, and let
`φ` be a closed smooth real form on `Z`. Then at every `x`, the exterior derivative of the glued
form `∑ᵢ (ρᵢ ∘ b) • (g i)^* φ` is `∑ᵢ d(ρᵢ ∘ b) ∧ (g i)^* φ`, over the indices `i` with `b x` in
the topological support of `ρ i`; the degree `0 + 1 + k` of the wedge is read as `k + 1`. -/
theorem mextDeriv_sum_finsupport_smul_mpullback_apply [IsManifold IX 2 X] [IsManifold IZ 2 Z]
    {U : ι → Set M} (hρ : ρ.IsSubordinate U) (hU : ∀ i, IsOpen (U i)) (hb : ContMDiff IX IM ∞ b)
    {g : ι → X → Z} (hg : ∀ i x, b x ∈ U i → ContMDiffAt IX IZ ∞ (g i) x)
    {φ : RoughForm IZ Z ℝ k} (hφs : IsSmoothForm IZ ∞ φ) (hφ : mextDeriv φ = 0) (x : X)
    (v : Fin (k + 1) → TangentSpace IX x) :
    mextDeriv (fun x ↦ ∑ i ∈ ρ.finsupport (b x), ρ i (b x) • mpullback IX IZ (g i) φ x) x v =
      ∑ i ∈ ρ.fintsupport (b x),
        (mextDeriv (RoughForm.ofFunction IX (ρ i ∘ b))).wedge (mpullback IX IZ (g i) φ) x
          (v ∘ Fin.cast (show 0 + 1 + k = k + 1 by omega)) := by
  set S := ρ.fintsupport (b x)
  let θ : ι → RoughForm IX X ℝ k := fun i y ↦ ρ i (b y) • mpullback IX IZ (g i) φ y
  have hθ : ∀ i ∈ S, IsSmoothForm IX 1 (θ i) := fun i _ ↦
    (isSmoothForm_fun_smul_mpullback ((ρ i).contMDiff.comp hb) ((hU i).preimage hb.continuous)
      ((tsupport_comp_subset_preimage _ hb.continuous).trans (preimage_mono (hρ i)))
      (fun y hy ↦ hg i y hy) (by simp) hφs).of_le (by simp)
  have hgerm : ∀ᶠ y in 𝓝 x,
      ∑ i ∈ ρ.finsupport (b y), ρ i (b y) • mpullback IX IZ (g i) φ y = (∑ i ∈ S, θ i) y := by
    filter_upwards [hb.continuous.continuousAt.eventually
      (ρ.eventually_finsupport_subset (b x))] with y hy
    rw [Finset.sum_apply]
    refine Finset.sum_subset hy fun i _ hi ↦ ?_
    simp [show ρ i (b y) = 0 by simpa [ρ.mem_finsupport] using hi]
  rw [mextDeriv_congr_of_eventuallyEq hgerm, mextDeriv_sum θ S hθ, Finset.sum_apply,
    ContinuousAlternatingMap.sum_apply]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hxU : b x ∈ U i := hρ i ((ρ.mem_fintsupport_iff (b x) i).mp hi)
  have hpull := (hφs.contMDiff (g i x)).mpullback_form (hg i x hxU) (by simp)
  have hclosed : mextDeriv (mpullback IX IZ (g i) φ) x = 0 := by
    rw [← mpullback_mextDeriv_at ((hg i x hxU).of_le (by simp))
      ((hφs.contMDiff (g i x)).of_le (by simp)), hφ, mpullback_zero, Pi.zero_apply]
  -- `θ i` is the pointwise product `(ρ i ∘ b) • (g i)^* φ` of the Leibniz rule.
  have hleib : mextDeriv (θ i) x v = _ := mextDeriv_fun_smul (f := ρ i ∘ b)
    (((ρ i).contMDiff.comp hb).mdifferentiableAt (by simp)) (hpull.mdifferentiableAt (by simp)) v
  rw [hleib, hclosed, ContinuousAlternatingMap.coe_zero, Pi.zero_apply, mul_zero, add_zero]

end TauCeti

namespace SmoothPartitionOfUnity

open TauCeti

/-- **The differentials of the weights of a partition of unity sum to zero.** For a smooth
partition of unity `ρ` on `M` and a `C¹` map `b : X → M`, the differentials of the functions
`ρ i ∘ b`, over the indices `i` with `b x` in the topological support of `ρ i`, sum to zero
at `x`. -/
theorem sum_fintsupport_mextDeriv_ofFunction_comp [IsManifold IX 1 X] (hb : ContMDiff IX IM 1 b)
    (x : X) :
    ∑ i ∈ ρ.fintsupport (b x), mextDeriv (RoughForm.ofFunction IX (ρ i ∘ b)) x = 0 := by
  have hsmooth : ∀ i ∈ ρ.fintsupport (b x), IsSmoothForm IX 1 (RoughForm.ofFunction IX (ρ i ∘ b)) :=
    fun i _ ↦ isSmoothForm_ofFunction_iff.mpr (((ρ i).contMDiff.of_le (by simp)).comp hb)
  have hsum : ∑ i ∈ ρ.fintsupport (b x), RoughForm.ofFunction IX (ρ i ∘ b) =
      RoughForm.ofFunction IX (∑ i ∈ ρ.fintsupport (b x), ρ i ∘ b) := by
    funext y
    ext v
    simp [Finset.sum_apply]
  have hone : ∀ᶠ y in 𝓝 x, (∑ i ∈ ρ.fintsupport (b x), ρ i ∘ b) y = (0 : X → ℝ) y + 1 := by
    filter_upwards [hb.continuous.continuousAt.eventually
      (ρ.eventually_finsupport_subset (b x))] with y hy
    simpa [Finset.sum_apply] using ρ.sum_finsupport' (x₀ := b y) (mem_univ _) hy
  rw [← Finset.sum_apply, ← mextDeriv_sum _ _ hsmooth, hsum,
    mextDeriv_ofFunction_eq_of_eventuallyEq_add_const hone, mextDeriv_ofFunction_zero,
    Pi.zero_apply]

end SmoothPartitionOfUnity

end
