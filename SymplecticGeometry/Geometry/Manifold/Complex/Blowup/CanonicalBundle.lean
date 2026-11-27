/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Chart.Basic
public import SymplecticGeometry.Geometry.Manifold.Complex.Hypersurface.LineBundle
public import TauCeti.Analysis.Normed.Module.Alternating.TopDegree
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Canonical
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle
public import TauCeti.Topology.Algebra.Module.FiniteDimension

import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Chart.Change
import SymplecticGeometry.Geometry.Manifold.Projectivization.TwistCore
import SymplecticGeometry.Analysis.Normed.Module.Alternating.TopDegree
import SymplecticGeometry.Topology.Algebra.Module.TensorProduct
import TauCeti.LinearAlgebra.TensorProduct.Separation
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.TensorProduct
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Canonical
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hom
import SymplecticGeometry.Analysis.Normed.Module.TensorProduct.ProjectiveSeminorm
import SymplecticGeometry.Topology.VectorBundle.Pullback

/-!
# The canonical bundle of the blowup

Let `M` be a complex manifold modelled on `E = ℂⁿ⁺¹` and `c` a chart of its holomorphic atlas at
`p₀` with `c p₀ = 0`. This file gives local equations of the exceptional divisor of
`SymplecticGeometry.Blowup c`, as data `SymplecticGeometry.HypersurfaceData` indexed by
`Option (Fin (n + 1))`:

* the index `none` is the complement of the divisor, `Blowup.offDivisorOpens c`, with local
  equation `1`;
* the index `some i` is the domain of the chart `blowupModelChart i ∘ Blowup.lift c`, inside the
  image of the model, with local equation the coordinate `w i` of that chart, which is the
  coordinate `i` of the point of `E` under the point of the model.

The transition functions are `w i` from `some i` to `none` and its inverse from `none` to
`some i`. From `some i` to `some j` the transition is the ratio `v i / v j` of homogeneous
coordinates `v` of the line of the point of the model; off the divisor it is the ratio
`z i / z j` of the coordinates of the point `z` of `E` below. It is Tau Ceti's
`Projectivization.twistTransition (-1) j i`, the transition function of the tautological
bundle `𝒪(-1)`.

For a holomorphic chart `φ` of `M` at `p₀` and the blowdown `π : Blowup c → M`, the file also
computes the pull-back by `π` of the coordinate form of `φ`. For a chart `e` of a manifold
modelled on `E` and a basis `b` of `E`, the coordinate form `dz₁ ∧ ⋯ ∧ dzₙ₊₁` of `e` at `x` is the
determinant form `b.continuousDet` pulled back by the differential of `e` at `x`; for the chart
`chartAt E x₀` this is Tau Ceti's `TauCeti.CanonicalBundle.coordForm`
(`TauCeti.CanonicalBundle.coordForm_eq_compContinuousLinearMap_mfderiv`).

It computes this in the chart `liftChart c φ` followed by `blowupModelChart i` of the blowup.
In that chart, `φ ∘ π` is the blowdown of the model read in the chart `i`,
`w ↦ (z i = w i, z j = w i * w j for j ≠ i)`, whose Jacobian determinant is `(w i) ^ n`
(`SymplecticGeometry.BlowupModel.det_fderiv_blowdown_blowupModelChart_symm`). So the pull-back
is `(w i) ^ n` times the coordinate form of the chart
(`SymplecticGeometry.Blowup.coordForm_blowdown`).
For `φ = c`, the lifted chart is `Blowup.lift c` over the source of `c`
(`SymplecticGeometry.Blowup.liftChart_self`), so the chart is `blowupModelChart i ∘ lift c`.

The Jacobian of a chart change of the model is computed from that of the blowdown: the chart
change intertwines the blowdowns read in the two charts, which gives the determinant where
`w i ≠ 0`, and continuity extends it to the whole source of the chart change.

Finally the file defines the isomorphism `K ≅ π^*K_M ⊗ 𝒪(nE)` of canonical bundles fibre by
fibre. Since the pull-back of a form by the blowdown vanishes on the exceptional divisor for
`n > 0`, it is not defined as that pull-back, but chart by chart: at `z`, in the preferred chart
of `hypersurfaceData c`, its inverse sends `σ ⊗ a` to `a` times `σ` pulled back by the
differential of the blowdown (chart `none`), or by that of the chart `blowupModelChart i ∘ lift c`
followed by the inverse of that of `c` (chart `some i`). The Jacobians above show that these
maps differ, from one chart to another, exactly by the transition functions of `𝒪(nE)`, so that
the value in every chart containing `z` is the same.

The file then gives holomorphic local frames of `π^*K_M ⊗ 𝒪(nE)`, the source of the inverse of
`canonicalBundleEquiv`: for a chart `e` of the maximal atlas of `M` and an index `j`, the
coordinate form of `e` at `π z` tensored with the element of coordinate `1` in the chart `j` of
`𝒪(nE)`. It is holomorphic over the chart `j` and the source of `e`, as a tensor product
(Tau Ceti's `ContMDiffOn.tmul_section`) of the pull-back by `π` of a holomorphic form and of a
section with constant coordinate, and nowhere zero there, as a tensor product of nonzero
vectors. For `j = some i` one takes `e = c`, the frame of `canonicalBundleEquiv_symm_tmul_some`;
off the divisor, `j = none` and `e = chartAt _ (π z₀)` give a frame near each point `z₀`, the
one of `canonicalBundleEquiv_symm_tmul_none`.

These frames show that `canonicalBundleEquiv` is holomorphic on total spaces. Since the fibres
are lines, a fibrewise linear map out of `π^*K_M ⊗ 𝒪(nE)` is holomorphic near a point once it
sends one nowhere zero holomorphic local section to a holomorphic one
(`ContMDiffOn.bundleMap_of_finrank_eq_one`). The inverse sends the frame on
the chart `some i` to the coordinate form of `blowupModelChart i ∘ lift c`, and the frame built
from `e` off the divisor to the coordinate form of `e ∘ π`; both are holomorphic. The forward
direction follows by Tau Ceti's `TauCeti.contMDiff_bundle_symm`.

## Main definitions

* `SymplecticGeometry.Blowup.hypersurfaceData c`: the local equations of the exceptional divisor.
  Its cover, local equations and transition functions are given by `hypersurfaceData_U_none`,
  `hypersurfaceData_U_some`, `hypersurfaceData_f_none`, `hypersurfaceData_f_some` and the lemmas
  `hypersurfaceData_g_*`.
* `SymplecticGeometry.Blowup.canonicalBundleEquiv c z`: the fibrewise isomorphism of the
  canonical bundle of the blowup with `π^*K_M ⊗ 𝒪(nE)`.

## Main results

* `SymplecticGeometry.Blowup.support_hypersurfaceData`: the common zero set of the local
  equations is the exceptional divisor `Blowup.exceptionalDivisor c`.
* `SymplecticGeometry.BlowupModel.hasFDerivAt_blowdown_blowupModelChart_symm`: the derivative of
  the blowdown of the model read in the chart `i`.
* `SymplecticGeometry.BlowupModel.det_fderiv_blowdown_blowupModelChart_symm`: its Jacobian
  determinant is `(w i) ^ n`.
* `SymplecticGeometry.Blowup.coordForm_blowdown`: the pull-back by the blowdown of the coordinate
  form of `φ` is `(w i) ^ n` times the coordinate form of the chart `i` of the blowup.
* `SymplecticGeometry.BlowupModel.det_fderiv_blowupModelChart_symm_trans`: the change from the
  chart `i` to the chart `k` of the model has Jacobian determinant `(update w i 1 k ^ n)⁻¹`.
* `SymplecticGeometry.Blowup.coordForm_liftChart_trans_blowupModelChart`: so the coordinate forms
  of the charts `i` and `k` of the blowup differ by the factor `g⁻ⁿ`, with `g` the transition
  function `(hypersurfaceData c).g (some k) (some i)`. Unlike `coordForm_blowdown`, this
  compares the two coordinate forms on the exceptional divisor too.
* `SymplecticGeometry.Blowup.canonicalBundleEquiv_symm_tmul_none` and
  `SymplecticGeometry.Blowup.canonicalBundleEquiv_symm_tmul_some`: the inverse of
  `canonicalBundleEquiv` in the charts `none` and `some i`, at every point of these charts.
  `SymplecticGeometry.Blowup.canonicalBundleEquiv_symm_continuousDet_mfderiv_tmul_none` evaluates
  the first on the frame built from a holomorphic chart `e` of `M`: it gives the coordinate form
  of `e ∘ π`.
* `SymplecticGeometry.Blowup.contMDiffOn_continuousDet_mfderiv_tmul_localTriv_symm` and
  `SymplecticGeometry.Blowup.continuousDet_mfderiv_tmul_localTriv_symm_ne_zero`: the local frames
  of `π^*K_M ⊗ 𝒪(nE)` are holomorphic and nowhere zero; the `_some` forms do this for the frame on
  the chart `some i` built from `c`.
* `SymplecticGeometry.Blowup.contMDiff_canonicalBundleEquiv` and
  `SymplecticGeometry.Blowup.contMDiff_canonicalBundleEquiv_symm`: `canonicalBundleEquiv` is
  holomorphic on total spaces in both directions.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 1,
  §4 (the exceptional divisor of the blowup of a point and its local equations).
* [C. Schnell, lecture notes on complex manifolds][Schnell2024], Lemma 23.5.
-/

public noncomputable section

open Function Module Set Projectivization
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace SymplecticGeometry

variable {n : ℕ}

namespace BlowupModel

/-- The blowdown of the model read in the chart `i`, `w ↦ w i • update w i 1`, has at `w` the
derivative `v ↦ w i • update v i 0 + v i • update w i 1`. -/
theorem hasFDerivAt_blowdown_blowupModelChart_symm (i : Fin (n + 1)) (w : Fin (n + 1) → ℂ) :
    HasFDerivAt (fun w ↦ ((blowupModelChart i).symm w).blowdown)
      (w i • (ContinuousLinearMap.id ℂ (Fin (n + 1) → ℂ) -
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) i).smulRight
            (Pi.single i 1)) +
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) i).smulRight
          (update w i 1)) w := by
  set A := ContinuousLinearMap.id ℂ (Fin (n + 1) → ℂ) -
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) i).smulRight (Pi.single i 1)
  have hA : (fun w : Fin (n + 1) → ℂ ↦ update w i 1) = fun w ↦ A w + Pi.single i 1 := by
    ext w j
    by_cases h : j = i
    · subst h; simp [A]
    · simp [A, h]
  have hg : HasFDerivAt (fun w : Fin (n + 1) → ℂ ↦ update w i 1) A w :=
    hA ▸ (A.hasFDerivAt).add_const _
  simp_rw [blowdown_blowupModelChart_symm_apply]
  exact (hasFDerivAt_apply i w).smul hg

/-- **The Jacobian of the blowdown in a chart.** In the chart `i` of the model, the blowdown is
`w ↦ (z i = w i, z j = w i * w j for j ≠ i)`, and its Jacobian determinant is `(w i) ^ n`. -/
theorem det_fderiv_blowdown_blowupModelChart_symm (i : Fin (n + 1)) (w : Fin (n + 1) → ℂ) :
    LinearMap.det (fderiv ℂ (fun w ↦ ((blowupModelChart i).symm w).blowdown) w :
      (Fin (n + 1) → ℂ) →ₗ[ℂ] Fin (n + 1) → ℂ) = w i ^ n := by
  rw [(hasFDerivAt_blowdown_blowupModelChart_symm i w).fderiv, ← LinearMap.det_toMatrix',
    Matrix.det_succ_row _ i, Finset.sum_eq_single i (fun j _ hj ↦ by
      simp [LinearMap.toMatrix'_apply, hj]) (by simp)]
  have : (LinearMap.toMatrix' (((w i • (ContinuousLinearMap.id ℂ (Fin (n + 1) → ℂ) -
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) i).smulRight
            (Pi.single i 1)) +
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) i).smulRight
          (update w i 1)) : (Fin (n + 1) → ℂ) →L[ℂ] _) : (Fin (n + 1) → ℂ) →ₗ[ℂ] _)).submatrix
        i.succAbove i.succAbove = w i • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [LinearMap.toMatrix'_apply, Fin.succAbove_ne]
    · simp [LinearMap.toMatrix'_apply, Fin.succAbove_ne, hab]
  rw [this]
  simp [LinearMap.toMatrix'_apply]

/-- Where also the coordinate `i` does not vanish, the Jacobian of the chart change follows from
that of the blowdown, which the chart change intertwines. -/
private theorem det_fderiv_blowupModelChart_symm_trans_of_ne_zero (i k : Fin (n + 1))
    {w : Fin (n + 1) → ℂ} (hw : update w i 1 k ≠ 0) (hi : w i ≠ 0) :
    LinearMap.det (fderiv ℂ ((blowupModelChart i).symm.trans (blowupModelChart k)) w :
      (Fin (n + 1) → ℂ) →ₗ[ℂ] Fin (n + 1) → ℂ) = (update w i 1 k ^ n)⁻¹ := by
  set T := (blowupModelChart i).symm.trans (blowupModelChart k)
  have hS : T.source ∈ nhds w :=
    T.open_source.mem_nhds (by rw [blowupModelChart_symm_trans_source]; exact hw)
  have hT : DifferentiableAt ℂ T w :=
    ((contDiffOn_blowupModelChart_symm_trans i k 1).differentiableOn one_ne_zero).differentiableAt
      hS
  have heq : (fun w ↦ ((blowupModelChart i).symm w).blowdown) =ᶠ[nhds w]
      (fun w ↦ ((blowupModelChart k).symm w).blowdown) ∘ T := by
    filter_upwards [hS] with w' hw'
    rw [OpenPartialHomeomorph.trans_source] at hw'
    simp only [comp_apply, T, OpenPartialHomeomorph.coe_trans,
      (blowupModelChart k).left_inv hw'.2]
  have h := (((hasFDerivAt_blowdown_blowupModelChart_symm k (T w)).comp w
    hT.hasFDerivAt).congr_of_eventuallyEq heq).fderiv
  have hdet := det_fderiv_blowdown_blowupModelChart_symm i w
  rw [h, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
    ← (hasFDerivAt_blowdown_blowupModelChart_symm k (T w)).fderiv,
    det_fderiv_blowdown_blowupModelChart_symm, blowupModelChart_symm_trans_apply_self,
    mul_pow, mul_assoc] at hdet
  refine eq_inv_of_mul_eq_one_right (mul_left_cancel₀ (pow_ne_zero n hi) ?_)
  rw [mul_one]
  exact hdet

/-- **The Jacobian of the chart changes of the model.** On its source, where
`update w i 1 k ≠ 0`, the change from the chart `i` to the chart `k` of the model has Jacobian
determinant `(update w i 1 k ^ n)⁻¹`: it is `1` for `k = i` and `(w k ^ n)⁻¹` for `k ≠ i`. -/
theorem det_fderiv_blowupModelChart_symm_trans (i k : Fin (n + 1)) {w : Fin (n + 1) → ℂ}
    (hw : update w i 1 k ≠ 0) :
    LinearMap.det (fderiv ℂ ((blowupModelChart i).symm.trans (blowupModelChart k)) w :
      (Fin (n + 1) → ℂ) →ₗ[ℂ] Fin (n + 1) → ℂ) = (update w i 1 k ^ n)⁻¹ := by
  set T := (blowupModelChart i).symm.trans (blowupModelChart k)
  -- Moving the coordinate `i` keeps the point in the source and the right side unchanged, and
  -- where `w i ≠ 0` the identity holds; it extends to `w i = 0` by continuity.
  have hcont : ContinuousOn (fun w ↦ LinearMap.det (fderiv ℂ T w :
      (Fin (n + 1) → ℂ) →ₗ[ℂ] Fin (n + 1) → ℂ)) T.source :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      ((contDiffOn_blowupModelChart_symm_trans i k 1).continuousOn_fderiv_of_isOpen
        T.open_source le_rfl)
  have hline : Continuous fun t : ℂ ↦ LinearMap.det (fderiv ℂ T (update w i t) :
      (Fin (n + 1) → ℂ) →ₗ[ℂ] Fin (n + 1) → ℂ) :=
    hcont.comp_continuous (continuous_const.update i continuous_id) fun t ↦ by
      rw [blowupModelChart_symm_trans_source]
      simpa using hw
  have key := hline.ext_on (dense_compl_singleton 0) continuous_const fun t ht ↦ by
    exact (det_fderiv_blowupModelChart_symm_trans_of_ne_zero i k (w := update w i t)
      (by simpa using hw) (by simpa using ht)).trans (by rw [update_idem])
  simpa using congrFun key (w i)

end BlowupModel

namespace Blowup

open BlowupModel

section HypersurfaceData

open GluedAlong (inr)

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M] {p₀ : M}
  (c : BlowupChart (n := n) M p₀)

/-! ### The cover, the local equations and the transition functions -/

/-- The open sets of the cover: the complement of the divisor, and the domains of the charts
`blowupModelChart i ∘ lift c` in the image of the model. -/
private def divisorU : Option (Fin (n + 1)) → Set (Blowup c)
  | none => offDivisorOpens c
  | some i => range (inr (gluingHomeomorph c)) ∩ lift c ⁻¹' (blowupModelChart i).source

/-- The local equations: `1` off the divisor, and the coordinate `i` of the point of `E` below in
the chart `i`. -/
private def divisorF : Option (Fin (n + 1)) → Blowup c → ℂ
  | none => fun _ ↦ 1
  | some i => fun z ↦ (lift c z).blowdown i

/-- The transition functions of the local equations. -/
private def divisorG : Option (Fin (n + 1)) → Option (Fin (n + 1)) → Blowup c → ℂ
  | none, none => fun _ ↦ 1
  | none, some i => fun z ↦ ((lift c z).blowdown i)⁻¹
  | some i, none => fun z ↦ (lift c z).blowdown i
  | some i, some j => fun z ↦ twistTransition (-1) j i (lift c z).pr

open scoped Classical in
/-- The preferred chart at a point: `none` off the divisor, and a chart of the line on it. -/
private def divisorIndexAt (z : Blowup c) : Option (Fin (n + 1)) :=
  if z ∈ exceptionalDivisor c then some (exists_mem_affineOpen (lift c z).pr).choose else none

private theorem divisorF_some_apply (i : Fin (n + 1)) (z : Blowup c) :
    divisorF c (some i) z = (lift c z).blowdown i :=
  (rfl)

/-- In the chart `i`, a point is on the divisor exactly when its local equation vanishes. -/
private theorem divisorF_some_eq_zero_iff {i : Fin (n + 1)} {z : Blowup c}
    (hz : z ∈ divisorU c (some i)) :
    divisorF c (some i) z = 0 ↔ z ∈ exceptionalDivisor c := by
  obtain ⟨⟨y, rfl⟩, hy⟩ := hz
  rw [mem_preimage, lift_inr] at hy
  rw [divisorF_some_apply, lift_inr, blowdown_apply_eq_zero_iff i hy,
    inr_mem_exceptionalDivisor_iff]

private theorem divisorF_some_ne_zero {i : Fin (n + 1)} {z : Blowup c}
    (hi : z ∈ divisorU c (some i)) (h : z ∈ divisorU c none) : divisorF c (some i) z ≠ 0 :=
  fun h0 ↦ (mem_offDivisorOpens c).1 h ((divisorF_some_eq_zero_iff c hi).1 h0)

private theorem mem_affineOpen_of_mem_divisorU {i : Fin (n + 1)} {z : Blowup c}
    (hz : z ∈ divisorU c (some i)) : (lift c z).pr ∈ affineOpen i := by
  simpa using hz.2

/-- The local equations of the charts `i` and `j` differ by the ratio of the homogeneous
coordinates `i` and `j` of the line. -/
private theorem divisorF_some_eq_mul {i j : Fin (n + 1)} {z : Blowup c}
    (hj : z ∈ divisorU c (some j)) :
    divisorF c (some i) z = twistTransition (-1) j i (lift c z).pr * divisorF c (some j) z :=
  (twistTransition_neg_one_mul i (mem_affineOpen_of_mem_divisorU c hj)
    (lift c z).blowdown_mem_submodule).symm


private theorem mem_divisorU_divisorIndexAt (z : Blowup c) :
    z ∈ divisorU c (divisorIndexAt c z) := by
  by_cases hz : z ∈ exceptionalDivisor c
  · simp only [divisorIndexAt, hz, ite_true]
    have hr : z ∈ range (inr (gluingHomeomorph c)) := by
      rw [range_inr]
      exact Or.inl hz
    refine ⟨hr, ?_⟩
    rw [mem_preimage, blowupModelChart_source, mem_preimage]
    exact (exists_mem_affineOpen (lift c z).pr).choose_spec
  · simp only [divisorIndexAt, hz, ite_false]
    exact (mem_offDivisorOpens c).2 hz


private theorem divisorF_eq_divisorG_mul {i j : Option (Fin (n + 1))} {z : Blowup c}
    (hi : z ∈ divisorU c i) (hj : z ∈ divisorU c j) :
    divisorF c i z = divisorG c i j z * divisorF c j z := by
  cases i with
  | none =>
    cases j with
    | none => simp [divisorF, divisorG]
    | some j =>
      exact (inv_mul_cancel₀ (divisorF_some_ne_zero c hj hi)).symm
  | some i =>
    cases j with
    | none => simp [divisorF, divisorG]
    | some j => exact divisorF_some_eq_mul c hj

private theorem divisorG_ne_zero {i j : Option (Fin (n + 1))} {z : Blowup c}
    (hi : z ∈ divisorU c i) (hj : z ∈ divisorU c j) : divisorG c i j z ≠ 0 := by
  cases i with
  | none =>
    cases j with
    | none => exact one_ne_zero
    | some j => exact inv_ne_zero (divisorF_some_ne_zero c hj hi)
  | some i =>
    cases j with
    | none => exact divisorF_some_ne_zero c hi hj
    | some j =>
      exact twistTransition_ne_zero (-1) (mem_affineOpen_of_mem_divisorU c hj)
        (mem_affineOpen_of_mem_divisorU c hi)

private theorem divisorG_mul_divisorG {i j k : Option (Fin (n + 1))} {z : Blowup c}
    (hi : z ∈ divisorU c i) (hj : z ∈ divisorU c j) (hk : z ∈ divisorU c k) :
    divisorG c i j z * divisorG c j k z = divisorG c i k z := by
  by_cases h0 : z ∈ divisorU c none
  · -- Off the divisor every local equation is nonzero, and the transition functions are their
    -- ratios.
    have hne {a : Option (Fin (n + 1))} (ha : z ∈ divisorU c a) : divisorF c a z ≠ 0 := by
      cases a with
      | none => exact one_ne_zero
      | some a => exact divisorF_some_ne_zero c ha h0
    have hdiv {a b : Option (Fin (n + 1))} (ha : z ∈ divisorU c a) (hb : z ∈ divisorU c b) :
        divisorG c a b z = divisorF c a z / divisorF c b z :=
      eq_div_of_mul_eq (hne hb) (divisorF_eq_divisorG_mul c ha hb).symm
    rw [hdiv hi hj, hdiv hj hk, hdiv hi hk, div_mul_div_cancel₀ (hne hj)]
  · -- On the divisor all three charts are charts of the model.
    cases i with
    | none => exact absurd hi h0
    | some i =>
      cases j with
      | none => exact absurd hj h0
      | some j =>
        cases k with
        | none => exact absurd hk h0
        | some k =>
          exact twistTransition_mul_twistTransition (-1) k i
            (mem_affineOpen_of_mem_divisorU c hj)

variable [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]
  [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]

private theorem isOpen_divisorU (i : Option (Fin (n + 1))) : IsOpen (divisorU c i) := by
  cases i with
  | none => exact (offDivisorOpens c).isOpen
  | some i =>
    exact (contMDiffOn_lift c).continuousOn.isOpen_inter_preimage
      (GluedAlong.isOpen_range_inr _) (blowupModelChart i).open_source

private theorem contMDiffOn_divisorF_some (i : Fin (n + 1)) :
    ContMDiffOn 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ) ω (divisorF c (some i))
      (range (inr (gluingHomeomorph c))) :=
  ((contDiff_apply ℂ (fun _ ↦ ℂ) i).contMDiff.comp
    (BlowupModel.contMDiff_blowdown ω)).comp_contMDiffOn (contMDiffOn_lift c)

private theorem contMDiffOn_divisorF (i : Option (Fin (n + 1))) :
    ContMDiffOn 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ) ω (divisorF c i) (divisorU c i) := by
  cases i with
  | none => exact contMDiffOn_const
  | some i => exact (contMDiffOn_divisorF_some c i).mono fun _ hz ↦ hz.1

private theorem contMDiffOn_divisorG (i j : Option (Fin (n + 1))) :
    ContMDiffOn 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ) ω (divisorG c i j) (divisorU c i ∩ divisorU c j) := by
  cases i with
  | none =>
    cases j with
    | none => exact contMDiffOn_const
    | some j =>
      exact ContMDiffOn.inv₀ ((contMDiffOn_divisorF_some c j).mono
        (inter_subset_right.trans inter_subset_left))
        fun _ hz ↦ divisorF_some_ne_zero c hz.2 hz.1
  | some i =>
    cases j with
    | none => exact (contMDiffOn_divisorF_some c i).mono fun _ hz ↦ hz.1.1
    | some j =>
      refine (contMDiffOn_twistTransition (-1) j i ω).comp
        (((BlowupModel.contMDiff_pr ω).comp_contMDiffOn (contMDiffOn_lift c)).mono
          fun _ hz ↦ hz.1.1) fun _ hz ↦ ?_
      exact ⟨mem_affineOpen_of_mem_divisorU c hz.2, mem_affineOpen_of_mem_divisorU c hz.1⟩

/-! ### The local equations of the exceptional divisor -/

/-- **The local equations of the exceptional divisor.** The cover of the blowup by the
complement `offDivisorOpens c` of the exceptional divisor (the index `none`), with local
equation `1`, and by the domains of the charts `blowupModelChart i ∘ lift c` in the image of the
model (the index `some i`), with local equation the coordinate `w i` of the chart. The transition
functions are `w i` from `some i` to `none`, its inverse from `none` to `some i`, and, from
`some i` to `some j`, the ratio `v i / v j` of homogeneous coordinates of the line of the point
of the model (Tau Ceti's `Projectivization.twistTransition (-1) j i`). -/
def hypersurfaceData :
    HypersurfaceData 𝓘(ℂ, Fin (n + 1) → ℂ) (Blowup c) (Option (Fin (n + 1))) where
  U := divisorU c
  isOpen_U := isOpen_divisorU c
  indexAt := divisorIndexAt c
  mem_U_indexAt := mem_divisorU_divisorIndexAt c
  g := divisorG c
  g_ne_zero := divisorG_ne_zero c
  g_mul_g := divisorG_mul_divisorG c
  f := divisorF c
  contMDiffOn_f := contMDiffOn_divisorF c
  contMDiffOn_g := contMDiffOn_divisorG c
  f_eq_g_mul := divisorF_eq_divisorG_mul c

/-- The chart `none` is the complement of the exceptional divisor. -/
@[simp]
theorem hypersurfaceData_U_none :
    (hypersurfaceData c).U none = offDivisorOpens c :=
  (rfl)

/-- The chart `some i` is the domain of the chart `blowupModelChart i ∘ lift c` in the image of
the model. -/
theorem hypersurfaceData_U_some (i : Fin (n + 1)) :
    (hypersurfaceData c).U (some i) =
      range (inr (gluingHomeomorph c)) ∩ lift c ⁻¹' (blowupModelChart i).source :=
  (rfl)

/-- A point of the model lies in the chart `some i` exactly when its line lies in the affine
open `affineOpen i`. -/
@[simp]
theorem inr_mem_hypersurfaceData_U_some_iff (i : Fin (n + 1)) {y : modelOpens c} :
    inr (gluingHomeomorph c) y ∈ (hypersurfaceData c).U (some i) ↔
      (y : BlowupModel n).pr ∈ affineOpen i := by
  simp [hypersurfaceData_U_some]

/-- The preferred chart of a point off the divisor is `none`. -/
theorem hypersurfaceData_indexAt_of_notMem {z : Blowup c} (hz : z ∉ exceptionalDivisor c) :
    (hypersurfaceData c).indexAt z = none := by
  simp [hypersurfaceData, divisorIndexAt, hz]

/-- The preferred chart of a point of the divisor is a chart `some i`. -/
theorem exists_hypersurfaceData_indexAt_eq_some {z : Blowup c} (hz : z ∈ exceptionalDivisor c) :
    ∃ i, (hypersurfaceData c).indexAt z = some i :=
  ⟨(exists_mem_affineOpen (lift c z).pr).choose, by simp [hypersurfaceData, divisorIndexAt, hz]⟩

/-- The local equation off the divisor is `1`. -/
@[simp]
theorem hypersurfaceData_f_none (z : Blowup c) : (hypersurfaceData c).f none z = 1 :=
  (rfl)

/-- The local equation of the chart `some i` is the coordinate `i` of the point of `E` under
the point of the model, which is the coordinate `w i` of the chart `blowupModelChart i`. -/
@[simp]
theorem hypersurfaceData_f_some (i : Fin (n + 1)) (z : Blowup c) :
    (hypersurfaceData c).f (some i) z = (lift c z).blowdown i :=
  (rfl)

/-- The local equation of the chart `some i` is the coordinate `w i` of the chart
`blowupModelChart i ∘ lift c`. -/
theorem hypersurfaceData_f_some_eq_blowupModelChart (i : Fin (n + 1)) (z : Blowup c) :
    (hypersurfaceData c).f (some i) z = blowupModelChart i (lift c z) i := by
  rw [hypersurfaceData_f_some, blowupModelChart_apply_self]

@[simp]
theorem hypersurfaceData_g_none_none (z : Blowup c) : (hypersurfaceData c).g none none z = 1 :=
  (rfl)

/-- The transition function from the chart `none` to the chart `some i` is the inverse of the
local equation of `some i`. -/
@[simp]
theorem hypersurfaceData_g_none_some (i : Fin (n + 1)) (z : Blowup c) :
    (hypersurfaceData c).g none (some i) z = ((lift c z).blowdown i)⁻¹ :=
  (rfl)

/-- The transition function from the chart `some i` to the chart `none` is the local equation
of `some i`. -/
@[simp]
theorem hypersurfaceData_g_some_none (i : Fin (n + 1)) (z : Blowup c) :
    (hypersurfaceData c).g (some i) none z = (lift c z).blowdown i :=
  (rfl)

/-- The transition function from the chart `some i` to the chart `some j` is the transition
function of `𝒪(-1)` from the chart `j` to the chart `i` at the line of the point of the model,
that is, the ratio `v i / v j` of its homogeneous coordinates
(`hypersurfaceData_g_some_some_eq`). -/
@[simp]
theorem hypersurfaceData_g_some_some (i j : Fin (n + 1)) (z : Blowup c) :
    (hypersurfaceData c).g (some i) (some j) z = twistTransition (-1) j i (lift c z).pr :=
  (rfl)

/-- The transition function from the chart `some i` to the chart `some j` is the ratio
`v i / v j` of the coordinates of any `v` spanning the line of the point of the model. -/
theorem hypersurfaceData_g_some_some_eq (i j : Fin (n + 1)) {z : Blowup c} {v : Fin (n + 1) → ℂ}
    (hv : v ≠ 0) (hz : (lift c z).pr = mk ℂ v hv) :
    (hypersurfaceData c).g (some i) (some j) z = v i / v j := by
  rw [hypersurfaceData_g_some_some, hz, twistTransition_mk, zpow_neg, zpow_one, inv_div]

/-! ### The support -/

/-- **The support of the local equations is the exceptional divisor.** -/
theorem support_hypersurfaceData : (hypersurfaceData c).support = exceptionalDivisor c := by
  ext z
  rw [HypersurfaceData.mem_support_iff]
  refine ⟨fun ⟨i, hi, h0⟩ ↦ ?_, fun hz ↦ ?_⟩
  · cases i with
    | none => exact absurd h0 one_ne_zero
    | some i => exact (divisorF_some_eq_zero_iff c hi).1 h0
  · have hi := (hypersurfaceData c).mem_U_indexAt z
    obtain ⟨i, hi'⟩ := exists_hypersurfaceData_indexAt_eq_some c hz
    rw [hi'] at hi
    exact ⟨some i, hi, (divisorF_some_eq_zero_iff c hi).2 hz⟩

end HypersurfaceData

section CoordForm

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M] {p₀ : M} (c φ : BlowupChart (n := n) M p₀)
  [hc : Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]
  [hφ : Fact (φ.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℂ (Fin (n + 1) → ℂ))

/-- **The coordinate form pulled back by the blowdown.** Let `φ` be a holomorphic chart of `M` at
the centre, and `χ` the chart `liftChart c φ` followed by `blowupModelChart i` of the blowup,
with coordinates `w`. At a point `z` of the source of `χ`, the coordinate form of `φ` at the
blowdown of `z`, pulled back by the differential of the blowdown, is `(w i) ^ n` times the
coordinate form of `χ` at `z`; here the coordinate form of a chart is the determinant form of
the basis `b` pulled back by its differential. -/
theorem coordForm_blowdown (i : Fin (n + 1)) {z : Blowup c}
    (hz : z ∈ ((liftChartPartialDiffeomorph c φ).toOpenPartialHomeomorph.trans
      (blowupModelChart i)).source) :
    (b.continuousDet.compContinuousLinearMap (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ)
        𝓘(ℂ, Fin (n + 1) → ℂ) φ (blowdown c z))).compContinuousLinearMap
        (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) (blowdown c) z) =
      (blowupModelChart i (liftChart c φ z) i) ^ n •
        b.continuousDet.compContinuousLinearMap
          (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ)
            ((liftChartPartialDiffeomorph c φ).toOpenPartialHomeomorph.trans
              (blowupModelChart i)) z) := by
  have hs : (liftChartPartialDiffeomorph c φ).toOpenPartialHomeomorph.source =
      blowdown c ⁻¹' φ.source :=
    liftChartPartialDiffeomorph_source c φ
  set χ := (liftChartPartialDiffeomorph c φ).toOpenPartialHomeomorph.trans (blowupModelChart i)
  have hχ : χ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω (Blowup c) :=
    liftChart_mem_maximalAtlas c φ i
  have hzχ := hz
  simp only [χ, OpenPartialHomeomorph.trans_source, hs,
    PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, coe_liftChartPartialDiffeomorph,
    Set.mem_inter_iff, Set.mem_preimage] at hzχ
  -- Near `z`, `φ ∘ blowdown c` is the blowdown of the model read in the chart `χ`.
  have heq : (fun z' ↦ φ (blowdown c z')) =ᶠ[nhds z]
      (fun w ↦ ((blowupModelChart i).symm w).blowdown) ∘ χ := by
    filter_upwards [χ.open_source.mem_nhds hz] with z' hz'
    simp only [χ, OpenPartialHomeomorph.trans_source, hs,
      PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, coe_liftChartPartialDiffeomorph,
      Set.mem_inter_iff, Set.mem_preimage] at hz'
    simp only [comp_apply, χ, OpenPartialHomeomorph.coe_trans,
      PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, coe_liftChartPartialDiffeomorph]
    rw [(blowupModelChart i).left_inv hz'.2, blowdown_liftChart c φ hz'.1]
  have hφd : MDifferentiableAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) φ (blowdown c z) :=
    (contMDiffAt_of_mem_maximalAtlas hφ.out hzχ.1).mdifferentiableAt (by simp)
  have hbd : MDifferentiableAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) (blowdown c) z :=
    ((contMDiff_blowdown c) z).mdifferentiableAt (by simp)
  have hχd : MDifferentiableAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) χ z :=
    (contMDiffAt_of_mem_maximalAtlas hχ hz).mdifferentiableAt (by simp)
  have hχz : χ z = blowupModelChart i (liftChart c φ z) := by
    simp only [χ, OpenPartialHomeomorph.coe_trans, comp_apply,
      PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, coe_liftChartPartialDiffeomorph]
  rw [b.continuousDet_compContinuousLinearMap_mfderiv_comp hφd hbd hχd
    (hasFDerivAt_blowdown_blowupModelChart_symm i (χ z)).differentiableAt heq,
    det_fderiv_blowdown_blowupModelChart_symm, hχz]

/-- **The coordinate forms of two charts of the blowup.** At a point `z` in the sources of the
charts `χᵢ` and `χₖ` of the blowup, `liftChart c c` followed by `blowupModelChart i` and by
`blowupModelChart k` (over the source of `c`, `liftChart c c` is `Blowup.lift c`,
`liftChart_self`), the coordinate form of `χₖ` is `g⁻ⁿ` times that of `χᵢ`, where
`g = (hypersurfaceData c).g (some k) (some i) z` is the ratio `v k / v i` of homogeneous
coordinates of the line of the point of the model (`hypersurfaceData_g_some_some_eq`). The
coordinate form of a chart is the determinant form of the basis `b` pulled back by its
differential. -/
theorem coordForm_liftChart_trans_blowupModelChart (i k : Fin (n + 1)) {z : Blowup c}
    (hi : z ∈ ((liftChartPartialDiffeomorph c c).toOpenPartialHomeomorph.trans
      (blowupModelChart i)).source)
    (hk : z ∈ ((liftChartPartialDiffeomorph c c).toOpenPartialHomeomorph.trans
      (blowupModelChart k)).source) :
    b.continuousDet.compContinuousLinearMap
        (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ)
          ((liftChartPartialDiffeomorph c c).toOpenPartialHomeomorph.trans
            (blowupModelChart k)) z) =
      (((hypersurfaceData c).g (some k) (some i) z) ^ n)⁻¹ •
        b.continuousDet.compContinuousLinearMap
          (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ)
            ((liftChartPartialDiffeomorph c c).toOpenPartialHomeomorph.trans
              (blowupModelChart i)) z) := by
  set L := (liftChartPartialDiffeomorph c c).toOpenPartialHomeomorph
  set χi := L.trans (blowupModelChart i)
  set χk := L.trans (blowupModelChart k)
  set T := (blowupModelChart i).symm.trans (blowupModelChart k)
  have hL (z' : Blowup c) : L z' = liftChart c c z' := by
    simp only [L, PartialDiffeomorph.toFun'_toOpenPartialHomeomorph,
      coe_liftChartPartialDiffeomorph]
  have hχi (z' : Blowup c) : χi z' = blowupModelChart i (liftChart c c z') := by
    simp only [χi, OpenPartialHomeomorph.coe_trans, comp_apply, hL]
  have hmem {j : Fin (n + 1)} {z' : Blowup c} (hz' : z' ∈ (L.trans (blowupModelChart j)).source) :
      liftChart c c z' ∈ (blowupModelChart j).source := by
    rw [OpenPartialHomeomorph.trans_source] at hz'
    rw [← hL]
    exact hz'.2
  -- The point `χᵢ z` lies in the source of the chart change `T`.
  have hT : χi z ∈ T.source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨by simp, ?_⟩
    rw [mem_preimage, hχi, (blowupModelChart i).left_inv (hmem hi)]
    exact hmem hk
  -- Near `z`, the chart `χₖ` is `T ∘ χᵢ`.
  have heq : χk =ᶠ[nhds z] T ∘ χi := by
    filter_upwards [χi.open_source.mem_nhds hi] with z' hz'
    simp only [comp_apply, T, χk, χi, OpenPartialHomeomorph.coe_trans, hL,
      (blowupModelChart i).left_inv (hmem hz')]
  have hχd : MDifferentiableAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) χi z :=
    (contMDiffAt_of_mem_maximalAtlas (liftChart_mem_maximalAtlas c c i) hi).mdifferentiableAt
      (by simp)
  have hTd : DifferentiableAt ℂ T (χi z) :=
    ((contDiffOn_blowupModelChart_symm_trans i k 1).differentiableOn one_ne_zero).differentiableAt
      (T.open_source.mem_nhds hT)
  have h := b.continuousDet_compContinuousLinearMap_mfderiv_of_eventuallyEq hχd hTd heq
  -- The factor: `T`'s Jacobian at `χᵢ z`, with `update (χᵢ z) i 1` spanning the line.
  have hsrc : update (χi z) i 1 k ≠ 0 := by
    have := hT
    rwa [blowupModelChart_symm_trans_source] at this
  have hg : (hypersurfaceData c).g (some k) (some i) z = update (χi z) i 1 k := by
    have hz0 : blowdown c z ∈ c.source := by
      simpa [χi, OpenPartialHomeomorph.trans_source, L] using hi.1
    have hpr : (lift c z).pr = mk ℂ (update (χi z) i 1) (update_ne_zero _ i one_ne_zero) := by
      rw [← liftChart_self c hz0, ← pr_blowupModelChart_symm_apply, hχi,
        (blowupModelChart i).left_inv (hmem hi)]
    rw [hypersurfaceData_g_some_some_eq c k i _ hpr, update_self, div_one]
  rw [hg, ← det_fderiv_blowupModelChart_symm_trans i k hsrc, h]

end CoordForm

section CanonicalBundleEquiv

open scoped TensorProduct TauCeti.ModuleTopology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M] {p₀ : M} (c : BlowupChart (n := n) M p₀)
  [hc : Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]

/-- The differential of the blowdown in the chart `none`, and in the chart `some i` the
differential of the chart `χᵢ = blowupModelChart i ∘ liftChart c c` of the blowup followed by
the inverse of that of `c`. -/
private def chartDeriv : Option (Fin (n + 1)) → (z : Blowup c) →
    (TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) z →L[ℂ]
      TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) (blowdown c z))
  | none, z => mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) (blowdown c) z
  | some i, z =>
    (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) c (blowdown c z)).inverse ∘L
      mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ)
        ((liftChartPartialDiffeomorph c c).toOpenPartialHomeomorph.trans (blowupModelChart i)) z

/-- A point of the chart `some i` lies in the source of the chart `χᵢ` of the blowup, and its
blowdown in the source of `c`. -/
private theorem mem_source_of_mem_U_some {i : Fin (n + 1)} {z : Blowup c}
    (hz : z ∈ (hypersurfaceData c).U (some i)) :
    z ∈ ((liftChartPartialDiffeomorph c c).toOpenPartialHomeomorph.trans
      (blowupModelChart i)).source ∧ blowdown c z ∈ c.source ∧ liftChart c c z = lift c z := by
  rw [hypersurfaceData_U_some] at hz
  have hx := blowdown_mem_source c hz.1
  have hl := liftChart_self c hx
  refine ⟨?_, hx, hl⟩
  have hs : (liftChartPartialDiffeomorph c c).toOpenPartialHomeomorph.source =
      blowdown c ⁻¹' c.source :=
    liftChartPartialDiffeomorph_source c c
  rw [OpenPartialHomeomorph.trans_source, hs]
  refine ⟨hx, ?_⟩
  simp only [mem_preimage, PartialDiffeomorph.toFun'_toOpenPartialHomeomorph,
    coe_liftChartPartialDiffeomorph, hl]
  exact hz.2

/-- On the chart `j`, the map `chartDeriv c j` is invertible. -/
private theorem isInvertible_chartDeriv {j : Option (Fin (n + 1))} {z : Blowup c}
    (hz : z ∈ (hypersurfaceData c).U j) : (chartDeriv c j z).IsInvertible := by
  cases j with
  | none =>
    rw [hypersurfaceData_U_none, SetLike.mem_coe, mem_offDivisorOpens] at hz
    exact (isLocalDiffeomorphAt_blowdown c hz).isInvertible_mfderiv (by simp)
  | some i =>
    obtain ⟨hzχ, hx, -⟩ := mem_source_of_mem_U_some c hz
    exact ((c.isLocalDiffeomorphAt_of_mem_maximalAtlas hc.out hx).isInvertible_mfderiv
      (by simp)).inverse.comp
      ((OpenPartialHomeomorph.isLocalDiffeomorphAt_of_mem_maximalAtlas _
        (liftChart_mem_maximalAtlas c c i) hzχ).isInvertible_mfderiv (by simp))

/-- The value on `b` of a form at the blowdown of `z`, read in the chart `c`. -/
private def chartCoeff (b : Basis (Fin (finrank ℂ (Fin (n + 1) → ℂ))) ℂ (Fin (n + 1) → ℂ))
    (z : Blowup c) (σ : TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M (blowdown c z)) : ℂ :=
  (σ.compContinuousLinearMap
      (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) c (blowdown c z)).inverse :
    (Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ) b

/-- In the chart `some k`, a form `σ` composed with `chartDeriv c (some k) z` is `μ` times the
coordinate form of the chart `χₖ`, where `μ` is the value on `b` of `σ` read in the chart `c`. -/
private theorem compContinuousLinearMap_chartDeriv_some
    (b : Basis (Fin (finrank ℂ (Fin (n + 1) → ℂ))) ℂ (Fin (n + 1) → ℂ)) (k : Fin (n + 1))
    (z : Blowup c) (σ : TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M (blowdown c z)) :
    σ.compContinuousLinearMap (chartDeriv c (some k) z) =
      chartCoeff c b z σ •
        b.continuousDet.compContinuousLinearMap
          (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ)
            ((liftChartPartialDiffeomorph c c).toOpenPartialHomeomorph.trans
              (blowupModelChart k)) z) := by
  refine Eq.trans ?_
    (ContinuousAlternatingMap.compContinuousLinearMap_eq_apply_smul_continuousDet
      (σ.compContinuousLinearMap
        (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) c (blowdown c z)).inverse :
        (Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ) b _)
  ext v
  simp only [chartDeriv, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  -- Both sides apply `σ` to the vectors `dc⁻¹ (dχₖ (v j))`, read once through the tangent spaces
  -- and once through `Fin (n + 1) → ℂ`, which they are by definition; `simp` does not see that.
  rfl

/-- In the chart `some i`, a form `σ` composed with the differential of the blowdown is `μ`
times `(w i) ^ n` times the coordinate form of the chart `χᵢ`, with `μ` as in
`compContinuousLinearMap_chartDeriv_some`. -/
private theorem compContinuousLinearMap_chartDeriv_none
    (b : Basis (Fin (finrank ℂ (Fin (n + 1) → ℂ))) ℂ (Fin (n + 1) → ℂ)) {i : Fin (n + 1)}
    {z : Blowup c} (hz : z ∈ (hypersurfaceData c).U (some i))
    (σ : TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M (blowdown c z)) :
    σ.compContinuousLinearMap (chartDeriv c none z) =
      chartCoeff c b z σ •
        ((lift c z).blowdown i ^ n •
          b.continuousDet.compContinuousLinearMap
            (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ)
              ((liftChartPartialDiffeomorph c c).toOpenPartialHomeomorph.trans
                (blowupModelChart i)) z)) := by
  obtain ⟨hzχ, hx, hl⟩ := mem_source_of_mem_U_some c hz
  set D := mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) c (blowdown c z)
  have hD : D.IsInvertible :=
    (c.isLocalDiffeomorphAt_of_mem_maximalAtlas hc.out hx).isInvertible_mfderiv (by simp)
  have h := coordForm_blowdown c c b i hzχ
  rw [hl, blowupModelChart_apply_self] at h
  rw [← h]
  refine Eq.trans ?_
    (ContinuousAlternatingMap.compContinuousLinearMap_eq_apply_smul_continuousDet
      (σ.compContinuousLinearMap D.inverse :
        (Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ) b
      (D.comp (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) (blowdown c) z)))
  ext v
  simp only [chartDeriv, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  exact congrArg σ (funext fun j ↦ (hD.inverse_apply_self _).symm)

/-- **The maps of two charts agree up to the transition function.** At a point of the charts `j`
and `k`, a form composed with `chartDeriv c j z` is `g k j ^ n` times the form composed with
`chartDeriv c k z`, with `g` the transition function of `hypersurfaceData c`. -/
private theorem compContinuousLinearMap_chartDeriv_eq {j k : Option (Fin (n + 1))} {z : Blowup c}
    (hj : z ∈ (hypersurfaceData c).U j) (hk : z ∈ (hypersurfaceData c).U k)
    (σ : TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M (blowdown c z)) :
    σ.compContinuousLinearMap (chartDeriv c j z) =
      (hypersurfaceData c).g k j z ^ n • σ.compContinuousLinearMap (chartDeriv c k z) := by
  have hg := (hypersurfaceData c).g_ne_zero hk hj
  set b := Module.finBasis ℂ (Fin (n + 1) → ℂ)
  cases j with
  | none =>
    cases k with
    | none => rw [(hypersurfaceData c).g_self hj, one_pow, one_smul]
    | some i =>
      rw [compContinuousLinearMap_chartDeriv_none c b hk, compContinuousLinearMap_chartDeriv_some,
        hypersurfaceData_g_some_none, smul_comm]
  | some i =>
    cases k with
    | none =>
      have hw : (lift c z).blowdown i ≠ 0 := by
        simpa using (hypersurfaceData c).g_ne_zero hj hk
      rw [compContinuousLinearMap_chartDeriv_some c b,
        compContinuousLinearMap_chartDeriv_none c b hj,
        hypersurfaceData_g_none_some, smul_smul, smul_smul]
      congr 1
      rw [mul_right_comm, inv_pow, inv_mul_cancel₀ (pow_ne_zero n hw), one_mul]
    | some k =>
      obtain ⟨hzi, -, -⟩ := mem_source_of_mem_U_some c hj
      obtain ⟨hzk, -, -⟩ := mem_source_of_mem_U_some c hk
      rw [compContinuousLinearMap_chartDeriv_some c b, compContinuousLinearMap_chartDeriv_some c b,
        coordForm_liftChart_trans_blowupModelChart c b i k hzi hzk, smul_smul, smul_smul]
      congr 1
      field_simp

/-- **The canonical bundle of the blowup.** The fibrewise isomorphism, at each point `z` of the
blowup `Blowup c` with blowdown `π`, of the canonical bundle `K` of the blowup with the tensor
product of the pull-back `π^*K_M` of the canonical bundle of `M` with the line bundle `𝒪(nE)` of
`n` times the exceptional divisor `E`, the line bundle of `(hypersurfaceData c).lineBundleCore n`.
Off the divisor its inverse sends `σ ⊗ a` to `a` times the pull-back of `σ` by the blowdown
(`canonicalBundleEquiv_symm_tmul_none`). In the chart `some i`, where the frame of `𝒪(nE)` is
`(w i)⁻ⁿ`, the inverse sends the coordinate form of `c` tensored with that frame to the
coordinate form of the chart `blowupModelChart i ∘ lift c`
(`canonicalBundleEquiv_symm_tmul_some`). For `n = 0` the line bundle is trivial and this is the
pull-back `K ≅ π^*K_M`.

At `z` it is `ω ↦ (ω ∘ L⁻¹) ⊗ 1`, for `L` the differential of the blowdown (chart `none`), or
that of the chart `blowupModelChart i ∘ lift c` followed by the inverse of that of `c` (chart
`some i`), in the preferred chart at `z`. Together with its holomorphy, it gives the identity
`K = π^*K_M ⊗ 𝒪(nE)` of canonical bundles that is part of the milestone
*First Chern class of a blowup at a point*. -/
def canonicalBundleEquiv (z : Blowup c) :
    TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) (Blowup c) z ≃L[ℂ]
      (Bundle.Pullback (blowdown c) (TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M) z ⊗[ℂ]
        ((hypersurfaceData c).lineBundleCore n).Fiber z) :=
  have hL := isInvertible_chartDeriv c ((hypersurfaceData c).mem_U_indexAt z)
  (ContinuousLinearEquiv.ofContinuousLinearMap _ _ hL.self_comp_inverse hL.inverse_comp_self)
    |>.continuousAlternatingMapCongrLeft.trans (TensorProduct.ridL ℂ
      (Bundle.Pullback (blowdown c) (TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M) z)).symm

/-- The inverse of `canonicalBundleEquiv` in the preferred chart at `z`. -/
private theorem canonicalBundleEquiv_symm_tmul (z : Blowup c)
    (σ : TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M (blowdown c z)) (y : ℂ) :
    (canonicalBundleEquiv c z).symm (TensorProduct.tmul ℂ
        (M := Bundle.Pullback (blowdown c) (TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M) z)
        (N := ((hypersurfaceData c).lineBundleCore n).Fiber z) σ y) =
      y • σ.compContinuousLinearMap (chartDeriv c ((hypersurfaceData c).indexAt z) z) := by
  refine ((ContinuousLinearEquiv.symm_trans_apply _ _ _).trans (congrArg _
    (TensorProduct.ridL_tmul ℂ
      (Bundle.Pullback (blowdown c) (TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M) z)
      σ y))).trans
    ((map_smul _ y σ).trans (congrArg (y • ·) ((ContinuousLinearEquiv.symm_apply_eq _).2 ?_)))
  ext v
  simp [Function.comp_def,
    (isInvertible_chartDeriv c ((hypersurfaceData c).mem_U_indexAt z)).self_apply_inverse]

/-- The inverse of `canonicalBundleEquiv` in any chart `j` containing `z`: it sends `σ` tensored
with the element of coordinate `a` in the chart `j` to `a • σ ∘ chartDeriv c j z`. -/
private theorem canonicalBundleEquiv_symm_tmul_localTriv_symm {j : Option (Fin (n + 1))}
    {z : Blowup c} (hz : z ∈ (hypersurfaceData c).U j)
    (σ : TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M (blowdown c z)) (a : ℂ) :
    (canonicalBundleEquiv c z).symm (TensorProduct.tmul ℂ
        (M := Bundle.Pullback (blowdown c) (TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M) z)
        (N := ((hypersurfaceData c).lineBundleCore n).Fiber z) σ
        ((((hypersurfaceData c).lineBundleCore n).localTriv j).symm z a)) =
      a • σ.compContinuousLinearMap (chartDeriv c j z) := by
  have hz' : z ∈ (((hypersurfaceData c).lineBundleCore n).localTriv j).baseSet := by simpa using hz
  refine (congrArg (fun y : ((hypersurfaceData c).lineBundleCore n).Fiber z ↦
    (canonicalBundleEquiv c z).symm (TensorProduct.tmul ℂ
      (M := Bundle.Pullback (blowdown c) (TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M) z)
      (N := ((hypersurfaceData c).lineBundleCore n).Fiber z) σ y))
    (VectorBundleCore.localTriv_symm_apply _ _ hz' a)).trans
    ((canonicalBundleEquiv_symm_tmul c z σ _).trans ?_)
  rw [ScalarCocycle.lineBundleCore_coordChange_apply, ScalarCocycle.lineBundleCore_indexAt,
    compContinuousLinearMap_chartDeriv_eq c hz ((hypersurfaceData c).mem_U_indexAt z), zpow_natCast,
    mul_comm, mul_smul]

/-- **`canonicalBundleEquiv` off the exceptional divisor.** At a point `z` of the chart `none`,
the complement of the exceptional divisor, the inverse of `canonicalBundleEquiv` sends `σ`
tensored with the element of coordinate `a` in the chart `none` of `𝒪(nE)` to `a` times the
pull-back of `σ` by the differential of the blowdown. -/
theorem canonicalBundleEquiv_symm_tmul_none {z : Blowup c} (hz : z ∉ exceptionalDivisor c)
    (σ : TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M (blowdown c z)) (a : ℂ) :
    (canonicalBundleEquiv c z).symm (TensorProduct.tmul ℂ
        (M := Bundle.Pullback (blowdown c) (TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M) z)
        (N := ((hypersurfaceData c).lineBundleCore n).Fiber z) σ
        ((((hypersurfaceData c).lineBundleCore n).localTriv none).symm z a)) =
      a • σ.compContinuousLinearMap
        (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) (blowdown c) z) := by
  have hz' : z ∈ (hypersurfaceData c).U none := by
    rwa [hypersurfaceData_U_none, SetLike.mem_coe, mem_offDivisorOpens]
  rw [canonicalBundleEquiv_symm_tmul_localTriv_symm c hz', chartDeriv]

/-- **`canonicalBundleEquiv` on the frame of a chart off the exceptional divisor.** For a
holomorphic chart `e` of `M` and a point `y` off the exceptional divisor whose blowdown lies in
the source of `e`, the inverse of `canonicalBundleEquiv` sends the coordinate form of `e` at the
blowdown of `y`, tensored with the element of coordinate `a` in the chart `none` of `𝒪(nE)`, to
`a` times the coordinate form at `y` of `e ∘ blowdown c`. -/
theorem canonicalBundleEquiv_symm_continuousDet_mfderiv_tmul_none
    {e : OpenPartialHomeomorph M (Fin (n + 1) → ℂ)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)
    (b : Basis (Fin (finrank ℂ (Fin (n + 1) → ℂ))) ℂ (Fin (n + 1) → ℂ)) {y : Blowup c}
    (hy : y ∉ exceptionalDivisor c) (hye : blowdown c y ∈ e.source) (a : ℂ) :
    (canonicalBundleEquiv c y).symm (TensorProduct.tmul ℂ
        (M := Bundle.Pullback (blowdown c) (TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M) y)
        (N := ((hypersurfaceData c).lineBundleCore n).Fiber y)
        (b.continuousDet.compContinuousLinearMap
          (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) e (blowdown c y)))
        ((((hypersurfaceData c).lineBundleCore n).localTriv none).symm y a)) =
      a • b.continuousDet.compContinuousLinearMap
        (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) (e ∘ blowdown c) y) := by
  rw [canonicalBundleEquiv_symm_tmul_none c hy,
    mfderiv_comp y ((contMDiffAt_of_mem_maximalAtlas he hye).mdifferentiableAt (by simp))
      ((contMDiff_blowdown c y).mdifferentiableAt (by simp))]
  exact congrArg (a • ·)
    (ContinuousAlternatingMap.compContinuousLinearMap_compContinuousLinearMap _ _ _)

/-- **`canonicalBundleEquiv` in the chart `some i`.** At a point `z` of the chart `some i` of the
exceptional divisor, the inverse of `canonicalBundleEquiv` sends the coordinate form of `c` at
the blowdown of `z`, tensored with the element of coordinate `a` in the chart `some i` of
`𝒪(nE)`, to `a` times the coordinate form at `z` of the chart `χᵢ`, `liftChart c c` followed by
`blowupModelChart i` (over the source of `c`, `liftChart c c` is `Blowup.lift c`,
`liftChart_self`). The coordinate form of a chart is the determinant form of the basis `b`
pulled back by its differential. The element of coordinate `1` is the frame `(w i)⁻ⁿ` of
`𝒪(nE)`; off the divisor, the pull-back by the blowdown of the coordinate form of `c` is
`(w i) ^ n` times that of `χᵢ` (`coordForm_blowdown`), so this agrees with
`canonicalBundleEquiv_symm_tmul_none`. -/
theorem canonicalBundleEquiv_symm_tmul_some {i : Fin (n + 1)} {z : Blowup c}
    (hz : z ∈ (hypersurfaceData c).U (some i))
    (b : Basis (Fin (finrank ℂ (Fin (n + 1) → ℂ))) ℂ (Fin (n + 1) → ℂ)) (a : ℂ) :
    (canonicalBundleEquiv c z).symm (TensorProduct.tmul ℂ
        (M := Bundle.Pullback (blowdown c) (TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M) z)
        (N := ((hypersurfaceData c).lineBundleCore n).Fiber z)
        (b.continuousDet.compContinuousLinearMap
          (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) c (blowdown c z)))
        ((((hypersurfaceData c).lineBundleCore n).localTriv (some i)).symm z a)) =
      a • b.continuousDet.compContinuousLinearMap
        (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ)
          ((liftChartPartialDiffeomorph c c).toOpenPartialHomeomorph.trans
            (blowupModelChart i)) z) := by
  obtain ⟨-, hx, -⟩ := mem_source_of_mem_U_some c hz
  have hD := (c.isLocalDiffeomorphAt_of_mem_maximalAtlas hc.out hx).isInvertible_mfderiv
    (by simp)
  rw [canonicalBundleEquiv_symm_tmul_localTriv_symm c hz]
  congr 1
  ext v
  simp only [chartDeriv, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  exact congrArg b.continuousDet (funext fun _ ↦ hD.self_apply_inverse _)

section Frames

open Bundle

/-- **Local frames of `π^*K_M ⊗ 𝒪(nE)`.** For a holomorphic chart `e` of `M` and an index `j` of
`hypersurfaceData c`, the section `z ↦ dz_e ⊗ s_j` of `π^*K_M ⊗ 𝒪(nE)`, the coordinate form of `e`
at the blowdown of `z` tensored with the element of coordinate `1` in the chart `j` of `𝒪(nE)`, is
holomorphic on the chart `j` of `hypersurfaceData c` over the source of `e`. -/
theorem contMDiffOn_continuousDet_mfderiv_tmul_localTriv_symm {e : OpenPartialHomeomorph M
    (Fin (n + 1) → ℂ)} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)
    (b : Basis (Fin (finrank ℂ (Fin (n + 1) → ℂ))) ℂ (Fin (n + 1) → ℂ)) (j : Option (Fin (n + 1))) :
    ContMDiffOn 𝓘(ℂ, Fin (n + 1) → ℂ)
      (𝓘(ℂ, Fin (n + 1) → ℂ).prod 𝓘(ℂ, TauCeti.ProjectiveTensor ℂ
        ((Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ) ℂ)) ω
      (fun z ↦ TotalSpace.mk' (TauCeti.ProjectiveTensor ℂ
          ((Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ) ℂ)
        (E := fun z ↦
          Bundle.Pullback (blowdown c) (TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M) z ⊗[ℂ]
            ((hypersurfaceData c).lineBundleCore n).Fiber z) z
        ((b.continuousDet.compContinuousLinearMap
          (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) e (blowdown c z)) :
            Bundle.Pullback (blowdown c) (TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M) z)
          ⊗ₜ[ℂ] (((hypersurfaceData c).lineBundleCore n).localTriv j).symm z 1))
      ((hypersurfaceData c).U j ∩ blowdown c ⁻¹' e.source) := by
  have hU : IsOpen ((hypersurfaceData c).U j ∩ blowdown c ⁻¹' e.source) :=
    ((hypersurfaceData c).isOpen_U j).inter (e.open_source.preimage (blowdown c).continuous)
  refine ContMDiffOn.tmul_section (b := id) (F₂ := ℂ)
    (F₁ := (Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ)
    (E₁ := (blowdown c) *ᵖ (TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M))
    (E₂ := ((hypersurfaceData c).lineBundleCore n).Fiber) ?_ ?_
  · intro z hz
    rw [Bundle.Pullback.contMDiffWithinAt_iff (blowdown c) (contMDiff_blowdown c _)]
    refine ⟨contMDiffWithinAt_id, ?_⟩
    exact ((TauCeti.CanonicalBundle.contMDiffAt_continuousDet_compContinuousLinearMap_mfderiv
      (contMDiffAt_of_mem_maximalAtlas he hz.2) (by simp) b).comp z
      (contMDiff_blowdown c z)).contMDiffWithinAt
  · have hsub : (hypersurfaceData c).U j ∩ blowdown c ⁻¹' e.source ⊆
        (((hypersurfaceData c).lineBundleCore n).localTriv j).baseSet := fun z hz ↦ by
      simpa using hz.1
    have : MemTrivializationAtlas (((hypersurfaceData c).lineBundleCore n).localTriv j) :=
      ⟨⟨j, rfl⟩⟩
    exact (((hypersurfaceData c).lineBundleCore n).localTriv j).contMDiffOn_section_symm hU hsub
      (contMDiffOn_const (c := (1 : ℂ)))

/-- **The local frames of `π^*K_M ⊗ 𝒪(nE)` do not vanish.** At a point `z` of the chart `j` of
`hypersurfaceData c` whose blowdown lies in the source of a holomorphic chart `e` of `M`, the
coordinate form of `e` at the blowdown of `z` tensored with the element of coordinate `1` in the
chart `j` of `𝒪(nE)` is nonzero. -/
theorem continuousDet_mfderiv_tmul_localTriv_symm_ne_zero {e : OpenPartialHomeomorph M
    (Fin (n + 1) → ℂ)} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)
    (b : Basis (Fin (finrank ℂ (Fin (n + 1) → ℂ))) ℂ (Fin (n + 1) → ℂ)) {j : Option (Fin (n + 1))}
    {z : Blowup c} (hz : z ∈ (hypersurfaceData c).U j) (hze : blowdown c z ∈ e.source) :
    (b.continuousDet.compContinuousLinearMap
          (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) e (blowdown c z)) :
        Bundle.Pullback (blowdown c) (TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M) z) ⊗ₜ[ℂ]
      (((hypersurfaceData c).lineBundleCore n).localTriv j).symm z 1 ≠ 0 :=
  TauCeti.tmul_ne_zero
    (b.continuousDet_compContinuousLinearMap_mfderiv_extend_ne_zero he le_top hze)
    (((((hypersurfaceData c).lineBundleCore n).localTriv j).symm_apply_ne_zero_iff ℂ
      (by simpa using hz)).2 one_ne_zero)

/-- **The local frame of `π^*K_M ⊗ 𝒪(nE)` on the chart `some i`.** The coordinate form of `c` at
the blowdown of `z` tensored with the element of coordinate `1` in the chart `some i` of
`𝒪(nE)`, the frame that `canonicalBundleEquiv_symm_tmul_some` evaluates, is holomorphic on the
chart `some i` of `hypersurfaceData c`. -/
theorem contMDiffOn_continuousDet_mfderiv_tmul_localTriv_symm_some
    (b : Basis (Fin (finrank ℂ (Fin (n + 1) → ℂ))) ℂ (Fin (n + 1) → ℂ)) (i : Fin (n + 1)) :
    ContMDiffOn 𝓘(ℂ, Fin (n + 1) → ℂ)
      (𝓘(ℂ, Fin (n + 1) → ℂ).prod 𝓘(ℂ, TauCeti.ProjectiveTensor ℂ
        ((Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ) ℂ)) ω
      (fun z ↦ TotalSpace.mk' (TauCeti.ProjectiveTensor ℂ
          ((Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ) ℂ)
        (E := fun z ↦
          Bundle.Pullback (blowdown c) (TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M) z ⊗[ℂ]
            ((hypersurfaceData c).lineBundleCore n).Fiber z) z
        ((b.continuousDet.compContinuousLinearMap
          (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) c (blowdown c z)) :
            Bundle.Pullback (blowdown c) (TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M) z)
          ⊗ₜ[ℂ] (((hypersurfaceData c).lineBundleCore n).localTriv (some i)).symm z 1))
      ((hypersurfaceData c).U (some i)) :=
  (contMDiffOn_continuousDet_mfderiv_tmul_localTriv_symm c hc.out b (some i)).mono
    fun _ hz ↦ ⟨hz, (mem_source_of_mem_U_some c hz).2.1⟩

/-- The local frame of `π^*K_M ⊗ 𝒪(nE)` on the chart `some i`, built from the coordinate form of
`c`, does not vanish there. -/
theorem continuousDet_mfderiv_tmul_localTriv_symm_some_ne_zero
    (b : Basis (Fin (finrank ℂ (Fin (n + 1) → ℂ))) ℂ (Fin (n + 1) → ℂ)) {i : Fin (n + 1)}
    {z : Blowup c} (hz : z ∈ (hypersurfaceData c).U (some i)) :
    (b.continuousDet.compContinuousLinearMap
          (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) c (blowdown c z)) :
        Bundle.Pullback (blowdown c) (TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M) z) ⊗ₜ[ℂ]
      (((hypersurfaceData c).lineBundleCore n).localTriv (some i)).symm z 1 ≠ 0 :=
  continuousDet_mfderiv_tmul_localTriv_symm_ne_zero c hc.out b hz
    (mem_source_of_mem_U_some c hz).2.1

end Frames

/-- The pull-back by the blowdown of a holomorphic vector bundle on `M` is a holomorphic vector
bundle on the blowup. -/
instance contMDiffVectorBundle_pullback_blowdown {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] {E : M → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (Bundle.TotalSpace F E)] [FiberBundle F E]
    [VectorBundle ℂ F E] [ContMDiffVectorBundle ω F E 𝓘(ℂ, Fin (n + 1) → ℂ)] :
    ContMDiffVectorBundle ω F (Bundle.Pullback (blowdown c) E) 𝓘(ℂ, Fin (n + 1) → ℂ) :=
  Bundle.Pullback.contMDiffVectorBundle (contMDiff_blowdown c)

section Holomorphy

open Bundle

/-- **The inverse of `canonicalBundleEquiv` is holomorphic.** The map of total spaces
`⟨z, τ⟩ ↦ ⟨z, (canonicalBundleEquiv c z).symm τ⟩`, from `π^*K_M ⊗ 𝒪(nE)` to the canonical bundle
of the blowup, is holomorphic. -/
theorem contMDiff_canonicalBundleEquiv_symm :
    ContMDiff
      (𝓘(ℂ, Fin (n + 1) → ℂ).prod 𝓘(ℂ, TauCeti.ProjectiveTensor ℂ
        ((Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ) ℂ))
      (𝓘(ℂ, Fin (n + 1) → ℂ).prod
        𝓘(ℂ, (Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ)) ω
      (fun p : TotalSpace (TauCeti.ProjectiveTensor ℂ
          ((Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ) ℂ)
          (fun z ↦
            Bundle.Pullback (blowdown c) (TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M) z ⊗[ℂ]
              ((hypersurfaceData c).lineBundleCore n).Fiber z) ↦
        TotalSpace.mk' ((Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ)
          (E := TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) (Blowup c)) p.proj
          ((canonicalBundleEquiv c p.proj).symm p.snd)) := by
  set b := Module.finBasis ℂ (Fin (n + 1) → ℂ)
  -- The fibres are lines. Each use below passes `hF` as `by exact hF`, which elaborates it
  -- after the instances on the fibre are found; passed as a term, `hF` fixes them by
  -- unification first, and the proof runs out of heartbeats.
  have hF : finrank ℂ (TauCeti.ProjectiveTensor ℂ
      ((Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ) ℂ) = 1 := by
    rw [TauCeti.ProjectiveTensor.finrank_eq_mul, b.finrank_continuousAlternatingMap_eq_one,
      Module.finrank_self]
  -- Near each point, test the inverse on a nowhere zero holomorphic section of
  -- `π^*K_M ⊗ 𝒪(nE)`, whose image is a coordinate form.
  intro p
  by_cases hp : p.proj ∈ exceptionalDivisor c
  · -- On the chart `some i`, the frame built from `c` goes to the coordinate form of `χᵢ`.
    obtain ⟨i, hi⟩ := exists_hypersurfaceData_indexAt_eq_some c hp
    have hpi : p.proj ∈ (hypersurfaceData c).U (some i) :=
      hi ▸ (hypersurfaceData c).mem_U_indexAt p.proj
    have hU := (hypersurfaceData c).isOpen_U (some i)
    have key := ContMDiffOn.bundleMap_of_finrank_eq_one (n := ω) (F := TauCeti.ProjectiveTensor ℂ
        ((Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ) ℂ)
      (F' := (Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ)
      (by exact hF) hU
      (contMDiffOn_continuousDet_mfderiv_tmul_localTriv_symm_some c b i)
      (fun z hz ↦ continuousDet_mfderiv_tmul_localTriv_symm_some_ne_zero c b hz)
      (A := fun z ↦ ((canonicalBundleEquiv c z).symm :
        _ →L[ℂ] TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) (Blowup c) z))
    refine (key fun z hz ↦ ?_).contMDiffAt
      ((hU.preimage (FiberBundle.continuous_proj _ _)).mem_nhds hpi)
    refine ((TauCeti.CanonicalBundle.contMDiffAt_continuousDet_compContinuousLinearMap_mfderiv
      (contMDiffAt_of_mem_maximalAtlas (liftChart_mem_maximalAtlas c c i)
        (mem_source_of_mem_U_some c hz).1) (by simp) b).contMDiffWithinAt).congr_of_mem
      (fun y hy ↦ ?_) hz
    simp only [ContinuousLinearEquiv.coe_coe, canonicalBundleEquiv_symm_tmul_some c hy b,
      one_smul]
  · -- Off the divisor, the frame built from a chart `e` of `M` goes to the coordinate form of
    -- `e ∘ π`.
    set e := chartAt (Fin (n + 1) → ℂ) (blowdown c p.proj)
    have he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M :=
      IsManifold.chart_mem_maximalAtlas _
    have hU : IsOpen ((hypersurfaceData c).U none ∩ blowdown c ⁻¹' e.source) :=
      ((hypersurfaceData c).isOpen_U none).inter (e.open_source.preimage (blowdown c).continuous)
    have hpU : p.proj ∈ (hypersurfaceData c).U none ∩ blowdown c ⁻¹' e.source :=
      ⟨by simpa [hypersurfaceData_U_none] using hp, mem_chart_source _ _⟩
    have key := ContMDiffOn.bundleMap_of_finrank_eq_one (n := ω) (F := TauCeti.ProjectiveTensor ℂ
        ((Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ) ℂ)
      (F' := (Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ)
      (by exact hF) hU
      (contMDiffOn_continuousDet_mfderiv_tmul_localTriv_symm c he b none)
      (fun z hz ↦ continuousDet_mfderiv_tmul_localTriv_symm_ne_zero c he b hz.1 hz.2)
      (A := fun z ↦ ((canonicalBundleEquiv c z).symm :
        _ →L[ℂ] TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) (Blowup c) z))
    refine (key fun z hz ↦ ?_).contMDiffAt
      ((hU.preimage (FiberBundle.continuous_proj _ _)).mem_nhds hpU)
    have he' : ContMDiffAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (e ∘ blowdown c) z :=
      (contMDiffAt_of_mem_maximalAtlas he hz.2).comp z (contMDiff_blowdown c z)
    refine ((TauCeti.CanonicalBundle.contMDiffAt_continuousDet_compContinuousLinearMap_mfderiv
      he' (by simp) b).contMDiffWithinAt).congr_of_mem (fun y hy ↦ ?_) hz
    have hy' : y ∉ exceptionalDivisor c := by
      simpa [hypersurfaceData_U_none] using hy.1
    simp only [ContinuousLinearEquiv.coe_coe,
      canonicalBundleEquiv_symm_continuousDet_mfderiv_tmul_none c he b hy' hy.2, one_smul]

/-- **`canonicalBundleEquiv` is holomorphic.** The map of total spaces
`⟨z, σ⟩ ↦ ⟨z, canonicalBundleEquiv c z σ⟩`, from the canonical bundle of the blowup to
`π^*K_M ⊗ 𝒪(nE)`, is holomorphic. Tau Ceti's `TauCeti.bundleDiffeomorph` packages it, with its
inverse (`contMDiff_canonicalBundleEquiv_symm`), as a biholomorphism of total spaces. -/
theorem contMDiff_canonicalBundleEquiv :
    ContMDiff
      (𝓘(ℂ, Fin (n + 1) → ℂ).prod
        𝓘(ℂ, (Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ))
      (𝓘(ℂ, Fin (n + 1) → ℂ).prod 𝓘(ℂ, TauCeti.ProjectiveTensor ℂ
        ((Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ) ℂ)) ω
      (fun p : TotalSpace ((Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ)
          (TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) (Blowup c)) ↦
        TotalSpace.mk' (TauCeti.ProjectiveTensor ℂ
            ((Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ) ℂ)
          (E := fun z ↦
            Bundle.Pullback (blowdown c) (TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M) z ⊗[ℂ]
              ((hypersurfaceData c).lineBundleCore n).Fiber z) p.proj
          (canonicalBundleEquiv c p.proj p.snd)) := by
  have key := TauCeti.contMDiff_bundle_symm (n := ω) (IB := 𝓘(ℂ, Fin (n + 1) → ℂ))
    (F₁ := TauCeti.ProjectiveTensor ℂ
      ((Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ) ℂ)
    (F₂ := (Fin (n + 1) → ℂ) [⋀^Fin (finrank ℂ (Fin (n + 1) → ℂ))]→L[ℂ] ℂ)
    (E₁ := fun z ↦
      Bundle.Pullback (blowdown c) (TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) M) z ⊗[ℂ]
        ((hypersurfaceData c).lineBundleCore n).Fiber z)
    (E₂ := TauCeti.CanonicalBundle 𝓘(ℂ, Fin (n + 1) → ℂ) (Blowup c))
    (fun z ↦ (canonicalBundleEquiv c z).symm) (contMDiff_canonicalBundleEquiv_symm c)
  simpa only [ContinuousLinearEquiv.symm_symm] using key

end Holomorphy

end CanonicalBundleEquiv

end Blowup

end SymplecticGeometry

end
