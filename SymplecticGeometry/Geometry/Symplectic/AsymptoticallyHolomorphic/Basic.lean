/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.RescaledChart
public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.Power.Basic
public import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.JetNorm
public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.Power.Connection
public import TauCeti.LinearAlgebra.Complex.LinearPart
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Sections read in rescaled unitary charts, and their jet norms

Let `D` be rescaled unitary charts (`SymplecticGeometry.RescaledUnitaryCharts`) for a principal
`Circle`-bundle `P`. For a power `k` and a point `x`, the chart `D.chart k x` and the frame
`D.frame k x` turn a section `s` of the line bundle `PowerBundle P k` into a complex function on
`StdSpace ι`: its value at `z` is the coordinate of `s` at the point `(D.chart k x).symm z`, in the
unitary frame `[D.frame k x _, 1]` of that fibre. This is `D.reading k x s`, and
`SymplecticGeometry.RescaledUnitaryCharts.apply_chart_symm_eq_mk` recovers `s` from it. The
reading is complex linear in `s`.

The `r`-jet norm `D.jetNorm k r s x` is the jet norm `SymplecticGeometry.jetNormAt ℝ r` of the
reading at the centre `0` of the chart: the sum, over the orders `j ≤ r`, of the norms of the
`j`-th derivatives (Mathlib's `iteratedFDeriv`) of the reading there. Its lemmas come from those
of `jetNormAt`. It is nonnegative and monotone in `r`; for `k₀ ≤ k` its order `0` is the norm of
`s x`, since the chart sends `x` to `0` (`SymplecticGeometry.RescaledUnitaryCharts.chart_symm_zero`)
and the frame is unitary; it vanishes on the zero section, is unchanged by negation, and scales
by `‖c‖` under multiplication by `c : ℂ`; and for sections whose readings are `C^r` at `0` it
satisfies the triangle inequality.

The connection `powerConnection α k` is read in the same chart and frame as
`D.connectionReading k x s z = df_z + i A₀(z) f(z)`, for `f` the reading of `s` and
`A₀(z) v = -ω₀(z, v) / 2` the model connection form, `ω₀` being `stdForm ι`.
`SymplecticGeometry.RescaledUnitaryCharts.powerConnection_chart_symm_apply` shows that, at a
point `z` of the ball of radius `ρ₀ * √k` where the reading of `s` is differentiable, this is the
coordinate of `D_k s` in the frame, at the image of `z` and on the image of a vector under the
derivative of the inverse chart. It follows from the local
formula `SymplecticGeometry.powerConnection_apply_frame`, applied to the frame, which is smooth on
the image of that ball, and from `SymplecticGeometry.RescaledUnitaryCharts.connectionForm_eq_model`.
The `∂̄` reading `D.dbarReading k x s z` is Tau Ceti's complex-antilinear part
`TauCeti.complexAntilinearPart` of `D.connectionReading k x s z`, for the structure `J` pushed
forward by the chart at `z` and multiplication by `i` on `ℂ`. Both readings commute with
multiplication by `c : ℂ`, and are additive on sections whose readings are differentiable at `z`.
The `r`-jet norm of the `∂̄` reading, `D.dbarJetNorm k r s x`, is its jet norm at `0`; it is
nonnegative and monotone in `r`, vanishes on the zero section, is unchanged by negation, scales by
`‖c‖` under multiplication by `c : ℂ`, and satisfies the triangle inequality for sections whose
readings are differentiable near `0` and whose `∂̄` readings are `C^r` at `0`.

These are the chart norms by which the estimates on asymptotically holomorphic sequences of
sections are stated, in the rescaled metrics `k ω(·, J ·)`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.4
* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996]
* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002],
  Lemma 1
-/

public section

open scoped Manifold ContDiff
open TauCeti Bundle Metric
open scoped Topology

namespace SymplecticGeometry

namespace RescaledUnitaryCharts

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {ι : Type*} [Fintype ι]
  {P : M → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ x, TopologicalSpace (P x)]
  [FiberBundle Circle P] [∀ x, MulAction Circleᵐᵒᵖ (P x)] [PrincipalBundle Circle P]
  [ContMDiffFiberBundle ∞ Circle P I (𝓡 1)]
  {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
  {α : SmoothForm (I.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1} {k₀ : ℕ} {ρ₀ : ℝ}
  (D : RescaledUnitaryCharts P σ J α ι k₀ ρ₀)

/-- The **reading of a section** `s` of `PowerBundle P k` in the chart `D.chart k x` and the
frame `D.frame k x`: the complex function on `StdSpace ι` whose value at `z` is the coordinate
of `s ((D.chart k x).symm z)` in the frame `[D.frame k x _, 1]` of its fibre. -/
noncomputable def reading (k : ℕ) (x : M) (s : Π y, PowerBundle P k y) : StdSpace ι → ℂ :=
  fun z ↦ PowerModel.toComplex ((AssociatedBundle.mkLinearIsometryEquiv ℂ Circle
    (D.frame k x ((D.chart k x).symm z))).symm (s ((D.chart k x).symm z)))

theorem reading_def (k : ℕ) (x : M) (s : Π y, PowerBundle P k y) (z : StdSpace ι) :
    D.reading k x s z = PowerModel.toComplex ((AssociatedBundle.mkLinearIsometryEquiv ℂ Circle
      (D.frame k x ((D.chart k x).symm z))).symm (s ((D.chart k x).symm z))) :=
  (rfl)

/-- A section is recovered from its reading: at the point `(D.chart k x).symm z`, it is the
class of the frame and of the reading at `z`. -/
theorem apply_chart_symm_eq_mk (k : ℕ) (x : M) (s : Π y, PowerBundle P k y) (z : StdSpace ι) :
    s ((D.chart k x).symm z) = AssociatedBundle.mk Circle (D.frame k x ((D.chart k x).symm z))
      (PowerModel.toComplex.symm (D.reading k x s z)) := by
  rw [reading_def, LinearIsometryEquiv.symm_apply_apply,
    ← AssociatedBundle.mkLinearIsometryEquiv_apply (𝕜 := ℂ),
    LinearIsometryEquiv.apply_symm_apply]

@[simp]
theorem reading_add (k : ℕ) (x : M) (s t : Π y, PowerBundle P k y) :
    D.reading k x (s + t) = D.reading k x s + D.reading k x t := by
  ext z
  simp only [reading_def, Pi.add_apply, map_add]

@[simp]
theorem reading_smul (k : ℕ) (x : M) (c : ℂ) (s : Π y, PowerBundle P k y) :
    D.reading k x (c • s) = c • D.reading k x s := by
  ext z
  simp only [reading_def, Pi.smul_apply, map_smul]

@[simp]
theorem reading_zero (k : ℕ) (x : M) : D.reading k x (0 : Π y, PowerBundle P k y) = 0 := by
  simpa using D.reading_smul k x 0 0

@[simp]
theorem reading_neg (k : ℕ) (x : M) (s : Π y, PowerBundle P k y) :
    D.reading k x (-s) = -D.reading k x s := by
  ext z
  simp only [reading_def, Pi.neg_apply, map_neg]

@[simp]
theorem reading_sub (k : ℕ) (x : M) (s t : Π y, PowerBundle P k y) :
    D.reading k x (s - t) = D.reading k x s - D.reading k x t := by
  ext z
  simp only [reading_def, Pi.sub_apply, map_sub]

/-- The reading has the norm of the section: at `z`, it is `‖s ((D.chart k x).symm z)‖`. -/
@[simp]
theorem norm_reading (k : ℕ) (x : M) (s : Π y, PowerBundle P k y) (z : StdSpace ι) :
    ‖D.reading k x s z‖ = ‖s ((D.chart k x).symm z)‖ := by
  rw [reading_def, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]

/-- The **`r`-jet norm at `x`** of a section `s` of `PowerBundle P k`: the jet norm
`SymplecticGeometry.jetNormAt ℝ r` at `0` of the reading of `s` in the chart and the frame
centred at `x`, that is, the sum over the orders `j ≤ r` of the norms of its `j`-th derivatives
at `0`. -/
noncomputable def jetNorm (k r : ℕ) (s : Π y, PowerBundle P k y) (x : M) : ℝ :=
  jetNormAt ℝ r (D.reading k x s) 0

theorem jetNorm_def (k r : ℕ) (s : Π y, PowerBundle P k y) (x : M) :
    D.jetNorm k r s x = jetNormAt ℝ r (D.reading k x s) 0 :=
  (rfl)

theorem jetNorm_nonneg (k r : ℕ) (s : Π y, PowerBundle P k y) (x : M) :
    0 ≤ D.jetNorm k r s x := by
  rw [jetNorm_def]
  exact jetNormAt_nonneg _ _ _

/-- The jet norm grows with the order. -/
theorem jetNorm_mono (k : ℕ) (s : Π y, PowerBundle P k y) (x : M) :
    Monotone fun r ↦ D.jetNorm k r s x := by
  simpa only [jetNorm_def] using jetNormAt_mono (D.reading k x s) 0

/-- The jet norm of order `0` is the norm of the section at the centre. -/
theorem jetNorm_zero {k : ℕ} (hk : k₀ ≤ k) (s : Π y, PowerBundle P k y) (x : M) :
    D.jetNorm k 0 s x = ‖s x‖ := by
  rw [jetNorm_def, jetNormAt_zero, norm_reading, D.chart_symm_zero hk x]

/-- The zero section has jet norm `0`. -/
@[simp]
theorem jetNorm_zero_fun (k r : ℕ) (x : M) :
    D.jetNorm k r (0 : Π y, PowerBundle P k y) x = 0 := by
  rw [jetNorm_def, reading_zero, jetNormAt_zero_fun]

@[simp]
theorem jetNorm_neg (k r : ℕ) (s : Π y, PowerBundle P k y) (x : M) :
    D.jetNorm k r (-s) x = D.jetNorm k r s x := by
  rw [jetNorm_def, jetNorm_def, reading_neg, jetNormAt_neg]

/-- The **triangle inequality for jet norms**, for sections whose readings are `C^r` at `0`. -/
theorem jetNorm_add_le {k r : ℕ} {s t : Π y, PowerBundle P k y} {x : M}
    (hs : ContDiffAt ℝ r (D.reading k x s) 0) (ht : ContDiffAt ℝ r (D.reading k x t) 0) :
    D.jetNorm k r (s + t) x ≤ D.jetNorm k r s x + D.jetNorm k r t x := by
  simpa only [jetNorm_def, reading_add] using jetNormAt_add_le hs ht

/-- The jet norm of a complex multiple `c • s` is `‖c‖` times that of `s`. -/
@[simp]
theorem jetNorm_smul (k r : ℕ) (s : Π y, PowerBundle P k y) (x : M) (c : ℂ) :
    D.jetNorm k r (c • s) x = ‖c‖ * D.jetNorm k r s x := by
  rw [jetNorm_def, jetNorm_def, reading_smul, jetNormAt_smul]


/-! ### The connection and `∂̄` read in the chart -/

/-- The **connection read in the chart**: at `z`, the real-linear map
`v ↦ df_z v - (ω₀(z, v) / 2) • (i f(z))` on `StdSpace ι`, for `f` the reading of `s` and `ω₀`
the standard symplectic form. It is `df_z + i A₀(z) f(z)`, with `A₀(z) v = -ω₀(z, v) / 2` the
model connection form of the rescaled unitary charts
(`SymplecticGeometry.RescaledUnitaryCharts.connectionForm_eq_model`). For `k₀ ≤ k`, at a point `z`
of the ball of radius `ρ₀ * √k` where `f` is differentiable, it is `powerConnection α k s` read in
the chart and the frame
(`SymplecticGeometry.RescaledUnitaryCharts.powerConnection_chart_symm_apply`). -/
noncomputable def connectionReading (k : ℕ) (x : M) (s : Π y, PowerBundle P k y)
    (z : StdSpace ι) : StdSpace ι →L[ℝ] ℂ :=
  fderiv ℝ (D.reading k x s) z -
    ((2⁻¹ : ℝ) • LinearMap.toContinuousLinearMap ((stdForm ι).toBilinForm z)).smulRight
      (Complex.I * D.reading k x s z)

theorem connectionReading_def (k : ℕ) (x : M) (s : Π y, PowerBundle P k y) (z : StdSpace ι) :
    D.connectionReading k x s z = fderiv ℝ (D.reading k x s) z -
      ((2⁻¹ : ℝ) • LinearMap.toContinuousLinearMap ((stdForm ι).toBilinForm z)).smulRight
        (Complex.I * D.reading k x s z) :=
  (rfl)

theorem connectionReading_apply (k : ℕ) (x : M) (s : Π y, PowerBundle P k y)
    (z v : StdSpace ι) :
    D.connectionReading k x s z v = fderiv ℝ (D.reading k x s) z v -
      (2⁻¹ * stdForm ι z v : ℝ) • (Complex.I * D.reading k x s z) := by
  rw [connectionReading_def, sub_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, LinearMap.coe_toContinuousLinearMap', smul_eq_mul]

/-- The connection read in the chart is additive on sections whose readings are differentiable
at `z`. -/
theorem connectionReading_add {k : ℕ} {x : M} {s t : Π y, PowerBundle P k y} {z : StdSpace ι}
    (hs : DifferentiableAt ℝ (D.reading k x s) z) (ht : DifferentiableAt ℝ (D.reading k x t) z) :
    D.connectionReading k x (s + t) z =
      D.connectionReading k x s z + D.connectionReading k x t z := by
  ext v
  simp only [connectionReading_apply, reading_add, fderiv_add hs ht, Pi.add_apply,
    add_apply, mul_add, smul_add]
  abel

@[simp]
theorem connectionReading_neg (k : ℕ) (x : M) (s : Π y, PowerBundle P k y) (z : StdSpace ι) :
    D.connectionReading k x (-s) z = -D.connectionReading k x s z := by
  ext v
  simp only [connectionReading_apply, reading_neg, fderiv_neg, Pi.neg_apply,
    neg_apply, mul_neg, smul_neg]
  abel

@[simp]
theorem connectionReading_smul (k : ℕ) (x : M) (c : ℂ) (s : Π y, PowerBundle P k y)
    (z : StdSpace ι) :
    D.connectionReading k x (c • s) z = c • D.connectionReading k x s z := by
  ext v
  simp only [connectionReading_apply, reading_smul, fderiv_const_smul_field, Pi.smul_apply,
    smul_apply, smul_eq_mul, Complex.real_smul]
  ring

@[simp]
theorem connectionReading_zero (k : ℕ) (x : M) (z : StdSpace ι) :
    D.connectionReading k x (0 : Π y, PowerBundle P k y) z = 0 := by
  ext v
  simp [connectionReading_apply]

/-- **The connection in a rescaled unitary chart.** For `k₀ ≤ k`, at a point `z` of the ball of
radius `ρ₀ * √k` where the reading of `s` is differentiable, `D_k s` at `(D.chart k x).symm z`,
evaluated on the image of `v` under the derivative of the inverse chart, is the class of the frame
and of the connection read in the chart, `D.connectionReading k x s z v`. -/
theorem powerConnection_chart_symm_apply [∀ y, Nonempty (P y)] (hα : IsCircleConnectionForm α)
    {k : ℕ} (hk : k₀ ≤ k) {x : M} {s : Π y, PowerBundle P k y} {z : StdSpace ι}
    (hz : z ∈ ball 0 (ρ₀ * √k)) (hs : DifferentiableAt ℝ (D.reading k x s) z) (v : StdSpace ι) :
    powerConnection α k s ((D.chart k x).symm z)
        (mfderiv 𝓘(ℝ, StdSpace ι) I (D.chart k x).symm z v) =
      AssociatedBundle.mk Circle (D.frame k x ((D.chart k x).symm z))
        (PowerModel.toComplex.symm (D.connectionReading k x s z v)) := by
  set ψ := D.chart k x
  have hzt : z ∈ ψ.target := D.ball_subset_target hk x hz
  have hψz : ψ (ψ.symm z) = z := ψ.right_inv hzt
  have hU : IsOpen (ψ.symm '' ball 0 (ρ₀ * √k)) :=
    ψ.toOpenPartialHomeomorph.isOpen_image_symm_of_subset_target isOpen_ball
      (D.ball_subset_target hk x)
  -- The coordinate of `s` in the frame, as a function on `M` with values in `PowerModel k`, is
  -- `g ∘ ψ`, with `g` the reading followed by the real-linear equivalence `L`.
  set L : ℂ ≃L[ℝ] PowerModel k :=
    (PowerModel.toComplex (k := k)).symm.toContinuousLinearEquiv.restrictScalars ℝ
  have hL (w : ℂ) : L w = PowerModel.toComplex.symm w :=
    ContinuousLinearEquiv.restrictScalars_apply ℝ _ w
  set g : StdSpace ι → PowerModel k := L ∘ D.reading k x s
  have hgw (w : StdSpace ι) : g w = L (D.reading k x s w) := rfl
  have hg : HasFDerivAt g ((L : ℂ →L[ℝ] PowerModel k).comp (fderiv ℝ (D.reading k x s) z)) z :=
    L.hasFDerivAt.comp z hs.hasFDerivAt
  have hψ : MDifferentiableAt I 𝓘(ℝ, StdSpace ι) ψ (ψ.symm z) :=
    ψ.mdifferentiableAt (by simp) (ψ.map_target hzt)
  have hgd : MDifferentiableAt 𝓘(ℝ, StdSpace ι) 𝓘(ℝ, PowerModel k) g z :=
    hg.differentiableAt.mdifferentiableAt
  have hf : MDifferentiableAt I 𝓘(ℝ, PowerModel k) (g ∘ ψ) (ψ.symm z) := (hψz ▸ hgd).comp _ hψ
  have hsf : ∀ y ∈ ψ.symm '' ball 0 (ρ₀ * √k),
      s y = AssociatedBundle.mk Circle (D.frame k x y) ((g ∘ ψ) y) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [Function.comp_apply, PartialDiffeomorph.symm_toPartialEquiv,
      ψ.right_inv (D.ball_subset_target hk x hw), hgw, hL]
    exact D.apply_chart_symm_eq_mk k x s w
  -- The connection form in the frame, read in the chart, is the model.
  have hc : (k : ℝ) * mpullback I (I.prod (𝓡 1))
      (fun y ↦ ManifoldTotalSpace.homeomorph Circle P ⟨y, D.frame k x y⟩) α.val (ψ.symm z)
        ![mfderiv 𝓘(ℝ, StdSpace ι) I ψ.symm z v] = -(2⁻¹ * stdForm ι z v) := by
    have h0 := D.connectionForm_eq_model hk x z hz v
    rw [mpullback_apply, (stdForm ι).radialPrimitive_apply z v] at h0
    convert h0 using 4
    rename_i i
    fin_cases i
    -- Both sides are `mfderiv … v`; `Matrix.cons_val_zero` does not apply, since `![v]` is typed
    -- in `StdSpace ι` and the other vector in a tangent space.
    rfl
  have hsm (c w : ℂ) : c • L w = L (c * w) := by
    rw [hL, hL, ← map_smul, smul_eq_mul]
  rw [powerConnection_apply_frame α k hα hU (D.contMDiffOn_frame hk x) ⟨z, hz, rfl⟩ hf hsf,
    mvfderiv_comp_apply_of_eq _ hgd hψ hψz, ψ.mfderiv_apply_mfderiv_symm_apply (by simp) hzt v,
    mvfderiv_eq_fderiv_apply g z (v : TangentSpace 𝓘(ℝ, StdSpace ι) z), hg.fderiv,
    Function.comp_apply, hψz, hgw, hsm,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, ← map_add, hL,
    connectionReading_apply]
  congr 2
  push_cast
  rw [mul_assoc Complex.I, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, hc, Complex.real_smul]
  push_cast
  ring

/-- The **`∂̄` reading of a section** `s` of `PowerBundle P k` at `z`: the complex-antilinear part
(Tau Ceti's `TauCeti.complexAntilinearPart`) of the connection read in the chart,
`D.connectionReading k x s z`, for the structure `J` pushed forward by the chart at `z` and
multiplication by `i` on `ℂ`. Where the reading of `s` is differentiable at `z`, the connection
read in the chart is `D_k s` read there
(`SymplecticGeometry.RescaledUnitaryCharts.powerConnection_chart_symm_apply`). -/
noncomputable def dbarReading (k : ℕ) (x : M) (s : Π y, PowerBundle P k y) (z : StdSpace ι) :
    StdSpace ι →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (complexAntilinearPart
    (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph z : StdSpace ι →ₗ[ℝ] StdSpace ι)
    (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
    (D.connectionReading k x s z : StdSpace ι →ₗ[ℝ] ℂ))

theorem dbarReading_def (k : ℕ) (x : M) (s : Π y, PowerBundle P k y) (z : StdSpace ι) :
    D.dbarReading k x s z = LinearMap.toContinuousLinearMap (complexAntilinearPart
      (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph z : StdSpace ι →ₗ[ℝ] StdSpace ι)
      (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
      (D.connectionReading k x s z : StdSpace ι →ₗ[ℝ] ℂ)) :=
  (rfl)

/-- The `∂̄` reading is additive on sections whose readings are differentiable at `z`. -/
theorem dbarReading_add {k : ℕ} {x : M} {s t : Π y, PowerBundle P k y} {z : StdSpace ι}
    (hs : DifferentiableAt ℝ (D.reading k x s) z) (ht : DifferentiableAt ℝ (D.reading k x t) z) :
    D.dbarReading k x (s + t) z = D.dbarReading k x s z + D.dbarReading k x t z := by
  rw [dbarReading_def, D.connectionReading_add hs ht, ContinuousLinearMap.toLinearMap_add,
    complexAntilinearPart_add, map_add, dbarReading_def, dbarReading_def]

@[simp]
theorem dbarReading_neg (k : ℕ) (x : M) (s : Π y, PowerBundle P k y) (z : StdSpace ι) :
    D.dbarReading k x (-s) z = -D.dbarReading k x s z := by
  rw [dbarReading_def, connectionReading_neg, ContinuousLinearMap.toLinearMap_neg,
    complexAntilinearPart_neg, map_neg, dbarReading_def]

@[simp]
theorem dbarReading_smul (k : ℕ) (x : M) (c : ℂ) (s : Π y, PowerBundle P k y) (z : StdSpace ι) :
    D.dbarReading k x (c • s) z = c • D.dbarReading k x s z := by
  ext v
  simp only [dbarReading_def, connectionReading_smul, LinearMap.coe_toContinuousLinearMap',
    complexAntilinearPart_apply, ContinuousLinearMap.coe_coe, smul_apply,
    AlmostComplexStructure.ofComplexModule_apply, smul_eq_mul, Complex.real_smul]
  ring

@[simp]
theorem dbarReading_zero (k : ℕ) (x : M) (z : StdSpace ι) :
    D.dbarReading k x (0 : Π y, PowerBundle P k y) z = 0 := by
  rw [dbarReading_def, connectionReading_zero, ContinuousLinearMap.toLinearMap_zero,
    complexAntilinearPart_zero, map_zero]

/-- The **`r`-jet norm of `∂̄ s` at `x`**: the jet norm `SymplecticGeometry.jetNormAt ℝ r` at `0`
of the `∂̄` reading of `s` in the chart and the frame centred at `x`, that is, the sum over the
orders `j ≤ r` of the norms of its `j`-th derivatives at `0`. -/
noncomputable def dbarJetNorm (k r : ℕ) (s : Π y, PowerBundle P k y) (x : M) : ℝ :=
  jetNormAt ℝ r (D.dbarReading k x s) 0

theorem dbarJetNorm_def (k r : ℕ) (s : Π y, PowerBundle P k y) (x : M) :
    D.dbarJetNorm k r s x = jetNormAt ℝ r (D.dbarReading k x s) 0 :=
  (rfl)

theorem dbarJetNorm_nonneg (k r : ℕ) (s : Π y, PowerBundle P k y) (x : M) :
    0 ≤ D.dbarJetNorm k r s x := by
  rw [dbarJetNorm_def]
  exact jetNormAt_nonneg _ _ _

/-- The jet norm of `∂̄ s` grows with the order. -/
theorem dbarJetNorm_mono (k : ℕ) (s : Π y, PowerBundle P k y) (x : M) :
    Monotone fun r ↦ D.dbarJetNorm k r s x := by
  simpa only [dbarJetNorm_def] using jetNormAt_mono (D.dbarReading k x s) 0

@[simp]
theorem dbarJetNorm_zero_fun (k r : ℕ) (x : M) :
    D.dbarJetNorm k r (0 : Π y, PowerBundle P k y) x = 0 := by
  rw [dbarJetNorm_def, funext (D.dbarReading_zero k x), ← Pi.zero_def, jetNormAt_zero_fun]

@[simp]
theorem dbarJetNorm_neg (k r : ℕ) (s : Π y, PowerBundle P k y) (x : M) :
    D.dbarJetNorm k r (-s) x = D.dbarJetNorm k r s x := by
  rw [dbarJetNorm_def, dbarJetNorm_def, funext (D.dbarReading_neg k x s), ← Pi.neg_def,
    jetNormAt_neg]

@[simp]
theorem dbarJetNorm_smul (k r : ℕ) (s : Π y, PowerBundle P k y) (x : M) (c : ℂ) :
    D.dbarJetNorm k r (c • s) x = ‖c‖ * D.dbarJetNorm k r s x := by
  rw [dbarJetNorm_def, dbarJetNorm_def, funext (D.dbarReading_smul k x c s), ← Pi.smul_def,
    jetNormAt_smul]

/-- The **triangle inequality for jet norms of `∂̄`**, for sections whose readings are
differentiable near `0` and whose `∂̄` readings are `C^r` at `0`. -/
theorem dbarJetNorm_add_le {k r : ℕ} {s t : Π y, PowerBundle P k y} {x : M}
    (hs : ∀ᶠ z in 𝓝 0, DifferentiableAt ℝ (D.reading k x s) z)
    (ht : ∀ᶠ z in 𝓝 0, DifferentiableAt ℝ (D.reading k x t) z)
    (hs' : ContDiffAt ℝ r (D.dbarReading k x s) 0) (ht' : ContDiffAt ℝ r (D.dbarReading k x t) 0) :
    D.dbarJetNorm k r (s + t) x ≤ D.dbarJetNorm k r s x + D.dbarJetNorm k r t x := by
  have h : D.dbarReading k x (s + t) =ᶠ[𝓝 0] D.dbarReading k x s + D.dbarReading k x t :=
    (hs.and ht).mono fun z hz ↦ D.dbarReading_add hz.1 hz.2
  rw [dbarJetNorm_def, jetNormAt_congr_of_eventuallyEq r h]
  exact jetNormAt_add_le hs' ht'

end RescaledUnitaryCharts

end SymplecticGeometry

end
