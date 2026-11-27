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
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.CauchyRiemann.OneZeroPart
public import TauCeti.LinearAlgebra.Complex.LinearPart
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import TauCeti.Analysis.Calculus.ContDiff.Differentiable
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Sections read in rescaled unitary charts, jet norms, and asymptotically holomorphic sequences

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
forward by the chart at `z` and multiplication by `i` on `ℂ`. For `k₀ ≤ k`, at a point `z` of the
ball of radius `ρ₀ * √k` where the reading of `s` is differentiable, it is the `(0,1)`-part
`J.zeroOnePart (powerConnection α k s)` read in the chart and the frame
(`SymplecticGeometry.RescaledUnitaryCharts.zeroOnePart_powerConnection_chart_symm_apply`), since
the derivative of the inverse chart carries the pushed-forward structure to `J`
(`TauCeti.SmoothAlmostComplexStructure.mfderiv_symm_apply_chartPushforward_apply`). Both readings
commute with multiplication by `c : ℂ`, and are additive on sections whose readings are
differentiable at `z`.
The `r`-jet norm of the `∂̄` reading, `D.dbarJetNorm k r s x`, is its jet norm at `0`; it is
nonnegative and monotone in `r`, vanishes on the zero section, is unchanged by negation, scales by
`‖c‖` under multiplication by `c : ℂ`, and satisfies the triangle inequality for sections whose
readings are differentiable near `0` and whose `∂̄` readings are `C^r` at `0`.

These are the chart norms by which the estimates on asymptotically holomorphic sequences of
sections are stated, in the rescaled metrics `k ω(·, J ·)`.

For a complex function `f` on the chart, `D.dbarFun k x f z` is the complex-antilinear part of
`fderiv ℝ f z` for the same structure. The product of a section `s` with a function `g : M → ℂ`
reads as the product of the readings, and its connection and `∂̄` readings obey the Leibniz rule
(`SymplecticGeometry.RescaledUnitaryCharts.dbarReading_fun_smul`). With the Leibniz bound
`SymplecticGeometry.jetNormAt_fun_smul_le`, this bounds the jet norms of `g • s` and of its `∂̄`
(`SymplecticGeometry.RescaledUnitaryCharts.jetNorm_fun_smul_le`,
`SymplecticGeometry.RescaledUnitaryCharts.dbarJetNorm_fun_smul_le`).

A sequence `s`, with `s k` a section of `PowerBundle P k`, is asymptotically holomorphic
(`SymplecticGeometry.RescaledUnitaryCharts.IsAsymptoticallyHolomorphic`) when, for large `k`, the
readings of `s k` and their `∂̄` readings are smooth at the centre of every chart, and, for each
order `r`, its `r`-jet norms are bounded and those of `∂̄` are `O(k ^ (-1/2))`, with one constant
for all large `k` and all centres. The smoothness is needed because `iteratedFDeriv` vanishes
where a function is not differentiable, so that the bounds alone would allow sections that are
nowhere continuous. The bounds are written with explicit constants and `∀ᶠ k in Filter.atTop`.
The zero sequence is asymptotically holomorphic; so are negatives, complex multiples, sums, and
products with functions `g k` whose readings are smooth and satisfy the same bounds. A sequence
is uniformly transverse with constant `η`
(`SymplecticGeometry.IsUniformlyTransverse`) when, for large `k` and every `x`, either `‖s k x‖`
or `(2π k)^(-1/2)` times the norm of the `(1,0)`-part of `powerConnection α k (s k) x` is at
least `η`, the norm of the tangent space being that of a Riemannian metric on `M`. A sequence
whose norm is at least `η` everywhere is uniformly transverse
(`SymplecticGeometry.IsUniformlyTransverse.of_le_norm`), and the notion is monotone in `η`.

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
multiplication by `i` on `ℂ`. For `k₀ ≤ k`, at a point `z` of the ball of radius `ρ₀ * √k` where
the reading of `s` is differentiable, it is the `(0,1)`-part `J.zeroOnePart` of `D_k s` read in
the chart and the frame
(`SymplecticGeometry.RescaledUnitaryCharts.zeroOnePart_powerConnection_chart_symm_apply`). -/
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

/-- **The `∂̄` reading is `∂̄ s` read in the chart.** For `k₀ ≤ k`, at a point `z` of the ball of
radius `ρ₀ * √k` where the reading of `s` is differentiable, the `(0,1)`-part `J.zeroOnePart` of
`D_k s` at `(D.chart k x).symm z`, evaluated on the image of `v` under the derivative of the
inverse chart, is the class of the frame and of the `∂̄` reading, `D.dbarReading k x s z v`. -/
theorem zeroOnePart_powerConnection_chart_symm_apply [∀ y, Nonempty (P y)]
    (hα : IsCircleConnectionForm α) {k : ℕ} (hk : k₀ ≤ k) {x : M} {s : Π y, PowerBundle P k y}
    {z : StdSpace ι} (hz : z ∈ ball 0 (ρ₀ * √k)) (hs : DifferentiableAt ℝ (D.reading k x s) z)
    (v : StdSpace ι) :
    J.zeroOnePart (powerConnection α k s ((D.chart k x).symm z))
        (mfderiv 𝓘(ℝ, StdSpace ι) I (D.chart k x).symm z v) =
      AssociatedBundle.mk Circle (D.frame k x ((D.chart k x).symm z))
        (PowerModel.toComplex.symm (D.dbarReading k x s z v)) := by
  have hJ := J.mfderiv_symm_apply_chartPushforward_apply (D.chart k x)
    (D.ball_subset_target hk x hz) v
  rw [J.zeroOnePart_apply, ← hJ, D.powerConnection_chart_symm_apply hα hk hz hs,
    D.powerConnection_chart_symm_apply hα hk hz hs, dbarReading_def,
    LinearMap.coe_toContinuousLinearMap', complexAntilinearPart_apply]
  simp only [← AssociatedBundle.mkLinearIsometryEquiv_apply (𝕜 := ℂ), ContinuousLinearMap.coe_coe,
    AlmostComplexStructure.ofComplexModule_apply, ← map_smul, ← map_add, smul_eq_mul,
    Complex.real_smul]
  rw [algebra_compatible_smul ℂ (2⁻¹ : ℝ), ← map_smul, ← map_smul, smul_eq_mul,
    Complex.coe_algebraMap]

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

/-- The `∂̄` reading is additive, as an equality of germs at `z₀`, on sections whose readings are
differentiable near `z₀`. -/
theorem dbarReading_add_eventuallyEq {k : ℕ} {x : M} {s t : Π y, PowerBundle P k y}
    {z₀ : StdSpace ι} (hs : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℝ (D.reading k x s) z)
    (ht : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℝ (D.reading k x t) z) :
    D.dbarReading k x (s + t) =ᶠ[𝓝 z₀] D.dbarReading k x s + D.dbarReading k x t :=
  (hs.and ht).mono fun _ hz ↦ D.dbarReading_add hz.1 hz.2

/-- The **triangle inequality for jet norms of `∂̄`**, for sections whose readings are
differentiable near `0` and whose `∂̄` readings are `C^r` at `0`. -/
theorem dbarJetNorm_add_le {k r : ℕ} {s t : Π y, PowerBundle P k y} {x : M}
    (hs : ∀ᶠ z in 𝓝 0, DifferentiableAt ℝ (D.reading k x s) z)
    (ht : ∀ᶠ z in 𝓝 0, DifferentiableAt ℝ (D.reading k x t) z)
    (hs' : ContDiffAt ℝ r (D.dbarReading k x s) 0) (ht' : ContDiffAt ℝ r (D.dbarReading k x t) 0) :
    D.dbarJetNorm k r (s + t) x ≤ D.dbarJetNorm k r s x + D.dbarJetNorm k r t x := by
  rw [dbarJetNorm_def, jetNormAt_congr_of_eventuallyEq r (D.dbarReading_add_eventuallyEq hs ht)]
  exact jetNormAt_add_le hs' ht'

/-! ### Smoothness and germs of the readings -/

/-- The connection read in the chart is `C^n` at `z` where the reading of the section is
`C^(n + 1)`. -/
theorem contDiffAt_connectionReading {n : ℕ∞} {k : ℕ} {x : M}
    {s : Π y, PowerBundle P k y} {z : StdSpace ι}
    (hs : ContDiffAt ℝ (n + 1) (D.reading k x s) z) :
    ContDiffAt ℝ n (D.connectionReading k x s) z := by
  let B : StdSpace ι →ₗ[ℝ] StdSpace ι →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ (stdForm ι).toBilinForm
  have hB : ContDiff ℝ n fun w ↦ (2⁻¹ : ℝ) • B w :=
    (LinearMap.toContinuousLinearMap B).contDiff.const_smul _
  have h := (hs.fderiv_right le_rfl).sub
    (hB.contDiffAt.smulRight ((contDiffAt_const (c := Complex.I)).mul (hs.of_le le_self_add)))
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w ↦ connectionReading_def ..)

/-- On a boundaryless manifold, the `∂̄` reading is `C^n` at a point `z` of the target of the
chart where the reading of the section is `C^(n + 1)`. -/
theorem contDiffAt_dbarReading [I.Boundaryless] {n : ℕ∞} {k : ℕ} {x : M}
    {s : Π y, PowerBundle P k y} {z : StdSpace ι} (hz : z ∈ (D.chart k x).target)
    (hs : ContDiffAt ℝ (n + 1) (D.reading k x s) z) :
    ContDiffAt ℝ n (D.dbarReading k x s) z := by
  have hJ : ContDiffAt ℝ n (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph) z :=
    ((J.contDiffOn_chartPushforward (D.chart k x).contMDiffOn
      (D.chart k x).symm.contMDiffOn).contDiffAt
      ((D.chart k x).open_target.mem_nhds hz)).of_le (by exact_mod_cast le_top)
  have hC := D.contDiffAt_connectionReading hs
  have h := (hC.add ((hC.clm_comp hJ).const_smul Complex.I)).const_smul (2⁻¹ : ℝ)
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w ↦ ?_)
  ext v
  simp [dbarReading_def, complexAntilinearPart_apply,
    AlmostComplexStructure.ofComplexModule_apply]

/-- The connection read in the chart at `z` depends only on the germ at `z` of the reading. -/
theorem connectionReading_congr_of_eventuallyEq {k : ℕ} {x : M} {s t : Π y, PowerBundle P k y}
    {z : StdSpace ι} (h : D.reading k x s =ᶠ[𝓝 z] D.reading k x t) :
    D.connectionReading k x s z = D.connectionReading k x t z := by
  rw [connectionReading_def, connectionReading_def, h.fderiv_eq, h.eq_of_nhds]

/-- The `∂̄` reading at `z` depends only on the germ at `z` of the reading. -/
theorem dbarReading_congr_of_eventuallyEq {k : ℕ} {x : M} {s t : Π y, PowerBundle P k y}
    {z : StdSpace ι} (h : D.reading k x s =ᶠ[𝓝 z] D.reading k x t) :
    D.dbarReading k x s z = D.dbarReading k x t z := by
  rw [dbarReading_def, dbarReading_def, D.connectionReading_congr_of_eventuallyEq h]

/-- Sections whose readings have the same germ at `z` have `∂̄` readings with the same germ
at `z`. -/
theorem dbarReading_eventuallyEq {k : ℕ} {x : M} {s t : Π y, PowerBundle P k y}
    {z : StdSpace ι} (h : D.reading k x s =ᶠ[𝓝 z] D.reading k x t) :
    D.dbarReading k x s =ᶠ[𝓝 z] D.dbarReading k x t :=
  h.eventually_nhds.mono fun _ hw ↦ D.dbarReading_congr_of_eventuallyEq hw

/-! ### Products with complex functions -/

/-- The **`∂̄` of a complex function `f` on the chart** at `z`: the complex-antilinear part
(Tau Ceti's `TauCeti.complexAntilinearPart`) of its derivative `fderiv ℝ f z`, for the structure
`J` pushed forward by the chart `D.chart k x` at `z` and multiplication by `i` on `ℂ`. -/
noncomputable def dbarFun (k : ℕ) (x : M) (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    StdSpace ι →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (complexAntilinearPart
    (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph z : StdSpace ι →ₗ[ℝ] StdSpace ι)
    (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap (fderiv ℝ f z : StdSpace ι →ₗ[ℝ] ℂ))

omit [∀ x, MulAction Circleᵐᵒᵖ (P x)] [PrincipalBundle Circle P] in
theorem dbarFun_def (k : ℕ) (x : M) (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    D.dbarFun k x f z = LinearMap.toContinuousLinearMap (complexAntilinearPart
      (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph z : StdSpace ι →ₗ[ℝ] StdSpace ι)
      (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
      (fderiv ℝ f z : StdSpace ι →ₗ[ℝ] ℂ)) :=
  (rfl)

omit [∀ x, MulAction Circleᵐᵒᵖ (P x)] [PrincipalBundle Circle P] in
/-- The `∂̄` of a complex function `f` on the chart, applied to `v`, is
`½ (df_z v + i df_z (J_z v))`, for `J_z` the structure `J` pushed forward by the chart at `z`. -/
theorem dbarFun_apply (k : ℕ) (x : M) (f : StdSpace ι → ℂ) (z v : StdSpace ι) :
    D.dbarFun k x f z v = (2⁻¹ : ℝ) • (fderiv ℝ f z v + Complex.I * fderiv ℝ f z
      ((J.chartPushforward (D.chart k x).toOpenPartialHomeomorph z : StdSpace ι →ₗ[ℝ] StdSpace ι)
        v)) := by
  simp only [dbarFun_def, LinearMap.coe_toContinuousLinearMap', complexAntilinearPart_apply,
    ContinuousLinearMap.coe_coe, AlmostComplexStructure.ofComplexModule_apply, smul_eq_mul]

omit [∀ x, MulAction Circleᵐᵒᵖ (P x)] [PrincipalBundle Circle P] in
/-- `∂̄` is additive on functions that are differentiable at `z`. -/
theorem dbarFun_add {k : ℕ} {x : M} {f g : StdSpace ι → ℂ} {z : StdSpace ι}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    D.dbarFun k x (f + g) z = D.dbarFun k x f z + D.dbarFun k x g z := by
  rw [dbarFun_def, fderiv_add hf hg, ContinuousLinearMap.toLinearMap_add,
    complexAntilinearPart_add, map_add, dbarFun_def, dbarFun_def]

omit [∀ x, MulAction Circleᵐᵒᵖ (P x)] [PrincipalBundle Circle P] in
/-- `∂̄` commutes with multiplication by a complex constant. -/
@[simp]
theorem dbarFun_const_smul (k : ℕ) (x : M) (c : ℂ) (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    D.dbarFun k x (c • f) z = c • D.dbarFun k x f z := by
  ext v
  simp only [dbarFun_apply, fderiv_const_smul_field c, Pi.smul_apply, smul_apply,
    smul_eq_mul, Complex.real_smul]
  ring

omit [∀ x, MulAction Circleᵐᵒᵖ (P x)] [PrincipalBundle Circle P] in
@[simp]
theorem dbarFun_zero (k : ℕ) (x : M) (z : StdSpace ι) :
    D.dbarFun k x (0 : StdSpace ι → ℂ) z = 0 := by
  ext v
  simp [dbarFun_apply]

/-- The reading of the product of a section `s` with a function `g : M → ℂ` is the product of
the reading of `s` with `g` read in the chart. -/
@[simp]
theorem reading_fun_smul (k : ℕ) (x : M) (g : M → ℂ) (s : Π y, PowerBundle P k y) :
    D.reading k x (fun y ↦ g y • s y) =
      fun z ↦ g ((D.chart k x).symm z) • D.reading k x s z := by
  ext z
  simp only [reading_def, map_smul]

/-- The **Leibniz rule for the connection read in the chart**: for `G` the function `g` read in
the chart and `f` the reading of `s`, both differentiable at `z`, the connection reading of
`g • s` at `z` is `G z • (df_z + i A₀(z) f(z)) + f z • dG_z`. -/
theorem connectionReading_fun_smul {k : ℕ} {x : M} {g : M → ℂ} {s : Π y, PowerBundle P k y}
    {z : StdSpace ι} (hg : DifferentiableAt ℝ (fun w ↦ g ((D.chart k x).symm w)) z)
    (hs : DifferentiableAt ℝ (D.reading k x s) z) :
    D.connectionReading k x (fun y ↦ g y • s y) z =
      g ((D.chart k x).symm z) • D.connectionReading k x s z +
        D.reading k x s z • fderiv ℝ (fun w ↦ g ((D.chart k x).symm w)) z := by
  ext v
  simp only [connectionReading_apply, reading_fun_smul, smul_eq_mul, fderiv_fun_mul hg hs,
    add_apply, smul_apply, Complex.real_smul]
  ring

/-- The **Leibniz rule for `∂̄` read in the chart**: for `G` the function `g` read in the chart
and `f` the reading of `s`, both differentiable at `z`, the `∂̄` reading of `g • s` at `z` is
`G z • ∂̄ f (z) + f z • ∂̄ G (z)`. -/
theorem dbarReading_fun_smul {k : ℕ} {x : M} {g : M → ℂ} {s : Π y, PowerBundle P k y}
    {z : StdSpace ι} (hg : DifferentiableAt ℝ (fun w ↦ g ((D.chart k x).symm w)) z)
    (hs : DifferentiableAt ℝ (D.reading k x s) z) :
    D.dbarReading k x (fun y ↦ g y • s y) z =
      g ((D.chart k x).symm z) • D.dbarReading k x s z +
        D.reading k x s z • D.dbarFun k x (fun w ↦ g ((D.chart k x).symm w)) z := by
  ext v
  simp only [dbarReading_def, dbarFun_def, D.connectionReading_fun_smul hg hs,
    LinearMap.coe_toContinuousLinearMap', complexAntilinearPart_apply, ContinuousLinearMap.coe_coe,
    add_apply, smul_apply, AlmostComplexStructure.ofComplexModule_apply, smul_eq_mul,
    Complex.real_smul, map_add]
  ring

/-- The Leibniz rule for `∂̄` read in the chart, as an equality of germs at `z₀`, where `g` read
in the chart and the reading of `s` are differentiable near `z₀`. -/
theorem dbarReading_fun_smul_eventuallyEq {k : ℕ} {x : M} {g : M → ℂ}
    {s : Π y, PowerBundle P k y} {z₀ : StdSpace ι}
    (hg : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℝ (fun w ↦ g ((D.chart k x).symm w)) z)
    (hs : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℝ (D.reading k x s) z) :
    D.dbarReading k x (fun y ↦ g y • s y) =ᶠ[𝓝 z₀]
      fun z ↦ g ((D.chart k x).symm z) • D.dbarReading k x s z +
        D.reading k x s z • D.dbarFun k x (fun w ↦ g ((D.chart k x).symm w)) z :=
  (hg.and hs).mono fun _ hz ↦ D.dbarReading_fun_smul hz.1 hz.2

/-- The **Leibniz bound for jet norms of sections**: for `G` the function `g` read in the chart
centred at `x`, if `G` and the reading of `s` are `C^r` at `0`, the `r`-jet norm of `g • s` at
`x` is at most `2 ^ r` times the product of the `r`-jet norms of `G` at `0` and of `s`
at `x`. -/
theorem jetNorm_fun_smul_le {k r : ℕ} {g : M → ℂ} {s : Π y, PowerBundle P k y} {x : M}
    (hg : ContDiffAt ℝ r (fun z ↦ g ((D.chart k x).symm z)) 0)
    (hs : ContDiffAt ℝ r (D.reading k x s) 0) :
    D.jetNorm k r (fun y ↦ g y • s y) x ≤
      2 ^ r * jetNormAt ℝ r (fun z ↦ g ((D.chart k x).symm z)) 0 * D.jetNorm k r s x := by
  rw [jetNorm_def, reading_fun_smul, jetNorm_def]
  exact jetNormAt_fun_smul_le hg hs

/-- The **Leibniz bound for jet norms of `∂̄`**: for `G` the function `g` read in the chart
centred at `x`, if `G` and the reading of `s` are differentiable near `0`, and `G`, the reading
of `s`, `∂̄ G` and the `∂̄` reading of `s` are `C^r` at `0`, then the `r`-jet norm of
`∂̄ (g • s)` at `x` is at most `2 ^ r` times
`J(G) * J(∂̄ s) + J(s) * J(∂̄ G)`, each `J` an `r`-jet norm at `0` or at `x`. -/
theorem dbarJetNorm_fun_smul_le {k r : ℕ} {g : M → ℂ} {s : Π y, PowerBundle P k y} {x : M}
    (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℝ (fun w ↦ g ((D.chart k x).symm w)) z)
    (hs : ∀ᶠ z in 𝓝 0, DifferentiableAt ℝ (D.reading k x s) z)
    (hg' : ContDiffAt ℝ r (fun z ↦ g ((D.chart k x).symm z)) 0)
    (hs' : ContDiffAt ℝ r (D.reading k x s) 0)
    (hdg : ContDiffAt ℝ r (D.dbarFun k x fun z ↦ g ((D.chart k x).symm z)) 0)
    (hds : ContDiffAt ℝ r (D.dbarReading k x s) 0) :
    D.dbarJetNorm k r (fun y ↦ g y • s y) x ≤
      2 ^ r * (jetNormAt ℝ r (fun z ↦ g ((D.chart k x).symm z)) 0 *
          D.dbarJetNorm k r s x +
        D.jetNorm k r s x * jetNormAt ℝ r (D.dbarFun k x fun z ↦ g ((D.chart k x).symm z)) 0) := by
  rw [dbarJetNorm_def, jetNormAt_congr_of_eventuallyEq r
    (D.dbarReading_fun_smul_eventuallyEq hg hs)]
  refine (jetNormAt_add_le (hg'.smul hds) (hs'.smul hdg)).trans ?_
  refine (add_le_add (jetNormAt_fun_smul_le hg' hds) (jetNormAt_fun_smul_le hs' hdg)).trans ?_
  rw [← dbarJetNorm_def, ← jetNorm_def]
  exact le_of_eq (by ring)

/-! ### Asymptotically holomorphic sequences -/

/-- A sequence `s` of sections, `s k` of `PowerBundle P k`, is **asymptotically holomorphic**
for the rescaled unitary charts `D` when, for `k` large, the reading of `s k` and its `∂̄`
reading are smooth at the centre of the chart at every point `x`, and, for every order `r`,
there is a constant `C` such that, for `k` large and every point `x`, the `r`-jet norm of `s k`
at `x` is at most `C` and that of `∂̄ (s k)` at most `C * k ^ (-1/2)`. -/
def IsAsymptoticallyHolomorphic (s : ∀ k : ℕ, Π y, PowerBundle P k y) : Prop :=
  (∀ᶠ k in Filter.atTop, ∀ x : M,
    ContDiffAt ℝ ∞ (D.reading k x (s k)) 0 ∧ ContDiffAt ℝ ∞ (D.dbarReading k x (s k)) 0) ∧
  ∀ r : ℕ, ∃ C : ℝ, ∀ᶠ k in Filter.atTop, ∀ x : M,
    D.jetNorm k r (s k) x ≤ C ∧ D.dbarJetNorm k r (s k) x ≤ C * (k : ℝ) ^ (-1 / 2 : ℝ)

theorem isAsymptoticallyHolomorphic_def (s : ∀ k : ℕ, Π y, PowerBundle P k y) :
    D.IsAsymptoticallyHolomorphic s ↔
      (∀ᶠ k in Filter.atTop, ∀ x : M,
        ContDiffAt ℝ ∞ (D.reading k x (s k)) 0 ∧ ContDiffAt ℝ ∞ (D.dbarReading k x (s k)) 0) ∧
      ∀ r : ℕ, ∃ C : ℝ, ∀ᶠ k in Filter.atTop, ∀ x : M,
        D.jetNorm k r (s k) x ≤ C ∧ D.dbarJetNorm k r (s k) x ≤ C * (k : ℝ) ^ (-1 / 2 : ℝ) :=
  Iff.rfl

/-- The zero sequence of sections is asymptotically holomorphic. -/
theorem isAsymptoticallyHolomorphic_zero :
    D.IsAsymptoticallyHolomorphic fun k ↦ (0 : Π y, PowerBundle P k y) := by
  refine ⟨Filter.Eventually.of_forall fun k x ↦ ?_, fun _ ↦
    ⟨0, Filter.Eventually.of_forall fun _ _ ↦ by simp⟩⟩
  rw [reading_zero, funext (D.dbarReading_zero k x)]
  exact ⟨contDiffAt_const, contDiffAt_const⟩

/-- The negative of an asymptotically holomorphic sequence is asymptotically holomorphic. -/
theorem IsAsymptoticallyHolomorphic.neg {s : ∀ k : ℕ, Π y, PowerBundle P k y}
    (hs : D.IsAsymptoticallyHolomorphic s) : D.IsAsymptoticallyHolomorphic fun k ↦ -s k := by
  refine ⟨hs.1.mono fun k hk x ↦ ?_, fun r ↦ ?_⟩
  · rw [reading_neg, funext (D.dbarReading_neg k x (s k))]
    exact ⟨(hk x).1.neg, (hk x).2.neg⟩
  · obtain ⟨C, hC⟩ := hs.2 r
    exact ⟨C, hC.mono fun k hk x ↦ by simpa using hk x⟩

/-- A complex multiple of an asymptotically holomorphic sequence is asymptotically
holomorphic. -/
theorem IsAsymptoticallyHolomorphic.const_smul {s : ∀ k : ℕ, Π y, PowerBundle P k y}
    (hs : D.IsAsymptoticallyHolomorphic s) (c : ℂ) :
    D.IsAsymptoticallyHolomorphic fun k ↦ c • s k := by
  refine ⟨hs.1.mono fun k hk x ↦ ?_, fun r ↦ ?_⟩
  · rw [reading_smul, funext (D.dbarReading_smul k x c (s k))]
    exact ⟨(hk x).1.const_smul c, (hk x).2.const_smul c⟩
  · obtain ⟨C, hC⟩ := hs.2 r
    refine ⟨‖c‖ * C, hC.mono fun k hk x ↦ ?_⟩
    rw [jetNorm_smul, dbarJetNorm_smul, mul_assoc]
    exact ⟨by gcongr; exact (hk x).1, by gcongr; exact (hk x).2⟩

/-- The **sum of asymptotically holomorphic sequences** is asymptotically holomorphic. -/
theorem IsAsymptoticallyHolomorphic.add {s t : ∀ k : ℕ, Π y, PowerBundle P k y}
    (hs : D.IsAsymptoticallyHolomorphic s) (ht : D.IsAsymptoticallyHolomorphic t) :
    D.IsAsymptoticallyHolomorphic fun k ↦ s k + t k := by
  refine ⟨(hs.1.and ht.1).mono fun k ⟨hks, hkt⟩ x ↦ ?_, fun r ↦ ?_⟩
  · obtain ⟨hf, hdf⟩ := hks x
    obtain ⟨hh, hdh⟩ := hkt x
    rw [reading_add]
    exact ⟨hf.add hh, (hdf.add hdh).congr_of_eventuallyEq (D.dbarReading_add_eventuallyEq
      (hf.eventually_differentiableAt (by exact_mod_cast le_top))
      (hh.eventually_differentiableAt (by exact_mod_cast le_top)))⟩
  obtain ⟨Cs, hCs⟩ := hs.2 r
  obtain ⟨Ct, hCt⟩ := ht.2 r
  refine ⟨Cs + Ct,
    (((hCs.and hCt).and hs.1).and ht.1).mono fun k ⟨⟨⟨hks, hkt⟩, hks'⟩, hkt'⟩ x ↦ ?_⟩
  obtain ⟨hf, hdf⟩ := hks' x
  obtain ⟨hh, hdh⟩ := hkt' x
  have hr : (r : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  constructor
  · exact (D.jetNorm_add_le (hf.of_le hr) (hh.of_le hr)).trans (add_le_add (hks x).1 (hkt x).1)
  · refine (D.dbarJetNorm_add_le ?_ ?_ (hdf.of_le hr) (hdh.of_le hr)).trans ?_
    · exact hf.eventually_differentiableAt (by exact_mod_cast le_top)
    · exact hh.eventually_differentiableAt (by exact_mod_cast le_top)
    · rw [add_mul]
      exact add_le_add (hks x).2 (hkt x).2

/-- The **product of an asymptotically holomorphic sequence with a sequence of bounded
functions**: let `g k : M → ℂ` be functions whose readings `G = g k ∘ (D.chart k x).symm` and
their `∂̄` are, for `k` large, smooth at `0` for every `x`, and have, for every order `r` and
uniformly in `x` for `k` large, `r`-jet norms at `0` at most a constant and `∂̄` jet norms at `0`
at most a constant times `k ^ (-1/2)`. If `s` is asymptotically holomorphic, then
`fun k y ↦ g k y • s k y` is asymptotically holomorphic. -/
theorem IsAsymptoticallyHolomorphic.fun_smul {s : ∀ k : ℕ, Π y, PowerBundle P k y}
    {g : ℕ → M → ℂ} (hs : D.IsAsymptoticallyHolomorphic s)
    (hg : ∀ r : ℕ, ∃ C : ℝ, ∀ᶠ k in Filter.atTop, ∀ x : M,
      jetNormAt ℝ r (fun z ↦ g k ((D.chart k x).symm z)) 0 ≤ C ∧
        jetNormAt ℝ r (D.dbarFun k x fun z ↦ g k ((D.chart k x).symm z)) 0 ≤
          C * (k : ℝ) ^ (-1 / 2 : ℝ))
    (hg' : ∀ᶠ k in Filter.atTop, ∀ x : M,
      ContDiffAt ℝ ∞ (fun z ↦ g k ((D.chart k x).symm z)) 0 ∧
        ContDiffAt ℝ ∞ (D.dbarFun k x fun z ↦ g k ((D.chart k x).symm z)) 0) :
    D.IsAsymptoticallyHolomorphic fun k y ↦ g k y • s k y := by
  refine ⟨(hs.1.and hg').mono fun k ⟨hks, hkg⟩ x ↦ ?_, fun r ↦ ?_⟩
  · obtain ⟨hf, hdf⟩ := hks x
    obtain ⟨hG, hdG⟩ := hkg x
    rw [reading_fun_smul]
    refine ⟨hG.smul hf, ((hG.smul hdf).add (hf.smul hdG)).congr_of_eventuallyEq
      (D.dbarReading_fun_smul_eventuallyEq ?_ ?_)⟩
    · exact hG.eventually_differentiableAt (by exact_mod_cast le_top)
    · exact hf.eventually_differentiableAt (by exact_mod_cast le_top)
  obtain ⟨Cs, hCs⟩ := hs.2 r
  obtain ⟨Cg, hCg⟩ := hg r
  set c : ℝ := 2 ^ r
  have : 0 ≤ c := by positivity
  refine ⟨2 * c * Cg * Cs,
    (((hCs.and hCg).and hs.1).and hg').mono fun k ⟨⟨⟨hks, hkg⟩, hks'⟩, hkg'⟩ x ↦ ?_⟩
  obtain ⟨hf, hdf⟩ := hks' x
  obtain ⟨hG, hdG⟩ := hkg' x
  obtain ⟨hJf, hJdf⟩ := hks x
  obtain ⟨hJG, hJdG⟩ := hkg x
  have hr : (r : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have : 0 ≤ (k : ℝ) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg k) _
  have hCs₀ : 0 ≤ Cs := (D.jetNorm_nonneg k r (s k) x).trans hJf
  have hCg₀ : 0 ≤ Cg := (jetNormAt_nonneg r _ 0).trans hJG
  have := D.dbarJetNorm_nonneg k r (s k) x
  have := D.jetNorm_nonneg k r (s k) x
  have := jetNormAt_nonneg (𝕜 := ℝ) r (D.dbarFun k x fun z ↦ g k ((D.chart k x).symm z)) 0
  have := jetNormAt_nonneg (𝕜 := ℝ) r (fun z ↦ g k ((D.chart k x).symm z)) 0
  constructor
  · refine (D.jetNorm_fun_smul_le (hG.of_le hr) (hf.of_le hr)).trans ?_
    calc c * jetNormAt ℝ r (fun z ↦ g k ((D.chart k x).symm z)) 0 * D.jetNorm k r (s k) x
        ≤ c * Cg * Cs := by gcongr
      _ ≤ 2 * c * Cg * Cs := by
        have : 0 ≤ c * Cg * Cs := by positivity
        linarith
  · refine (D.dbarJetNorm_fun_smul_le
      (hG.eventually_differentiableAt (by exact_mod_cast le_top))
      (hf.eventually_differentiableAt (by exact_mod_cast le_top))
      (hG.of_le hr) (hf.of_le hr) (hdG.of_le hr) (hdf.of_le hr)).trans ?_
    calc c * (jetNormAt ℝ r (fun z ↦ g k ((D.chart k x).symm z)) 0 * D.dbarJetNorm k r (s k) x +
          D.jetNorm k r (s k) x *
            jetNormAt ℝ r (D.dbarFun k x fun z ↦ g k ((D.chart k x).symm z)) 0)
        ≤ c * (Cg * (Cs * (k : ℝ) ^ (-1 / 2 : ℝ)) + Cs * (Cg * (k : ℝ) ^ (-1 / 2 : ℝ))) := by
          gcongr
      _ = 2 * c * Cg * Cs * (k : ℝ) ^ (-1 / 2 : ℝ) := by ring

end RescaledUnitaryCharts

/-! ### Uniformly transverse sequences -/

section Transverse

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {P : M → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ x, TopologicalSpace (P x)]
  [FiberBundle Circle P] [∀ x, Nonempty (P x)] [∀ x, MulAction Circleᵐᵒᵖ (P x)]
  [PrincipalBundle Circle P] [ContMDiffFiberBundle ∞ Circle P I (𝓡 1)]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- A sequence `s` of sections, `s k` of `PowerBundle P k`, is **uniformly transverse** with
constant `η` for the almost complex structure `J` and the connection form `α` when, for `k` large
and every point `x`, `η ≤ max ‖s k x‖ ((2π k)^(-1/2) ‖∂ (s k) x‖)`, where `∂ (s k) x` is the
`(1,0)`-part `J.oneZeroPart` of the covariant derivative `powerConnection α k (s k) x`, and its
norm is the operator norm for the Riemannian metric on `M` and the norm of the fibre. -/
def IsUniformlyTransverse (J : SmoothAlmostComplexStructure I M)
    (α : SmoothForm (I.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1) (η : ℝ)
    (s : ∀ k : ℕ, Π y, PowerBundle P k y) : Prop :=
  ∀ᶠ k in Filter.atTop, ∀ x : M, η ≤ max ‖s k x‖
    ((2 * Real.pi * k) ^ (-1 / 2 : ℝ) * ‖J.oneZeroPart (powerConnection α k (s k) x)‖)

variable {J : SmoothAlmostComplexStructure I M}
  {α : SmoothForm (I.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1}

theorem isUniformlyTransverse_def {η : ℝ} {s : ∀ k : ℕ, Π y, PowerBundle P k y} :
    IsUniformlyTransverse J α η s ↔ ∀ᶠ k in Filter.atTop, ∀ x : M, η ≤ max ‖s k x‖
      ((2 * Real.pi * k) ^ (-1 / 2 : ℝ) * ‖J.oneZeroPart (powerConnection α k (s k) x)‖) :=
  Iff.rfl

/-- A sequence whose norm is at least `η` everywhere, for `k` large, is uniformly transverse with
constant `η`. -/
theorem IsUniformlyTransverse.of_le_norm {η : ℝ} {s : ∀ k : ℕ, Π y, PowerBundle P k y}
    (hs : ∀ᶠ k in Filter.atTop, ∀ x : M, η ≤ ‖s k x‖) : IsUniformlyTransverse J α η s :=
  hs.mono fun _ hk x ↦ le_max_of_le_left (hk x)

/-- Uniform transversality with a constant `η` gives it with every smaller constant. -/
theorem IsUniformlyTransverse.mono {η η' : ℝ} {s : ∀ k : ℕ, Π y, PowerBundle P k y}
    (hs : IsUniformlyTransverse J α η s) (hη : η' ≤ η) : IsUniformlyTransverse J α η' s :=
  Filter.Eventually.mono hs fun _ hk x ↦ hη.trans (hk x)

end Transverse

end SymplecticGeometry

end
