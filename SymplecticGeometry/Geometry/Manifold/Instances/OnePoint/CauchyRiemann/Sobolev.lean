/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Complex.Beltrami.ZeroOnePart
public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.Basic
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.CauchyRiemann.ZeroOneForm
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Sobolev.Hilbert
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Sobolev.CovariantDerivative
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Sobolev.SmoothHomMul
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm
import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.SMulLp
import SymplecticGeometry.Analysis.Complex.Wirtinger.Beurling.Estimate
import SymplecticGeometry.Analysis.Complex.Wirtinger.Commutator
import SymplecticGeometry.Analysis.Normed.Operator.ComplexLinearPart
import SymplecticGeometry.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.ZeroOnePart
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Tames
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# The Cauchy–Riemann operators `D_J` of `𝒪(1)` on Sobolev sections

Let `L = 𝒪(1)` be the line bundle `OnePoint.twistCore 1` on the sphere `OnePoint ℂ`, with the
connection `∇ = twistOneConnection` and, for an almost complex structure `J`, the operator
`D_J s = J.zeroOnePart (∇ s)` of
`SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.Basic`. This file
extends `D_J` to Sobolev sections, as a bounded operator

`W^{k+1,2}(L) → W^{k,2}(Λ^{0,1} ⊗ L)`

for every order `k`, where the spaces are Tau Ceti's `TauCeti.SobolevSection` and
`TauCeti.zeroOneSobolevSections` over one finite bundle atlas `twistCoreAtlas 1` of `L`, chosen
once, and `Λ^{0,1}` is taken for the standard complex structure `i` of the sphere.

The operator is the composite `π^{0,1}_i ∘ Φ_J ∘ ∇` of three bounded operators:

* the Sobolev realization `IsCovariantDerivativeOn.sobolevL` of the connection, from
  `W^{k+1,2}(L)` to `W^{k,2}` of `L`-valued one-forms;
* the action `TauCeti.SobolevSection.contMDiffHomMulL` of the smooth field
  `Φ_J = TauCeti.SmoothAlmostComplexStructure.zeroOnePartL J` of `(0,1)`-projections for `J`,
  a smooth section of the endomorphism bundle of the `L`-valued one-forms
  (`TauCeti.SmoothAlmostComplexStructure.contMDiff_zeroOnePartL`);
* Tau Ceti's projection `TauCeti.zeroOnePartSobolevL` onto the `(0,1)`-forms for `i`.

On the Sobolev section of a `C^{k+1}` section `s`, the chart data of the operator agree almost
everywhere, in every chart, with the chart readings of the `(0,1)`-part for `i` of `D_J s`
(`SymplecticGeometry.chartValueL_twistOneDelBarSobolev_ofContMDiffSection_ae_coord`). The last
projection loses nothing when a two-form tames both `J` and `i`: then the `(0,1)`-projection
for `i` is injective on the `(0,1)`-forms for `J` at every point
(`TauCeti.SmoothAlmostComplexStructure.injOn_zeroOnePart_of_tames`).

Only the middle factor depends on `J`. So `D_J` is continuous in `J`, from the `C^∞` topology
`TauCeti.SmoothAlmostComplexStructure.frameTopology` to the operator norm
(`SymplecticGeometry.continuous_twistOneDelBarSobolev`): the section of `(0,1)`-projections is
continuous in `J` (`TauCeti.SmoothAlmostComplexStructure.continuous_zeroOnePartSection`), and
the action of a smooth hom section on Sobolev sections is continuous in the section for the
frame topology (`TauCeti.SobolevSection.tendsto_contMDiffHomMulL_of_tendsto`).

Tau Ceti's realization `TauCeti.IsRealCauchyRiemannOperator.sobolevSuccL`
(`Geometry/Manifold/VectorBundle/Sobolev/CauchyRiemann/HigherOrder.lean`) is not used: it
realizes an operator that is Cauchy–Riemann for the complex structure of the charts, which
`π^{0,1}_i ∘ D_J` is not in general.

## Main definitions and results

* `SymplecticGeometry.twistCoreAtlas n`: the finite bundle atlas of `𝒪(n)`.
* `SymplecticGeometry.twistOneDelBarSobolev J k`: the operator `D_J` from `W^{k+1,2}` sections of
  `𝒪(1)` to `W^{k,2}` `(0,1)`-forms with values in `𝒪(1)`.
* `SymplecticGeometry.chartValueL_twistOneDelBarSobolev_ofContMDiffSection_ae_coord`: on a
  `C^{k+1}` section `s`, its chart data agree almost everywhere with the chart readings of the
  `(0,1)`-part for `i` of `D_J s`.
* `SymplecticGeometry.continuous_twistOneDelBarSobolev`: `D_J` depends continuously on `J`;
  `SymplecticGeometry.continuous_twistOneDelBarSobolev_tames` restricts this to the structures
  tamed by a two-form.
* `SymplecticGeometry.exists_coord_zeroOnePart_twistOneDelBar_apply`: for `J` tamed together
  with `i` by a two-form, in each chart of a finite bundle atlas of `𝒪(1)` the reading of the
  `(0,1)`-part for `i` of `D_J s` is the complex-antilinear map whose value at `1` is
  `c₂ (∂bar u + μ ∂u) + Z u`, for the reading `u` of `s`, with `c₂`, `μ`, `Z` smooth near the
  closed chart image, `c₂ ≠ 0` and `‖μ‖ ≤ m < 1` there. The coefficient `μ` is the negative of
  the Beltrami coefficient of `J` in the chart, so the bound is `norm_beltrami_lt_one_of_tames`
  and compactness. The reading of the two `(0,1)`-projections is
  `TauCeti.FiniteBundleAtlas.coord_tangentHom_zeroOnePart_zeroOnePart`, the pointwise algebra is
  in `SymplecticGeometry.Analysis.Complex.Beltrami.ZeroOnePart`, and `Z` comes from the
  zeroth-order term of the connection, which is complex linear
  (`IsCovariantDerivativeOn.chartZeroOrder_apply_smul`, `twistOneConnection_const_smul`).
* `SymplecticGeometry.chartZeroOrder_twistOneConnection_apply`: that zeroth-order term in a chart
  is `c ↦ c • Γ 1`, and `Γ 1` is smooth
  (`SymplecticGeometry.contDiffOn_chartZeroOrder_twistOneConnection_apply_one`).
* `SymplecticGeometry.exists_sum_eLpNorm_iteratedFDeriv_coord_smul_le`: the estimate of order `k`
  in one chart. For `χ` smooth with support in the domain of chart `i`, the `L²` norms on the
  chart image of the derivatives of order at most `k + 1` of the reading of `χ s` are bounded,
  uniformly in the smooth sections `s`, by those of order at most `k` of the reading of the
  `(0,1)`-part for `i` of `D_J s` and of the reading of `s`. With `u` the reading of `s` and `χ'`
  that of `χ`, a cutoff `ψ` equal to one near the support of `χ'` turns `χ' u` into a smooth
  function `v` on the plane. On the chart image,
  `∂bar v + μ ∂v = (χ' / c₂) θ(1) + ((∂bar + μ ∂) χ' - (χ' / c₂) Z) u` for the reading `θ` of
  the `(0,1)`-part of `D_J s`, by Tau Ceti's product rules `TauCeti.conjWirtingerDeriv_smul_apply`
  and `TauCeti.wirtingerDeriv_smul_apply`. The estimate for `∂bar + μ ∂` in the plane,
  `TauCeti.exists_sum_eLpNorm_iteratedFDeriv_le_of_norm_le`, bounds `v`, and the Leibniz rule
  on the chart image, `exists_eLpNorm_iteratedFDeriv_smul_le_of_isOpen`, bounds the two products.

The proof of `exists_coord_zeroOnePart_twistOneDelBar_apply` adapts those of Tau Ceti's
`TauCeti.FiniteBundleAtlas.coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder`
and `TauCeti.FiniteBundleAtlas.exists_norm_chartZeroOrder_apply_le`
(`TauCeti/Geometry/Manifold/VectorBundle/CauchyRiemann/Chart.lean`), the case `μ = 0`, `c₂ = 1`
of an operator that is Cauchy–Riemann for `i`, to the operators `D_J`. The proof of
`exists_sum_eLpNorm_iteratedFDeriv_coord_smul_le` is the order-`k` form, for `D_J`, of that of
Tau Ceti's `TauCeti.IsRealCauchyRiemannOperator.exists_eLpNorm_coord_smul_add_eLpNorm_fderiv_le`
(`TauCeti/Geometry/Manifold/VectorBundle/Sobolev/CauchyRiemann/Estimate.lean`), whose steps it
follows: the compact chart image of the support of `χ`, the smoothness of the reading of `s`, and
the reading of `χ s` as `χ' u`.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1 and C.2.
-/

public section

open Bundle MeasureTheory Set TauCeti TauCeti.Manifold
open OnePoint (twistCore)
open ComplexConjugate
open scoped Manifold ContDiff ENNReal NNReal Topology TauCeti.ComplexManifold
open scoped VectorBundle.ComplexToReal

noncomputable section

namespace SymplecticGeometry

/-- The finite bundle atlas of `𝒪(n)` on which its Sobolev sections are built, chosen once. -/
def twistCoreAtlas (n : ℤ) : FiniteBundleAtlas ℂ (OnePoint ℂ) ℂ (twistCore (𝕜 := ℂ) n).Fiber :=
  Classical.choice FiniteBundleAtlas.nonempty

variable (J : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)) (k : ℕ)

/-- **The operator `D_J` on Sobolev sections.** For an almost complex structure `J` on the sphere,
the bounded operator `W^{k+1,2}(𝒪(1)) → W^{k,2}(Λ^{0,1} ⊗ 𝒪(1))`, with `Λ^{0,1}` for the standard
complex structure `i`, given by `π^{0,1}_i ∘ Φ_J ∘ ∇`: the Sobolev realization of the connection
`twistOneConnection`, then the `(0,1)`-projection for `J` at every point, then the projection
`TauCeti.zeroOnePartSobolevL` onto the `(0,1)`-forms for `i`. -/
def twistOneDelBarSobolev :
    SobolevSection (twistCoreAtlas 1) volume 2 (k + 1) →L[ℝ]
      zeroOneSobolevSections (twistCoreAtlas 1) volume 2 k :=
  (zeroOnePartSobolevL (twistCoreAtlas 1) volume 2 k).comp
    ((SobolevSection.contMDiffHomMulL (twistCoreAtlas 1).tangentHom
        (twistCoreAtlas 1).tangentHom.closure_dom_subset_baseSet volume 2 k
        (J.contMDiff_zeroOnePartL le_rfl)).comp
      (isCovariantDerivativeOn_twistOneConnection.sobolevL (twistCoreAtlas 1)
        (contMDiffCovariantDerivativeOn_twistOneConnection ⊤) volume 2 k))

theorem twistOneDelBarSobolev_def :
    twistOneDelBarSobolev J k = (zeroOnePartSobolevL (twistCoreAtlas 1) volume 2 k).comp
      ((SobolevSection.contMDiffHomMulL (twistCoreAtlas 1).tangentHom
          (twistCoreAtlas 1).tangentHom.closure_dom_subset_baseSet volume 2 k
          (J.contMDiff_zeroOnePartL le_rfl)).comp
        (isCovariantDerivativeOn_twistOneConnection.sobolevL (twistCoreAtlas 1)
          (contMDiffCovariantDerivativeOn_twistOneConnection ⊤) volume 2 k)) :=
  (rfl)

/-- The operator applied to a Sobolev section, as the three operators applied in turn. -/
theorem twistOneDelBarSobolev_apply (w : SobolevSection (twistCoreAtlas 1) volume 2 (k + 1)) :
    twistOneDelBarSobolev J k w = zeroOnePartSobolevL (twistCoreAtlas 1) volume 2 k
      (SobolevSection.contMDiffHomMulL (twistCoreAtlas 1).tangentHom
        (twistCoreAtlas 1).tangentHom.closure_dom_subset_baseSet volume 2 k
        (J.contMDiff_zeroOnePartL le_rfl)
        (isCovariantDerivativeOn_twistOneConnection.sobolevL (twistCoreAtlas 1)
          (contMDiffCovariantDerivativeOn_twistOneConnection ⊤) volume 2 k w)) :=
  (rfl)

/-- **Agreement on smooth sections.** On the Sobolev section of a `C^{k+1}` section `s` of `𝒪(1)`,
the chart data of `twistOneDelBarSobolev J k` agree almost everywhere on every chart image with the
chart readings of the `(0,1)`-part for `i` of the one-form `twistOneDelBar J s`. -/
theorem chartValueL_twistOneDelBarSobolev_ofContMDiffSection_ae_coord
    (s : Cₛ^((k + 1 : ℕ) : WithTop ℕ∞)⟮𝓘(ℝ, ℂ); ℂ, (twistCore (𝕜 := ℂ) 1).Fiber⟯)
    (i : Fin (twistCoreAtlas 1).n) :
    (twistCoreAtlas 1).tangentHom.sectionChartData.chartValueL volume 2 k i
        (((twistOneDelBarSobolev J k (SobolevSection.ofContMDiffSection (twistCoreAtlas 1)
          volume 2 (k + 1) s) : SobolevSection (twistCoreAtlas 1).tangentHom volume 2 k)) :
          (twistCoreAtlas 1).tangentHom.sectionChartData.SobolevData volume 2 k)
      =ᵐ[volume.restrict ((twistCoreAtlas 1).image i)]
        (twistCoreAtlas 1).tangentHom.coord i fun x ↦ 𝒊.zeroOnePart (twistOneDelBar J s x) := by
  have hcov (i : Fin (twistCoreAtlas 1).n) :
      (twistCoreAtlas 1).tangentHom.sectionChartData.chartValueL volume 2 k i
          ((isCovariantDerivativeOn_twistOneConnection.sobolevL (twistCoreAtlas 1)
            (contMDiffCovariantDerivativeOn_twistOneConnection ⊤) volume 2 k
              (SobolevSection.ofContMDiffSection (twistCoreAtlas 1) volume 2 (k + 1) s) :
              SobolevSection (twistCoreAtlas 1).tangentHom volume 2 k) :
            (twistCoreAtlas 1).tangentHom.sectionChartData.SobolevData volume 2 k)
        =ᵐ[volume.restrict ((twistCoreAtlas 1).tangentHom.image i)]
          (twistCoreAtlas 1).tangentHom.coord i (twistOneConnection s) := by
    rw [FiniteBundleAtlas.image_tangentHom]
    exact isCovariantDerivativeOn_twistOneConnection.chartValueL_sobolevL_ofContMDiffSection_ae
      (twistCoreAtlas 1) (contMDiffCovariantDerivativeOn_twistOneConnection ⊤) volume 2 k s i
  -- The chart data of `Φ_J ∇s` are the readings of the section `x ↦ Φ_J x (∇s x)`.
  have hΦ := SobolevSection.chartValueL_contMDiffHomMulL_ae_coord_self
    (A := (twistCoreAtlas 1).tangentHom) (J.contMDiff_zeroOnePartL le_rfl)
    hcov i
  simp only [FiniteBundleAtlas.image_tangentHom, SmoothAlmostComplexStructure.zeroOnePartL_apply]
    at hΦ
  rw [twistOneDelBarSobolev_apply]
  simp_rw [twistOneDelBar_def]
  exact (FiniteBundleAtlas.ae_image_tangentHom_iff _ volume i).1
    (chartValueL_zeroOnePartSobolevL_ae_coord ((FiniteBundleAtlas.ae_image_tangentHom_iff _ volume
      i).2 hΦ))

/-! ### Continuity in the almost complex structure -/

variable {ι : Type*}
  (e : ι → Trivialization (ℂ →L[ℝ] ℂ) (π (ℂ →L[ℝ] ℂ) (fun x : OnePoint ℂ ↦
    TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) x)))
  [∀ i, MemTrivializationAtlas (e i)] (U : ι → TopologicalSpace.Opens (OnePoint ℂ))
  (hU : ∀ i, (U i : Set (OnePoint ℂ)) ⊆ (e i).baseSet)

/-- **Continuity in `J`.** For frames `e`, `U` of the tangent endomorphism bundle of the sphere
whose domains cover it, the operator `twistOneDelBarSobolev J k` depends continuously on `J`, from
the `C^∞` topology `SmoothAlmostComplexStructure.frameTopology e U hU` on almost complex
structures to the operator norm topology. -/
theorem continuous_twistOneDelBarSobolev (hcover : ∀ x, ∃ i, x ∈ U i) (k : ℕ) :
    let _ := SmoothAlmostComplexStructure.frameTopology e U hU
    Continuous fun J ↦ twistOneDelBarSobolev J k := by
  let _ := SmoothAlmostComplexStructure.frameTopology e U hU
  -- The preferred trivializations of the endomorphism bundle of the `𝒪(1)`-valued one-forms give
  -- frames that cover the sphere.
  let e' (x : OnePoint ℂ) := trivializationAt ((ℂ →L[ℝ] ℂ) →L[ℝ] ℂ →L[ℝ] ℂ)
    (fun x : OnePoint ℂ ↦
      (TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] VectorBundleCore.Fiber (twistCore (𝕜 := ℂ) 1) x) →L[ℝ]
        TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] VectorBundleCore.Fiber (twistCore (𝕜 := ℂ) 1) x) x
  let U' (x : OnePoint ℂ) : TopologicalSpace.Opens (OnePoint ℂ) := ⟨_, (e' x).open_baseSet⟩
  have hΦ : Continuous fun J : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ) ↦
      SobolevSection.contMDiffHomMulL (twistCoreAtlas 1).tangentHom
        (twistCoreAtlas 1).tangentHom.closure_dom_subset_baseSet volume 2 k
        (J.zeroOnePartSection (F := ℂ) (V := (twistCore (𝕜 := ℂ) 1).Fiber)).contMDiff :=
    continuous_iff_continuousAt.2 fun J₀ ↦
      SobolevSection.tendsto_contMDiffHomMulL_of_tendsto
        (fun x ↦ ⟨x, mem_baseSet_trivializationAt _ _ x⟩)
        (@Continuous.tendsto _ _ (SmoothAlmostComplexStructure.frameTopology e U hU)
          (ContMDiffSection.frameTopology (I := 𝓘(ℝ, ℂ)) (n := ∞) e' U' fun _ ↦ subset_rfl) _
          (SmoothAlmostComplexStructure.continuous_zeroOnePartSection e U hU hcover e' U'
            fun _ ↦ subset_rfl) J₀)
  rw [funext (twistOneDelBarSobolev_def · k)]
  refine continuous_const.clm_comp ((hΦ.congr fun J ↦ ?_).clm_comp continuous_const)
  exact SobolevSection.contMDiffHomMulL_congr _ _ (funext J.zeroOnePartSection_apply)

/-- **Continuity in `J` on the structures tamed by `σ`.** The restriction of
`continuous_twistOneDelBarSobolev` to the almost complex structures tamed by a two-form `σ`, with
the subspace topology of `SmoothAlmostComplexStructure.frameTopology e U hU`. -/
theorem continuous_twistOneDelBarSobolev_tames (hcover : ∀ x, ∃ i, x ∈ U i)
    (σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)) (k : ℕ) :
    let _ := SmoothAlmostComplexStructure.frameTopology e U hU
    Continuous fun J : {J // σ.Tames J} ↦ twistOneDelBarSobolev J.val k := by
  let _ := SmoothAlmostComplexStructure.frameTopology e U hU
  exact (continuous_twistOneDelBarSobolev e U hU hcover k).comp continuous_subtypeVal

/-! ### The operator in the charts of an atlas -/

/-- In a chart `i` of a finite bundle atlas `A` of `𝒪(1)`, the zeroth-order term of
`twistOneConnection` applied to the fibre value `1` is smooth on the part of the chart target over
the base set of the bundle chart. -/
theorem contDiffOn_chartZeroOrder_twistOneConnection_apply_one
    (A : FiniteBundleAtlas ℂ (OnePoint ℂ) ℂ (twistCore (𝕜 := ℂ) 1).Fiber) (i : Fin A.n) :
    ContDiffOn ℝ ∞ (fun z ↦ A.chartZeroOrder twistOneConnection i z 1)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.triv i).baseSet) := by
  have := isCovariantDerivativeOn_twistOneConnection.contDiffOn_chartZeroOrder A
    (contMDiffCovariantDerivativeOn_twistOneConnection ⊤) isOpen_univ i
  rw [inter_univ] at this
  exact this.clm_apply contDiffOn_const

/-- In a chart `i` of a finite bundle atlas `A` of `𝒪(1)`, the zeroth-order term of
`twistOneConnection` at a point of the chart image is complex linear in the fibre value:
`Γ z c = c • Γ z 1`. -/
theorem chartZeroOrder_twistOneConnection_apply
    (A : FiniteBundleAtlas ℂ (OnePoint ℂ) ℂ (twistCore (𝕜 := ℂ) 1).Fiber) {i : Fin A.n} {z : ℂ}
    (hz : z ∈ A.image i) (c : ℂ) :
    A.chartZeroOrder twistOneConnection i z c = c • A.chartZeroOrder twistOneConnection i z 1 := by
  rw [← isCovariantDerivativeOn_twistOneConnection.mono (subset_univ (A.triv i).baseSet)
    |>.chartZeroOrder_apply_smul A (fun _ _ _ hσ ↦ twistOneConnection_const_smul _ hσ) hz,
    smul_eq_mul, mul_one]

/-- **`D_J` in the charts.** Let a two-form `σ` tame both `J` and the standard structure `i` of
the sphere, and let `A` be a finite bundle atlas of `𝒪(1)`, such as `twistCoreAtlas 1`. For each
chart `i` of `A` there are an open set `U` containing the closure of the chart image and
functions `c₂ μ Z : ℂ → ℂ`, smooth on `U`, with `c₂ ≠ 0` on `U` and `‖μ‖ ≤ m` on the closure of
the chart image for some `m < 1`, such that the following holds for every section `s` of `𝒪(1)`
and every point `z` of the chart image over which `s` is differentiable. With `u = A.coord i s`
the chart reading of `s`, the chart reading at `z` of the `(0,1)`-part for `i` of `D_J s` is the
complex-antilinear map `v ↦ conj v · (c₂ (∂bar u + μ ∂u) + Z u)`. -/
theorem exists_coord_zeroOnePart_twistOneDelBar_apply
    {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)} (hJ : σ.Tames J) (hi : σ.Tames 𝒊)
    (A : FiniteBundleAtlas ℂ (OnePoint ℂ) ℂ (twistCore (𝕜 := ℂ) 1).Fiber) (i : Fin A.n) :
    ∃ U : Set ℂ, IsOpen U ∧ closure (A.image i : Set ℂ) ⊆ U ∧
      ∃ c₂ μ Z : ℂ → ℂ, ContDiffOn ℝ ∞ c₂ U ∧ ContDiffOn ℝ ∞ μ U ∧ ContDiffOn ℝ ∞ Z U ∧
        (∀ z ∈ U, c₂ z ≠ 0) ∧ (∃ m < 1, ∀ z ∈ closure (A.image i : Set ℂ), ‖μ z‖ ≤ m) ∧
        ∀ (s : Π x, (twistCore (𝕜 := ℂ) 1).Fiber x), ∀ z ∈ A.image i,
          MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
            (fun x ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) x (s x))
            ((A.chart i).symm z) →
          ∀ v : ℂ, A.tangentHom.coord i (fun x ↦ 𝒊.zeroOnePart (twistOneDelBar J s x)) z v =
            conj v * (c₂ z * ((fderiv ℝ (A.coord i s) z).complexAntilinearPart 1 +
                μ z * (fderiv ℝ (A.coord i s) z).complexLinearPart 1) +
              Z z * A.coord i s z) := by
  set K := J.inChart (A.center i)
  set G : ℂ → ℂ →L[ℝ] ℂ := fun z ↦ A.chartZeroOrder twistOneConnection i z 1
  set U : Set ℂ := (A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.triv i).baseSet
  have hUt : U ⊆ (extChartAt 𝓘(ℝ, ℂ) (A.center i)).target := fun z hz ↦ by simpa using hz.1
  -- `J` read in the chart is a complex structure on `ℂ` with `K 1 ≠ -i`.
  have hKK (z : ℂ) (hz : z ∈ U) (v : ℂ) : K z (K z v) = -v :=
    J.inChart_inChart (A.center i) (hUt hz) v
  have hK1 (z : ℂ) (hz : z ∈ U) : K z 1 ≠ -Complex.I :=
    SmoothAlmostComplexStructure.inChart_apply_one_ne_neg_I_of_tames hJ hi (A.center i) (hUt hz)
  have hden (z : ℂ) (hz : z ∈ U) : conj (K z 1) - Complex.I ≠ 0 :=
    Complex.conj_sub_I_ne_zero (hK1 z hz)
  set c₂ : ℂ → ℂ := fun z ↦ 2⁻¹ * (1 + Complex.I * conj ((K z).complexLinearPart 1))
  set μ : ℂ → ℂ := fun z ↦ (K z 1 - Complex.I) / (conj (K z 1) - Complex.I) with hμ
  set Z : ℂ → ℂ := fun z ↦ c₂ z * ((G z).complexAntilinearPart 1 +
    μ z * (G z).complexLinearPart 1)
  have hKs : ContDiffOn ℝ ∞ K U := (J.contDiffOn_inChart (A.center i)).mono hUt
  have hGs : ContDiffOn ℝ ∞ G U := contDiffOn_chartZeroOrder_twistOneConnection_apply_one A i
  have hconj {f : ℂ → ℂ} (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (fun z ↦ conj (f z)) U :=
    Complex.conjCLE.contDiff.comp_contDiffOn hf
  have hK1s : ContDiffOn ℝ ∞ (fun z ↦ K z 1) U := hKs.clm_apply contDiffOn_const
  have hc₂s : ContDiffOn ℝ ∞ c₂ U := contDiffOn_const.mul
    (contDiffOn_const.add (contDiffOn_const.mul (hconj (hKs.complexLinearPart_apply 1))))
  have hμs : ContDiffOn ℝ ∞ μ U := by
    simp only [hμ, div_eq_mul_inv]
    exact (hK1s.sub contDiffOn_const).mul (((hconj hK1s).sub contDiffOn_const).inv hden)
  have hcl : closure (A.image i : Set ℂ) ⊆ U :=
    (A.closure_image_subset_chart_image_closure_dom i).trans (A.chart_image_closure_dom_subset i)
  refine ⟨U, (A.chart i).isOpen_inter_preimage_symm (A.triv i).open_baseSet, hcl, c₂, μ, Z, hc₂s,
    hμs, hc₂s.mul ((hGs.complexAntilinearPart_apply 1).add (hμs.mul
      (hGs.complexLinearPart_apply 1))), fun z hz ↦ mul_ne_zero (inv_ne_zero two_ne_zero)
      (ContinuousLinearMap.one_add_I_mul_conj_complexLinearPart_one_ne_zero (hKK z hz) (hK1 z hz)),
    ?_, ?_⟩
  · -- `‖μ‖ < 1` at every point, and the closure of the chart image is compact.
    have hlt (z : ℂ) (hz : z ∈ U) : ‖μ z‖ < 1 := by
      have := norm_beltrami_lt_one_of_tames J hJ hi (A.center i) (hUt hz)
      rwa [← norm_neg, ← neg_div, neg_sub] at this
    obtain ⟨a, ha, hle⟩ := (A.isCompact_closure_image i).exists_forall_le'
      (hμs.continuousOn.norm.neg.mono hcl) fun z hz ↦ neg_lt_neg (hlt z (hcl hz))
    exact ⟨-a, by linarith, fun z hz ↦ le_neg_of_le_neg (hle z hz)⟩
  · intro s z hz hs v
    have hzU : z ∈ U := hcl (subset_closure hz)
    have hcov := isCovariantDerivativeOn_twistOneConnection.mono (subset_univ (A.triv i).baseSet)
    -- `Γu` is `u · Γ1`, since the zeroth-order term is complex linear.
    have hΓ : A.chartZeroOrder twistOneConnection i z (A.coord i s z) = A.coord i s z • G z :=
      chartZeroOrder_twistOneConnection_apply A hz _
    simp_rw [twistOneDelBar_def]
    rw [A.coord_tangentHom_zeroOnePart_zeroOnePart J hz,
      ContinuousLinearMap.complexAntilinearPartL_half_smul_add_I_smul_comp_apply (hKK z hzU)
        (hK1 z hzU),
      hcov.coord_tangentHom_eq_fderiv_add_chartZeroOrder A hz hs, hΓ]
    simp only [ContinuousLinearMap.complexLinearPart_add,
      ContinuousLinearMap.complexAntilinearPart_add, add_apply,
      ContinuousLinearMap.complexLinearPart_complex_smul,
      ContinuousLinearMap.complexAntilinearPart_complex_smul, smul_apply, smul_eq_mul, c₂, μ, Z]
    ring

/-! ### The estimate of order `k` in one chart -/

/-- `∂bar + μ ∂` of `v = χ' u` at a point, when `θ₁` is `c₂ (∂bar u + μ ∂u) + Z u` there: it is
`(χ' / c₂) θ₁ + ((∂bar + μ ∂) χ' - (χ' / c₂) Z) u`, by Tau Ceti's product rules
`TauCeti.conjWirtingerDeriv_smul_apply` and `TauCeti.wirtingerDeriv_smul_apply`. -/
private theorem conjWirtingerDeriv_add_smul_wirtingerDeriv_eq_of_eventuallyEq_smul
    {v χ' u c₂ μ Z : ℂ → ℂ} {z θ₁ : ℂ} (hv : v =ᶠ[𝓝 z] fun y ↦ χ' y • u y)
    (hχ' : DifferentiableAt ℝ χ' z) (hu : DifferentiableAt ℝ u z) (hc : c₂ z ≠ 0)
    (hθ₁ : θ₁ = c₂ z * ((fderiv ℝ u z).complexAntilinearPart 1 +
      μ z * (fderiv ℝ u z).complexLinearPart 1) + Z z * u z) :
    conjWirtingerDeriv v z 1 + μ z • wirtingerDeriv v z 1 =
      (χ' z * (c₂ z)⁻¹) • θ₁ + ((fderiv ℝ χ' z).complexAntilinearPart 1 +
        μ z * (fderiv ℝ χ' z).complexLinearPart 1 - χ' z * (c₂ z)⁻¹ * Z z) • u z := by
  rw [hv.conjWirtingerDeriv_eq, hv.wirtingerDeriv_eq, conjWirtingerDeriv_smul_apply hχ' hu,
    wirtingerDeriv_smul_apply hχ' hu, hθ₁, ← conjWirtingerDeriv_eq_complexAntilinearPart,
    ← wirtingerDeriv_eq_complexLinearPart, ← conjWirtingerDeriv_eq_complexAntilinearPart,
    ← wirtingerDeriv_eq_complexLinearPart]
  simp only [smul_eq_mul]
  field_simp
  ring


/-- The planar form of `exists_sum_eLpNorm_iteratedFDeriv_coord_smul_le`: on an open set `W` with
compact closure, for a cutoff `χ'` vanishing on `W` off a compact `K ⊆ W` and every `u` and `θ`
related on `W` as the readings of `s` and of the `(0,1)`-part of `D_J s` are, the derivatives of
order at most `k + 1` of `χ' u` are bounded in `L²(W)` by those of order at most `k` of `θ`
and `u`. -/
private theorem exists_sum_eLpNorm_iteratedFDeriv_mul_le {W U T K : Set ℂ} (hW : IsOpen W)
    (hWc : IsCompact (closure W)) (hU : IsOpen U) (hWU : closure W ⊆ U) (hT : IsOpen T)
    (hWT : closure W ⊆ T) (hK : IsCompact K) (hKW : K ⊆ W) {χ' c₂ μ Z : ℂ → ℂ}
    (hχ' : ContDiffOn ℝ ∞ χ' T) (hχK : ∀ z ∈ W, z ∉ K → χ' z = 0) (hc₂ : ContDiffOn ℝ ∞ c₂ U)
    (hμ : ContDiffOn ℝ ∞ μ U) (hZ : ContDiffOn ℝ ∞ Z U) (hc₂0 : ∀ z ∈ U, c₂ z ≠ 0) {m : ℝ}
    (hm1 : m < 1) (hmμ : ∀ z ∈ closure W, ‖μ z‖ ≤ m) :
    ∃ C : ℝ≥0, ∀ (u : ℂ → ℂ) (θ : ℂ → ℂ →L[ℝ] ℂ), ContDiffOn ℝ ∞ u W →
      (∀ z ∈ W, ∀ v : ℂ, θ z v = conj v * (c₂ z * ((fderiv ℝ u z).complexAntilinearPart 1 +
        μ z * (fderiv ℝ u z).complexLinearPart 1) + Z z * u z)) →
      ∑ j ∈ Finset.range (k + 2), eLpNorm (iteratedFDeriv ℝ j fun z ↦ χ' z • u z) 2
          (volume.restrict W) ≤
        C * (∑ j ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ j θ) 2 (volume.restrict W) +
          ∑ j ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ j u) 2 (volume.restrict W)) := by
  have hk : ((k : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hWU' : W ⊆ U := subset_closure.trans hWU
  have hWT' : W ⊆ T := subset_closure.trans hWT
  obtain ⟨ψ, hψ, -, hψ1, hψc, hψW⟩ := hK.exists_contDiff_cutoff_eventuallyEq_one hW hKW
  -- The operator `P g = ∂bar g + μ ∂g`, and the coefficients `a`, `b` of
  -- `P (χ' u) = a θ(1) + b u` on `W`.
  set P : (ℂ → ℂ) → ℂ → ℂ := fun g z ↦
    (fderiv ℝ g z).complexAntilinearPart 1 + μ z * (fderiv ℝ g z).complexLinearPart 1
  have hP {g : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ U) (hg : ContDiffOn ℝ ∞ g V) :
      ContDiffOn ℝ ∞ (P g) V := by
    have hg' := hg.fderiv_of_isOpen hV (m := ∞) le_rfl
    exact (hg'.complexAntilinearPart_apply 1).add
      ((hμ.mono hVU).mul (hg'.complexLinearPart_apply 1))
  set t := U ∩ T
  have ht : IsOpen t := hU.inter hT
  have hWt : closure W ⊆ t := subset_inter hWU hWT
  set a : ℂ → ℂ := fun z ↦ χ' z * (c₂ z)⁻¹
  set b : ℂ → ℂ := fun z ↦ P χ' z - χ' z * (c₂ z)⁻¹ * Z z
  have hc₂i : ContDiffOn ℝ ∞ (fun z ↦ (c₂ z)⁻¹) t :=
    (hc₂.mono inter_subset_left).inv fun z hz ↦ hc₂0 z hz.1
  have ha : ContDiffOn ℝ ∞ a t := (hχ'.mono inter_subset_right).mul hc₂i
  have hb : ContDiffOn ℝ ∞ b t := (hP ht inter_subset_left (hχ'.mono inter_subset_right)).sub
    (((hχ'.mono inter_subset_right).mul hc₂i).mul (hZ.mono inter_subset_left))
  -- The constants: the estimate for `∂bar + μ ∂` in the plane, and the Leibniz rule.
  obtain ⟨C₁, hC₁⟩ := exists_sum_eLpNorm_iteratedFDeriv_le_of_norm_le (F := ℂ) hψc hU
    (hψW.trans hWU') hμ (m := m.toNNReal) (Real.toNNReal_lt_one.2 hm1)
    (fun z hz ↦ (hmμ z (subset_closure (hψW hz))).trans (Real.le_coe_toNNReal m)) k
  obtain ⟨Cχ, hCχ⟩ := exists_eLpNorm_iteratedFDeriv_smul_le_of_isOpen (F := ℂ) volume
    one_le_two hW hT hWc subset_closure hWT (hχ'.of_le hk)
  obtain ⟨Ca, hCa⟩ := exists_eLpNorm_iteratedFDeriv_smul_le_of_isOpen (F := ℂ) volume
    one_le_two hW ht hWc subset_closure hWt (ha.of_le hk)
  obtain ⟨Cb, hCb⟩ := exists_eLpNorm_iteratedFDeriv_smul_le_of_isOpen (F := ℂ) volume
    one_le_two hW ht hWc subset_closure hWt (hb.of_le hk)
  refine ⟨C₁ * (k + 1) * (Ca + Cb + Cχ), fun u θ hu hθ ↦ ?_⟩
  set ν := volume.restrict W
  -- `θ` is `v ↦ conj v · g` on `W`.
  set g : ℂ → ℂ := fun z ↦ c₂ z * P u z + Z z * u z
  have hg : ContDiffOn ℝ ∞ g W :=
    ((hc₂.mono hWU').mul (hP hW hWU' hu)).add ((hZ.mono hWU').mul hu)
  have hθg (z : ℂ) (hz : z ∈ W) : θ z = g z • (Complex.conjCLE : ℂ →L[ℝ] ℂ) := by
    refine ContinuousLinearMap.ext fun w ↦ ?_
    rw [hθ z hz w]
    simp only [smul_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, smul_eq_mul, g,
      P]
    ring
  have hθs : ContDiffOn ℝ ∞ θ W := (hg.smul contDiffOn_const).congr hθg
  have hθ₁ (z : ℂ) (hz : z ∈ W) : θ z 1 = g z := by simp [hθg z hz]
  have hθ₁le (l : ℕ) : eLpNorm (iteratedFDeriv ℝ l fun z ↦ θ z 1) 2 ν ≤
      eLpNorm (iteratedFDeriv ℝ l θ) 2 ν := by
    refine eLpNorm_mono_ae ((ContinuousOn.continuousOn_iteratedFDeriv
      (hθs.clm_apply contDiffOn_const) hW
      (by exact_mod_cast le_top)).aestronglyMeasurable hW.measurableSet) ?_
    filter_upwards [ae_restrict_mem hW.measurableSet] with z hz
    simpa using norm_iteratedFDeriv_clm_apply_const (c := (1 : ℂ))
      (hθs.contDiffAt (hW.mem_nhds hz)) (n := l) (by exact_mod_cast le_top)
  -- The smooth function `v` on the plane, equal to `w = χ' u` on `W`.
  set w : ℂ → ℂ := fun z ↦ χ' z • u z
  have hw : ContDiffOn ℝ ∞ w W := (hχ'.mono hWT').smul hu
  set v : ℂ → ℂ := fun z ↦ ψ z • w z
  have hv : ContDiff ℝ ∞ v := hw.contDiff_smul_of_tsupport_subset hW hψ.contDiffOn hψW
  have hvψ : tsupport v ⊆ tsupport ψ := tsupport_smul_subset_left _ _
  have hvW : tsupport v ⊆ W := hvψ.trans hψW
  have hvw : EqOn v w W := fun z hz ↦ by
    by_cases hzK : z ∈ K
    · simp only [v, (hψ1 z hzK).self_of_nhds, one_smul]
    · simp only [v, w, hχK z hz hzK, zero_smul, smul_zero]
  have hvol {f : ℂ → ℂ} (hf : tsupport f ⊆ W) (j : ℕ) :
      eLpNorm (iteratedFDeriv ℝ j f) 2 volume = eLpNorm (iteratedFDeriv ℝ j f) 2 ν := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hW.measurableSet.nullMeasurableSet,
      indicator_eq_self.2 ((support_iteratedFDeriv_subset j).trans hf)]
  -- `P v = a θ(1) + b u` on `W`, and `P v` vanishes off `tsupport v`.
  set Pv : ℂ → ℂ := fun z ↦ conjWirtingerDeriv v z 1 + μ z • wirtingerDeriv v z 1
  have hPvW : tsupport Pv ⊆ W :=
    (tsupport_conjWirtingerDeriv_add_smul_wirtingerDeriv_subset μ 1).trans hvW
  have hPv : EqOn Pv (fun z ↦ a z • θ z 1 + b z • u z) W := fun z hz ↦
    conjWirtingerDeriv_add_smul_wirtingerDeriv_eq_of_eventuallyEq_smul
      (hvw.eventuallyEq_of_mem (hW.mem_nhds hz))
      ((hχ'.contDiffAt (hT.mem_nhds (hWT' hz))).differentiableAt (by simp))
      ((hu.contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp))
      (hc₂0 z (hWU' hz)) (hθ₁ z hz)
  -- The bounds of each term over `ν`.
  set T' := ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l θ) 2 ν
  set Y := ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l u) 2 ν
  have hPvj (j : ℕ) (hj : j ≤ k) :
      eLpNorm (iteratedFDeriv ℝ j Pv) 2 ν ≤ Ca * T' + Cb * Y := by
    refine (eLpNorm_iteratedFDeriv_restrict_congr_of_eqOn volume 2 hW hPv j).trans_le
      ((eLpNorm_iteratedFDeriv_add_restrict_le volume one_le_two hW
        ((ha.mono (subset_closure.trans hWt)).smul (hθs.clm_apply contDiffOn_const))
        ((hb.mono (subset_closure.trans hWt)).smul hu) (j := j) (by exact_mod_cast le_top)).trans
      (add_le_add ?_ (hCb u (hu.of_le hk) j hj)))
    exact (hCa _ ((hθs.clm_apply contDiffOn_const).of_le hk) j hj).trans
      (by gcongr; exact Finset.sum_le_sum fun l _ ↦ hθ₁le l)
  -- Assemble.
  have hsum {f : ℕ → ℝ≥0∞} {B : ℝ≥0∞} (h : ∀ j ≤ k, f j ≤ B) :
      ∑ j ∈ Finset.range (k + 1), f j ≤ (k + 1) * B :=
    (Finset.sum_le_card_nsmul _ _ _ fun j hj ↦ h j (Finset.mem_range_succ_iff.1 hj)).trans_eq
      (by simp [nsmul_eq_mul])
  have hvj (j : ℕ) : eLpNorm (iteratedFDeriv ℝ j v) 2 volume =
      eLpNorm (iteratedFDeriv ℝ j w) 2 ν :=
    (hvol hvW j).trans (eLpNorm_iteratedFDeriv_restrict_congr_of_eqOn volume 2 hW hvw j)
  calc _ = ∑ j ∈ Finset.range (k + 2), eLpNorm (iteratedFDeriv ℝ j v) 2 volume :=
        Finset.sum_congr rfl fun j _ ↦ (hvj j).symm
    _ ≤ C₁ * (∑ j ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ j Pv) 2 volume +
          ∑ j ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ j v) 2 volume) := hC₁ v hv hvψ
    _ ≤ C₁ * ((k + 1) * (Ca * T' + Cb * Y) + (k + 1) * (Cχ * Y)) := by
        gcongr
        · exact hsum fun j hj ↦ (hvol hPvW j).trans_le (hPvj j hj)
        · exact hsum fun j hj ↦ (hvj j).trans_le (hCχ u (hu.of_le hk) j hj)
    _ ≤ C₁ * ((k + 1) * ((Ca + Cb + Cχ) * (T' + Y))) := by
        rw [← mul_add]
        gcongr
        calc Ca * T' + Cb * Y + Cχ * Y ≤ Ca * (T' + Y) + Cb * (T' + Y) + Cχ * (T' + Y) := by
              gcongr
              · exact le_self_add
              · exact le_add_self
              · exact le_add_self
          _ = _ := by ring
    _ = _ := by
        push_cast
        ring

/-- **The order-`k` estimate for `D_J` in a chart.** Let a two-form `σ` tame both `J` and the
standard structure `i` of the sphere, let `A` be a finite bundle atlas of `𝒪(1)`, such as
`twistCoreAtlas 1`, and let `χ` be a smooth function whose support has closure in the domain of
chart `i`. There is a constant `C` such that for every smooth section `s` of `𝒪(1)`, on the image
of the chart, the `L²` norms of the derivatives of order at most `k + 1` of the reading of `χ s`
are at most `C` times the sum of the `L²` norms of the derivatives of order at most `k` of the
reading of the `(0,1)`-part for `i` of `D_J s` and of the reading of `s`. -/
theorem exists_sum_eLpNorm_iteratedFDeriv_coord_smul_le
    {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)} (hJ : σ.Tames J) (hi : σ.Tames 𝒊)
    (A : FiniteBundleAtlas ℂ (OnePoint ℂ) ℂ (twistCore (𝕜 := ℂ) 1).Fiber) (i : Fin A.n)
    {χ : OnePoint ℂ → ℝ} (hχ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ χ) (hχi : tsupport χ ⊆ A.dom i) :
    ∃ C : ℝ≥0, ∀ s : Π x, (twistCore (𝕜 := ℂ) 1).Fiber x,
      ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞
        (fun x ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) x (s x)) →
      ∑ m ∈ Finset.range (k + 2), eLpNorm (iteratedFDeriv ℝ m (A.coord i fun x ↦ χ x • s x)) 2
          (volume.restrict (A.image i)) ≤
        C * (∑ m ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ m
            (A.tangentHom.coord i fun x ↦ 𝒊.zeroOnePart (twistOneDelBar J s x))) 2
              (volume.restrict (A.image i)) +
          ∑ m ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ m (A.coord i s)) 2
            (volume.restrict (A.image i))) := by
  have hW : IsOpen (A.image i : Set ℂ) := (A.image i).isOpen
  have hcl := A.closure_image_subset_target i
  -- `χ` read in the chart vanishes on the chart image off the compact set `K`.
  set K : Set ℂ := A.chart i '' tsupport χ
  have hK : IsCompact K := (isClosed_tsupport χ).isCompact.image_of_continuousOn
    ((A.chart i).continuousOn.mono (hχi.trans (A.dom_subset_chart_source i)))
  have hKW : K ⊆ A.image i := fun y hy ↦ A.mem_image.2 (image_mono hχi hy)
  set χ' : ℂ → ℂ := fun y ↦ (χ ((A.chart i).symm y) : ℂ)
  have hχ' : ContDiffOn ℝ ∞ χ' (A.chart i).target :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (A.contDiffOn_comp_chart_symm hχ i)
  have hχK (z : ℂ) (hz : z ∈ A.image i) (hzK : z ∉ K) : χ' z = 0 := by
    by_contra h
    exact hzK ⟨_, subset_tsupport _ fun h' ↦ h (by simp [χ', h']),
      (A.chart i).right_inv (hcl (subset_closure hz))⟩
  obtain ⟨U, hUo, hWU, c₂, μ, Z, hc₂, hμ, hZ, hc₂0, ⟨m, hm1, hmμ⟩, hθ⟩ :=
    exists_coord_zeroOnePart_twistOneDelBar_apply J hJ hi A i
  obtain ⟨C, hC⟩ := exists_sum_eLpNorm_iteratedFDeriv_mul_le (k := k) hW
    (A.isCompact_closure_image i) hUo hWU (A.chart i).open_target hcl hK hKW hχ' hχK hc₂ hμ hZ
    hc₂0 hm1 hmμ
  refine ⟨C, fun s hs ↦ ?_⟩
  have hu : ContDiffOn ℝ ∞ (A.coord i s) (A.image i) :=
    ((contDiffOn_trivialization_comp_chart_symm_of_contMDiff hs
      (IsManifold.chart_mem_maximalAtlas _) (A.triv i)).congr fun y _ ↦ A.coord_def i s y).mono
        ((A.image_subset_chart_image_closure_dom i).trans (A.chart_image_closure_dom_subset i))
  have hcw : EqOn (A.coord i fun x ↦ χ x • s x) (fun z ↦ χ' z • A.coord i s z) (A.image i) :=
    fun z hz ↦ (A.coord_fun_smul i χ s hz).trans (Complex.coe_smul _ _).symm
  refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ ↦
    eLpNorm_iteratedFDeriv_restrict_congr_of_eqOn volume 2 hW hcw j) ?_
  exact hC _ _ hu fun z hz ↦ hθ s z hz ((hs _).mdifferentiableAt (by simp))

end SymplecticGeometry
