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
import SymplecticGeometry.Analysis.Normed.Operator.ComplexLinearPart
import SymplecticGeometry.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.ZeroOnePart
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Tames

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
  (`chartZeroOrder_twistOneConnection_smul`).

The proof of `exists_coord_zeroOnePart_twistOneDelBar_apply` adapts those of Tau Ceti's
`TauCeti.FiniteBundleAtlas.coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder`
and `TauCeti.FiniteBundleAtlas.exists_norm_chartZeroOrder_apply_le`
(`TauCeti/Geometry/Manifold/VectorBundle/CauchyRiemann/Chart.lean`), the case `μ = 0`, `c₂ = 1`
of an operator that is Cauchy–Riemann for `i`, to the operators `D_J`.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1 and C.2.
-/

public section

open Bundle MeasureTheory Set TauCeti TauCeti.Manifold
open OnePoint (twistCore)
open ComplexConjugate
open scoped Manifold ContDiff ENNReal Topology TauCeti.ComplexManifold VectorBundle.ComplexToReal

noncomputable section

namespace SymplecticGeometry

/-- The standard complex structure of the Riemann sphere. -/
local notation "𝒊" => SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)

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
  have hΦ := SobolevSection.chartValueL_contMDiffHomMulL_ae_coord
    (h := (twistCoreAtlas 1).tangentHom.closure_dom_subset_baseSet)
    (J.contMDiff_zeroOnePartL le_rfl) hcov i
  -- The atlas `A.tangentHom.ofBaseSet A.tangentHom.closure_dom_subset_baseSet`, in which
  -- `contMDiffHomMulL` lands, is `A.tangentHom` itself, by the eta rule for structures.
  simp only [SmoothAlmostComplexStructure.zeroOnePartL_apply,
    FiniteBundleAtlas.image_tangentHom] at hΦ
  have h := (FiniteBundleAtlas.ae_image_tangentHom_iff _ volume i).1
    (chartValueL_zeroOnePartSobolevL_ae_coord (θ := fun x ↦ J.zeroOnePart
      (twistOneConnection s x)) (i := i) ((FiniteBundleAtlas.ae_image_tangentHom_iff _ volume i).2
        hΦ))
  rw [twistOneDelBarSobolev_apply]
  simp_rw [twistOneDelBar_def]
  exact h

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

/-- In every chart of a finite bundle atlas of `𝒪(1)`, the zeroth-order term of the connection
`twistOneConnection` commutes with complex scalars on the chart image, since the connection is
complex linear. -/
theorem chartZeroOrder_twistOneConnection_smul
    (A : FiniteBundleAtlas ℂ (OnePoint ℂ) ℂ (twistCore (𝕜 := ℂ) 1).Fiber) (i : Fin A.n) {z : ℂ}
    (hz : z ∈ A.image i) (c v : ℂ) :
    A.chartZeroOrder twistOneConnection i z (c • v) =
      c • A.chartZeroOrder twistOneConnection i z v := by
  have hcov := isCovariantDerivativeOn_twistOneConnection.mono (subset_univ (A.triv i).baseSet)
  have hx : (A.chart i).symm z ∈ (A.triv i).baseSet :=
    A.dom_subset_baseSet i (A.symm_mem_dom hz)
  have hσ := Manifold.mdifferentiableAt_symm_of_mem_baseSet (I := 𝓘(ℝ, ℂ)) v hx
  have heq : twistOneConnection (fun x ↦ (A.triv i).symm x (c • v)) ((A.chart i).symm z) =
      twistOneConnection (c • fun x ↦ (A.triv i).symm x v) ((A.chart i).symm z) := by
    refine isCovariantDerivativeOn_twistOneConnection.congr_of_eventuallyEq
      (Manifold.mdifferentiableAt_symm_of_mem_baseSet (c • v) hx) (hσ.const_smul_section c)
      Filter.univ_mem ?_
    filter_upwards [(A.triv i).open_baseSet.mem_nhds hx] with y hy
    rw [Pi.smul_apply, ← (A.triv i).coe_symmₗ (R := ℂ) hy, map_smul]
  rw [hcov.chartZeroOrder_apply_eq_coord_tangentHom A hz,
    hcov.chartZeroOrder_apply_eq_coord_tangentHom A hz,
    FiniteBundleAtlas.coord_tangentHom, FiniteBundleAtlas.coord_tangentHom, heq,
    twistOneConnection_const_smul c hσ]
  ext w
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply, smul_apply]
  rw [Trivialization.coe_continuousLinearMapAt_eq_coe_continuousLinearMapAt ℝ ℂ, map_smul,
    ← Trivialization.coe_continuousLinearMapAt_eq_coe_continuousLinearMapAt ℝ ℂ]

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
  set K := J.inChart (A.center i) with hK
  set G : ℂ → ℂ →L[ℝ] ℂ := fun z ↦ A.chartZeroOrder twistOneConnection i z 1 with hG
  set U : Set ℂ := (A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.triv i).baseSet
  have hUt : U ⊆ (extChartAt 𝓘(ℝ, ℂ) (A.center i)).target := fun z hz ↦ by simpa using hz.1
  -- `J` read in the chart is a complex structure on `ℂ` with `K 1 ≠ -i`.
  have hKK (z : ℂ) (hz : z ∈ U) (v : ℂ) : K z (K z v) = -v :=
    J.inChart_inChart (A.center i) (hUt hz) v
  have hK1 (z : ℂ) (hz : z ∈ U) : K z 1 ≠ -Complex.I := fun h ↦ by
    have := SmoothAlmostComplexStructure.im_inChart_apply_one_pos_of_tames hJ hi (A.center i)
      (hUt hz)
    rw [← hK, h] at this
    norm_num at this
  have hden (z : ℂ) (hz : z ∈ U) : conj (K z 1) - Complex.I ≠ 0 := fun h ↦ hK1 z hz (by
    simpa using congrArg conj (sub_eq_zero.1 h))
  set c₂ : ℂ → ℂ := fun z ↦ 2⁻¹ * (1 + Complex.I * conj ((K z).complexLinearPart 1))
  set μ : ℂ → ℂ := fun z ↦ (K z 1 - Complex.I) / (conj (K z 1) - Complex.I) with hμ
  set Z : ℂ → ℂ := fun z ↦ c₂ z * ((G z).complexAntilinearPart 1 +
    μ z * (G z).complexLinearPart 1)
  have hKs : ContDiffOn ℝ ∞ K U := (J.contDiffOn_inChart (A.center i)).mono hUt
  have hGs : ContDiffOn ℝ ∞ G U := by
    have := (isCovariantDerivativeOn_twistOneConnection.contDiffOn_chartZeroOrder A
      (contMDiffCovariantDerivativeOn_twistOneConnection ⊤) isOpen_univ i)
    rw [inter_univ] at this
    exact this.clm_apply contDiffOn_const
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
    have hΓ : A.chartZeroOrder twistOneConnection i z (A.coord i s z) = A.coord i s z • G z := by
      rw [hG, ← chartZeroOrder_twistOneConnection_smul A i hz, smul_eq_mul, mul_one]
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

end SymplecticGeometry
