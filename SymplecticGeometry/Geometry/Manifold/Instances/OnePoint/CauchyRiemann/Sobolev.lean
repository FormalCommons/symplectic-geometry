/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.Basic
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.CauchyRiemann.ZeroOneForm
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Sobolev.CovariantDerivative
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Sobolev.SmoothHomMul
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm

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

On smooth sections the operator is the `(0,1)`-part for `i` of `D_J`
(`SymplecticGeometry.twistOneDelBarSobolev_ofContMDiffSection`). The last projection loses nothing
when a two-form tames both `J` and `i`: then the
`(0,1)`-projection for `i` is injective on the `(0,1)`-forms for `J` at every point
(`TauCeti.SmoothAlmostComplexStructure.injOn_zeroOnePart_of_tames`).

Tau Ceti's realization `TauCeti.IsRealCauchyRiemannOperator.sobolevSuccL`
(`Geometry/Manifold/VectorBundle/Sobolev/CauchyRiemann/HigherOrder.lean`) is not used: it
realizes an operator that is Cauchy–Riemann for the complex structure of the charts, which
`π^{0,1}_i ∘ D_J` is not in general.

## Main definitions and results

* `SymplecticGeometry.twistCoreAtlas n`: the finite bundle atlas of `𝒪(n)`.
* `SymplecticGeometry.twistOneDelBarSobolev J k`: the operator `D_J` from `W^{k+1,2}` sections of
  `𝒪(1)` to `W^{k,2}` `(0,1)`-forms with values in `𝒪(1)`.
* `SymplecticGeometry.twistOneDelBarSobolev_ofContMDiffSection`: on a `C^{k+1}` section `s`, its
  chart data are the readings of the `(0,1)`-part for `i` of `D_J s`.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1 and C.2.
-/

public section

open Bundle MeasureTheory Set TauCeti TauCeti.Manifold
open OnePoint (twistCore)
open scoped Manifold ContDiff ENNReal TauCeti.ComplexManifold VectorBundle.ComplexToReal

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
the chart data of `twistOneDelBarSobolev J k` are, in every chart, the readings of the `(0,1)`-part
for `i` of the one-form `twistOneDelBar J s`. -/
theorem twistOneDelBarSobolev_ofContMDiffSection
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

end SymplecticGeometry
