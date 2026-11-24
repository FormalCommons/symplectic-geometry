/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DeRham.FundamentalClass
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Homotopy
public import TauCeti.Geometry.Manifold.Orientation.AddCircle
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.AddCircle
import TauCeti.Geometry.Manifold.Instances.AddCircle
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Rectangle integrals of closed two-forms as periods

Let `σ` be a closed two-form on a manifold `M` and `u : ℝ × ℝ → M` a smooth map with period `1`
in each variable. Then the rectangle integral `∫_{[0,1]²} u^* σ` (Tau Ceti's
`TauCeti.rectangleIntegral`) is a period of `σ` on the integral homology `H₂(M; ℤ)`, a value of
`TauCeti.closedFormHomologyPeriod σ`.

The proof goes through the torus `T² = AddCircle 1 × AddCircle 1`. The integral over a torus of
the pullback of `σ` by a smooth map is a period
(`TauCeti.Manifold.Orientation.integralTopForm_mpullback_eq_closedFormHomologyPeriod`, once the
product model `𝓘(ℝ).prod 𝓘(ℝ)` of the torus is identified with `𝓘(ℝ, ℝ × ℝ)` by
`modelWithCornersSelf_prod`). The map `u` descends along the quotient map `ℝ × ℝ → T²`, a
surjective local diffeomorphism (`AddCircle.isLocalDiffeomorph_prodMap_coe`), to a smooth map
`v : T² → M` (`IsLocalDiffeomorph.existsUnique_contMDiff_comp_eq`). The integral of `v^* σ` over
the torus is the integral over the square `[0, 1) × [0, 1)` of `v^* σ` on the standard frame
(`AddCircle.integralTopForm_prod_eq_setIntegral`, applied as in Tau Ceti's
`AddCircle.integralTopForm_wedge_timeForm`). Since the quotient map has the identity as derivative
(`AddCircle.mfderiv_prodMap_coe`), that integrand is the one of `u^* σ`. Up to a null set the square
is `[0, 1]²`, where Fubini's theorem (`TauCeti.IsSmoothForm.setIntegral_eq_rectangleIntegral`)
turns the integral into the rectangle integral.

## Main results

* `AddCircle.integralTopForm_mpullback_mem_range_closedFormHomologyPeriod`: the integral over the
  torus `AddCircle p × AddCircle q` of the pullback of a closed two-form is a period of the form on
  `H₂(M; ℤ)`.
* `TauCeti.rectangleIntegral_mem_range_closedFormHomologyPeriod_of_periodic`: the rectangle
  integral of a closed two-form over a smooth map of `ℝ²` with period `1` in both variables is a
  period of the form on `H₂(M; ℤ)`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §10.2.
-/

public section

open Set MeasureTheory
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- The integral over a closed oriented surface modelled on `ℝ × ℝ` of the pullback of a closed
two-form is a period, for any model of the surface equal to `𝓘(ℝ, ℝ × ℝ)`. This lets the product
model `𝓘(ℝ).prod 𝓘(ℝ)` of a torus be used. -/
private theorem integralTopForm_mpullback_mem_range_of_eq {C : Type} [TopologicalSpace C]
    [hC : ChartedSpace (ℝ × ℝ) C] [T2Space C] [CompactSpace C]
    {J : ModelWithCorners ℝ (ℝ × ℝ) (ℝ × ℝ)} (hJ : J = 𝓘(ℝ, ℝ × ℝ)) [hCJ : IsManifold J ∞ C]
    (o : Manifold.Orientation J C (Fin 2)) (σ : closedForms I M 2) {v : C → M}
    (hv : ContMDiff J I ∞ v) :
    integralTopForm o (mpullback J I v σ.val.val) ∈ range (closedFormHomologyPeriod σ) := by
  subst hJ
  exact ⟨_, (o.integralTopForm_mpullback_eq_closedFormHomologyPeriod (by simp) σ hv).symm⟩

/-- **Integrals over a torus of closed two-forms are periods.** For a closed two-form `σ` on `M`
and a smooth map `v : AddCircle p × AddCircle q → M`, the integral of `v^* σ` over the torus, with
its product orientation, is the period of `σ` on some class of `H₂(M; ℤ)`. -/
theorem _root_.AddCircle.integralTopForm_mpullback_mem_range_closedFormHomologyPeriod (p q : ℝ)
    [Fact (0 < p)] [Fact (0 < q)] (σ : closedForms I M 2) {v : AddCircle p × AddCircle q → M}
    (hv : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) I ∞ v) :
    integralTopForm ((AddCircle.orientation p).prod (AddCircle.orientation q))
      (mpullback (𝓘(ℝ).prod 𝓘(ℝ)) I v σ.val.val) ∈ range (closedFormHomologyPeriod σ) :=
  -- The torus is charted on `ModelProd ℝ ℝ`, which is `ℝ × ℝ` by definition; the instances are
  -- given explicitly since instance search does not see through `ModelProd`.
  integralTopForm_mpullback_mem_range_of_eq (C := AddCircle p × AddCircle q)
    (hC := prodChartedSpace ℝ _ ℝ _) (J := 𝓘(ℝ).prod 𝓘(ℝ))
    (hCJ := inferInstanceAs (IsManifold (𝓘(ℝ).prod 𝓘(ℝ)) ∞ (AddCircle p × AddCircle q)))
    modelWithCornersSelf_prod.symm _ σ hv

/-- **Rectangle integrals over doubly periodic maps are periods.** Let `σ` be a closed two-form on
`M` and `u : ℝ × ℝ → M` a smooth map with `u (t + 1, s) = u (t, s)` and `u (t, s + 1) = u (t, s)`.
Then `∫_{[0,1]²} u^* σ` is the period of `σ` on some class of `H₂(M; ℤ)`. -/
theorem rectangleIntegral_mem_range_closedFormHomologyPeriod_of_periodic (σ : closedForms I M 2)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u) (h₁ : ∀ t s, u (t + 1, s) = u (t, s))
    (h₂ : ∀ t s, u (t, s + 1) = u (t, s)) :
    rectangleIntegral σ.val.val u (0, 0) (1, 1) ∈ range (closedFormHomologyPeriod σ) := by
  set Q := Prod.map ((↑) : ℝ → AddCircle (1 : ℝ)) ((↑) : ℝ → AddCircle (1 : ℝ))
  have hQ := AddCircle.isLocalDiffeomorph_prodMap_coe (1 : ℝ) 1 ∞
  have hQs : Function.Surjective Q := AddCircle.prodMap_coe_surjective (1 : ℝ) 1
  -- `u` is constant on the fibres of `Q`, so it descends to the torus.
  have hfac : Function.FactorsThrough u Q := by
    rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h
    obtain ⟨h₁', h₂'⟩ := Prod.ext_iff.1 h
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 h₁')
    obtain ⟨l, hl⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 h₂')
    have p₁ (s : ℝ) : Function.Periodic (fun t ↦ u (t, s)) 1 := fun t ↦ h₁ t s
    have p₂ (t : ℝ) : Function.Periodic (fun s ↦ u (t, s)) 1 := fun s ↦ h₂ t s
    have eb₁ : b₁ = a₁ + k • (1 : ℝ) := by linarith
    have eb₂ : b₂ = a₂ + l • (1 : ℝ) := by linarith
    rw [eb₁, eb₂]
    exact ((p₁ a₂).zsmul k a₁).symm.trans ((p₂ _).zsmul l a₂).symm
  obtain ⟨v, ⟨hv, hvQ⟩, -⟩ := hQ.existsUnique_contMDiff_comp_eq hQs le_rfl hu hfac
  -- The integral over the torus is a period.
  have hper := AddCircle.integralTopForm_mpullback_mem_range_closedFormHomologyPeriod 1 1 σ hv
  -- It is the integral over the fundamental square of `v^* σ` on the standard frame.
  have hσ : IsSmoothForm I 1 σ.val.val := σ.val.isSmoothForm.of_le (by simp)
  have hint : IntegrableTopForm (mpullback (𝓘(ℝ).prod 𝓘(ℝ)) I v σ.val.val) :=
    (hσ.mpullback (hv.of_le (by simp))).integrableTopForm
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
      (Module.Basis.finTwoProd ℝ)
  rw [AddCircle.integralTopForm_prod_eq_setIntegral 1 1 hint 0 0] at hper
  -- Since `Q` has derivative the identity, that integrand is the one of `u^* σ`.
  have hpt (z : ℝ × ℝ) :
      mpullback (𝓘(ℝ).prod 𝓘(ℝ)) I v σ.val.val
          ((z.1 : AddCircle (1 : ℝ)), (z.2 : AddCircle (1 : ℝ)))
        ![(1, 0), (0, 1)] = mpullback 𝓘(ℝ, ℝ × ℝ) I u σ.val.val z ![(1, 0), (0, 1)] := by
    symm
    rw [← hvQ, mpullback_comp_at (hQ.contMDiff.mdifferentiableAt (by simp) (x := z))
      (hv.mdifferentiableAt (by simp)), mpullback_apply, AddCircle.mfderiv_prodMap_coe]
    -- The identity of `ℝ × ℝ` is stated between tangent spaces, which are `ℝ × ℝ` by definition,
    -- so the lemmas about `ContinuousLinearMap.id` do not apply as rewrites here.
    rfl
  simp_rw [hpt, zero_add] at hper
  -- By Fubini (`IsSmoothForm.setIntegral_eq_rectangleIntegral`) the rectangle integral is the
  -- integral over the closed square, which differs from the half-open one by a null set.
  rw [← (hσ.of_le zero_le_one).setIntegral_eq_rectangleIntegral (hu.of_le (by simp))
    (a := (0, 0)) (b := (1, 1)) (by simp), Icc_prod_eq, Measure.volume_eq_prod]
  rw [Measure.volume_eq_prod,
    setIntegral_congr_set (Measure.set_prod_ae_eq Ico_ae_eq_Icc Ico_ae_eq_Icc)] at hper
  convert hper using 3
  simp only [mpullback_apply]
  refine congrArg _ (funext fun j ↦ ?_)
  fin_cases j <;> simp

end TauCeti

end
