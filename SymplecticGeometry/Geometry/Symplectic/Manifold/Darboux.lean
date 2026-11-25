/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.TransAffine
public import TauCeti.Geometry.Symplectic.Manifold.Darboux
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Darboux charts with a prescribed derivative

Let `σ` be a closed two-form on a manifold `M` modelled on a finite-dimensional real space `E`,
let `p` be an interior point of `M`, let `(F, form₀)` be a symplectic vector space, and let
`A : T_p M ≃ F` be a linear isomorphism with `form₀ (A v) (A w) = σ_p v w`. Then there is a smooth
partial diffeomorphism `chart` from `M` to `F`, defined near `p`, with `chart p = 0`, with
derivative `A` at `p`, which pulls the constant form `form₀` back to `σ` on its source.

The proof composes a Darboux chart `χ` of Tau Ceti with the linear map `A ∘ (dχ_p)⁻¹`, which is a
linear symplectomorphism because `χ` already pulls a constant form back to `σ`. Only the centre of
the chart is constrained, so no Moser argument is needed beyond the one in Tau Ceti's theorem.

Any two charts that pull the same constant form back to `σ` have transition maps whose
derivatives preserve that form.

## Main results

* `TauCeti.SmoothTwoForm.trans_toDiffeomorph_darbouxChart`: composing a Darboux chart with a
  linear symplectomorphism gives a Darboux chart for the target form, with the composed
  derivative at every point.
* `TauCeti.SmoothTwoForm.transAffine_darbouxChart`: so does following a Darboux chart by an affine
  map `z ↦ A (z - p)` whose linear part `A` preserves the constant form.
* `TauCeti.SymplecticForm.apply_fderiv_transition_eq`: the derivatives of transition maps between
  two Darboux charts for the same constant form preserve that form.
* `TauCeti.SmoothTwoForm.exists_darbouxChart_mvfderiv_eq_of_isInteriorPoint`: Darboux charts with
  a prescribed derivative at an interior point, for a closed two-form.
* `TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_mvfderiv_eq`: Darboux charts with a
  prescribed derivative on a boundaryless symplectic manifold.

`trans_toDiffeomorph_darbouxChart` and its proof adapt Tau Ceti's private
`TauCeti.SmoothTwoForm.trans_toDiffeomorph_darboux`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 3.2.2 and Corollary 3.2.3.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- Composing a chart `chart` into `F₁` that pulls `form₁` back to `σ` with a linear
symplectomorphism `L : (F₁, form₁) ≃ (F₂, form₂)` gives a chart into `F₂` with the same source,
with values `L ∘ chart` and derivative `L ∘ d chart` at every point, which pulls `form₂` back to `σ`
on the source. -/
theorem trans_toDiffeomorph_darbouxChart {F₁ F₂ : Type*}
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    {σ : SmoothTwoForm I M} {form₁ : SymplecticForm F₁} {form₂ : SymplecticForm F₂}
    {chart : PartialDiffeomorph I 𝓘(ℝ, F₁) M F₁ ∞}
    (hchart : ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
      σ.eval₂ x v w = form₁ (mvfderiv I chart x v) (mvfderiv I chart x w))
    (L : F₁ ≃L[ℝ] F₂) (hL : SymplecticForm.IsSymplectomorphism form₁ form₂ L.toLinearEquiv) :
    let chart' := chart.trans L.toDiffeomorph.toPartialDiffeomorph
    chart'.source = chart.source ∧ (∀ x, chart' x = L (chart x)) ∧
      (∀ x, mvfderiv I chart' x = L.toContinuousLinearMap.comp (mvfderiv I chart x)) ∧
      ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        σ.eval₂ x v w = form₂ (mvfderiv I chart' x v) (mvfderiv I chart' x w) := by
  intro chart'
  have hsrc : chart'.source = chart.source := by simp [chart']
  have hcoe (y : M) : chart' y = L (chart y) := by simp [chart']
  have hderiv (x : M) :
      mvfderiv I chart' x = L.toContinuousLinearMap.comp (mvfderiv I chart x) := by
    ext v
    rw [show ⇑chart' = ⇑L ∘ ⇑chart from funext hcoe, L.mvfderiv_comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  refine ⟨hsrc, hcoe, hderiv, fun x hx v w ↦ ?_⟩
  rw [hderiv x, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ← ContinuousLinearEquiv.coe_toLinearEquiv, hL.apply,
    hchart x hx v w]

/-- If a chart `φ` into `F` pulls the constant form `form₀` back to `σ` on its source, and `A`
preserves `form₀`, then the chart `φ.transAffine p A`, which is `φ` followed by
`z ↦ A (z - p)`, also pulls `form₀` back to `σ` on the source of `φ`. -/
theorem transAffine_darbouxChart {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {σ : SmoothTwoForm I M} {form₀ : SymplecticForm F} {φ : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞}
    (hφ : ∀ x ∈ φ.source, ∀ v w : TangentSpace I x,
      σ.eval₂ x v w = form₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (p : F) {A : F ≃L[ℝ] F} (hA : SymplecticForm.IsSymplectomorphism form₀ form₀ A.toLinearEquiv)
    (x : M) (hx : x ∈ φ.source) (v w : TangentSpace I x) :
    σ.eval₂ x v w =
      form₀ (mvfderiv I (φ.transAffine p A) x v) (mvfderiv I (φ.transAffine p A) x w) := by
  have hτ : ∀ y ∈ (φ.transSubRight p).source, ∀ v w : TangentSpace I y,
      σ.eval₂ y v w = form₀ (mvfderiv I (φ.transSubRight p) y v)
        (mvfderiv I (φ.transSubRight p) y w) := by
    intro y hy v w
    rw [PartialDiffeomorph.transSubRight_source] at hy
    rw [φ.mvfderiv_transSubRight p hy, hφ y hy]
  rw [PartialDiffeomorph.transAffine_def]
  exact (trans_toDiffeomorph_darbouxChart hτ A hA).2.2.2 x (by simpa using hx) v w

end SmoothTwoForm

namespace SymplecticForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Let `φ` and `ψ` be charts into `F`, and `x` a point of both sources at which both pull the
constant form `form₀` back to the same two-form `σ`. Then the derivative of the transition map
`ψ ∘ φ⁻¹` at `φ x` preserves `form₀`. -/
theorem apply_fderiv_transition_eq (form₀ : SymplecticForm F) {σ : SmoothTwoForm I M}
    {φ ψ : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞} {x : M} (hxφ : x ∈ φ.source)
    (hxψ : x ∈ ψ.source)
    (hφ : ∀ v w : TangentSpace I x, σ.eval₂ x v w = form₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hψ : ∀ v w : TangentSpace I x, σ.eval₂ x v w = form₀ (mvfderiv I ψ x v) (mvfderiv I ψ x w))
    (v w : F) :
    form₀ (fderiv ℝ (fun z ↦ ψ (φ.symm z)) (φ x) v)
        (fderiv ℝ (fun z ↦ ψ (φ.symm z)) (φ x) w) = form₀ v w := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  obtain ⟨a, rfl⟩ := (φ.bijective_mvfderiv hn hxφ).surjective v
  obtain ⟨b, rfl⟩ := (φ.bijective_mvfderiv hn hxφ).surjective w
  have hcomp (a : TangentSpace I x) :
      fderiv ℝ (fun z ↦ ψ (φ.symm z)) (φ x) (mvfderiv I φ x a) = mvfderiv I ψ x a := by
    have h := φ.mfderiv_symm_trans_apply_mfderiv_apply ψ hn hxφ hxψ a
    rwa [PartialDiffeomorph.coe_trans, mfderiv_eq_fderiv, ← mvfderiv_apply_eq_mfderiv_apply,
      ← mvfderiv_apply_eq_mfderiv_apply] at h
  rw [hcomp, hcomp, ← hψ, hφ]

end SymplecticForm

namespace SmoothTwoForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Darboux charts with a prescribed derivative, at an interior point.** Let `σ` be a closed
two-form on `M`, `p` an interior point, and `A : T_p M ≃ F` a linear isomorphism onto a symplectic
vector space `(F, form₀)` with `form₀ (A v) (A w) = σ_p v w`. Then there is a smooth partial
diffeomorphism `chart` from `M` to `F` whose source contains `p`, with `chart p = 0` and
`d chart_p = A`, which pulls `form₀` back to `σ` on its source. -/
theorem exists_darbouxChart_mvfderiv_eq_of_isInteriorPoint {σ : SmoothTwoForm I M}
    (hσ : σ.IsClosed) (form₀ : SymplecticForm F) {p : M} (hp : I.IsInteriorPoint p)
    (A : TangentSpace I p ≃L[ℝ] F) (hA : ∀ v w, form₀ (A v) (A w) = σ.eval₂ p v w) :
    ∃ chart : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞,
      p ∈ chart.source ∧ chart p = 0 ∧ mvfderiv I chart p = A.toContinuousLinearMap ∧
      ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        σ.eval₂ x v w = form₀ (mvfderiv I chart x v) (mvfderiv I chart x w) := by
  -- `σ_p` is `form₀` transported along `A⁻¹`, hence nondegenerate.
  have hbil : σ.bilinFormAt p = (form₀.transport A.symm.toLinearEquiv).toBilinForm := by
    ext v w
    rw [SmoothForm.bilinFormAt_apply, ← hA]
    simp
  obtain ⟨χ, form₁, hpχ, hχp, hχ⟩ := exists_darbouxChart_of_nondegenerate_of_isInteriorPoint hσ
    (hbil ▸ (form₀.transport A.symm.toLinearEquiv).nondegenerate) hp
  -- The derivative of `χ` at `p` is a linear isomorphism `D`.
  let D : TangentSpace I p ≃L[ℝ] E :=
    (LinearEquiv.ofBijective _ (χ.bijective_mvfderiv (by simp) hpχ)).toContinuousLinearEquiv
  have hD (v : TangentSpace I p) : D v = mvfderiv I χ p v := by
    rw [LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.ofBijective_apply,
      ContinuousLinearMap.coe_coe]
  -- `B := A ∘ D⁻¹` is a linear symplectomorphism from `(E, form₁)` to `(F, form₀)`.
  let B : E ≃L[ℝ] F := D.symm.trans A
  have hB : SymplecticForm.IsSymplectomorphism form₁ form₀ B.toLinearEquiv := by
    refine SymplecticForm.isSymplectomorphism_iff.2 fun u w ↦ ?_
    obtain ⟨a, rfl⟩ := D.surjective u
    obtain ⟨b, rfl⟩ := D.surjective w
    rw [ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_apply_apply,
      ContinuousLinearEquiv.symm_apply_apply, hA, hD, hD]
    exact hχ p hpχ a b
  obtain ⟨hsrc, hcoe, hderiv, hpull⟩ := trans_toDiffeomorph_darbouxChart hχ B hB
  refine ⟨_, hsrc ▸ hpχ, by rw [hcoe, hχp, map_zero], ?_, fun x hx ↦ hpull x (hsrc ▸ hx)⟩
  ext v
  rw [hderiv p, ContinuousLinearMap.comp_apply, ← hD]
  simp [B]

/-- **Darboux charts with a prescribed derivative.** Let `(M, σ)` be a boundaryless symplectic
manifold modelled on a finite-dimensional space, `p : M`, and `A : T_p M ≃ F` a linear
symplectomorphism onto a symplectic vector space `(F, form₀)`, that is
`form₀ (A v) (A w) = σ_p v w`. Then there is a smooth partial diffeomorphism `chart` from `M` to
`F` whose source contains `p`, with `chart p = 0` and `d chart_p = A`, which pulls `form₀` back to
`σ` on its source.

For `F = StdSpace (Fin n)` and `form₀ = stdForm (Fin n)`, such charts cover `M`:
at each point `p`, a linear symplectomorphism `A` from `T_p M` onto the standard model exists by
the linear Darboux theorem `SymplecticGeometry.exists_isSymplectomorphism_stdForm`, applied to the
symplectic form `σ_p`. Their transition maps have symplectic derivatives by
`TauCeti.SymplecticForm.apply_fderiv_transition_eq`. Darboux charts into the model space `E` at
every point are Tau Ceti's
`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_of_symplecticForm`.

Milestone: *Darboux theorem with prescribed derivative*. -/
theorem IsSymplectic.exists_darbouxChart_mvfderiv_eq [BoundarylessManifold I M]
    {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic) (form₀ : SymplecticForm F) {p : M}
    (A : TangentSpace I p ≃L[ℝ] F) (hA : ∀ v w, form₀ (A v) (A w) = σ.eval₂ p v w) :
    ∃ chart : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞,
      p ∈ chart.source ∧ chart p = 0 ∧ mvfderiv I chart p = A.toContinuousLinearMap ∧
      ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        σ.eval₂ x v w = form₀ (mvfderiv I chart x v) (mvfderiv I chart x w) :=
  exists_darbouxChart_mvfderiv_eq_of_isInteriorPoint hσ.isClosed form₀
    BoundarylessManifold.isInteriorPoint A hA

end SmoothTwoForm

end TauCeti

end
