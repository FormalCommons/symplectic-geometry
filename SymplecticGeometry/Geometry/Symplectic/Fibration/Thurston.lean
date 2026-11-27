/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.RestrictsTo
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Symplectic.Fibration.Basic
import SymplecticGeometry.Geometry.Symplectic.Manifold.Family
import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import SymplecticGeometry.Geometry.Symplectic.Manifold.TwoForm

/-!
# Thurston's forms on symplectic fibrations

Let `A` be a smooth atlas of a map `π : M → B` with model fibre `F`, let `σ` be a nondegenerate
two-form on `F`, and let `τ` be a closed two-form on `M` that restricts to `σ` along `A`. For a
symplectic form `β` on `B`, the forms `τ + K π^* β` all restrict to `σ` along `A` and are closed.
When `M` is compact, they are moreover nondegenerate, hence symplectic, for every large enough
`K`. This is step 2 of the proof of Thurston's theorem on symplectic fibrations
([McDuffSalamon2017], Theorem 6.1.4; [Thurston1976]).

At a point `x`, the bilinear form of `τ + K π^* β` is `τ_x + K β_{π x}(d_x π ·, d_x π ·)`.
The derivative `d_x π` is onto, and `τ_x` is nondegenerate on its kernel since `τ` restricts to
the nondegenerate `σ` (`TauCeti.MapFiber.Atlas.RestrictsTo.isVerticallyNondegenerate`). So the
form `LinearMap.BilinForm.pullbackProd` of these data at the parameter `0` is nondegenerate
(`LinearMap.BilinForm.nondegenerate_pullbackProd_zero_iff`), and the openness of this condition
in the point and the parameter, together with the compactness of `M`, gives one bound `K₀` for
all points (`TauCeti.SmoothTwoForm.exists_forall_ge_forall_nondegenerate_add_smul_comp`).

## Main results

* `TauCeti.MapFiber.Atlas.exists_forall_ge_isSymplectic_add_smul_mpullback`: for compact `M`,
  there is `K₀` such that for every `K ≥ K₀` the form `τ + K π^* β` is symplectic and restricts
  to `σ` along `A`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.1 (Theorem 6.1.4, step 2 of its proof).
* [W. P. Thurston, *Some simple examples of symplectic manifolds*][Thurston1976].
* [V. Guillemin, E. Lerman and S. Sternberg, *Symplectic Fibrations and Multiplicity
  Diagrams*][GuilleminLermanSternberg1996], §1.5
-/

public section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.MapFiber.Atlas

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*}
  [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  [IsManifold IF ∞ F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} {M : Type*}
  [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M]
  {proj : M → B} {A : Atlas F proj} {σ : SmoothTwoForm IF F} {τ : SmoothTwoForm IM M}

/-- **Thurston's forms are symplectic for large `K`.** Let `A` be a smooth atlas of
`proj : M → B` with `M` compact, `σ` a nondegenerate two-form on the model fibre, and `τ` a closed
two-form on `M` that restricts to `σ` along `A`. For a symplectic form `β` on `B` there is `K₀`
such that, for every `K ≥ K₀`, the form `τ + K proj^* β` is symplectic and restricts to `σ`
along `A`. -/
theorem exists_forall_ge_isSymplectic_add_smul_mpullback [CompactSpace M]
    (hA : A.IsContMDiff ∞ IB IF IM) (hσ : σ.IsNondegenerate) (hτ : A.RestrictsTo σ τ)
    (hτc : τ.IsClosed) {β : SmoothTwoForm IB B} (hβ : β.IsSymplectic) :
    ∃ K₀ : ℝ, ∀ K ≥ K₀,
      (τ + K • SmoothForm.mpullback proj hA.contMDiff_proj β).IsSymplectic ∧
        A.RestrictsTo σ (τ + K • SmoothForm.mpullback proj hA.contMDiff_proj β) := by
  have hv := hτ.isVerticallyNondegenerate hA hσ
  have hβx := hβ.isNondegenerate.nondegenerate_bilinFormAt
  obtain ⟨K₀, hK₀⟩ := SmoothTwoForm.exists_forall_ge_forall_nondegenerate_add_smul_comp
    (hA.contMDiff_proj.of_le (by simp)) τ β (fun x ↦ hβx (proj x)) fun x ↦
      (LinearMap.BilinForm.nondegenerate_pullbackProd_zero_iff (SmoothForm.isAlt_bilinFormAt τ x)
        (SmoothForm.isAlt_bilinFormAt β (proj x)) (hβx (proj x))
        (hA.surjective_mfderiv (by simp) x)).2
        (SmoothTwoForm.isVerticallyNondegenerate_iff.1 hv x)
  refine ⟨K₀, fun K hK ↦ ⟨⟨hτc.add ((hβ.isClosed.mpullback _ _).smul K),
    SmoothTwoForm.isNondegenerate_def.2 fun x ↦ ?_⟩, hτ.add_mpullback two_ne_zero _ β K⟩⟩
  simpa using hK₀ K hK x

end TauCeti.MapFiber.Atlas

end
