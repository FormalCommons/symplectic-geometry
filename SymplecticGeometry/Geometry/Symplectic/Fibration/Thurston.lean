/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.RestrictsTo
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import SymplecticGeometry.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DeRham.Map
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Symplectic.Fibration.Basic
import SymplecticGeometry.Geometry.Symplectic.Fibration.ClosedExtension
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

Thurston's theorem itself follows. Over a connected base whose atlas has coordinate changes
preserving `σ`, a degree-two class that one fibre inclusion sends to `[σ]` is sent there by all
of them (`TauCeti.MapFiber.Atlas.forall_map_eq_of_map_eq`), and is then the class of a closed
form `τ` that restricts to `σ` (`TauCeti.MapFiber.Atlas.exists_isClosed_restricts_of_map_eq`,
step 1). Step 2 applied to `τ` gives the forms, and their class is `a + K [π^* β]` since
taking classes is linear.

## Main results

* `TauCeti.MapFiber.Atlas.exists_forall_ge_isSymplectic_add_smul_mpullback`: for compact `M`,
  there is `K₀` such that for every `K ≥ K₀` the form `τ + K π^* β` is symplectic and restricts
  to `σ` along `A`.
* `TauCeti.MapFiber.Atlas.exists_isSymplectic_restricts_mk_eq`: Thurston's theorem on
  symplectic fibrations. For compact `M` over a connected symplectic base `(B, β)`, and a class
  `a` that one fibre inclusion sends to `[σ]`, for every large enough `K` some symplectic form
  that restricts to `σ` along `A` represents `a + K [π^* β]`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.1 (Theorem 6.1.4 and step 2 of its proof).
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

/-- **Thurston's theorem on symplectic fibrations.** Let `A` be a smooth atlas of
`proj : M → B` with compact total space, whose coordinate changes preserve a symplectic form `σ`
on the model fibre, over a connected, Hausdorff, σ-compact base with a symplectic form `β`. Let
`a` be a de Rham class of degree two on `M` that the fibre inclusion
`v ↦ (A.trivAt b)⁻¹ (b', v)` of one chart over one point sends to the class of `σ`. Then there
is `K₀` such that, for every `K ≥ K₀`, some symplectic form `θ` on `M` restricts to `σ` along `A`
and represents the class `a + K [proj^* β]`.

Milestone: *Thurston's theorem on symplectic fibrations*. -/
theorem exists_isSymplectic_restricts_mk_eq [CompactSpace M] [PreconnectedSpace B] [T2Space B]
    [SigmaCompactSpace B] (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ)) (hσ : σ.IsSymplectic)
    {β : SmoothTwoForm IB B} (hβ : β.IsSymplectic) {a : deRhamCohomology IM M 2} {b b' : B}
    (hb' : b' ∈ (A.trivAt b).baseSet)
    (ha : deRhamCohomology.map ((A.trivAt b).fiberInclusionMap hb')
        ((A.trivAt b).contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm b) hb') 2 a =
      deRhamCohomology.mk IF 2 ⟨σ, hσ.isClosed.mem_closedForms⟩) :
    ∃ K₀ : ℝ, ∀ K ≥ K₀, ∃ θ : SmoothTwoForm IM M, ∃ hθ : θ.IsSymplectic, A.RestrictsTo σ θ ∧
      deRhamCohomology.mk IM 2 ⟨θ, hθ.isClosed.mem_closedForms⟩ =
        a + K • deRhamCohomology.mk IM 2
          ⟨SmoothForm.mpullback proj hA.contMDiff_proj β,
            (hβ.isClosed.mpullback _ _).mem_closedForms⟩ := by
  obtain ⟨τ, hτc, hτ, rfl⟩ := exists_isClosed_restricts_of_map_eq hA hH hσ.isClosed
    fun c c' hc' ↦ forall_map_eq_of_map_eq hA hH hσ.isClosed hb' ha hc'
  obtain ⟨K₀, hK₀⟩ :=
    exists_forall_ge_isSymplectic_add_smul_mpullback hA hσ.isNondegenerate hτ hτc hβ
  refine ⟨K₀, fun K hK ↦ ⟨_, (hK₀ K hK).1, (hK₀ K hK).2, ?_⟩⟩
  refine (congrArg (deRhamCohomology.mk IM 2) (Subtype.ext ?_)).trans
    ((map_add _ _ _).trans (congrArg _ (map_smul _ _ _)))
  simp

end TauCeti.MapFiber.Atlas

end
