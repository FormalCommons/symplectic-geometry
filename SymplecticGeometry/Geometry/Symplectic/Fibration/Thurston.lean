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
public import TauCeti.Geometry.Symplectic.Manifold.Orientation
public import SymplecticGeometry.Geometry.Symplectic.Fibration.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Manifold.FiberBundle.MapFiber
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Atlas
import SymplecticGeometry.Geometry.Symplectic.Orientation
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
all points (`TauCeti.SmoothTwoForm.exists_forall_ge_forall_nondegenerate_add_smul_comp`). Only
the vertical nondegeneracy of `τ` is used for this
(`TauCeti.MapFiber.Atlas.exists_forall_ge_forall_nondegenerate_add_smul_comp`).

The same bound makes the forms compatible with an oriented atlas, in the sense of
`TauCeti.MapFiber.Atlas.IsOrientedCompatible`, when the fibre pull-backs of `τ` have the
orientation `oF` of the model fibre and the base carries the orientation of `β`. The fibre
pull-backs of `τ + K π^* β` are those of `τ`
(`Bundle.Trivialization.mpullback_fiberInclusionMap_add_smul_mpullback`). At a point `x` of a
chart, the derivative of the chart is a linear equivalence `T_x M ≃ T B × T F` whose first
component is `d_x π` and which carries `τ_x` on the vertical vectors to the fibre pull-back of
`τ`. As the form stays nondegenerate for every `K ≥ K₀`, the library's
`TauCeti.SymplecticForm.map_orientation_of_forall_ge_nondegenerate_add_smul_comp` shows that the
chart carries its symplectic orientation to the product orientation.

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
* `TauCeti.MapFiber.Atlas.exists_forall_ge_isOrientedCompatible_add_smul_mpullback`: for compact
  `M`, if the fibre pull-backs of a closed `τ` are nondegenerate with orientation `oF`, there is
  `K₀` such that for every `K ≥ K₀` the form `τ + K π^* β` is compatible with the oriented atlas
  `A`, for the orientation of `β` on the base and `oF` on the fibre.
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

omit [IsManifold IF ∞ F] in
/-- **Thurston's forms are pointwise nondegenerate for large `K`.** Let `A` be a smooth atlas of
`proj : M → B` with `M` compact, `τ` a two-form on `M` that is vertically nondegenerate for
`proj`, and `β` a nondegenerate two-form on `B`. Then there is `K₀` such that, for every `K ≥ K₀`
and every point `x`, the bilinear form `τ_x + K β_{proj x}(d_x proj ·, d_x proj ·)` is
nondegenerate. -/
theorem exists_forall_ge_forall_nondegenerate_add_smul_comp [CompactSpace M]
    (hA : A.IsContMDiff ∞ IB IF IM) (hv : SmoothTwoForm.IsVerticallyNondegenerate IB proj τ)
    {β : SmoothTwoForm IB B} (hβ : β.IsNondegenerate) :
    ∃ K₀ : ℝ, ∀ K ≥ K₀, ∀ x, (τ.bilinFormAt x + K • (β.bilinFormAt (proj x)).comp
      (mfderiv IM IB proj x : TangentSpace IM x →ₗ[ℝ] _) (mfderiv IM IB proj x)).Nondegenerate :=
  SmoothTwoForm.exists_forall_ge_forall_nondegenerate_add_smul_comp
    (hA.contMDiff_proj.of_le (by simp)) τ β (fun x ↦ hβ.nondegenerate_bilinFormAt (proj x))
      fun x ↦ (LinearMap.BilinForm.nondegenerate_pullbackProd_zero_iff
        (SmoothForm.isAlt_bilinFormAt τ x) (SmoothForm.isAlt_bilinFormAt β (proj x))
        (hβ.nondegenerate_bilinFormAt (proj x)) (hA.surjective_mfderiv (by simp) x)).2
        (SmoothTwoForm.isVerticallyNondegenerate_iff.1 hv x)

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
  obtain ⟨K₀, hK₀⟩ := exists_forall_ge_forall_nondegenerate_add_smul_comp hA
    (hτ.isVerticallyNondegenerate hA hσ) hβ.isNondegenerate
  refine ⟨K₀, fun K hK ↦ ⟨⟨hτc.add ((hβ.isClosed.mpullback _ _).smul K),
    SmoothTwoForm.isNondegenerate_def.2 fun x ↦ ?_⟩, hτ.add_mpullback two_ne_zero _ β K⟩⟩
  simpa using hK₀ K hK x

/-- At a point of the source of a chart, the chart carries the symplectic orientation of a
nondegenerate form `τ + K proj^* β` with `K ≥ K₀`, where `K₀` is as in
`exists_forall_ge_forall_nondegenerate_add_smul_comp`, to the product of the symplectic
orientation of `β` and the symplectic orientation of the fibre pull-back of `τ`. -/
private theorem isOrientationPreservingAt_add_smul_mpullback [FiniteDimensional ℝ EF] {m k : ℕ}
    (hA : A.IsContMDiff ∞ IB IF IM) {oF : TauCeti.Manifold.Orientation IF F (Fin k)}
    (hτ : ∀ b b' (hb' : b' ∈ (A.trivAt b).baseSet),
      SmoothTwoForm.IsNondegenerate (SmoothForm.mpullback ((A.trivAt b).fiberInclusionMap hb')
        ((A.trivAt b).contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm b) hb') τ))
    (hτo : ∀ b b' (hb' : b' ∈ (A.trivAt b).baseSet),
      (hτ b b' hb').orientation (oF.card_eq.symm.trans (Fintype.card_fin k)) = oF)
    {β : SmoothTwoForm IB B} (hβ : β.IsNondegenerate) (hm : Module.finrank ℝ EB = m) {K₀ : ℝ}
    (hK₀ : ∀ K ≥ K₀, ∀ x, (τ.bilinFormAt x + K • (β.bilinFormAt (proj x)).comp
      (mfderiv IM IB proj x : TangentSpace IM x →ₗ[ℝ] _) (mfderiv IM IB proj x)).Nondegenerate)
    {K : ℝ} (hK : K₀ ≤ K)
    (hω : (τ + K • SmoothForm.mpullback proj hA.contMDiff_proj β).IsNondegenerate)
    (hM : Module.finrank ℝ EM = m + k) {b : B} {x : M} (hx : x ∈ (A.trivAt b).source) :
    TauCeti.Manifold.Orientation.IsOrientationPreservingAt (hω.orientation hM)
      ((hβ.orientation hm).prod oF) (A.trivAt b) x := by
  -- Write `x` as the image of `v` under the fibre inclusion over `b'`.
  obtain ⟨b', hb', v, rfl⟩ : ∃ (b' : B) (hb' : b' ∈ (A.trivAt b).baseSet) (v : F),
      (A.trivAt b).fiberInclusionMap hb' v = x :=
    ⟨proj x, (A.trivAt b).mem_source.1 hx, _, (A.trivAt b).fiberInclusionMap_snd_apply _⟩
  have hd : (A.trivAt b).toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF) :=
    hA.mdifferentiable_trivAt (n := ∞) (by simp) b
  have hpy : proj ((A.trivAt b).fiberInclusionMap hb' v) = b' :=
    (A.trivAt b).proj_fiberInclusionMap hb' v
  -- The inverse of the derivative of the chart sends `(0, w)` to the derivative of the fibre
  -- inclusion applied to `w`.
  have hsymm (w : TangentSpace IF v) : (hd.mfderiv hx).symm (0, w) =
      mfderiv IF IM ((A.trivAt b).fiberInclusionMap hb') v w := by
    have hey : (A.trivAt b).toOpenPartialHomeomorph ((A.trivAt b).fiberInclusionMap hb' v) =
        (b', v) := (A.trivAt b).apply_fiberInclusionMap hb' v
    rw [(A.trivAt b).mfderiv_fiberInclusionMap_apply hb' v
      (hd.mdifferentiableAt_symm ((A.trivAt b).mem_target.2 hb')), hd.coe_mfderiv_symm hx, hey]
  rw [TauCeti.Manifold.Orientation.isOrientationPreservingAt_iff]
  refine ⟨hd.mfderiv hx, ContinuousLinearMap.ext fun u ↦ congrFun (hd.coe_mfderiv hx) u, ?_⟩
  rw [TauCeti.SmoothTwoForm.IsNondegenerate.orientationAt_orientation,
    TauCeti.Manifold.Orientation.orientationAt_prod,
    show ((A.trivAt b) ((A.trivAt b).fiberInclusionMap hb' v)).1 = b' by simp,
    show ((A.trivAt b) ((A.trivAt b).fiberInclusionMap hb' v)).2 = v by simp, ← hτo b b' hb',
    TauCeti.SmoothTwoForm.IsNondegenerate.orientationAt_orientation,
    TauCeti.SmoothTwoForm.IsNondegenerate.orientationAt_orientation]
  refine TauCeti.SymplecticForm.map_orientation_of_forall_ge_nondegenerate_add_smul_comp
    (L := (mfderiv IM IB proj ((A.trivAt b).fiberInclusionMap hb' v)).toLinearMap)
    (τ := τ.bilinFormAt ((A.trivAt b).fiberInclusionMap hb' v))
    _ _ (hd.mfderiv hx).toLinearEquiv (fun u ↦ ?_) (fun w w' ↦ ?_) (fun c hc ↦ ?_) hK _ ?_ hm _ hM
  · exact ((A.trivAt b).mfderiv_proj_apply hx (hd.mdifferentiableAt hx) u).symm
  · refine (congrArg₂ (fun a c ↦ τ.bilinFormAt _ a c) (hsymm w) (hsymm w')).trans ?_
    beta_reduce
    rw [TauCeti.SmoothTwoForm.IsNondegenerate.toBilinForm_symplecticFormAt,
      SmoothForm.bilinFormAt_apply]
    exact ((SmoothForm.bilinFormAt_apply _ v w w').trans
      (SmoothForm.eval₂_mpullback _ _ τ v w w')).symm
  · rw [TauCeti.SmoothTwoForm.IsNondegenerate.toBilinForm_symplecticFormAt]
    have h := hK₀ c hc ((A.trivAt b).fiberInclusionMap hb' v)
    rw [hpy] at h
    exact h
  · rw [TauCeti.SmoothTwoForm.IsNondegenerate.toBilinForm_symplecticFormAt,
      TauCeti.SmoothTwoForm.IsNondegenerate.toBilinForm_symplecticFormAt,
      SmoothForm.bilinFormAt_add, SmoothForm.bilinFormAt_smul, SmoothForm.bilinFormAt_mpullback,
      hpy]

/-- **Thurston's forms are compatible with an oriented atlas for large `K`.** Let `A` be a smooth
atlas of `proj : M → B` with `M` compact, `oF` an orientation of the model fibre, and `τ` a closed
two-form on `M` whose pull-back to every fibre, read through a chart of `A`, is nondegenerate with
symplectic orientation `oF`. For a symplectic form `β` on `B` there is `K₀` such that, for every
`K ≥ K₀`, the form `τ + K proj^* β` is compatible with `A` for the symplectic orientation of `β`
on the base and `oF` on the fibre. -/
theorem exists_forall_ge_isOrientedCompatible_add_smul_mpullback [FiniteDimensional ℝ EF]
    [CompactSpace M] {m k : ℕ} (hA : A.IsContMDiff ∞ IB IF IM)
    {oF : TauCeti.Manifold.Orientation IF F (Fin k)}
    (hτ : ∀ b b' (hb' : b' ∈ (A.trivAt b).baseSet),
      SmoothTwoForm.IsNondegenerate (SmoothForm.mpullback ((A.trivAt b).fiberInclusionMap hb')
        ((A.trivAt b).contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm b) hb') τ))
    (hτo : ∀ b b' (hb' : b' ∈ (A.trivAt b).baseSet),
      (hτ b b' hb').orientation (oF.card_eq.symm.trans (Fintype.card_fin k)) = oF)
    (hτc : τ.IsClosed) {β : SmoothTwoForm IB B} (hβ : β.IsSymplectic)
    (hm : Module.finrank ℝ EB = m) :
    ∃ K₀ : ℝ, ∀ K ≥ K₀, A.IsOrientedCompatible hA (hβ.isNondegenerate.orientation hm) oF
      (τ + K • SmoothForm.mpullback proj hA.contMDiff_proj β) := by
  obtain ⟨K₀, hK₀⟩ := exists_forall_ge_forall_nondegenerate_add_smul_comp hA
    (isVerticallyNondegenerate_of_isNondegenerate_mpullback hA fun b ↦
      hτ b b (A.mem_baseSet_trivAt b)) hβ.isNondegenerate
  have hfib (K : ℝ) (b b' : B) (hb' : b' ∈ (A.trivAt b).baseSet) :=
    (A.trivAt b).mpullback_fiberInclusionMap_add_smul_mpullback hb'
      ((A.trivAt b).contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm b) hb') two_ne_zero
      hA.contMDiff_proj τ β K
  have hω (K : ℝ) (hK : K ≥ K₀) :
      (τ + K • SmoothForm.mpullback proj hA.contMDiff_proj β).IsNondegenerate :=
    SmoothTwoForm.isNondegenerate_def.2 fun x ↦ by simpa using hK₀ K hK x
  refine ⟨K₀, fun K hK ↦ ⟨⟨hτc.add ((hβ.isClosed.mpullback _ _).smul K), hω K hK⟩,
    fun b b' hb' ↦ hfib K b b' hb' ▸ hτ b b' hb', fun b b' hb' ↦ ?_, fun b x hx ↦ ?_⟩⟩
  · convert hτo b b' hb' using 2
    exact hfib K b b' hb'
  · -- The chart identifies the tangent space of `M` with that of `B × F`.
    have hM : Module.finrank ℝ EM = m + k := by
      have h₁ : Module.finrank ℝ EM = Module.finrank ℝ (EB × EF) :=
        ((hA.mdifferentiable_trivAt (n := ∞) (by simp) b).mfderiv hx).toLinearEquiv.finrank_eq
      have h₂ := oF.card_eq
      rw [Module.finrank_prod, hm] at h₁
      simp only [Fintype.card_fin] at h₂
      omega
    exact ⟨hM, isOrientationPreservingAt_add_smul_mpullback hA hτ hτo hβ.isNondegenerate hm hK₀
      hK (hω K hK) hM hx⟩

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
