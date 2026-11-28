/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Family
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Basic
public import SymplecticGeometry.LinearAlgebra.BilinearForm.Pullback
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.Compactness.Compact
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.VectorBundle.Hom
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth

/-!
# Openness of nondegeneracy for families of two-forms

For a smooth family of two-forms on `M`, given as a smooth two-form `σ` on `N × M` with slices
`σ_t = ι_t^* σ`, the points `(t, x)` at which `σ_t` has an invertible flat map
`T_x M → T_x^* M` form an open subset of `N × M`. When the model space is finite-dimensional,
having an invertible flat map at `x` is the same as being nondegenerate at `x`
(`TauCeti.SmoothTwoForm.isInvertible_flat_iff`). In that case the points at which a single
two-form is nondegenerate form an open set (Tau Ceti's
`TauCeti.SmoothTwoForm.isOpen_setOf_nondegenerate_bilinFormAt`), and, for two two-forms
`σ₀`, `σ₁` on `M`, the points at which every form `σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, is
nondegenerate form an open subset of `M`. The latter are the open sets on which the Moser
fields of Moser's argument are defined ([McDuffSalamon2017], §3.2).

Openness also holds for the family `τ + K f^* β` of the proof of Thurston's theorem on symplectic
fibrations ([McDuffSalamon2017], Theorem 6.1.4, step 2), for a `C^1` map `f : M → B` and
two-forms `τ` on `M` and `β` on `B`, once the parameter `K` is replaced by `s = K⁻¹`, which
makes sense at `s = 0` too ([GuilleminLermanSternberg1996], §1.5). The forms
`LinearMap.BilinForm.pullbackProd τ_x β_{f x} (d_x f) s` on `T_x M × T_{f x} B` are
nondegenerate on an open set of pairs `(s, x)`: in the trivializations of `TM` at `x₀` and of
`TB` at `f x₀`, they are carried to the forms `pullbackProd` of the coordinate expressions, on
`E × E_B` (`TauCeti.SmoothTwoForm.pullbackProd_inCoordinates_flat`), and these depend
continuously on `(s, x)` at `(s₀, x₀)`. When `M` is compact, nondegeneracy at `s = 0` at every
point thus gives one `K₀` such that `τ + K f^* β` is nondegenerate on all of `M` for every
`K ≥ K₀`.

## Main results

* `TauCeti.SmoothTwoForm.isOpen_setOfPred_isInvertible_flat_mpullback_prodMk`: the set of points of
  `N × M` at which the slice has an invertible flat map is open.
* `TauCeti.SmoothTwoForm.isOpen_setOfPred_forall_isInvertible_flat_mpullback_prodMk`: for compact
  `M`, the set of parameters whose slice has invertible flat maps everywhere is open.
* `TauCeti.SmoothTwoForm.isOpen_setOfPred_isInvertible_flat_add_smul_sub`: the same openness for the
  segment `σ₀ + s (σ₁ - σ₀)`, as a set of points `(s, x)` of `ℝ × M`.
* `TauCeti.SmoothTwoForm.isOpen_setOfPred_forall_mem_Icc_nondegenerate`: in finite dimensions, the
  set of points at which the whole segment from `σ₀` to `σ₁` is nondegenerate is open.
* `TauCeti.SmoothTwoForm.isOpen_setOfPred_forall_nondegenerate_bilinFormAt_add_smul`: in finite
  dimensions, for two-forms `σ₀`, `σ` on `M × N` with `M` compact, the set of pairs `(s, y)` of
  `ℝ × N` such that `σ₀ + s σ` is nondegenerate at every point of `M × {y}` is open.
* `TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_interiorEquiv_symm_mpullback_prodMk`: for a
  fixed nondegenerate `σ`, the fields `(σ♭)⁻¹ α_t` of a smooth family of one-forms `α_t` depend
  smoothly on `(t, x)`.
* `TauCeti.SmoothTwoForm.pullbackProd_inCoordinates_flat`: in the trivializations of `TM` and
  `TB`, the form `pullbackProd` of the coordinate expressions of `τ♭_x`, `β♭_{f x}` and `d_x f`
  is `pullbackProd τ_x β_{f x} (d_x f) s` carried along the trivializations.
* `TauCeti.SmoothTwoForm.isOpen_setOfPred_nondegenerate_pullbackProd`: in finite dimensions, for
  a `C^1` map `f`, the set of pairs `(s, x)` at which `pullbackProd τ_x β_{f x} (d_x f) s` is
  nondegenerate is open in `ℝ × M`.
* `TauCeti.SmoothTwoForm.exists_forall_ge_forall_nondegenerate_add_smul_comp`: for compact `M`
  and `β` nondegenerate along `f`, if these forms are nondegenerate at `s = 0` at every point,
  then `τ + K f^* β` is nondegenerate at every point for all large `K`.

The proofs of `isOpen_setOfPred_isInvertible_flat_mpullback_prodMk` and
`isOpen_setOfPred_forall_mem_Icc_nondegenerate` follow Tau Ceti's private
`exists_isOpen_isInvertible_flat`
(`TauCeti/Geometry/Symplectic/Manifold/RelativeMoser.lean`): the flat maps form a continuous
section along a projection, the invertible ones form an open set, and the tube lemma passes to
the compact parameter interval.

The passage from the open set to a bound `K₀` follows this library's
`LinearMap.BilinForm.exists_forall_ge_nondegenerate_add_smul_comp`
(`SymplecticGeometry/LinearAlgebra/BilinearForm/Pullback.lean`), with the tube lemma over
`M` in between.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
* [V. Guillemin, E. Lerman and S. Sternberg, *Symplectic Fibrations and Multiplicity
  Diagrams*][GuilleminLermanSternberg1996], §1.5
-/

public section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace SmoothTwoForm

/-- **Invertibility of the flat maps of a family is an open condition.** For a smooth two-form
`σ` on `N × M`, the set of points `(t, x)` at which the slice `σ_t = ι_t^* σ` has an invertible
flat map `T_x M → T_x^* M` is open in `N × M`. The model space of `M` is assumed complete. -/
theorem isOpen_setOfPred_isInvertible_flat_mpullback_prodMk [CompleteSpace E] {EN HN N : Type*}
    [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold J ∞ N]
    (σ : SmoothForm (J.prod I) (N × M) ℝ 2) :
    IsOpen {p : N × M |
      (flat (SmoothForm.mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) σ)
        p.2).IsInvertible} :=
  -- The bundles and the base map are given explicitly: unification would otherwise read the
  -- section along the identity.
  Continuous.isOpen_setOf_clm_bundle_isInvertible (𝕜 := ℝ) (F₁ := E) (F₂ := E →L[ℝ] ℝ)
    (E₁ := TangentSpace I) (E₂ := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (b := Prod.snd)
    (ϕ := fun p : N × M ↦
      flat (SmoothForm.mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) σ) p.2)
    (ContMDiff.continuous fun p ↦ contMDiffAt_sectionAlong_flat (b := Prod.snd)
      (σ := fun q : N × M ↦
        SmoothForm.mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) σ)
      (SmoothForm.contMDiff_mpullback_prodMk σ p))

/-- **Nondegeneracy of whole slices is an open condition on the parameter.** For a smooth
two-form `σ` on `N × M` with `M` compact, the set of parameters `t` at which the slice
`σ_t = ι_t^* σ` has an invertible flat map at every point of `M` is open in `N`. The model space of
`M` is assumed complete. -/
theorem isOpen_setOfPred_forall_isInvertible_flat_mpullback_prodMk [CompleteSpace E]
    [CompactSpace M] {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    [TopologicalSpace HN]
    {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold J ∞ N]
    (σ : SmoothForm (J.prod I) (N × M) ℝ 2) :
    IsOpen {t : N | ∀ x : M,
      (flat (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ)
        x).IsInvertible} := by
  -- the tube lemma for the compact factor `M`
  exact isOpen_forall_prodMk_mem continuous_id
    (isOpen_setOfPred_isInvertible_flat_mpullback_prodMk σ)

/-- **Invertibility of the flat maps along a segment is an open condition.** For two-forms `σ₀`,
`σ₁` on `M`, the set of points `(s, x)` of `ℝ × M` at which `σ₀ + s (σ₁ - σ₀)` has an invertible
flat map `T_x M → T_x^* M` is open. The model space of `M` is assumed complete. -/
theorem isOpen_setOfPred_isInvertible_flat_add_smul_sub [CompleteSpace E]
    (σ₀ σ₁ : SmoothTwoForm I M) :
    IsOpen {p : ℝ × M | ((σ₀ + p.1 • (σ₁ - σ₀)).flat p.2).IsInvertible} := by
  simpa only [SmoothForm.mpullback_prodMk_lineMapFamily, id_eq] using
    isOpen_setOfPred_isInvertible_flat_mpullback_prodMk
      (SmoothForm.lineMapFamily σ₀ σ₁ (contDiff_id (n := ∞)))

/-- **Nondegeneracy of a segment of two-forms is an open condition.** For two-forms `σ₀`, `σ₁`
on a finite-dimensional manifold, the set of points `x` at which every form
`σ₀ + s (σ₁ - σ₀)` with `s ∈ [0, 1]` is nondegenerate is open. -/
theorem isOpen_setOfPred_forall_mem_Icc_nondegenerate [FiniteDimensional ℝ E]
    (σ₀ σ₁ : SmoothTwoForm I M) :
    IsOpen {x : M | ∀ s ∈ Icc (0 : ℝ) 1,
      ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt x).Nondegenerate} := by
  have hO := isOpen_setOfPred_isInvertible_flat_add_smul_sub σ₀ σ₁
  refine isOpen_iff_forall_mem_open.2 fun x hx ↦ ?_
  have hsub : Icc (0 : ℝ) 1 ×ˢ {x} ⊆
      {p : ℝ × M | ((σ₀ + p.1 • (σ₁ - σ₀)).flat p.2).IsInvertible} := by
    rintro ⟨s, y⟩ ⟨hs, rfl : y = x⟩
    exact isInvertible_flat_iff.2 (hx s hs)
  obtain ⟨u, V, -, hV, hu, hxV, huV⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hO hsub
  exact ⟨V, fun y hy s hs ↦ isInvertible_flat_iff.1 (huV (mk_mem_prod (hu hs) hy)), hV,
    hxV rfl⟩

/-- **Nondegeneracy on whole slices along a line of two-forms is an open condition.** For
two-forms `σ₀`, `σ` on `M × N`, with `M` compact and both model spaces finite-dimensional, the set
of pairs `(s, y)` of `ℝ × N` such that `σ₀ + s σ` is nondegenerate at every point `(x, y)`,
`x ∈ M`, is open in `ℝ × N`. -/
theorem isOpen_setOfPred_forall_nondegenerate_bilinFormAt_add_smul [FiniteDimensional ℝ E]
    [CompactSpace M] {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    [FiniteDimensional ℝ EN] [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
    [TopologicalSpace N] [ChartedSpace HN N] [IsManifold J ∞ N]
    (σ₀ σ : SmoothTwoForm (I.prod J) (M × N)) :
    IsOpen {p : ℝ × N | ∀ x : M, ((σ₀ + p.1 • σ).bilinFormAt (x, p.2)).Nondegenerate} := by
  -- the points `(s, z)` of `ℝ × (M × N)` at which `σ₀ + s σ = σ₀ + s ((σ₀ + σ) - σ₀)` is
  -- nondegenerate form an open set, and the tube lemma passes to the compact factor `M`
  have hO := isOpen_setOfPred_isInvertible_flat_add_smul_sub σ₀ (σ₀ + σ)
  simp only [add_sub_cancel_left, isInvertible_flat_iff] at hO
  exact isOpen_forall_prodMk_mem continuous_id
    (hO.preimage (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd)))

/-- **Inverse flat maps of a fixed nondegenerate two-form along a family of one-forms.** For a
nondegenerate two-form `σ` on `M` and a smooth one-form `α` on `N × M` with slices `α_t`, the
vector fields `(σ♭)⁻¹ α_t` depend smoothly on `t`: the map `(t, x) ↦ (x, (σ♭)⁻¹ α_t (x))` is
smooth. This is `TauCeti.SmoothTwoForm.contMDiff_interiorEquiv_symm_mpullback_prodMk` for the
constant family `Prod.snd^* σ`. -/
theorem IsNondegenerate.contMDiff_interiorEquiv_symm_mpullback_prodMk [FiniteDimensional ℝ E]
    {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold J ∞ N]
    {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate) (α : SmoothForm (J.prod I) (N × M) ℝ 1) :
    ContMDiff (J.prod I) I.tangent ∞ (fun p : N × M ↦ (⟨p.2, hσ.interiorEquiv.symm
      (SmoothForm.mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α) p.2⟩ :
        TangentBundle I M)) := by
  -- The constant family `σ'` of `σ` on `N × M`, whose slices are all `σ`.
  set σ' : SmoothTwoForm (J.prod I) (N × M) := SmoothForm.mpullback Prod.snd contMDiff_snd σ
  have hσ' (t : N) :
      SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ' = σ :=
    SmoothForm.mpullback_prodMk_mpullback_snd σ t
  have hnd (t : N) : IsNondegenerate
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ') :=
    (hσ' t).symm ▸ hσ
  exact (SmoothTwoForm.contMDiff_interiorEquiv_symm_mpullback_prodMk σ' hnd α).congr fun p ↦ by
    simp only [IsNondegenerate.interiorEquiv_symm_apply, hσ']

section PullbackProd

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {f : M → B}

/-- Let `x` lie in the base set of the trivialization of `TM` at `x₀`, and `f x` in that of the
trivialization of `TB` at `f x₀`. Then the form `LinearMap.BilinForm.pullbackProd` of the
coordinate expressions of `τ♭_x`, `β♭_{f x}` and `d_x f`, a bilinear form on `E × EB`, is
`pullbackProd τ_x β_{f x} (d_x f) s` carried along the two trivializations. -/
theorem pullbackProd_inCoordinates_flat (τ : SmoothTwoForm I M) (β : SmoothTwoForm IB B)
    (s : ℝ) {x₀ x : M} (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hfx : f x ∈ (trivializationAt EB (TangentSpace IB) (f x₀)).baseSet) :
    LinearMap.BilinForm.pullbackProd
        (Manifold.tangentBilinFormInCoordinates x₀ x (τ.flat x)).toBilinForm
        (Manifold.tangentBilinFormInCoordinates (f x₀) (f x) (β.flat (f x))).toBilinForm
        (inTangentCoordinates I IB id f (mfderiv I IB f) x₀ x : E →ₗ[ℝ] EB) s =
      LinearMap.BilinForm.congr
        (((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ x
          hx).toLinearEquiv.prodCongr
          ((trivializationAt EB (TangentSpace IB) (f x₀)).continuousLinearEquivAt ℝ (f x)
            hfx).toLinearEquiv)
        (LinearMap.BilinForm.pullbackProd (τ.bilinFormAt x) (β.bilinFormAt (f x))
          (mfderiv I IB f x : TangentSpace I x →ₗ[ℝ] _) s) := by
  have hL : (inTangentCoordinates I IB id f (mfderiv I IB f) x₀ x : E →ₗ[ℝ] EB) =
      ((trivializationAt EB (TangentSpace IB) (f x₀)).continuousLinearEquivAt ℝ (f x)
        hfx).toLinearEquiv.toLinearMap ∘ₗ (mfderiv I IB f x : TangentSpace I x →ₗ[ℝ] _) ∘ₗ
        ((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ x
          hx).toLinearEquiv.symm.toLinearMap := by
    rw [inTangentCoordinates, ContinuousLinearMap.inCoordinates_eq (x₀ := id x₀) (x := id x) hx hfx]
    ext; simp
  rw [← LinearMap.BilinForm.pullbackProd_congr,
    Manifold.tangentBilinFormInCoordinates_toBilinForm x₀ hx,
    Manifold.tangentBilinFormInCoordinates_toBilinForm (f x₀) hfx, toBilinForm_flat,
    toBilinForm_flat, hL]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ EB]

/-- **Nondegeneracy of `pullbackProd` is open jointly in the parameter and the point.** For a
`C^1` map `f : M → B` between finite-dimensional manifolds and two-forms `τ` on `M` and `β` on
`B`, the set of pairs `(s, x)` of `ℝ × M` at which
`LinearMap.BilinForm.pullbackProd τ_x β_{f x} (d_x f) s`, a bilinear form on
`T_x M × T_{f x} B`, is nondegenerate is open. -/
theorem isOpen_setOfPred_nondegenerate_pullbackProd (hf : ContMDiff I IB 1 f)
    (τ : SmoothTwoForm I M) (β : SmoothTwoForm IB B) :
    IsOpen {p : ℝ × M | (LinearMap.BilinForm.pullbackProd (τ.bilinFormAt p.2)
      (β.bilinFormAt (f p.2)) (mfderiv I IB f p.2 : TangentSpace I p.2 →ₗ[ℝ] _)
      p.1).Nondegenerate} := by
  refine isOpen_iff_mem_nhds.2 fun ⟨s₀, x₀⟩ h₀ ↦ ?_
  -- The two forms and the differential of `f`, read in the trivializations of `TM` at `x₀` and
  -- of `TB` at `f x₀`, are continuous at `x₀`.
  set τc : M → E →L[ℝ] E →L[ℝ] ℝ := fun x ↦
    Manifold.tangentBilinFormInCoordinates x₀ x (τ.flat x)
  set βc : M → EB →L[ℝ] EB →L[ℝ] ℝ := fun x ↦
    Manifold.tangentBilinFormInCoordinates (f x₀) (f x) (β.flat (f x))
  set Lc : M → E →L[ℝ] EB := inTangentCoordinates I IB id f (mfderiv I IB f) x₀
  have hτc : ContinuousAt τc x₀ :=
    Manifold.continuousAt_tangentBilinFormInCoordinates τ.contMDiff_flat.continuous.continuousAt
  have hβc : ContinuousAt βc x₀ := Manifold.continuousAt_tangentBilinFormInCoordinates
    (β.contMDiff_flat.continuous.comp hf.continuous).continuousAt
  have hLc : ContinuousAt Lc x₀ :=
    (ContMDiffAt.mfderiv (fun _ ↦ f) id (hf.comp contMDiff_snd).contMDiffAt
      contMDiffAt_id (m := 0) (by norm_num)).continuousAt
  have hx₀ := FiberBundle.mem_baseSet_trivializationAt' (F := E) (E := TangentSpace I) x₀
  have hfx₀ := FiberBundle.mem_baseSet_trivializationAt' (F := EB) (E := TangentSpace IB) (f x₀)
  -- The form `pullbackProd` of the coordinate expressions, on `E × EB`, is nondegenerate near
  -- `(s₀, x₀)`. The arguments of `ContinuousAt.comp` are given: unification would otherwise
  -- unfold the coordinate expressions.
  have hev := LinearMap.BilinForm.eventually_nondegenerate_pullbackProd_of_continuousAt
    (ContinuousAt.comp (f := Prod.snd) (x := (s₀, x₀)) hτc continuousAt_snd)
    (ContinuousAt.comp (f := Prod.snd) (x := (s₀, x₀)) hβc continuousAt_snd)
    (ContinuousAt.comp (f := Prod.snd) (x := (s₀, x₀)) hLc continuousAt_snd) continuousAt_fst
    (by simp only [Function.comp_apply, τc, βc, Lc]
        rwa [pullbackProd_inCoordinates_flat τ β s₀ hx₀ hfx₀,
          LinearMap.BilinForm.nondegenerate_congr_iff])
  have hW : ∀ᶠ p : ℝ × M in 𝓝 (s₀, x₀), p.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet ∧
      f p.2 ∈ (trivializationAt EB (TangentSpace IB) (f x₀)).baseSet :=
    (continuousAt_snd.eventually ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
      hx₀)).and ((hf.continuous.continuousAt.comp continuousAt_snd).eventually
      ((trivializationAt EB (TangentSpace IB) (f x₀)).open_baseSet.mem_nhds hfx₀))
  -- Over the base sets, it is the form of the statement carried along the trivializations.
  filter_upwards [hev, hW] with ⟨s, x⟩ hp ⟨hx, hfx⟩
  simp only [Function.comp_apply, τc, βc, Lc] at hp
  rwa [pullbackProd_inCoordinates_flat τ β s hx hfx,
    LinearMap.BilinForm.nondegenerate_congr_iff] at hp

/-- **A uniform bound for adding a large multiple of a pulled-back form.** Let `f : M → B` be a
`C^1` map between finite-dimensional manifolds with `M` compact, `τ` a two-form on `M` and `β`
a two-form on `B` that is nondegenerate at every point `f x`. If, at every `x`, the form
`LinearMap.BilinForm.pullbackProd τ_x β_{f x} (d_x f) 0` is nondegenerate, then there is `K₀`
such that `τ + K f^* β`, that is `τ_x + K β_{f x}(d_x f ·, d_x f ·)`, is nondegenerate at every
point of `M` for every `K ≥ K₀`. -/
theorem exists_forall_ge_forall_nondegenerate_add_smul_comp [CompactSpace M]
    (hf : ContMDiff I IB 1 f) (τ : SmoothTwoForm I M) (β : SmoothTwoForm IB B)
    (hβ : ∀ x, (β.bilinFormAt (f x)).Nondegenerate)
    (h₀ : ∀ x, (LinearMap.BilinForm.pullbackProd (τ.bilinFormAt x) (β.bilinFormAt (f x))
      (mfderiv I IB f x : TangentSpace I x →ₗ[ℝ] _) 0).Nondegenerate) :
    ∃ K₀ : ℝ, ∀ K ≥ K₀, ∀ x, (τ.bilinFormAt x + K • (β.bilinFormAt (f x)).comp
      (mfderiv I IB f x : TangentSpace I x →ₗ[ℝ] _) (mfderiv I IB f x)).Nondegenerate := by
  -- The parameters `s` with `pullbackProd` nondegenerate at every point form a neighbourhood
  -- of `0`, and `pullbackProd` at `s = K⁻¹` is nondegenerate exactly when `τ + K f^* β` is.
  have h := (isOpen_forall_prodMk_mem continuous_id
    (isOpen_setOfPred_nondegenerate_pullbackProd hf τ β)).mem_nhds h₀
  refine eventually_atTop.1 ?_
  filter_upwards [tendsto_inv_atTop_zero.eventually h, eventually_gt_atTop 0] with K hK hK₀ x
  have hKx := hK x
  rwa [id_eq, LinearMap.BilinForm.nondegenerate_pullbackProd_iff_of_ne_zero
    (SmoothForm.isAlt_bilinFormAt τ x) (SmoothForm.isAlt_bilinFormAt β (f x)) (hβ x)
    (inv_ne_zero hK₀.ne'), inv_inv] at hKx

end PullbackProd
end SmoothTwoForm

end TauCeti

end
