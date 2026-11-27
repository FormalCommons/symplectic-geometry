/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.ComplementarySubbundle
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import SymplecticGeometry.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.Geometry.Manifold.ContMDiff.ContinuousLinearEquiv
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Section
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity

/-!
# Orthogonal complements of smooth subbundles for a smooth field of bilinear forms

Let `E` be a `C^n` vector bundle with finite-dimensional model fibre `F` over a complete
nontrivially normed field `𝕜`, let `β` be a `C^n` field of bilinear forms on `E`, that is a `C^n`
section of the bundle with fibres `E x →L[𝕜] E x →L[𝕜] 𝕜`, and let `V` be a family of subspaces of
the fibres with `C^n` local frames of size `r`. Write `V^β x` for the `β x`-orthogonal of `V x`,
the vectors `w` with `β x v w = 0` for every `v ∈ V x`. If `V x` and `V^β x` are complementary in
every fibre, this file shows that `V^β` has `C^n` local frames of size `finrank 𝕜 F - r`, so it
is a `C^n` subbundle of `E` too. By Mathlib's
`LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate`, this is the case when every
`β x` is reflexive (for instance symmetric or alternating) and nondegenerate on `V x`.

Near a point, take a `C^n` frame `D₁, …, D_r` of `V` on an open set `U`, and let `G y` be the
Gram operator `c ↦ (β y (D j y) (∑ i, c i • D i y))_j` on `Fin r → 𝕜`. It is a `C^n` family of
invertible operators on `U`, and the projection of `v ∈ E y` onto `V y` along `V^β y` is
`∑ i, c i • D i y` with `c = (G y)⁻¹ (β y (D j y) v)_j`
(`LinearMap.BilinForm.projection_orthogonal_eq_iff`). So this projection `P` is a `C^n` map of
total spaces, and so is the projection `1 - P` onto `V^β` along `V`, whose ranges are the fibres
of `V^β`.
Tau Ceti's constant-rank criterion
`TauCeti.hasLocalContMDiffSubbundleFrames_of_contMDiff_totalSpace_range` then gives the frames.
This follows the proof of Tau Ceti's
`Bundle.ContMDiffRiemannianMetric.hasLocalContMDiffSubbundleFrames_orthogonalSpanFamily`, where
the family is orthonormal for a Hermitian metric and the Gram operator is the identity.

## Main results

* `TauCeti.HasLocalContMDiffSubbundleFrames.contMDiff_totalSpace_projection_orthogonal`: the
  projection of `E` onto `V` along `V^β` is a `C^n` map from the total space of `E` to itself.
* `TauCeti.HasLocalContMDiffSubbundleFrames.orthogonal_of_isCompl`,
  `TauCeti.HasLocalContMDiffSubbundleFrames.orthogonal`: `V^β` has `C^n` local frames of size
  `finrank 𝕜 F - r`.
* `TauCeti.HasLocalContMDiffSubbundleFrames.contMDiff_totalSpace_projectionOnto_orthogonal`,
  `TauCeti.HasLocalContMDiffSubbundleFrames.contMDiff_totalSpace_orthogonal_projectionOnto`: the
  projections onto `V` along `V^β` and onto `V^β` along `V` are `C^n` maps from the total space of
  `E` to those of the subbundles.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Lemma 10.32
  and Proposition 10.34, for the local frame criterion that Tau Ceti proves.
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.4,
  where symplectic orthogonal complements of subbundles along a submanifold are used.
-/

public section

open Bundle Module Set Filter
open scoped Manifold ContDiff Topology

namespace TauCeti.HasLocalContMDiffSubbundleFrames

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} {E : B → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
  {β : Π x, E x →L[𝕜] E x →L[𝕜] 𝕜} {V : Π x, Submodule 𝕜 (E x)} {r : ℕ}

/-- The Gram operator of a frame `D` for `β` at `y`: it sends `c : Fin r → 𝕜` to the family
`(β y (D j y) (∑ i, c i • D i y))_j`. -/
private noncomputable def gram (β : Π x, E x →L[𝕜] E x →L[𝕜] 𝕜) (D : Fin r → Π x, E x) (y : B) :
    (Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜) :=
  ∑ i, ∑ j, β y (D j y) (D i y) • (ContinuousLinearMap.proj i).smulRight (Pi.single j 1)

private theorem gram_apply (D : Fin r → Π x, E x) (y : B) (c : Fin r → 𝕜) (j : Fin r) :
    gram β D y c j = β y (D j y) (∑ i, c i • D i y) := by
  simp [gram, Finset.sum_apply, Pi.single_apply, map_sum, mul_comm]

variable [TopologicalSpace B] {F : Type*} [TopologicalSpace (TotalSpace F E)]

/-- A vector of `E y` pairs with every vector of `V y` as another one does, if it does so with
the members of a frame. -/
private theorem apply_eq_of_forall_apply_eq {D : Fin r → Π x, E x} {U : Set B}
    (hD : IsSubbundleFrameOn F V D U) {y : B} (hy : y ∈ U) {v w : E y}
    (h : ∀ j, β y (D j y) w = β y (D j y) v) : ∀ u ∈ V y, β y u w = β y u v := by
  intro u hu
  rw [← hD.span_eq hy] at hu
  simpa using LinearMap.eqOn_span (f := (β y).toLinearMap₁₂.flip w)
    (g := (β y).toLinearMap₁₂.flip v) (s := range (D · y)) (by rintro _ ⟨j, rfl⟩; simp [h j]) hu

variable [CompleteSpace 𝕜]

/-- On the domain of a frame of `V`, the Gram operator is invertible when `V` and `V^β` are
complementary. -/
private theorem exists_gram_eq {D : Fin r → Π x, E x} {U : Set B}
    (hD : IsSubbundleFrameOn F V D U)
    (hc : ∀ x, IsCompl (V x) (LinearMap.BilinForm.orthogonal (β x).toLinearMap₁₂ (V x)))
    {y : B} (hy : y ∈ U) :
    ∃ e : (Fin r → 𝕜) ≃L[𝕜] (Fin r → 𝕜), (e : (Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜)) = gram β D y := by
  have hinj : Function.Injective (gram β D y) := by
    refine (injective_iff_map_eq_zero (gram β D y)).mpr fun c hc0 ↦ ?_
    have horth : ∑ i, c i • D i y ∈ LinearMap.BilinForm.orthogonal (β y).toLinearMap₁₂ (V y) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro u hu
      simpa using apply_eq_of_forall_apply_eq (β := β) hD hy (v := 0) (w := ∑ i, c i • D i y)
        (fun j ↦ by rw [map_zero, ← gram_apply, hc0, Pi.zero_apply]) u hu
    have h0 : ∑ i, c i • D i y = 0 :=
      (Submodule.disjoint_def.mp (hc y).disjoint) _
        (Submodule.sum_smul_mem _ c fun i _ ↦ hD.apply_mem i hy) horth
    exact funext (Fintype.linearIndependent_iff.mp (hD.linearIndependent hy) c h0)
  let e := LinearEquiv.ofInjectiveEndo (gram β D y : (Fin r → 𝕜) →ₗ[𝕜] (Fin r → 𝕜)) hinj
  refine ⟨e.toContinuousLinearEquiv, ContinuousLinearMap.ext fun c ↦ ?_⟩
  simp only [e, ContinuousLinearEquiv.coe_coe, LinearEquiv.coe_toContinuousLinearEquiv',
    LinearEquiv.coe_ofInjectiveEndo, ContinuousLinearMap.coe_coe]

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B]
  {n : ℕ∞ω} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- **The `β`-orthogonal projection onto a smooth subbundle is smooth.** Let `β` be a `C^n` field
of bilinear forms on `E`, and `V` a family of subspaces of the fibres with `C^n` local frames, such
that `V x` and its `β x`-orthogonal are complementary in every fibre. Then the projection of `E`
onto `V` along the `β`-orthogonal of `V` is a `C^n` map from the total space of `E` to itself. -/
theorem contMDiff_totalSpace_projection_orthogonal
    (hV : HasLocalContMDiffSubbundleFrames IB n F (Fin r) V)
    (hβ : ContMDiff IB (IB.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] 𝕜)) n
      (fun x ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] 𝕜) x (β x)))
    (hc : ∀ x, IsCompl (V x) (LinearMap.BilinForm.orthogonal (β x).toLinearMap₁₂ (V x))) :
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
      (fun p : TotalSpace F E ↦ (⟨p.proj, (V p.proj).projection _ (hc p.proj) p.snd⟩ :
        TotalSpace F E)) := by
  intro p₀
  obtain ⟨U, hU, hp₀, D, hD, hDs⟩ := hasLocalContMDiffSubbundleFrames_iff.mp hV p₀.proj
  have hUn : U ∈ 𝓝 p₀.proj := hU.mem_nhds hp₀
  have hpr := contMDiffAt_proj E (IB := IB) (n := n) (p := p₀)
  -- The frame, the form and the Gram operator, read along the projection of the total space.
  have hDp (i : Fin r) : ContMDiffAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
      (fun p : TotalSpace F E ↦ TotalSpace.mk' F p.proj (D i p.proj)) p₀ :=
    ((hDs i).contMDiffAt hUn).comp p₀ hpr
  have hβp := (hβ p₀.proj).comp p₀ hpr
  have hG : ContMDiffOn IB 𝓘(𝕜, (Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜)) n (gram β D) U :=
    contMDiffOn_finsetSum fun i _ ↦ contMDiffOn_finsetSum fun j _ ↦
      (hβ.contMDiffOn.clm_bundle_apply₂_trivial (hDs j) (hDs i)).smul contMDiffOn_const
  obtain ⟨e, he⟩ := exists_gram_eq hD hc hp₀
  have hinv : ContMDiffAt (IB.prod 𝓘(𝕜, F)) 𝓘(𝕜, (Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜)) n
      (fun p : TotalSpace F E ↦ (gram β D p.proj).inverse) p₀ :=
    contMDiffWithinAt_univ.1 <|
      ((hG.contMDiffAt hUn).comp p₀ hpr).contMDiffWithinAt.clm_inverse ⟨e, he⟩
  -- The pairings of a vector with the frame.
  have hb : ContMDiffAt (IB.prod 𝓘(𝕜, F)) 𝓘(𝕜, Fin r → 𝕜) n
      (fun p : TotalSpace F E ↦ fun j ↦ β p.proj (D j p.proj) p.snd) p₀ :=
    contMDiffAt_pi_module_iff.mpr fun j ↦
      hβp.clm_bundle_apply₂_trivial (hDp j) contMDiffAt_id
  -- The coefficients of the projection in the frame.
  let a : TotalSpace F E → Fin r → 𝕜 := fun p ↦
    (gram β D p.proj).inverse fun j ↦ β p.proj (D j p.proj) p.snd
  have ha : ∀ i, ContMDiffAt (IB.prod 𝓘(𝕜, F)) 𝓘(𝕜, 𝕜) n (fun p ↦ a p i) p₀ :=
    contMDiffAt_pi_module_iff.mp (hinv.clm_apply hb)
  have hsum := ContMDiffAt.sum_sectionAlong (b := TotalSpace.proj) Finset.univ
    (fun i p ↦ a p i • D i p.proj) hpr fun i _ ↦ (ha i).smul_totalSpace (hDp i)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [(FiberBundle.continuous_proj F E).continuousAt.preimage_mem_nhds hUn] with p hp
  obtain ⟨e', he'⟩ := exists_gram_eq hD hc hp
  refine congrArg (TotalSpace.mk p.proj) ?_
  refine (LinearMap.BilinForm.projection_orthogonal_eq_iff (β p.proj).toLinearMap₁₂ (hc p.proj)
    _ _).mpr ⟨?_, fun u hu ↦ ?_⟩
  · exact Submodule.sum_smul_mem _ (a p) fun i _ ↦ hD.apply_mem i hp
  · refine apply_eq_of_forall_apply_eq hD hp (fun j ↦ ?_) u hu
    have hGa : gram β D p.proj (a p) = fun j ↦ β p.proj (D j p.proj) p.snd := by
      simp only [a, ← he', ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply]
    simpa [gram_apply] using congrFun hGa j

variable [ContMDiffVectorBundle n F E IB]

/-- **Smooth frames of the `β`-orthogonal of a smooth subbundle.** Let `β` be a `C^n` field of
bilinear forms on a `C^n` vector bundle `E` with finite-dimensional model fibre `F`, and `V` a
family of subspaces of the fibres with `C^n` local frames of size `r`, such that `V x` and its
`β x`-orthogonal are complementary in every fibre. Then the `β`-orthogonal of `V` has `C^n`
local frames of size `finrank 𝕜 F - r`. -/
theorem orthogonal_of_isCompl [FiniteDimensional 𝕜 F]
    (hV : HasLocalContMDiffSubbundleFrames IB n F (Fin r) V)
    (hβ : ContMDiff IB (IB.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] 𝕜)) n
      (fun x ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] 𝕜) x (β x)))
    (hc : ∀ x, IsCompl (V x) (LinearMap.BilinForm.orthogonal (β x).toLinearMap₁₂ (V x))) :
    HasLocalContMDiffSubbundleFrames IB n F (Fin (finrank 𝕜 F - r))
      fun x ↦ LinearMap.BilinForm.orthogonal (β x).toLinearMap₁₂ (V x) := by
  refine hasLocalContMDiffSubbundleFrames_of_contMDiff_totalSpace_range (F₁ := F)
    (fun x ↦ Submodule.projection _ (V x) (hc x).symm) ?_
    (fun x ↦ Submodule.range_projection _) fun x ↦ ?_
  · -- The projection onto the orthogonal is the identity minus the projection onto `V`.
    refine (ContMDiff.sub_sectionAlong (b := TotalSpace.proj)
      (s := fun p : TotalSpace F E ↦ p.snd) contMDiff_id
      (hV.contMDiff_totalSpace_projection_orthogonal hβ hc)).congr fun p ↦ ?_
    refine congrArg (TotalSpace.mk p.proj) ?_
    rw [Submodule.projection_eq_self_sub_projection]
  · obtain ⟨U, -, hx, D, hD, -⟩ := hasLocalContMDiffSubbundleFrames_iff.mp hV x
    have := VectorBundle.finiteDimensional 𝕜 F E x
    have hE := VectorBundle.finrank_eq 𝕜 F E x
    have hVr : finrank 𝕜 (V x) = r := by simpa using hD.finrank_eq hx
    have := Submodule.finrank_add_eq_of_isCompl (hc x)
    omega

/-- **Smooth frames of the orthogonal of a smooth subbundle for a reflexive form.** Let `β` be a
`C^n` field of reflexive bilinear forms (for instance symmetric or alternating ones) on a `C^n`
vector bundle `E` with finite-dimensional model fibre `F`, and `V` a family of subspaces of the
fibres with `C^n` local frames of size `r`, on which every `β x` is nondegenerate. Then the
`β`-orthogonal of `V` has `C^n` local frames of size `finrank 𝕜 F - r`. It is complementary to
`V` in every fibre, by `LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate`. -/
theorem orthogonal [FiniteDimensional 𝕜 F]
    (hV : HasLocalContMDiffSubbundleFrames IB n F (Fin r) V)
    (hβ : ContMDiff IB (IB.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] 𝕜)) n
      (fun x ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] 𝕜) x (β x)))
    (hrefl : ∀ x, LinearMap.BilinForm.IsRefl (β x).toLinearMap₁₂)
    (hnd : ∀ x, (LinearMap.BilinForm.restrict (β x).toLinearMap₁₂ (V x)).Nondegenerate) :
    HasLocalContMDiffSubbundleFrames IB n F (Fin (finrank 𝕜 F - r))
      fun x ↦ LinearMap.BilinForm.orthogonal (β x).toLinearMap₁₂ (V x) :=
  hV.orthogonal_of_isCompl hβ fun x ↦
    have := VectorBundle.finiteDimensional 𝕜 F E x
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate (hrefl x) (hnd x)

variable [IsRCLikeNormedField 𝕜] [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul 𝕜 (E x)]

/-- **The `β`-orthogonal projection onto a smooth subbundle is smooth.** Under the hypotheses of
`TauCeti.HasLocalContMDiffSubbundleFrames.orthogonal_of_isCompl`, the projection of `E` onto `V`
along its `β`-orthogonal is a `C^n` map from the total space of `E` to that of the subbundle
`V`. -/
theorem contMDiff_totalSpace_projectionOnto_orthogonal [FiniteDimensional 𝕜 F]
    (hV : HasLocalContMDiffSubbundleFrames IB n F (Fin r) V)
    (hβ : ContMDiff IB (IB.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] 𝕜)) n
      (fun x ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] 𝕜) x (β x)))
    (hc : ∀ x, IsCompl (V x) (LinearMap.BilinForm.orthogonal (β x).toLinearMap₁₂ (V x))) :
    letI := subbundleTopology F (F' := Fin r → 𝕜) V
    letI := hV.fiberBundle
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, Fin r → 𝕜)) n
      (fun w : TotalSpace F E ↦ (⟨w.proj, (V w.proj).projectionOnto _ (hc w.proj) w.snd⟩ :
        TotalSpace (Fin r → 𝕜) fun x ↦ V x)) :=
  hV.contMDiff_totalSpace_projectionOnto_of_isCompl (hV.orthogonal_of_isCompl hβ hc) hc

/-- **The projection onto the `β`-orthogonal of a smooth subbundle is smooth.** Under the
hypotheses of `TauCeti.HasLocalContMDiffSubbundleFrames.orthogonal_of_isCompl`, the projection of
`E` onto the `β`-orthogonal of `V` along `V` is a `C^n` map from the total space of `E` to
that of the subbundle given by the frames of
`TauCeti.HasLocalContMDiffSubbundleFrames.orthogonal_of_isCompl`. -/
theorem contMDiff_totalSpace_orthogonal_projectionOnto [FiniteDimensional 𝕜 F]
    (hV : HasLocalContMDiffSubbundleFrames IB n F (Fin r) V)
    (hβ : ContMDiff IB (IB.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] 𝕜)) n
      (fun x ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] 𝕜) x (β x)))
    (hc : ∀ x, IsCompl (V x) (LinearMap.BilinForm.orthogonal (β x).toLinearMap₁₂ (V x))) :
    letI := subbundleTopology F (F' := Fin (finrank 𝕜 F - r) → 𝕜)
      fun x ↦ LinearMap.BilinForm.orthogonal (β x).toLinearMap₁₂ (V x)
    letI := (hV.orthogonal_of_isCompl hβ hc).fiberBundle
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, Fin (finrank 𝕜 F - r) → 𝕜)) n
      (fun w : TotalSpace F E ↦ (⟨w.proj, Submodule.projectionOnto _ (V w.proj)
          (hc w.proj).symm w.snd⟩ :
        TotalSpace (Fin (finrank 𝕜 F - r) → 𝕜)
          fun x ↦ LinearMap.BilinForm.orthogonal (β x).toLinearMap₁₂ (V x))) :=
  (hV.orthogonal_of_isCompl hβ hc).contMDiff_totalSpace_projectionOnto_of_isCompl hV
    fun x ↦ (hc x).symm

end TauCeti.HasLocalContMDiffSubbundleFrames

end
