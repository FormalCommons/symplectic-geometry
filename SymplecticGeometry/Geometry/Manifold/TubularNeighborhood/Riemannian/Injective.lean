/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Coordinates
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Differential
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Neighborhood
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Radial
public import TauCeti.Geometry.Manifold.VectorBundle.ZeroSection
public import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.Normalized
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ZeroSection
import SymplecticGeometry.GroupTheory.GroupAction.Hom
import TauCeti.Geometry.Manifold.IsManifold.Basic
import SymplecticGeometry.Topology.VectorBundle.Basic

/-!
# A smooth injective map of the whole normal bundle

Let `f : M → N` be a smooth embedding between boundaryless manifolds, `N` Hausdorff and second
countable, with normal bundle `ν`. This file gives a smooth map `T : ν → N`, injective on all of
`ν`, equal to `f` on the zero section, whose normal derivative `f.normalFiberDeriv hn hdim T x`
(the normal class of its differential at `0_x` on vertical vectors) is `c x` times the identity,
for a function `c > 0` (`TauCeti.SmoothEmbedding.exists_contMDiff_injective_normalBundle`).

The map is the normal exponential of an auxiliary Riemannian metric on `N`, which is a
diffeomorphism on a neighbourhood of the zero section (Tau Ceti's
`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_normalExp_subset`), precomposed with a
fibrewise radial compression `TauCeti.vectorBundleRadialPartialDiffeomorphOfRadius` of `ν` into
that neighbourhood, for an auxiliary metric on `ν`. The compression follows the proof of Tau Ceti's
`TauCeti.SmoothEmbedding.exists_diffeomorph_normalBundle_riemannian_subset`; the differential along
the zero section comes from `TauCeti.SmoothEmbedding.mfderiv_normalExp_zeroSection_apply` and the
chain rule. Unlike Tau Ceti's tubular diffeomorphisms, the statement records that differential.

## Main results

* `TauCeti.SmoothEmbedding.exists_contMDiff_injective_normalBundle`: a smooth injective
  `T : ν → N` with `T (0_x) = f x`, whose normal derivative at each `x` is a positive multiple of
  the identity.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 4.
-/

public section

noncomputable section

open Bundle Function Module Set
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  {V G N : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace G] {J : ModelWithCorners ℝ V G} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ∞ N] [J.Boundaryless] [T2Space N] [SecondCountableTopology N]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- A smooth embedding `f` extends to a smooth map `T` of its normal bundle into the target,
injective on the whole bundle and equal to `f` on the zero section, whose normal derivative
`f.normalFiberDeriv hn hdim T x` sends `v` to `c x • v`, where `c x > 0`. -/
theorem exists_contMDiff_injective_normalBundle (f : SmoothEmbedding I J ∞ M N)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) :
    letI := f.normalSpaceFiberBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero) hdim
    letI := f.normalSpaceVectorBundle (WithTop.coe_ne_zero.2 ENat.top_ne_zero) hdim
    ∃ T : TotalSpace P (fun x ↦ f.NormalSpace x (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) → N,
      ContMDiff (I.prod 𝓘(ℝ, P)) J ∞ T ∧ Injective T ∧
      (∀ x, T (zeroSection P _ x) = f x) ∧
      ∃ c : M → ℝ, (∀ x, 0 < c x) ∧
        ∀ x (v : f.NormalSpace x (WithTop.coe_ne_zero.2 ENat.top_ne_zero)),
        f.normalFiberDeriv (WithTop.coe_ne_zero.2 ENat.top_ne_zero) hdim T x v = c x • v := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  have := f.normalSpaceContMDiffVectorBundle (m := ∞) hn (by simp) hdim
  let ν : M → Type _ := fun x ↦ f.NormalSpace x hn
  rcases isEmpty_or_nonempty M with hM | hM
  · have : IsEmpty (TotalSpace P ν) := ⟨fun p ↦ hM.false p.proj⟩
    exact ⟨isEmptyElim, fun p ↦ isEmptyElim p, fun p ↦ isEmptyElim p, fun x ↦ isEmptyElim x,
      fun _ ↦ 1, fun _ ↦ one_pos, fun x ↦ isEmptyElim x⟩
  have : T2Space M := f.isEmbedding.t2Space
  have : SecondCountableTopology M := f.isEmbedding.isInducing.secondCountableTopology
  have := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  have := Manifold.locallyCompact_of_finiteDimensional (M := N) J
  -- An auxiliary metric on `N`, and the normal exponential on a neighbourhood of the zero
  -- section on which it is a diffeomorphism.
  obtain ⟨gN⟩ := nonempty_contMDiffRiemannianMetric (IB := J) (n := ⊤) (F := V)
    (E := fun y : N ↦ TangentSpace J y)
  let : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨gN.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle J ∞ V (fun y : N ↦ TangentSpace J y) :=
    Bundle.instIsContMDiffRiemannianBundle gN
  obtain ⟨Ψ, hzero, -, -, -, hΨ⟩ := f.exists_partialDiffeomorph_normalExp_subset (P := P)
    (m := ∞) hn (by simp) (by simp) hdim isOpen_univ (subset_univ _)
  -- An auxiliary metric on the normal bundle, and a radial compression into the source of `Ψ`.
  obtain ⟨gν⟩ := nonempty_contMDiffRiemannianMetric (IB := I) (n := ⊤) (F := P) (E := ν)
  let : RiemannianBundle ν := ⟨gν.toRiemannianMetric⟩
  let : ∀ x, NormedAddCommGroup (ν x) := fun x => inferInstance
  let : ∀ x, InnerProductSpace ℝ (ν x) := fun x => inferInstance
  let : IsContMDiffRiemannianBundle I ∞ P ν := Bundle.instIsContMDiffRiemannianBundle gν
  let : IsContinuousRiemannianBundle P ν := by
    obtain ⟨b, hb, heq⟩ :=
      IsContMDiffRiemannianBundle.exists_contMDiff (IB := I) (n := ∞) (F := P) (E := ν)
    exact ⟨b, hb.continuous, heq⟩
  obtain ⟨r, hr, -, hdisc⟩ := Ψ.open_source.exists_contMDiffMap_norm_le_subset_bundle
    (I := I) (n := ⊤) hzero (continuous_const (y := (1 : ℝ))) (fun _ => zero_lt_one)
  let R := vectorBundleRadialPartialDiffeomorphOfRadius (F := P) (V := ν) r.contMDiff hr
  have hRapply (p : TotalSpace P ν) :
      R p = ⟨p.proj, r p.proj • (Real.sqrt (1 + ‖p.snd‖ ^ 2))⁻¹ • p.snd⟩ := by
    rw [vectorBundleRadialPartialDiffeomorphOfRadius_apply, TotalSpace.radialMap_apply,
      vectorBundleScalarDiffeomorph_apply]
  have hRsrc (p : TotalSpace P ν) : p ∈ R.source := by
    rw [vectorBundleRadialPartialDiffeomorphOfRadius_source]
    exact mem_univ p
  have hRS (p : TotalSpace P ν) : R p ∈ Ψ.source := by
    have h := R.map_source (hRsrc p)
    rw [vectorBundleRadialPartialDiffeomorphOfRadius_target] at h
    exact hdisc _ _ (le_of_lt h)
  have hR : ContMDiff (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) ∞ R := fun p ↦
    R.contMDiffAt (hRsrc p)
  have hT : ContMDiff (I.prod 𝓘(ℝ, P)) J ∞ (fun p ↦ Ψ (R p)) :=
    Ψ.contMDiffOn.comp_contMDiff hR hRS
  have hzeroR (x : M) : R (zeroSection P ν x) = zeroSection P ν x := by
    rw [hRapply]
    exact congrArg (TotalSpace.mk' P x) (smul_eq_zero_of_right _ (smul_zero _))
  refine ⟨fun p ↦ Ψ (R p), hT, fun p p' h ↦ R.injOn (hRsrc p) (hRsrc p')
    (Ψ.injOn (hRS p) (hRS p') h), fun x ↦ ?_, r, hr, fun x v ↦ ?_⟩
  · dsimp only
    rw [hzeroR, hΨ, SmoothEmbedding.normalExp_zeroSection]
  -- The vertical vector of `v` is the velocity at `0` of the image of the line `t ↦ t • v`. The
  -- map sends this line to the image under `Ψ` of the reparametrized line `t ↦ s t • v`, with
  -- `s' 0 = r x`.
  have hΨ0 : MDifferentiableAt (I.prod 𝓘(ℝ, P)) J Ψ (zeroSection P ν x) :=
    (Ψ.contMDiffAt (hzero x)).mdifferentiableAt (by simp)
  rw [normalFiberDeriv_apply_eq_mfderiv_smul f hn hdim ((hT _).mdifferentiableAt (by simp))]
  let line : ℝ → TotalSpace P ν := fun t ↦ ⟨x, t • v⟩
  have hl : ContMDiff 𝓘(ℝ) (I.prod 𝓘(ℝ, P)) 1 line :=
    contMDiff_id.smul_totalSpace (contMDiff_const (c := (⟨x, v⟩ : TotalSpace P ν)))
  have hΨl : MDifferentiableAt 𝓘(ℝ) J (Ψ ∘ line) 0 :=
    MDifferentiableAt.comp_of_eq 0 hΨ0 (hl.mdifferentiableAt one_ne_zero)
      (by simp [line, zeroSection_def])
  let s : ℝ → ℝ := fun t ↦ r x * (Real.sqrt (1 + t ^ 2 * ‖(v : ν x)‖ ^ 2))⁻¹ * t
  have hs : HasDerivAt s (r x) 0 := by
    have hφ : DifferentiableAt ℝ (fun t : ℝ ↦ r x * (Real.sqrt (1 + t ^ 2 * ‖(v : ν x)‖ ^ 2))⁻¹)
        0 := (differentiableAt_const _).mul
      ((DifferentiableAt.sqrt (by fun_prop) (by positivity)).inv (by positivity))
    convert hφ.hasDerivAt.mul (hasDerivAt_id' (0 : ℝ)) using 1
    simp
  have hfun : (fun t : ℝ ↦ Ψ (R ⟨x, t • v⟩)) = (Ψ ∘ line) ∘ s := by
    funext t
    simp only [Function.comp_apply, line, hRapply, smul_smul, s, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, mul_assoc]
  have h2 := mfderiv_comp_apply_of_eq (0 : ℝ) hΨl
    hs.hasFDerivAt.hasMFDerivAt.mdifferentiableAt (by simp [s]) (1 : ℝ)
  -- `hs1` and `hlin` are stated here, not used by `rw` directly: the argument of these
  -- derivatives lives in `TangentSpace 𝓘(ℝ) 0`, which is `ℝ` only up to unfolding, so `rw` does
  -- not find the patterns of `toSpanSingleton_apply_one` and `map_eq_smul_map_one`.
  have hs1 : mfderiv 𝓘(ℝ) 𝓘(ℝ) s 0 (1 : ℝ) = r x := by
    rw [hs.hasFDerivAt.hasMFDerivAt.mfderiv]
    exact ContinuousLinearMap.toSpanSingleton_apply_one ℝ (r x)
  have hlin : mfderiv 𝓘(ℝ) J (Ψ ∘ line) 0 (r x) = r x • mfderiv 𝓘(ℝ) J (Ψ ∘ line) 0 (1 : ℝ) :=
    SymplecticGeometry.map_eq_smul_map_one _ (r x)
  have key : mfderiv 𝓘(ℝ) J (Ψ ∘ line) 0 (1 : ℝ) = f.normalRepresentative x hn v := by
    refine (Bundle.mfderiv_zeroSectionTangentEquiv_symm_inr hΨ0 v).symm.trans ?_
    rw [hΨ, f.mfderiv_normalExp_zeroSection_apply hn (by simp) hdim, map_zero, zero_add]
  have h1 : mfderiv 𝓘(ℝ) J (fun t : ℝ ↦ Ψ (R ⟨x, t • v⟩)) 0 (1 : ℝ) =
      r x • f.normalRepresentative x hn v := by
    rw [hfun]
    exact h2.trans ((congrArg _ hs1).trans (hlin.trans (congrArg _ key)))
  rw [h1, map_smul, normalClassL_apply, normalClass_normalRepresentative]

end TauCeti.SmoothEmbedding
