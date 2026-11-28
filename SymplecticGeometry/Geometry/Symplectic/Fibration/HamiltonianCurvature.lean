/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Fibration.PatchForm
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Manifold
import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Hamiltonian curvature, read in local coordinates

Let `A` be a smooth atlas of `proj : M → B` with fibre `F`, over a base without boundary
modelled on a finite-dimensional space `EB`, and `τ` a vertically closed two-form on `M` that
restricts to a nondegenerate `σ` on the fibres of `A` and whose horizontal spaces form an
Ehresmann connection `hD`. For a chart `e = A.trivAt b'` of `A` and the extended chart `φ` of
`B` at `b₀`, the map `ψ q = e⁻¹ (φ⁻¹ q.1, q.2)` reads `τ` as the two-form `ψ^* τ` on `EB × F`,
with mixed components `αᵢ(x)` for a basis `bs` of `EB`.

This file shows that `hD` has Hamiltonian curvature (`HasHamiltonianCurvature`) exactly when, for
every such chart and base chart, at every point `x = φ b` of the patch and for all `i j`, the
one-form `∂ᵢαⱼ(x) - ∂ⱼαᵢ(x)` on `F` is the differential of a smooth function on `F`.

## Main definitions

* `TauCeti.MapFiber.Atlas.HasExactMixedCurl`: at every point of every patch, each one-form
  `∂ᵢαⱼ(x) - ∂ⱼαᵢ(x)` on `F` (`TauCeti.RoughForm.mixedCurl` of `ψ^* τ`) is the differential of
  a smooth function on `F`.

## Main results

* `TauCeti.IsEhresmannConnection.hasHamiltonianCurvature_iff_local`: the equivalence.

## Implementation notes

Near a point of the patch, `ψ^* τ` agrees with a two-form `τ'` on all of `EB × F` whose fibre
components are `σ` and which is vertically closed
(`TauCeti.MapFiber.Atlas.IsContMDiff.exists_isVerticallyClosed_eq_mpullback_symm_extChartAt_symm`).
By `TauCeti.IsEhresmannConnection.curvatureIn_eq_snd_sum_curvature`, the curvature read in `e` is
the fibre part of a combination, with constant coefficients, of the curvatures of the connection
of `τ'` on the constant fields `bs i`, `bs j`, and by
`TauCeti.IsEhresmannConnection.exists_isHamiltonianVectorField_curvature_iff` each of these is
Hamiltonian exactly when `∂ᵢαⱼ - ∂ⱼαᵢ` has a primitive. For the converse direction, the
coordinate vectors at a point are extended to smooth fields on `B` by Tau Ceti's
`FiberBundle.contMDiffExtend`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Exercise 6.4.9, with [McDuffSalamon2019Errata]
* [V. Guillemin, E. Lerman, S. Sternberg, *Symplectic Fibrations and Multiplicity
  Diagrams*][GuilleminLermanSternberg1996], §1.4
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF]
  {HF : Type*} [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF}
  {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*}
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M]
  [ChartedSpace HM M] [IsManifold IM ∞ M]
  {proj : M → B} {A : MapFiber.Atlas F proj}

attribute [local instance] IsManifold.minSmoothness_of_isRCLikeNormedField

namespace MapFiber.Atlas

variable (A) (IB IF) {ι : Type*}

/-- The local form of Hamiltonian curvature: for every chart `e = A.trivAt b'` of `A`, every
extended chart `φ` of `B` at a point `b₀`, every `b` in the base set of `e` and in the source of
the chart at `b₀`, and all `i j`, the one-form `∂ᵢαⱼ(φ b) - ∂ⱼαᵢ(φ b)` on `F` is the
differential of a smooth function `g : F → ℝ`. Here `αₖ` are the mixed components, for `bs`, of
the pull-back of `τ` by `ψ q = e⁻¹ (φ⁻¹ q.1, q.2)`, and their curl is
`TauCeti.RoughForm.mixedCurl`. -/
def HasExactMixedCurl (τ : SmoothTwoForm IM M) (bs : Module.Basis ι ℝ EB) : Prop :=
  ∀ b' b₀ b, b ∈ (A.trivAt b').baseSet ∩ (chartAt HB b₀).source → ∀ i j,
    ∃ g : F → ℝ, ContMDiff IF 𝓘(ℝ) ∞ g ∧ ∀ (y : F) (w : TangentSpace IF y),
      mvfderiv IF g y w = RoughForm.mixedCurl (mpullback (𝓘(ℝ, EB).prod IF) IM
        (fun q : EB × F ↦ (A.trivAt b').toOpenPartialHomeomorph.symm
          ((extChartAt IB b₀).symm q.1, q.2)) τ.val) bs i j (extChartAt IB b₀ b) y w

theorem hasExactMixedCurl_def (τ : SmoothTwoForm IM M) (bs : Module.Basis ι ℝ EB) :
    A.HasExactMixedCurl IB IF τ bs ↔
      ∀ b' b₀ b, b ∈ (A.trivAt b').baseSet ∩ (chartAt HB b₀).source → ∀ i j,
        ∃ g : F → ℝ, ContMDiff IF 𝓘(ℝ) ∞ g ∧ ∀ (y : F) (w : TangentSpace IF y),
          mvfderiv IF g y w = RoughForm.mixedCurl (mpullback (𝓘(ℝ, EB).prod IF) IM
            (fun q : EB × F ↦ (A.trivAt b').toOpenPartialHomeomorph.symm
              ((extChartAt IB b₀).symm q.1, q.2)) τ.val) bs i j (extChartAt IB b₀ b) y w :=
  Iff.rfl

end MapFiber.Atlas

variable [FiniteDimensional ℝ EB] [IB.Boundaryless] [IsManifold IB ∞ B] [FiniteDimensional ℝ EF]
  [IsManifold IF ∞ F] [CompleteSpace EM]

namespace IsEhresmannConnection

/-- At a point `b` of a patch, the curvature read in the chart is the fibre part of a combination
of the curvatures `Ω'ᵢⱼ` of a connection on `EB × F` on the constant fields, and each `Ω'ᵢⱼ` is
Hamiltonian for `σ` along the fibre over `φ b` exactly when `∂ᵢαⱼ - ∂ⱼαᵢ` has a primitive. -/
private theorem exists_curvature_of_mem_patch {τ : SmoothTwoForm IM M} {n : ℕ∞ω}
    (hD : IsEhresmannConnection IM IB n proj (SmoothTwoForm.horizontalDistribution IB proj τ))
    (hn : 1 ≤ n) (hA : A.IsContMDiff ∞ IB IF IM) {σ : SmoothTwoForm IF F}
    (hσ : σ.IsNondegenerate) (hτ : SmoothTwoForm.IsVerticallyClosed IB proj τ)
    (hτσ : A.RestrictsTo σ τ) {ι : Type*} [Fintype ι] (bs : Module.Basis ι ℝ EB) {b' b₀ b : B}
    (hb : b ∈ (A.trivAt b').baseSet ∩ (chartAt HB b₀).source) :
    ∃ τ' : SmoothTwoForm (𝓘(ℝ, EB).prod IF) (EB × F),
      ∃ hD' : IsEhresmannConnection (𝓘(ℝ, EB).prod IF) 𝓘(ℝ, EB) ∞ Prod.fst
        (SmoothTwoForm.horizontalDistribution 𝓘(ℝ, EB) Prod.fst τ'),
      (∀ v₁ v₂ : Π b : B, TangentSpace IB b, ContMDiffAt IB IB.tangent 1 (T% v₁) b →
        ContMDiffAt IB IB.tangent 1 (T% v₂) b → ∀ y,
        hD.curvatureIn IF (A.trivAt b') b v₁ v₂ y =
          (∑ i, ∑ j, (bs.repr (mfderiv IB 𝓘(ℝ, EB) (extChartAt IB b₀) b (v₁ b)) i *
              bs.repr (mfderiv IB 𝓘(ℝ, EB) (extChartAt IB b₀) b (v₂ b)) j) •
            hD'.curvature (fun _ ↦ bs i) (fun _ ↦ bs j) (extChartAt IB b₀ b, y)).2) ∧
      ∀ i j, (∃ f : F → ℝ, ContMDiff IF 𝓘(ℝ) ∞ f ∧ σ.IsHamiltonianVectorField f
          fun y ↦ (hD'.curvature (fun _ ↦ bs i) (fun _ ↦ bs j) (extChartAt IB b₀ b, y)).2) ↔
        ∃ g : F → ℝ, ContMDiff IF 𝓘(ℝ) ∞ g ∧ ∀ (y : F) (w : TangentSpace IF y),
          mvfderiv IF g y w = RoughForm.mixedCurl (mpullback (𝓘(ℝ, EB).prod IF) IM
            (fun q : EB × F ↦ (A.trivAt b').toOpenPartialHomeomorph.symm
              ((extChartAt IB b₀).symm q.1, q.2)) τ.val) bs i j (extChartAt IB b₀ b) y w := by
  obtain ⟨U, hU, hbU, τ', hfib, hτ'c, hτ'ψ, hτ'τ⟩ :=
    hA.exists_isVerticallyClosed_eq_mpullback_symm_extChartAt_symm hτ hτσ hb
  have hnd : SmoothTwoForm.IsVerticallyNondegenerate 𝓘(ℝ, EB) Prod.fst τ' :=
    (SmoothTwoForm.isVerticallyNondegenerate_fst_iff τ').2 fun x ↦ (hfib x).symm ▸ hσ
  have hD' := hnd.isEhresmannConnection Manifold.isSubmersion_fst
  refine ⟨τ', hD', fun v₁ v₂ hv₁ hv₂ y ↦ ?_, fun i j ↦ ?_⟩
  · exact hD.curvatureIn_eq_snd_sum_curvature hn hA hb.1 hb.2 hD' (by simp)
      (hτ'τ b hb hbU y) bs hv₁ hv₂
  -- Near `φ b`, the mixed components of `τ'` are those of `ψ^* τ`.
  have hmix (k : ι) (y : F) (w : TangentSpace IF y) :
      (fun x' ↦ RoughForm.mixedComponent τ'.val bs k x' y ![w]) =ᶠ[𝓝 (extChartAt IB b₀ b)]
        fun x' ↦ RoughForm.mixedComponent (mpullback (𝓘(ℝ, EB).prod IF) IM
          (fun q : EB × F ↦ (A.trivAt b').toOpenPartialHomeomorph.symm
            ((extChartAt IB b₀).symm q.1, q.2)) τ.val) bs k x' y ![w] :=
    Filter.eventually_of_mem (hU.mem_nhds hbU) fun x' hx' ↦ by
      simp only [RoughForm.mixedComponent_apply, hτ'ψ (x', y) ⟨hx', mem_univ y⟩]
  have h := hD'.exists_isHamiltonianVectorField_curvature_iff bs
    ((hfib (extChartAt IB b₀ b)).symm ▸ hσ) (by simp)
    ((SmoothTwoForm.isVerticallyClosedOn_univ_iff.2 hτ'c).mono (subset_univ _)) i j
  rw [hfib] at h
  refine h.trans (exists_congr fun g ↦ and_congr_right fun _ ↦
    forall_congr' fun y ↦ forall_congr' fun w ↦ ?_)
  rw [RoughForm.mixedCurl_def, RoughForm.mixedCurl_def, (hmix j y w).fderiv_eq,
    (hmix i y w).fderiv_eq]

/-- **Hamiltonian curvature in local coordinates.** Let `A` be a smooth atlas of `proj : M → B`
with fibre `F`, over a Hausdorff base without boundary modelled on a finite-dimensional space
`EB`, with `F` modelled on a finite-dimensional space. Let `τ` be a vertically closed two-form
on `M` that restricts to a nondegenerate `σ` on the fibres of `A`, and whose horizontal spaces
form a `C^n` Ehresmann connection `hD`, `1 ≤ n`. Fix a basis `bs` of `EB`. Then `hD` has
Hamiltonian curvature exactly when, for every chart `e = A.trivAt b'`, every extended chart `φ`
of `B` at a point `b₀`, every `b` in the base set of `e` and in the source of the chart at `b₀`,
and all `i j`, some smooth `g : F → ℝ` has as differential the one-form `∂ᵢαⱼ(φ b) - ∂ⱼαᵢ(φ b)`
on `F`: the condition `MapFiber.Atlas.HasExactMixedCurl`. Here `αₖ(x)` is the mixed component,
for `bs`, of the pull-back of `τ` by `ψ q = e⁻¹ (φ⁻¹ q.1, q.2)`, and `∂ᵢ` differentiates in `x`
along `bs i`. -/
theorem hasHamiltonianCurvature_iff_local [T2Space B] {τ : SmoothTwoForm IM M} {n : ℕ∞ω}
    (hD : IsEhresmannConnection IM IB n proj (SmoothTwoForm.horizontalDistribution IB proj τ))
    (hn : 1 ≤ n) (hA : A.IsContMDiff ∞ IB IF IM) {σ : SmoothTwoForm IF F}
    (hσ : σ.IsNondegenerate) (hτ : SmoothTwoForm.IsVerticallyClosed IB proj τ)
    (hτσ : A.RestrictsTo σ τ) {ι : Type*} [Finite ι] (bs : Module.Basis ι ℝ EB) :
    hD.HasHamiltonianCurvature A σ ↔ A.HasExactMixedCurl IB IF τ bs := by
  have := Fintype.ofFinite ι
  rw [hasHamiltonianCurvature_def, MapFiber.Atlas.hasExactMixedCurl_def]
  constructor
  · intro H b' b₀ b hb i j
    obtain ⟨τ', hD', hsum, hiff⟩ := exists_curvature_of_mem_patch hD hn hA hσ hτ hτσ bs hb
    refine (hiff i j).1 ?_
    -- The vectors at `b` that `dφ` sends to `bs k`, extended to smooth fields on `B`.
    obtain ⟨L, hL⟩ := isInvertible_mfderiv_extChartAt (I := IB) (x := b₀)
      (by rw [extChartAt_source]; exact hb.2)
    set v : ι → Π c : B, TangentSpace IB c := fun k ↦
      FiberBundle.contMDiffExtend IB EB (L.symm (bs k) : TangentSpace IB b)
    have hv (k : ι) : ContMDiff IB IB.tangent ∞ (T% (v k)) :=
      FiberBundle.contMDiff_contMDiffExtend IB EB _
    have hvb (k : ι) : mfderiv IB 𝓘(ℝ, EB) (extChartAt IB b₀) b (v k b) = bs k := by
      simp only [v, FiberBundle.contMDiffExtend_apply_self, ← hL]
      exact L.apply_symm_apply (bs k)
    obtain ⟨f, hf, hX⟩ := H b' b hb.1 (v i) (v j) (hv i) (hv j)
    have hcurv : hD.curvatureIn IF (A.trivAt b') b (v i) (v j) =
        fun y ↦ (hD'.curvature (fun _ ↦ bs i) (fun _ ↦ bs j) (extChartAt IB b₀ b, y)).2 := by
      funext y
      rw [hsum (v i) (v j) ((hv i).contMDiffAt.of_le (by simp))
        ((hv j).contMDiffAt.of_le (by simp)) y, hvb, hvb]
      rw [Module.Basis.repr_self, Module.Basis.repr_self,
        Finset.sum_eq_single i (fun i' _ hi' ↦ ?_) (by simp),
        Finset.sum_eq_single j (fun j' _ hj' ↦ ?_) (by simp)]
      · rw [Finsupp.single_eq_same, Finsupp.single_eq_same, mul_one, one_smul]
      · rw [Finsupp.single_eq_of_ne hj', mul_zero, zero_smul]
      · exact Finset.sum_eq_zero fun j' _ ↦ by rw [Finsupp.single_eq_of_ne hi', zero_mul, zero_smul]
    exact ⟨f, hf, hcurv ▸ hX⟩
  · intro H b' b hb v₁ v₂ hv₁ hv₂
    have hb' : b ∈ (A.trivAt b').baseSet ∩ (chartAt HB b).source := ⟨hb, mem_chart_source HB b⟩
    obtain ⟨τ', hD', hsum, hiff⟩ := exists_curvature_of_mem_patch hD hn hA hσ hτ hτσ bs hb'
    choose f hf hX using fun i j ↦ (hiff i j).2 (H b' b b hb' i j)
    set c : ι → ι → ℝ := fun i j ↦
      bs.repr (mfderiv IB 𝓘(ℝ, EB) (extChartAt IB b) b (v₁ b)) i *
        bs.repr (mfderiv IB 𝓘(ℝ, EB) (extChartAt IB b) b (v₂ b)) j
    have hcurv : hD.curvatureIn IF (A.trivAt b') b v₁ v₂ = ∑ i, ∑ j, c i j •
        fun y ↦ (hD'.curvature (fun _ ↦ bs i) (fun _ ↦ bs j) (extChartAt IB b b, y)).2 := by
      funext y
      rw [hsum v₁ v₂ ((hv₁ b).of_le (by simp)) ((hv₂ b).of_le (by simp)) y]
      simp only [Finset.sum_apply, Pi.smul_apply]
      -- The tangent spaces of `EB × F` are `EB × EF` only by definition, so the fibre part is
      -- taken by the linear map `LinearMap.snd`.
      exact (map_sum (LinearMap.snd ℝ EB EF) _ _).trans
        (Finset.sum_congr rfl fun i _ ↦ (map_sum (LinearMap.snd ℝ EB EF) _ _).trans
          (Finset.sum_congr rfl fun j _ ↦ map_smul (LinearMap.snd ℝ EB EF) _ _))
    have hcf (i j : ι) : ContMDiff IF 𝓘(ℝ) ∞ (c i j • f i j) :=
      (contDiff_const_smul (c i j)).comp_contMDiff (hf i j)
    have hcs (i : ι) : ContMDiff IF 𝓘(ℝ) ∞ (∑ j, c i j • f i j) :=
      contMDiff_finsetSum' fun j _ ↦ hcf i j
    refine ⟨∑ i, ∑ j, c i j • f i j, ?_, ?_⟩
    · exact contMDiff_finsetSum' fun i _ ↦ hcs i
    rw [hcurv]
    refine SmoothTwoForm.IsHamiltonianVectorField.sum (fun i _ ↦ ?_) fun i _ ↦ ?_
    · exact SmoothTwoForm.IsHamiltonianVectorField.sum (fun j _ ↦ (hX i j).const_smul (c i j))
        fun j _ ↦ (hcf i j).mdifferentiable (by simp)
    · exact (hcs i).mdifferentiable (by simp)

end IsEhresmannConnection

end TauCeti

end
