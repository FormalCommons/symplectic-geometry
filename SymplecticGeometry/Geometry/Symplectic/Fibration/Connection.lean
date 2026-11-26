/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Fibration.HorizontalDistribution
public import SymplecticGeometry.Geometry.Manifold.Submersion.ParallelTransport.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Manifold.TwoForm.Basic
import SymplecticGeometry.Geometry.Manifold.FiberBundle.StructureGroup

/-!
# Symplectic connections

Let `proj : M → B` be a map with an atlas `A` whose model fibre `F` carries a two-form `σ`, and
let `D` be an Ehresmann connection on `proj`. The connection is *symplectic* when parallel
transport along every smooth curve of `B`, read in the model fibre through any two charts of
`A`, pulls `σ` back to itself. For an atlas whose coordinate changes preserve `σ`, the fibres
carry the forms that the charts carry to `σ`, and the condition says that transport is a
symplectomorphism between these fibre forms.

## Main definitions

* `TauCeti.IsEhresmannConnection.IsSymplectic hD A σ`: transport by `D` along every smooth
  curve, read in any two charts of `A`, preserves `σ`.

## Main results

* `TauCeti.IsEhresmannConnection.isSymplectic_iff_forall_exists`: for a proper map with a smooth
  atlas whose coordinate changes preserve `σ`, it suffices to check one pair of charts for each
  curve and pair of times, as a change of charts conjugates transport by coordinate changes
  (`TauCeti.IsEhresmannConnection.parallelTransportIn_coordChange`).
* `IsSymplectic.parallelTransportInDiffeomorph_mem_diffeomorphStabilizer`, in the namespace
  `TauCeti.IsEhresmannConnection`: the diffeomorphisms of the model fibre given by transport in
  the charts of a smooth atlas lie in the stabilizer of `σ`.
* `TauCeti.SmoothTwoForm.IsVerticallyClosed.mlieDerivForm_apply_eq_zero`: for a smooth atlas of
  `proj` and a vertically closed two-form `τ`, the Lie derivative of `τ` along a `C¹` vector
  field with horizontal values vanishes on pairs of vertical vectors. By Cartan's formula it is
  `ι_X dτ + d ι_X τ`; the first term vanishes by vertical closedness, and the second because
  `ι_X τ` is semibasic, so that its derivative pulls back to zero on the fibres
  (`Bundle.Trivialization.mextDeriv_apply_eq_zero_of_isSemibasic`).

## Implementation notes

Transport is only meaningful for a proper `proj`; elsewhere the definition takes junk values,
and the results here assume properness.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.3.
* [V. Guillemin, E. Lerman, S. Sternberg, *Symplectic Fibrations and Multiplicity
  Diagrams*][GuilleminLermanSternberg1996], §1.2.
-/

public section

noncomputable section

open Bundle Function
open scoped ContDiff Manifold

namespace TauCeti

namespace IsEhresmannConnection

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M] [IM.Boundaryless]
  [T2Space M]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B] [IB.Boundaryless]
  [T2Space B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF]
  {HF : Type*} [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF}
  {F : Type*} [TopologicalSpace F] [ChartedSpace HF F] [IsManifold IF ∞ F]
  {n : ℕ∞} {proj : M → B} {D : Π x : M, Submodule ℝ (TangentSpace IM x)}
  (hD : IsEhresmannConnection IM IB n proj D) (A : MapFiber.Atlas F proj)
  (σ : SmoothTwoForm IF F)

/-- An Ehresmann connection `D` on `proj` is *symplectic* for an atlas `A` of `proj` and a
two-form `σ` on its model fibre when, for every smooth curve `γ` in `B`, all times `s` and `t`,
and all charts `A.trivAt b` and `A.trivAt b'` whose base sets contain `γ s` and `γ t`, parallel
transport along `γ` from `s` to `t`, read in these charts, pulls `σ` back to `σ`. -/
def IsSymplectic : Prop :=
  ∀ γ : ℝ → B, ContMDiff 𝓘(ℝ, ℝ) IB ∞ γ → ∀ s t : ℝ, ∀ b b' : B,
    γ s ∈ (A.trivAt b).baseSet → γ t ∈ (A.trivAt b').baseSet →
      mpullback IF IF (hD.parallelTransportIn (A.trivAt b) (A.trivAt b') γ s t) σ.val = σ.val

omit [FiniteDimensional ℝ EM] [IM.Boundaryless] [T2Space M]
  [FiniteDimensional ℝ EB] [IsManifold IB ∞ B] [IB.Boundaryless] [T2Space B] in
theorem isSymplectic_def :
    hD.IsSymplectic A σ ↔ ∀ γ : ℝ → B, ContMDiff 𝓘(ℝ, ℝ) IB ∞ γ → ∀ s t : ℝ, ∀ b b' : B,
      γ s ∈ (A.trivAt b).baseSet → γ t ∈ (A.trivAt b').baseSet →
        mpullback IF IF (hD.parallelTransportIn (A.trivAt b) (A.trivAt b') γ s t) σ.val =
          σ.val :=
  Iff.rfl

variable {hD A σ}

/-- **One pair of charts suffices.** Let `D` be a `C^n` Ehresmann connection, `1 ≤ n`, on a
proper map `proj` with a smooth atlas `A` whose coordinate changes preserve `σ`. Then `D` is
symplectic exactly when, for every smooth curve `γ` and all times `s` and `t`, transport along
`γ` from `s` to `t` pulls `σ` back to `σ` when read in some pair of charts of `A` whose base sets
contain `γ s` and `γ t`. -/
theorem isSymplectic_iff_forall_exists (hn : 1 ≤ n) (hfp : IsProperMap proj)
    (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ)) :
    hD.IsSymplectic A σ ↔ ∀ γ : ℝ → B, ContMDiff 𝓘(ℝ, ℝ) IB ∞ γ → ∀ s t : ℝ,
      ∃ b b' : B, γ s ∈ (A.trivAt b).baseSet ∧ γ t ∈ (A.trivAt b').baseSet ∧
        mpullback IF IF (hD.parallelTransportIn (A.trivAt b) (A.trivAt b') γ s t) σ.val =
          σ.val := by
  refine ⟨fun h γ hγ s t ↦ ⟨γ s, γ t, A.mem_baseSet_trivAt _, A.mem_baseSet_trivAt _,
    h γ hγ s t _ _ (A.mem_baseSet_trivAt _) (A.mem_baseSet_trivAt _)⟩,
    fun h γ hγ s t b₂ b₂' hs₂ ht₂ ↦ ?_⟩
  obtain ⟨b, b', hs, ht, hT⟩ := h γ hγ s t
  obtain ⟨φ, hφ, hφe⟩ := MapFiber.Atlas.hasStructureGroup_iff.1 hH b₂ b (γ s) hs₂ hs
  obtain ⟨φ', hφ', hφ'e⟩ := MapFiber.Atlas.hasStructureGroup_iff.1 hH b' b₂' (γ t) ht ht₂
  have hn' : (n : ℕ∞ω) + 1 ≤ ∞ := by exact_mod_cast le_top
  have hf := hA.contMDiff_proj.of_le hn'
  have hconj : hD.parallelTransportIn (A.trivAt b₂) (A.trivAt b₂') γ s t =
      φ' ∘ hD.parallelTransportIn (A.trivAt b) (A.trivAt b') γ s t ∘ φ := by
    funext v
    rw [comp_apply, comp_apply, hφe, hφ'e]
    exact hD.parallelTransportIn_coordChange hn hf hfp (hγ.of_le hn') hs hs₂ ht v
  have hT' : MDifferentiable IF IF (hD.parallelTransportIn (A.trivAt b) (A.trivAt b') γ s t) :=
    (hD.contMDiff_parallelTransportIn hn hf hfp (hγ.of_le hn')
      ((hA.contMDiffOn_trivAt_symm b).of_le (by simp)) ((hA.contMDiffOn_trivAt b').of_le (by simp))
      hs ht).mdifferentiable (by simpa using (one_pos.trans_le hn).ne')
  have hdiff (ψ : F ≃ₘ⟮IF, IF⟯ F) : MDifferentiable IF IF ψ := ψ.mdifferentiable (by simp)
  have hstab {ψ : F ≃ₘ⟮IF, IF⟯ F} (hψ : ψ ∈ SmoothForm.diffeomorphStabilizer σ) :
      mpullback IF IF ψ σ.val = σ.val :=
    funext (SmoothForm.mem_diffeomorphStabilizer_iff_forall.1 hψ)
  rw [hconj, mpullback_comp (hT'.comp (hdiff φ)) (hdiff φ'), hstab hφ',
    mpullback_comp (hdiff φ) hT', hT, hstab hφ]

/-- **Transport by a symplectic connection is symplectic.** For a symplectic smooth Ehresmann
connection on a proper map with a smooth atlas `A`, transport along a smooth curve from `s` to
`t`, read as a diffeomorphism of the model fibre in two charts of `A` whose base sets contain
`γ s` and `γ t`, lies in the stabilizer of `σ`. -/
theorem IsSymplectic.parallelTransportInDiffeomorph_mem_diffeomorphStabilizer
    {hD : IsEhresmannConnection IM IB ∞ proj D}
    (h : hD.IsSymplectic A σ) (hfp : IsProperMap proj) (hA : A.IsContMDiff ∞ IB IF IM)
    {γ : ℝ → B} (hγ : ContMDiff 𝓘(ℝ, ℝ) IB ∞ γ) {s t : ℝ} {b b' : B}
    (hs : γ s ∈ (A.trivAt b).baseSet) (ht : γ t ∈ (A.trivAt b').baseSet) :
    hD.parallelTransportInDiffeomorph (A.trivAt b) (A.trivAt b') γ s t le_top
        (hA.contMDiff_proj.of_le (by simp)) hfp (hγ.of_le (by simp))
        (hA.contMDiffOn_trivAt b) (hA.contMDiffOn_trivAt_symm b) (hA.contMDiffOn_trivAt b')
        (hA.contMDiffOn_trivAt_symm b') hs ht ∈
      SmoothForm.diffeomorphStabilizer σ := by
  rw [SmoothForm.mem_diffeomorphStabilizer_iff_forall, coe_parallelTransportInDiffeomorph]
  exact congrFun (h γ hγ s t b b' hs ht)

end IsEhresmannConnection

namespace SmoothTwoForm

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF]
  {HF : Type*} [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF}
  {F : Type*} [TopologicalSpace F] [ChartedSpace HF F] [IsManifold IF ∞ F]
  {proj : M → B} {A : MapFiber.Atlas F proj} {τ : SmoothTwoForm IM M}

/-- **Lie derivatives of a vertically closed form along horizontal fields.** Let `A` be a smooth
atlas of `proj` and `τ` a two-form on `M` that is vertically closed for `proj`. For a `C¹` vector
field `X` on `M` whose values lie in the horizontal spaces of `τ`, the Lie derivative of `τ` along
`X` vanishes at every point on every pair of vertical vectors. -/
theorem IsVerticallyClosed.mlieDerivForm_apply_eq_zero (hA : A.IsContMDiff ∞ IB IF IM)
    (h : IsVerticallyClosed IB proj τ) {X : Π x : M, TangentSpace IM x}
    (hX : ContMDiff IM IM.tangent 1 fun y ↦ (X y : TangentBundle IM M))
    (hXh : ∀ x, X x ∈ horizontalDistribution IB proj τ x) {x : M} {η₁ η₂ : TangentSpace IM x}
    (hη₁ : η₁ ∈ (mfderiv IM IB proj x).ker) (hη₂ : η₂ ∈ (mfderiv IM IB proj x).ker) :
    mlieDerivForm X τ.val x ![η₁, η₂] = 0 := by
  -- The contraction `ι_X τ` vanishes on vertical vectors, as `X` is horizontal.
  have hsb : RoughForm.IsSemibasic IB proj (RoughForm.interior X τ.val) := by
    refine RoughForm.isSemibasic_iff.2 fun y v i hv ↦ ?_
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have hy := (SmoothForm.isAlt_bilinFormAt τ y).isRefl _ _
      (mem_horizontalDistribution_iff.1 (hXh y) (v 0) hv)
    rw [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply] at hy
    rw [RoughForm.interior_apply]
    rwa [show v = ![v 0] from funext fun i ↦ by rw [Subsingleton.elim i 0, Matrix.cons_val_zero]]
  have hsm : IsSmoothBundleForm (I := IM) (F := ℝ) (V := Trivial M ℝ) 1
      (RoughForm.interior X τ.val) :=
    (isSmoothBundleForm_def 1 _).2 ((τ.isSmoothForm.of_le (by simp)).interior hX).contMDiff
  rw [SmoothForm.mlieDerivForm_eq_interior_mextDeriv_add (hX.mdifferentiable one_ne_zero),
    Pi.add_apply, ContinuousAlternatingMap.add_apply,
    (A.trivAt (proj x)).mextDeriv_apply_eq_zero_of_isSemibasic
      (hA.mdifferentiable_trivAt (by simp) _) ((hA.contMDiffOn_trivAt_symm _).of_le (by simp))
      hsb hsm (A.mem_baseSet_trivAt _) (Fin.forall_fin_two.2 ⟨hη₁, hη₂⟩), add_zero,
    RoughForm.interior_apply]
  -- `(X, η₁, η₂)` is a permutation of `(η₁, η₂, X)`, on which `dτ` vanishes.
  have hσ : ![X x, η₁, η₂] = ![η₁, η₂, X x] ∘ (finRotate 3).symm := by
    ext i
    fin_cases i <;> simp
  have hperm := (mextDeriv τ.val x).toAlternatingMap.map_perm ![η₁, η₂, X x] (finRotate 3).symm
  rwa [← hσ, ContinuousAlternatingMap.coe_toAlternatingMap,
    isVerticallyClosed_iff.1 h x η₁ hη₁ η₂ hη₂ (X x), smul_zero] at hperm

end SmoothTwoForm

end TauCeti

end
