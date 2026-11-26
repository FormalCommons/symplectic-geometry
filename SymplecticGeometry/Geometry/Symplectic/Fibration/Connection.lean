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
import TauCeti.Geometry.Manifold.DifferentialForm.Flow.TimeDependent
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
* `TauCeti.SmoothTwoForm.IsVerticallyClosed.hasDerivAt_mpullback_comp_zero`: for a jointly `C²`
  time-dependent field `X` with complete suspension and horizontal values at time `t`, and a map
  `ι` that the flow of `X` from `s` to `t` carries into one fibre, the pull-back of a vertically
  closed `τ` along the flow from `s` to `u` composed with `ι` has zero velocity at `u = t`. This
  is Tau Ceti's `TauCeti.hasDerivAt_mpullback_timeDependentFlowOf_self`, moved to the base time
  `s` by `TauCeti.timeDependentFlowOf_trans`, combined with the lemma above. Applied to the field
  that the following lemma of `ParallelTransport/Smooth.lean` gives,
  `IsEhresmannConnection.exists_timeDependentField_eqOn_parallelTransport_of_mapsTo_baseSet`,
  it shows that over a short interval transport carries the pull-back of `τ` to one fibre to its
  pull-back to the other.
* `TauCeti.SmoothTwoForm.IsVerticallyClosed.mpullback_parallelTransportIn`: for a proper map
  with a smooth atlas `A` and a vertically closed `τ` whose horizontal spaces form an Ehresmann
  connection, transport along any smooth curve, read in two charts of `A`, carries the pull-back
  of `τ` to the later fibre to its pull-back to the earlier one. The times between which this
  holds form a transitive relation (`IsEhresmannConnection.parallelTransportIn_parallelTransportIn`)
  that holds between nearby times by the short-interval case, so Mathlib's
  `PreconnectedSpace.induction₂'` gives it for all times, as in
  `TauCeti.IsEhresmannConnection.exists_diffeomorph_eqOn_parallelTransport`.

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
open scoped ContDiff Manifold Topology

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

section Transport

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
  {proj : M → B} {A : MapFiber.Atlas F proj} {τ : SmoothTwoForm IM M}

omit [FiniteDimensional ℝ EB] [IsManifold IB ∞ B] [IB.Boundaryless] [T2Space B] in
/-- **Horizontal flows, restricted to fibres.** Let `A` be a smooth atlas of `proj`, `τ` a
vertically closed two-form on `M`, and `X` a jointly `C²` time-dependent vector field on `M` with
complete suspension, whose values at time `t` lie in the horizontal spaces of `τ`. If `ι : N → M`
is differentiable at `x` and the flow of `X` from `s` to `t` maps the image of `ι` into one fibre
of `proj`, then the pull-backs of `τ` at `x` along the flow from `s` to `u` composed with `ι` have
velocity zero at `u = t`. -/
theorem IsVerticallyClosed.hasDerivAt_mpullback_comp_zero
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] {HN : Type*} [TopologicalSpace HN]
    {IN : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    (hA : A.IsContMDiff ∞ IB IF IM) (h : IsVerticallyClosed IB proj τ)
    {X : ℝ → Π y : M, TangentSpace IM y}
    (hc : IsCompleteVectorField (timeDependentSuspensionField X))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod IM) IM.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle IM M))) {s t : ℝ}
    (hXh : ∀ y, X t y ∈ horizontalDistribution IB proj τ y) {ι : N → M} {x : N}
    (hι : MDifferentiableAt IN IM ι x)
    (hιt : ∀ y, proj (timeDependentFlowOf X s t (ι y)) = proj (timeDependentFlowOf X s t (ι x))) :
    HasDerivAt (F := EN [⋀^Fin 2]→L[ℝ] ℝ)
      (fun u ↦ mpullback IN IM (timeDependentFlowOf X s u ∘ ι) τ.val x) 0 t := by
  have hX₁ := hX.of_le (m := 1) one_le_two
  have hφ (r u : ℝ) : MDifferentiable IM IM (timeDependentFlowOf X r u) :=
    ((contMDiff_timeDependentFlowOf hc le_rfl hX₁).comp
      ((contMDiff_const (c := (r, u))).prodMk contMDiff_id)).mdifferentiable one_ne_zero
  set g := timeDependentFlowOf X s t ∘ ι
  have hg : MDifferentiableAt IN IM g x := (hφ s t _).comp x hι
  -- By the composition law, the flow from `s` to `u` is the flow from `t` to `u` after `g`.
  refine (hasDerivAt_mpullback_of_eq_comp (χ := timeDependentFlowOf X t) (g := g)
    (Filter.Eventually.of_forall fun u ↦ Filter.Eventually.of_forall fun y ↦
      (timeDependentFlowOf_trans hc hX₁ s t u (ι y)).symm) hg
    (Filter.Eventually.of_forall fun u ↦ hφ t u _)
    (hasDerivAt_mpullback_timeDependentFlowOf_self hX₁ t (g x)
      ((τ.isSmoothForm.contMDiff.mdifferentiable (by simp)) _))).congr_deriv ?_
  ext w
  rw [mpullback_apply]
  -- The derivative of `g` takes vertical values, as `proj` is constant along it.
  have hvert (i : Fin 2) : mfderiv IN IM g x (w i) ∈ (mfderiv IM IB proj (g x)).ker := by
    have hd := mfderiv_comp x ((hA.contMDiff_proj.mdifferentiable (by simp)) (g x)) hg
    rw [show proj ∘ g = fun _ ↦ proj (g x) from funext hιt, mfderiv_const] at hd
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.comp_apply, ← hd]
    exact zero_apply _
  have hw : (fun i ↦ mfderiv IN IM g x (w i)) =
      ![mfderiv IN IM g x (w 0), mfderiv IN IM g x (w 1)] := by
    ext i
    fin_cases i <;> rfl
  rw [hw]
  have hXt : ContMDiff IM IM.tangent 1 fun y ↦ (⟨y, X t y⟩ : TangentBundle IM M) :=
    hX₁.comp ((contMDiff_const (c := t)).prodMk contMDiff_id)
  -- The right side is the zero form evaluated at `w`; `rfl` closes it, as the zero form is read
  -- on the tangent spaces of `N`, through which `zero_apply` finds no instance.
  exact (h.mlieDerivForm_apply_eq_zero hA hXt hXh (hvert 0) (hvert 1)).trans rfl

/-- The local step of `IsVerticallyClosed.mpullback_parallelTransportIn`: let `A` be a smooth atlas
of a proper map `proj`, `τ` a vertically closed two-form on `M` whose horizontal spaces form an
Ehresmann connection `hD`, and `γ` a smooth curve that maps the interval `Set.Icc a b` into the
base set of one trivialization of the tangent bundle of `B`. For times `s` and `t` in that
interval, transport along `γ` from `s` to `t`, read in charts of `A` at `γ s` and `γ t`, pulls the
pull-back of `τ` to the fibre over `γ t` back to the pull-back of `τ` to the fibre over `γ s`. -/
private theorem IsVerticallyClosed.mpullback_parallelTransportIn_of_mapsTo_baseSet
    (hfp : IsProperMap proj) (hA : A.IsContMDiff ∞ IB IF IM) (h : IsVerticallyClosed IB proj τ)
    (hD : IsEhresmannConnection IM IB ∞ proj (horizontalDistribution IB proj τ)) {γ : ℝ → B}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) IB ∞ γ) {a b : ℝ}
    (e : Trivialization EB (π EB (TangentSpace IB))) [MemTrivializationAtlas e]
    (hγe : Set.MapsTo γ (Set.Icc a b) e.baseSet) {s t : ℝ} (hs : s ∈ Set.Icc a b)
    (ht : t ∈ Set.Icc a b) {b₁ b₂ : B} (hs₁ : γ s ∈ (A.trivAt b₁).baseSet)
    (ht₂ : γ t ∈ (A.trivAt b₂).baseSet) :
    mpullback IF IF (hD.parallelTransportIn (A.trivAt b₁) (A.trivAt b₂) γ s t)
        (mpullback IF IM ((A.trivAt b₂).fiberInclusionMap ht₂) τ.val) =
      mpullback IF IM ((A.trivAt b₁).fiberInclusionMap hs₁) τ.val := by
  have hn' : ((⊤ : ℕ∞) : ℕ∞ω) + 1 ≤ ∞ := by exact_mod_cast le_top
  have hf : ContMDiff IM IB ((⊤ : ℕ∞) + 1) proj := hA.contMDiff_proj.of_le hn'
  have hγ' : ContMDiff 𝓘(ℝ, ℝ) IB ((⊤ : ℕ∞) + 1) γ := hγ.of_le hn'
  obtain ⟨X, hc, hX, hXh, htrans⟩ :=
    hD.exists_timeDependentField_eqOn_parallelTransport_of_mapsTo_baseSet le_top hf hfp hγ' e hγe
  have hX₂ := hX.of_le (m := 2) (by simp)
  have htr := htrans s hs
  set φ := timeDependentFlowOf X s
  set ι := (A.trivAt b₁).fiberInclusionMap hs₁
  have hι : MDifferentiable IF IM ι :=
    ((A.trivAt b₁).contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm b₁)
      hs₁).mdifferentiable (by simp)
  -- The pull-backs of `τ` along `φ u ∘ ι` are constant in `u` on the interval, as `φ u ∘ ι` maps
  -- into the fibre over `γ u`.
  have hconst (v : F) :
      mpullback IF IM (φ t ∘ ι) τ.val v = mpullback IF IM (φ s ∘ ι) τ.val v := by
    have hderiv (u : ℝ) (hu : u ∈ Set.Icc a b) :
        HasDerivAt (F := EF [⋀^Fin 2]→L[ℝ] ℝ) (fun r ↦ mpullback IF IM (φ r ∘ ι) τ.val v) 0 u := by
      have hproj (y : F) : proj (φ u (ι y)) = γ u := by
        rw [htr u hu ((A.trivAt b₁).proj_fiberInclusionMap hs₁ y)]
        exact hD.parallelTransport_mem_preimage le_top hf hfp hγ'
          ((A.trivAt b₁).proj_fiberInclusionMap hs₁ y) u
      exact h.hasDerivAt_mpullback_comp_zero hA hc hX₂ (hXh u) (hι v) fun y ↦ by rw [hproj, hproj]
    have hk := constant_of_has_deriv_right_zero (E := EF [⋀^Fin 2]→L[ℝ] ℝ)
      (f := (fun r ↦ mpullback IF IM (φ r ∘ ι) τ.val v : ℝ → EF [⋀^Fin 2]→L[ℝ] ℝ))
      (fun r hr ↦ (hderiv r hr).continuousAt.continuousWithinAt)
      (fun r hr ↦ (hderiv r (Set.Ico_subset_Icc_self hr)).hasDerivWithinAt)
    rw [hk t ht, hk s hs]
  -- At time `t`, `φ t ∘ ι` is transport followed by the inclusion of the fibre over `γ t`.
  have hφt : φ t ∘ ι = (A.trivAt b₂).fiberInclusionMap ht₂ ∘
      hD.parallelTransportIn (A.trivAt b₁) (A.trivAt b₂) γ s t := funext fun y ↦ by
    rw [comp_apply, comp_apply, htr t ht ((A.trivAt b₁).proj_fiberInclusionMap hs₁ y),
      hD.fiberInclusionMap_parallelTransportIn le_top hf hfp hγ' hs₁ ht₂]
  have hP : MDifferentiable IF IF (hD.parallelTransportIn (A.trivAt b₁) (A.trivAt b₂) γ s t) :=
    (hD.contMDiff_parallelTransportIn le_top hf hfp hγ' (hA.contMDiffOn_trivAt_symm b₁)
      (hA.contMDiffOn_trivAt b₂) hs₁ ht₂).mdifferentiable (by simp)
  have hι₂ : MDifferentiable IF IM ((A.trivAt b₂).fiberInclusionMap ht₂) :=
    ((A.trivAt b₂).contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm b₂)
      ht₂).mdifferentiable (by simp)
  funext v
  rw [← mpullback_comp hP hι₂, ← hφt, hconst v, show φ s ∘ ι = ι from
    funext fun y ↦ timeDependentFlowOf_self X s _]

/-- **Transport preserves the fibre forms of a vertically closed form.** Let `A` be a smooth atlas
of a proper map `proj`, and `τ` a vertically closed two-form on `M` whose horizontal spaces form a
smooth Ehresmann connection `hD`, as they do when `τ` is vertically nondegenerate
(`IsVerticallyNondegenerate.isEhresmannConnection`). For a smooth curve `γ` in `B`, all times `s`
and `t`, and charts `A.trivAt b₁` and `A.trivAt b₂` whose base sets contain `γ s` and `γ t`,
transport along `γ` from `s` to `t`, read in these charts, pulls the pull-back of `τ` to the fibre
over `γ t` back to the pull-back of `τ` to the fibre over `γ s`. -/
theorem IsVerticallyClosed.mpullback_parallelTransportIn
    (hfp : IsProperMap proj) (hA : A.IsContMDiff ∞ IB IF IM) (h : IsVerticallyClosed IB proj τ)
    (hD : IsEhresmannConnection IM IB ∞ proj (horizontalDistribution IB proj τ)) {γ : ℝ → B}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) IB ∞ γ) {s t : ℝ} {b₁ b₂ : B}
    (hs₁ : γ s ∈ (A.trivAt b₁).baseSet) (ht₂ : γ t ∈ (A.trivAt b₂).baseSet) :
    mpullback IF IF (hD.parallelTransportIn (A.trivAt b₁) (A.trivAt b₂) γ s t)
        (mpullback IF IM ((A.trivAt b₂).fiberInclusionMap ht₂) τ.val) =
      mpullback IF IM ((A.trivAt b₁).fiberInclusionMap hs₁) τ.val := by
  have hn' : ((⊤ : ℕ∞) : ℕ∞ω) + 1 ≤ ∞ := by exact_mod_cast le_top
  have hf : ContMDiff IM IB ((⊤ : ℕ∞) + 1) proj := hA.contMDiff_proj.of_le hn'
  have hγ' : ContMDiff 𝓘(ℝ, ℝ) IB ((⊤ : ℕ∞) + 1) γ := hγ.of_le hn'
  -- Times between which transport, read in any two charts, carries one fibre form to the other.
  let R : ℝ → ℝ → Prop := fun u v ↦ ∀ (c₁ c₂ : B) (hu : γ u ∈ (A.trivAt c₁).baseSet)
    (hv : γ v ∈ (A.trivAt c₂).baseSet),
    mpullback IF IF (hD.parallelTransportIn (A.trivAt c₁) (A.trivAt c₂) γ u v)
        (mpullback IF IM ((A.trivAt c₂).fiberInclusionMap hv) τ.val) =
      mpullback IF IM ((A.trivAt c₁).fiberInclusionMap hu) τ.val
  have hP {c₁ c₂ : B} {u v : ℝ} (hu : γ u ∈ (A.trivAt c₁).baseSet)
      (hv : γ v ∈ (A.trivAt c₂).baseSet) :
      MDifferentiable IF IF (hD.parallelTransportIn (A.trivAt c₁) (A.trivAt c₂) γ u v) :=
    (hD.contMDiff_parallelTransportIn le_top hf hfp hγ' (hA.contMDiffOn_trivAt_symm c₁)
      (hA.contMDiffOn_trivAt c₂) hu hv).mdifferentiable (by simp)
  -- The relation is transitive: transport from `u` to `w` passes through the chart at `γ v`.
  have htrans : IsTrans ℝ R := ⟨fun u v w h₁ h₂ c₁ c₃ hu hw ↦ by
    have hv := A.mem_baseSet_trivAt (γ v)
    have hcomp : hD.parallelTransportIn (A.trivAt c₁) (A.trivAt c₃) γ u w =
        hD.parallelTransportIn (A.trivAt (γ v)) (A.trivAt c₃) γ v w ∘
          hD.parallelTransportIn (A.trivAt c₁) (A.trivAt (γ v)) γ u v := funext fun x ↦
      (hD.parallelTransportIn_parallelTransportIn le_top hf hfp hγ' _ hu hv w x).symm
    rw [hcomp, mpullback_comp (hP hu hv) (hP hv hw), h₂ _ _ hv hw, h₁ _ _ hu hv]⟩
  -- It holds between nearby times: near `u`, `γ` stays in the base set of one trivialization.
  have hloc (u : ℝ) : ∀ᶠ v in 𝓝 u, R u v ∧ R v u := by
    let e := trivializationAt EB (TangentSpace IB) (γ u)
    obtain ⟨a, b, hu, hab, hmaps⟩ := exists_Icc_mem_subset_of_mem_nhds
      (hγ.continuous.continuousAt.eventually_mem_baseSet_trivializationAt EB (TangentSpace IB))
    filter_upwards [hab] with v hv
    exact ⟨fun _ _ ↦ h.mpullback_parallelTransportIn_of_mapsTo_baseSet hfp hA hD hγ e hmaps hu hv,
      fun _ _ ↦ h.mpullback_parallelTransportIn_of_mapsTo_baseSet hfp hA hD hγ e hmaps hv hu⟩
  exact PreconnectedSpace.induction₂' R hloc htrans s t b₁ b₂ hs₁ ht₂

end Transport

end SmoothTwoForm

end TauCeti

end
