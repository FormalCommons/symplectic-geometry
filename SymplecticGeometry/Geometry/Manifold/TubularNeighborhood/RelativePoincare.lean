/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.TubularNeighborhood.RelativePoincare
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import TauCeti.Geometry.Manifold.DifferentialForm.Opens

/-!
# Relative primitives near an embedded submanifold

This file derives, from Tau Ceti's relative Poincaré lemma
`TauCeti.SmoothEmbedding.exists_isSmoothForm_relative_primitive`, two kinds of primitives of
closed forms near the image of a smooth embedding.

**The difference of two closed forms.** Let `f : Q → M` be an embedding into a boundaryless
Hausdorff second-countable manifold, and let `η₀`, `η₁` be closed smooth `(k + 1)`-forms on `M`
with the same pullback to `Q`. Then on a tube `W` around `f(Q)`, inside any given open set
containing `f(Q)`, there is a smooth `k`-form `β` with `dβ = η₁ - η₀` on `W` that vanishes along
`f(Q)`. Its coordinate expressions have zero derivative at each point `f q` at which `η₁` and `η₀`
agree as forms on `T_{f q} M`. This is the first step of the relative Moser theorems
([McDuffSalamon2017], Lemma 3.2.1 and Exercise 3.2.6; [CannasdaSilva2001], Theorem 7.4). The
proof applies the relative Poincaré lemma to `η₁ - η₀` and bundles the primitive as a smooth form
on the tube, as Tau Ceti's
`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_embedding_eventually_mpullback_eq` does inside its
proof.

**Prescribed pullback.** Let `f : M → N` be a smooth embedding of boundaryless
finite-dimensional manifolds, with `N` Hausdorff and second countable, let `θ` be a closed smooth
`(k + 1)`-form on `N`, and let `β` be a smooth `k`-form on `M` with `dβ = f^* θ`. Then on an open
neighbourhood of the image of `f`, `θ` has a smooth primitive whose pullback along `f` is `β`.
For `β = 0` its conclusion `f^* γ = 0` is weaker than that of the relative Poincaré lemma, whose
primitive vanishes along the image as an ambient tensor and has a first-jet property there; the
theorem generalizes the pullback condition to an arbitrary `β`. The proof follows the converse
half of McDuff–Salamon's Proposition 3.5.31 ([McDuffSalamon2017]):

* `TauCeti.SmoothForm.mpullback_sub_mextDerivₗ_eq_zero`: if `dβ = f^* θ` and `f^* ψ = β`, then
  `θ - dψ` pulls back to zero along `f`.
* `TauCeti.SmoothEmbedding.exists_mextDerivₗ_eq_and_mpullback_eq_of_leftInverse`: the theorem for
  an embedding with a smooth left inverse `ρ`. The form `θ - d(ρ^* β)` is closed with zero
  pullback along `f`, so the relative Poincaré lemma gives a primitive `μ` of it vanishing along
  `f`, and `ρ^* β + μ` is the primitive sought.
* `TauCeti.exists_mpullback_subtype_val_eq`, `TauCeti.contMDiffAt_mpullback_subtype_val_iff`,
  `TauCeti.mextDeriv_mpullback_subtype_val_apply`: every form on an open subset `U` is the
  restriction of one on the whole manifold, and at a point of `U` a form and its restriction
  have the same regularity and the same exterior derivative, since the inclusion is a local
  diffeomorphism (`IsLocalDiffeomorphAt.contMDiffAt_mpullback_form_iff`,
  `TauCeti.mpullback_mextDeriv_at`). They are the `Subtype.val` counterparts of Tau Ceti's
  `TauCeti.contMDiffAt_mpullback_inclusion_iff` and `TauCeti.mpullback_inclusion_mextDeriv`.

The theorem itself applies the case of a left inverse on the open neighbourhood where the smooth
retraction of `TauCeti.SmoothEmbedding.exists_contMDiffOn_retraction` is defined, and extends the
primitive to `N`.

## Main results

* `TauCeti.SmoothEmbedding.exists_mextDeriv_eq_and_mpullback_eq`: a primitive of `θ` near the
  image of `f` whose pullback along `f` is `β`.
* `TauCeti.SmoothEmbedding.exists_smoothForm_relative_primitive_sub`: the primitive of `η₁ - η₀`
  on a tube around `f(Q)`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
* [A. Cannas da Silva, *Lectures on Symplectic Geometry*][CannasdaSilva2001]
-/

public section

open Bundle Manifold Set
open scoped ContDiff Manifold

namespace TauCeti

section Restriction

variable {V G N : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace G]
  {J : ModelWithCorners ℝ V G} [TopologicalSpace N] [ChartedSpace G N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- Every form on an open subset `U` is the restriction of a form on the whole manifold: extend
it by zero. -/
theorem exists_mpullback_subtype_val_eq {U : TopologicalSpace.Opens N} (ξ : RoughForm J U F k) :
    ∃ γ : RoughForm J N F k, mpullback J J (Subtype.val : U → N) γ = ξ := by
  classical
  refine ⟨fun y ↦ if hy : y ∈ U then ξ ⟨y, hy⟩ else 0, funext fun x ↦ ?_⟩
  rw [mpullback_subtype_val_apply]
  exact dite_eq_left_of_eq_true (eq_true x.property)

/-- At a point of an open subset `U`, a form is `C^n` exactly when its restriction to `U` is. -/
theorem contMDiffAt_mpullback_subtype_val_iff [IsManifold J 1 N] {U : TopologicalSpace.Opens N}
    {n : WithTop ℕ∞} (γ : RoughForm J N F k) (x : U) :
    ContMDiffAt J (J.prod 𝓘(ℝ, V [⋀^Fin k]→L[ℝ] F)) n
        (fun y ↦ TotalSpace.mk' (V [⋀^Fin k]→L[ℝ] F) y
          (mpullback J J (Subtype.val : U → N) γ y)) x ↔
      ContMDiffAt J (J.prod 𝓘(ℝ, V [⋀^Fin k]→L[ℝ] F)) n
        (fun y ↦ TotalSpace.mk' (V [⋀^Fin k]→L[ℝ] F) y (γ y)) (x : N) :=
  (isLocalDiffeomorph_subtype_val (n := ω) x).contMDiffAt_mpullback_form_iff (by simp)

/-- At a point of an open subset `U` where a form is `C¹`, its restriction to `U` has the same
exterior derivative. -/
theorem mextDeriv_mpullback_subtype_val_apply [IsManifold J 2 N] {U : TopologicalSpace.Opens N}
    {γ : RoughForm J N F k} {x : U}
    (hγ : ContMDiffAt J (J.prod 𝓘(ℝ, V [⋀^Fin k]→L[ℝ] F)) 1
      (fun y ↦ TotalSpace.mk' (V [⋀^Fin k]→L[ℝ] F) y (γ y)) (x : N)) :
    mextDeriv (mpullback J J (Subtype.val : U → N) γ) x = mextDeriv γ x :=
  (mpullback_mextDeriv_at (contMDiff_subtypeVal x) hγ).symm.trans
    (mpullback_subtype_val_apply _ x)

end Restriction

section Pullback

variable {E H M V G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace G] {J : ModelWithCorners ℝ V G}
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- Let `β` be a `k`-form on `M` with `dβ = f^* θ`, and let `ψ` be a `k`-form on `N` with
`f^* ψ = β`. Then the form `θ - dψ` pulls back to zero along `f`. -/
theorem SmoothForm.mpullback_sub_mextDerivₗ_eq_zero {f : M → N} (hf : ContMDiff I J ∞ f)
    {θ : SmoothForm J N F (k + 1)} {β : SmoothForm I M F k}
    (hβ : mextDerivₗ I k β = SmoothForm.mpullback f hf θ) {ψ : SmoothForm J N F k}
    (hψ : SmoothForm.mpullback f hf ψ = β) :
    SmoothForm.mpullback f hf (θ - mextDerivₗ J k ψ) = 0 := by
  rw [map_sub, ← SmoothForm.mextDerivₗ_mpullback, hψ, hβ, sub_self]

end Pullback

namespace SmoothEmbedding

variable {E V H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N] [SecondCountableTopology N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Primitives with prescribed pullback, given a smooth retraction.** Let `f : M → N` be a
smooth embedding with a smooth left inverse `ρ : N → M`, `θ` a closed smooth `(k + 1)`-form on `N`
and `β` a smooth `k`-form on `M` with `dβ = f^* θ`. Then on some open neighbourhood `W` of the
image of `f`, `θ` has a smooth primitive `ξ` whose pullback along `f` is `β`. -/
theorem exists_mextDerivₗ_eq_and_mpullback_eq_of_leftInverse (f : SmoothEmbedding I J ∞ M N)
    {ρ : N → M} (hρ : ContMDiff J I ∞ ρ) (hρf : ρ ∘ f = _root_.id) {k : ℕ}
    {θ : SmoothForm J N F (k + 1)} (hθ : θ.IsClosed) {β : SmoothForm I M F k}
    (hβ : mextDerivₗ I k β = SmoothForm.mpullback f f.contMDiff θ) :
    ∃ W : TopologicalSpace.Opens N, ∃ hfW : ∀ x, f x ∈ W, ∃ ξ : SmoothForm J W F k,
      mextDerivₗ J k ξ = SmoothForm.mpullback Subtype.val contMDiff_subtypeVal θ ∧
      SmoothForm.mpullback (f.codRestrict W hfW) (f.codRestrict W hfW).contMDiff ξ = β := by
  -- The closed form `η = θ - d(ρ^* β)` pulls back to zero along `f`.
  let βN := SmoothForm.mpullback ρ hρ β
  let η := θ - mextDerivₗ J k βN
  have hdη : mextDeriv η.val = 0 :=
    (SmoothForm.isClosed_def η).1 (hθ.sub (SmoothForm.isClosed_mextDerivₗ βN))
  have hfβN : SmoothForm.mpullback f f.contMDiff βN = β := by
    refine Subtype.ext ?_
    rw [SmoothForm.mpullback_mpullback, SmoothForm.coe_mpullback, hρf, mpullback_id]
  have hfη : mpullback (F := F) I J f η.val = 0 := by
    rw [← SmoothForm.coe_mpullback _ f.contMDiff,
      SmoothForm.mpullback_sub_mextDerivₗ_eq_zero f.contMDiff hβ hfβN, ZeroMemClass.coe_zero]
  -- The relative Poincaré lemma gives a primitive `μ` of `η` on `W`, vanishing along `f`.
  obtain ⟨W, -, hfW, hprim⟩ := f.exists_isSmoothForm_relative_primitive (F := F) isOpen_univ
    (subset_univ _)
  obtain ⟨μ, hμ, hdμ, hμ0, -⟩ := hprim (le_top : (1 : ℕ∞) ≤ ⊤) η.isSmoothForm hdη hfη
  have hval : ContMDiff J J ∞ (Subtype.val : W → N) := contMDiff_subtypeVal
  have hf' : ∀ x, f x ∈ W := fun x ↦ hfW (mem_range_self x)
  let μS : SmoothForm J W F k := ⟨μ, hμ.mem_smoothBundleForms⟩
  -- `μS` is `μ` bundled with its smoothness; its value is `μ` by the definition just above.
  have hμS : μS.val = μ := rfl
  -- The primitive is `ρ^* β + μ`.
  refine ⟨W, hf', SmoothForm.mpullback Subtype.val hval βN + μS, Subtype.ext ?_, ?_⟩
  · rw [map_add, SmoothForm.mextDerivₗ_mpullback, Submodule.coe_add, mextDerivₗ_apply,
      SmoothForm.coe_mpullback, hμS, hdμ, ← mpullback_add, SmoothForm.coe_mpullback]
    congr 1
    exact congrArg Subtype.val (add_sub_cancel (mextDerivₗ J k βN) θ)
  · rw [map_add, SmoothForm.mpullback_mpullback]
    simp only [f.val_comp_codRestrict W hf']
    rw [hfβN, add_eq_left]
    refine Subtype.ext (funext fun x ↦ ?_)
    ext v
    rw [SmoothForm.coe_mpullback, hμS, mpullback_apply,
      show f.codRestrict W hf' x = ⟨f x, hf' x⟩ from Subtype.ext (f.val_codRestrict_apply ..), hμ0]
    simp

/-- **Primitives with prescribed pullback near an embedded submanifold.** Let `f : M → N` be a
smooth embedding, `θ` a closed smooth `(k + 1)`-form on `N` and `β` a smooth `k`-form on `M` with
`dβ = f^* θ`. Then there are an open neighbourhood `U` of the image of `f` and a `k`-form `γ` on
`N`, smooth at every point of `U`, with `dγ = θ` on `U` and `f^* γ = β`. -/
theorem exists_mextDeriv_eq_and_mpullback_eq (f : SmoothEmbedding I J ∞ M N) {k : ℕ}
    {θ : SmoothForm J N F (k + 1)} (hθ : θ.IsClosed) {β : SmoothForm I M F k}
    (hβ : mextDerivₗ I k β = SmoothForm.mpullback f f.contMDiff θ) :
    ∃ U : Set N, IsOpen U ∧ range f ⊆ U ∧ ∃ γ : RoughForm J N F k,
      (∀ x ∈ U, ContMDiffAt J (J.prod 𝓘(ℝ, V [⋀^Fin k]→L[ℝ] F)) ∞
        (fun y ↦ TotalSpace.mk' (V [⋀^Fin k]→L[ℝ] F) y (γ y)) x) ∧
      (∀ x ∈ U, mextDeriv γ x = θ.val x) ∧ mpullback I J f γ = β.val := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨∅, isOpen_empty, by simp [range_eq_empty], 0, by simp, by simp,
      funext fun x ↦ isEmptyElim x⟩
  obtain ⟨W, hW, hfW, -, r, hr, hrf⟩ := f.exists_contMDiffOn_retraction isOpen_univ (subset_univ _)
  -- On the open submanifold `T = W`, the map `r` is a smooth retraction.
  let T : TopologicalSpace.Opens N := ⟨W, hW⟩
  have hval : ContMDiff J J ∞ (Subtype.val : T → N) := contMDiff_subtypeVal
  have hρ : ContMDiff J I ∞ (fun y : T ↦ r y) := fun y ↦
    ((hr _ y.property).contMDiffAt (hW.mem_nhds y.property)).comp y hval.contMDiffAt
  have hfT : ∀ x, f x ∈ T := fun x ↦ hfW (mem_range_self x)
  let j := f.codRestrict T hfT
  have hvj : Subtype.val ∘ j = f := f.val_comp_codRestrict T hfT
  obtain ⟨W', hjW', ξ, hdξ, hjξ⟩ := j.exists_mextDerivₗ_eq_and_mpullback_eq_of_leftInverse hρ
    (funext fun x ↦ (congrArg r (f.val_codRestrict_apply T hfT x)).trans (hrf x))
    (hθ.mpullback _ hval) (by rw [hβ, SmoothForm.mpullback_mpullback]; simp only [hvj])
  -- Extend `ξ` from `W'` to `T`, then to `N`; both extensions are smooth at the points of `W'`.
  obtain ⟨γ', hγ'⟩ := exists_mpullback_subtype_val_eq ξ.val
  obtain ⟨γ, hγ⟩ := exists_mpullback_subtype_val_eq γ'
  have hγs (w : W') :
      ContMDiffAt J (J.prod 𝓘(ℝ, V [⋀^Fin k]→L[ℝ] F)) ∞
        (fun y ↦ TotalSpace.mk' (V [⋀^Fin k]→L[ℝ] F) y (γ' y)) (w : T) ∧
      ContMDiffAt J (J.prod 𝓘(ℝ, V [⋀^Fin k]→L[ℝ] F)) ∞
        (fun y ↦ TotalSpace.mk' (V [⋀^Fin k]→L[ℝ] F) y (γ y)) ((w : T) : N) := by
    have h₁ := (contMDiffAt_mpullback_subtype_val_iff γ' w).1 (hγ' ▸ ξ.contMDiff w)
    exact ⟨h₁, (contMDiffAt_mpullback_subtype_val_iff γ (w : T)).1 (hγ ▸ h₁)⟩
  refine ⟨Subtype.val '' (W' : Set T), hW.isOpenMap_subtypeVal _ W'.isOpen,
    fun _ ⟨x, hx⟩ ↦ ⟨j x, hjW' x, hx ▸ congrFun hvj x⟩, γ,
    fun _ ⟨t, ht, h⟩ ↦ h ▸ (hγs ⟨t, ht⟩).2, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨hs₁, hs₂⟩ := hγs ⟨t, ht⟩
    have e := mextDeriv_mpullback_subtype_val_apply (U := W') (x := ⟨t, ht⟩) (hs₁.of_le (by simp))
    rw [hγ', ← mextDerivₗ_apply, hdξ, SmoothForm.coe_mpullback, mpullback_subtype_val_apply,
      SmoothForm.coe_mpullback, mpullback_subtype_val_apply] at e
    rw [← mextDeriv_mpullback_subtype_val_apply (hs₂.of_le (by simp)), hγ, ← e]
  · let j' := j.codRestrict W' hjW'
    have hval' : ContMDiff J J ∞ (Subtype.val : W' → T) := contMDiff_subtypeVal
    have hf' : f = (Subtype.val ∘ Subtype.val) ∘ j' := by
      rw [Function.comp_assoc, j.val_comp_codRestrict W' hjW', hvj]
    rw [hf', mpullback_comp (j'.contMDiff.mdifferentiable (by simp))
      ((hval.comp hval').mdifferentiable (by simp)), mpullback_comp
      (hval'.mdifferentiable (by simp)) (hval.mdifferentiable (by simp)), hγ, hγ',
      ← SmoothForm.coe_mpullback _ j'.contMDiff, hjξ]

end SmoothEmbedding

namespace SmoothEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M]
  {E' H' Q : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

open TopologicalSpace in
/-- **A relative primitive of a difference of closed forms on a tube.** Let `f : Q → M` be a
smooth embedding and let `η₀`, `η₁` be closed smooth `(k + 1)`-forms on `M` with
`f^* η₁ = f^* η₀`. For every open set `O ⊇ f(Q)` there are an open set `W` with
`f(Q) ⊆ W ⊆ O` and a smooth `k`-form `β` on `W` with `dβ = η₁|_W - η₀|_W`, such that `β`
vanishes at every point `f q`, and the chart expression of `β` at `f q` has zero derivative
whenever `η₁` and `η₀` agree at `f q`. -/
theorem exists_smoothForm_relative_primitive_sub (f : SmoothEmbedding J I ∞ Q M) {k : ℕ}
    {η₀ η₁ : SmoothForm I M F (k + 1)} (h₀ : η₀.IsClosed) (h₁ : η₁.IsClosed)
    (hf : SmoothForm.mpullback f f.contMDiff η₁ = SmoothForm.mpullback f f.contMDiff η₀)
    {O : Set M} (hO : IsOpen O) (hfO : range f ⊆ O) :
    ∃ (W : Opens M) (_ : (W : Set M) ⊆ O) (hfW : range f ⊆ W) (β : SmoothForm I W F k),
      mextDeriv β.val =
        (SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal η₁ -
          SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal η₀).val ∧
      (∀ q, β.val ⟨f q, hfW (mem_range_self q)⟩ = 0) ∧
      ∀ q, η₁.val (f q) = η₀.val (f q) →
        HasFDerivAt (RoughForm.inChartAt β.val ⟨f q, hfW (mem_range_self q)⟩)
          (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F)
          (extChartAt I (⟨f q, hfW (mem_range_self q)⟩ : W) ⟨f q, hfW (mem_range_self q)⟩) := by
  have hf0 : mpullback (F := F) J I f (η₁ - η₀).val = 0 := by
    have h := congrArg Subtype.val (sub_eq_zero.2 hf)
    rwa [← map_sub, SmoothForm.coe_mpullback] at h
  obtain ⟨W, hWO, hfW, hprim⟩ := f.exists_isSmoothForm_relative_primitive (F := F) hO hfO
  obtain ⟨β, hβ, hdβ, hβ0, hβ1⟩ := hprim (r := ⊤) le_top (η₁ - η₀).isSmoothForm
    ((SmoothForm.isClosed_def _).1 (h₁.sub h₀)) hf0
  refine ⟨W, hWO, hfW, ⟨β, hβ.mem_smoothBundleForms⟩, ?_, hβ0, fun q hq ↦ hβ1 q ?_⟩
  · rw [hdβ, ← map_sub]
    exact (SmoothForm.coe_mpullback _ _ _).symm
  · rw [AddSubgroupClass.coe_sub, Pi.sub_apply, hq, sub_self]

end SmoothEmbedding

end TauCeti

end
