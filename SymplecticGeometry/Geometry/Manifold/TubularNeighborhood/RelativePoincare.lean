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
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Opens

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
([McDuffSalamon2017], Lemma 3.2.1 and Exercise 3.2.6; [CannasdaSilva2001Lectures], Theorem 7.4). The
proof applies the relative Poincaré lemma to `η₁ - η₀` and bundles the primitive as a smooth form
on the tube, as Tau Ceti's
`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_embedding_eventually_mpullback_eq` does inside its
proof.

**Prescribed pullback.** Let `f : Q → M` be a smooth embedding of boundaryless
finite-dimensional manifolds, with `M` Hausdorff and second countable, let `θ` be a closed smooth
`(k + 1)`-form on `M`, and let `β` be a smooth `k`-form on `Q` with `dβ = f^* θ`. Then on an open
neighbourhood of `f(Q)`, `θ` has a smooth primitive whose pullback along `f` is `β`.
For `β = 0` its conclusion `f^* γ = 0` is weaker than that of the relative Poincaré lemma, whose
primitive vanishes along the image as an ambient tensor and has a first-jet property there; the
theorem generalizes the pullback condition to an arbitrary `β`. The proof follows the converse
half of McDuff–Salamon's Proposition 3.5.31 ([McDuffSalamon2017]):

* `TauCeti.SmoothEmbedding.exists_mextDerivₗ_eq_and_mpullback_eq_of_leftInverse`: the theorem for
  an embedding with a smooth left inverse `ρ`. The closed forms `θ` and `d(ρ^* β)` both pull back
  to `dβ` along `f`, so the primitive of their difference from the first theorem gives a form `μ`
  vanishing along `f`, and `ρ^* β + μ` is the primitive sought.
The theorem itself applies the case of a left inverse on the open neighbourhood where the smooth
retraction of `TauCeti.SmoothEmbedding.exists_contMDiffOn_retraction` is defined, and extends the
primitive to `M` with the restriction lemmas `TauCeti.mpullback_subtype_val_surjective`,
`TauCeti.contMDiffAt_mpullback_subtype_val_iff` and `TauCeti.mpullback_subtype_val_mextDeriv`.

## Main results

* `TauCeti.SmoothEmbedding.exists_smoothForm_relative_primitive_sub`: the primitive of `η₁ - η₀`
  on a tube around `f(Q)`.
* `TauCeti.SmoothEmbedding.exists_mextDeriv_eq_and_mpullback_eq`: a primitive of `θ` near
  `f(Q)` whose pullback along `f` is `β`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
* [A. Cannas da Silva, *Lectures on Symplectic Geometry*][CannasdaSilva2001Lectures]
-/

public section

open Bundle Manifold Set
open scoped ContDiff Manifold

namespace TauCeti

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

/-- **Primitives with prescribed pullback, given a smooth retraction.** Let `f : Q → M` be a
smooth embedding with a smooth left inverse `ρ : M → Q`, `θ` a closed smooth `(k + 1)`-form on `M`
and `β` a smooth `k`-form on `Q` with `dβ = f^* θ`. Then on some open neighbourhood `W` of the
image of `f`, `θ` has a smooth primitive `ξ` whose pullback along `f` is `β`. -/
theorem exists_mextDerivₗ_eq_and_mpullback_eq_of_leftInverse (f : SmoothEmbedding J I ∞ Q M)
    {ρ : M → Q} (hρ : ContMDiff I J ∞ ρ) (hρf : ρ ∘ f = _root_.id) {k : ℕ}
    {θ : SmoothForm I M F (k + 1)} (hθ : θ.IsClosed) {β : SmoothForm J Q F k}
    (hβ : mextDerivₗ J k β = SmoothForm.mpullback f f.contMDiff θ) :
    ∃ W : TopologicalSpace.Opens M, ∃ hfW : ∀ x, f x ∈ W, ∃ ξ : SmoothForm I W F k,
      mextDerivₗ I k ξ = SmoothForm.mpullback Subtype.val contMDiff_subtypeVal θ ∧
      SmoothForm.mpullback (f.codRestrict W hfW) (f.codRestrict W hfW).contMDiff ξ = β := by
  let βM := SmoothForm.mpullback ρ hρ β
  have hfβM : SmoothForm.mpullback f f.contMDiff βM = β := by
    refine Subtype.ext ?_
    rw [SmoothForm.mpullback_mpullback, SmoothForm.coe_mpullback, hρf, mpullback_id]
  -- The closed forms `θ` and `d(ρ^* β)` have the same pullback `dβ` along `f`, so on a tube `W`
  -- their difference has a primitive `μ` vanishing along `f`.
  obtain ⟨W, -, hfW, μ, hdμ, hμ0, -⟩ := f.exists_smoothForm_relative_primitive_sub
    (SmoothForm.isClosed_mextDerivₗ βM) hθ
    (by rw [← SmoothForm.mextDerivₗ_mpullback, hfβM, hβ]) isOpen_univ (subset_univ _)
  have hval : ContMDiff I I ∞ (Subtype.val : W → M) := contMDiff_subtypeVal
  have hf' : ∀ x, f x ∈ W := fun x ↦ hfW (mem_range_self x)
  -- The primitive is `ρ^* β + μ`.
  refine ⟨W, hf', SmoothForm.mpullback Subtype.val hval βM + μ, ?_, ?_⟩
  · rw [map_add, SmoothForm.mextDerivₗ_mpullback,
      show mextDerivₗ I k μ = _ from Subtype.ext ((mextDerivₗ_apply ..).trans hdμ),
      add_sub_cancel]
  · rw [map_add, SmoothForm.mpullback_mpullback]
    simp only [f.val_comp_codRestrict W hf']
    rw [hfβM, add_eq_left]
    refine Subtype.ext (funext fun x ↦ ?_)
    rw [SmoothForm.coe_mpullback]
    refine mpullback_apply_eq_zero ?_
    rw [show f.codRestrict W hf' x = ⟨f x, hf' x⟩ from Subtype.ext (f.val_codRestrict_apply ..),
      hμ0]

/-- **Primitives with prescribed pullback near an embedded submanifold.** Let `f : Q → M` be a
smooth embedding, `θ` a closed smooth `(k + 1)`-form on `M` and `β` a smooth `k`-form on `Q` with
`dβ = f^* θ`. Then there are an open neighbourhood `U` of the image of `f` and a `k`-form `γ` on
`M`, smooth at every point of `U`, with `dγ = θ` on `U` and `f^* γ = β`. -/
theorem exists_mextDeriv_eq_and_mpullback_eq (f : SmoothEmbedding J I ∞ Q M) {k : ℕ}
    {θ : SmoothForm I M F (k + 1)} (hθ : θ.IsClosed) {β : SmoothForm J Q F k}
    (hβ : mextDerivₗ J k β = SmoothForm.mpullback f f.contMDiff θ) :
    ∃ U : Set M, IsOpen U ∧ range f ⊆ U ∧ ∃ γ : RoughForm I M F k,
      (∀ x ∈ U, ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) ∞
        (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (γ y)) x) ∧
      (∀ x ∈ U, mextDeriv γ x = θ.val x) ∧ mpullback J I f γ = β.val := by
  rcases isEmpty_or_nonempty Q with hM | hM
  · exact ⟨∅, isOpen_empty, by simp [range_eq_empty], 0, by simp, by simp,
      funext fun x ↦ isEmptyElim x⟩
  obtain ⟨W, hW, hfW, -, r, hr, hrf⟩ := f.exists_contMDiffOn_retraction isOpen_univ (subset_univ _)
  -- On the open submanifold `T = W`, the map `r` is a smooth retraction.
  let T : TopologicalSpace.Opens M := ⟨W, hW⟩
  have hval : ContMDiff I I ∞ (Subtype.val : T → M) := contMDiff_subtypeVal
  have hρ : ContMDiff I J ∞ (fun y : T ↦ r y) := fun y ↦
    ((hr _ y.property).contMDiffAt (hW.mem_nhds y.property)).comp y hval.contMDiffAt
  have hfT : ∀ x, f x ∈ T := fun x ↦ hfW (mem_range_self x)
  let j := f.codRestrict T hfT
  have hvj : Subtype.val ∘ j = f := f.val_comp_codRestrict T hfT
  obtain ⟨W', hjW', ξ, hdξ, hjξ⟩ := j.exists_mextDerivₗ_eq_and_mpullback_eq_of_leftInverse hρ
    (funext fun x ↦ (congrArg r (f.val_codRestrict_apply T hfT x)).trans (hrf x))
    (hθ.mpullback _ hval) (by rw [hβ, SmoothForm.mpullback_mpullback]; simp only [hvj])
  -- Extend `ξ` from `W'` to `T`, then to `M`; both extensions are smooth at the points of `W'`.
  obtain ⟨γ', hγ'⟩ := mpullback_subtype_val_surjective W' ξ.val
  obtain ⟨γ, hγ⟩ := mpullback_subtype_val_surjective T γ'
  have hγs (w : W') :
      ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) ∞
        (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (γ' y)) (w : T) ∧
      ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) ∞
        (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (γ y)) ((w : T) : M) := by
    have h₁ := (contMDiffAt_mpullback_subtype_val_iff γ' w).1 (hγ' ▸ ξ.contMDiff w)
    exact ⟨h₁, (contMDiffAt_mpullback_subtype_val_iff γ (w : T)).1 (hγ ▸ h₁)⟩
  refine ⟨Subtype.val '' (W' : Set T), hW.isOpenMap_subtypeVal _ W'.isOpen,
    fun _ ⟨x, hx⟩ ↦ ⟨j x, hjW' x, hx ▸ congrFun hvj x⟩, γ,
    fun _ ⟨t, ht, h⟩ ↦ h ▸ (hγs ⟨t, ht⟩).2, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    have e := congrFun (mpullback_subtype_val_mextDeriv (U := W') γ') ⟨t, ht⟩
    rw [hγ', ← mextDerivₗ_apply, hdξ, SmoothForm.coe_mpullback, mpullback_subtype_val_apply,
      SmoothForm.coe_mpullback, mpullback_subtype_val_apply, mpullback_subtype_val_apply] at e
    rw [← e, ← hγ, ← mpullback_subtype_val_mextDeriv, mpullback_subtype_val_apply]
  · let j' := j.codRestrict W' hjW'
    have hf' : f = (Subtype.val ∘ Subtype.val) ∘ j' := by
      rw [Function.comp_assoc, j.val_comp_codRestrict W' hjW', hvj]
    rw [hf', mpullback_comp (j'.contMDiff.mdifferentiable (by simp))
      (SymplecticGeometry.mdifferentiable_subtypeVal.comp
        SymplecticGeometry.mdifferentiable_subtypeVal),
      mpullback_comp SymplecticGeometry.mdifferentiable_subtypeVal
        SymplecticGeometry.mdifferentiable_subtypeVal, hγ, hγ',
      ← SmoothForm.coe_mpullback _ j'.contMDiff, hjξ]


end SmoothEmbedding

end TauCeti

end
