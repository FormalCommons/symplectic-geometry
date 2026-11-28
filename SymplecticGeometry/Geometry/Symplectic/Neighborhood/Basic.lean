/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Topology.VectorBundle.Pullback
import SymplecticGeometry.Geometry.Symplectic.Neighborhood.Extension
import SymplecticGeometry.Geometry.Symplectic.Neighborhood.Tubular
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Polar
import SymplecticGeometry.Geometry.Symplectic.Manifold.Opens
import TauCeti.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph
import SymplecticGeometry.Geometry.Manifold.IsManifold.SecondCountable
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Pullback

/-!
# Comparing neighbourhoods of a submanifold in two symplectic manifolds

Let `f₀ : Q → M₀` and `f₁ : Q → M₁` be smooth embeddings of one manifold into symplectic
manifolds `(M₀, ω₀)` and `(M₁, ω₁)` of the same dimension, with `f₁^* ω₁ = f₀^* ω₀` of constant
rank. Write `Wⱼ = d(fⱼ)_q(T_q Q)` and `Wⱼ^ω` for its symplectic complement in `T_{fⱼ q} Mⱼ`. Let
`L` be a smooth family of linear maps `L q : T_{f₀ q} M₀ → T_{f₁ q} M₁` that carry `W₀^ω` into
`W₁^ω` and preserve `ω` there.

`TauCeti.SmoothEmbedding.exists_symplectomorphism_opens_of_mpullback_eq` gives open
neighbourhoods `U₀` of `f₀ (Q)` and `U₁` of `f₁ (Q)` and a symplectomorphism `ψ : U₀ ≃ U₁` with
`ψ ∘ f₀ = f₁`, `dψ ∘ df₀ = df₁`, and `dψ v - L q v ∈ W₁` for `v ∈ W₀^ω`: on the reduced normal
spaces `W^ω / (W ∩ W^ω)`, `dψ` induces the same map as `L`. The symplectic, Lagrangian,
isotropic and coisotropic neighbourhood theorems of McDuff–Salamon, §3.4, are instances of it,
for suitable `L`.

## Proof

Tau Ceti's `TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible` gives almost complex
structures `J₀`, `J₁` compatible with `ω₀`, `ω₁`. It asks the manifold to be σ-compact, so `J₁`
is taken on an open neighbourhood `U` of `f₁ (Q)` in `M₁` only: `Q` embeds in the second
countable `M₀`, so its image has a second countable neighbourhood
(`IsLindelof.exists_opens_secondCountableTopology`), and `M₁` need not be second countable.
With them, `TauCeti.SmoothEmbedding.smoothExtendAlong`, for `f₀` and `f₁` with image restricted
to `U`, is a smooth family of linear symplectomorphisms `A q` with `A q ∘ df₀ = df₁` that agrees
with `L` modulo `W₁` on `W₀^ω` (`TauCeti.SmoothEmbedding.contMDiff_smoothExtendAlong`). Read
along `f₁` again (`Bundle.Pullback.contMDiffAt_hom_section_subtypeVal_iff`), this is
`TauCeti.SmoothEmbedding.exists_symplectomorphism_extension`. Then
`TauCeti.SmoothEmbedding.exists_symplectomorphism_opens_mfderiv_eq` gives `ψ` with derivative
`A q` at each `f₀ q`.

## Main results

* `TauCeti.SmoothEmbedding.exists_symplectomorphism_extension`: a smooth family of linear
  symplectomorphisms along the submanifold that extends the derivatives and agrees with `L` on
  the reduced normal spaces.
* `TauCeti.SmoothEmbedding.exists_symplectomorphism_opens_of_mpullback_eq`: the comparison
  theorem, with `M₀` second countable and `M₁` any Hausdorff manifold.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.4,
  proofs of Theorems 3.4.10 and 3.4.13.
* [K. Cieliebak, *Symplectic Geometry*, lecture notes][Cieliebak2010], Theorem 6.10.
-/

public section

open Bundle Manifold Module TopologicalSpace
open scoped ContDiff Manifold Bundle

namespace TauCeti.SmoothEmbedding

variable {EQ E₀ E₁ HQ H₀ H₁ Q M₀ M₁ : Type*}
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [FiniteDimensional ℝ EQ]
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace HQ] [TopologicalSpace H₀] [TopologicalSpace H₁]
  {J : ModelWithCorners ℝ EQ HQ} {I₀ : ModelWithCorners ℝ E₀ H₀}
  {I₁ : ModelWithCorners ℝ E₁ H₁}
  [J.Boundaryless] [I₀.Boundaryless] [I₁.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold J ∞ Q]
  [TopologicalSpace M₀] [ChartedSpace H₀ M₀] [IsManifold I₀ ∞ M₀] [T2Space M₀]
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁] [T2Space M₁]

omit [J.Boundaryless] [I₀.Boundaryless] [I₁.Boundaryless] in
/-- **A smooth symplectic extension along a submanifold.** Let `f₀ : Q → M₀` and `f₁ : Q → M₁`
be smooth embeddings into Hausdorff manifolds of the same dimension, `M₀` second countable, with
symplectic forms `ω₀` and `ω₁`, such that `f₁^* ω₁ = f₀^* ω₀` and the kernels of this form all
have dimension `k`. Let `L q : T_{f₀ q} M₀ →L[ℝ] T_{f₁ q} M₁` be a smooth section over `Q` of
the bundle of linear maps between the pull-backs `f₀ *ᵖ TM₀` and `f₁ *ᵖ TM₁` which maps the
symplectic complement of the tangent image of `f₀` at `q` into that of `f₁`, and preserves the
symplectic forms on it. Then there are linear symplectomorphisms
`A q : T_{f₀ q} M₀ ≃L[ℝ] T_{f₁ q} M₁`, forming a smooth section of the same bundle, with
`A q (df₀ v) = df₁ v`, and such that `A q v - L q v` lies in the tangent image of `f₁` for every
`v` in the symplectic complement of the tangent image of `f₀`. -/
theorem exists_symplectomorphism_extension [SecondCountableTopology M₀]
    (f₀ : SmoothEmbedding J I₀ ∞ Q M₀) (f₁ : SmoothEmbedding J I₁ ∞ Q M₁)
    {ω₀ : SmoothTwoForm I₀ M₀} {ω₁ : SmoothTwoForm I₁ M₁}
    (hω₀ : ω₀.IsSymplectic) (hω₁ : ω₁.IsSymplectic)
    (hσ : SmoothForm.mpullback f₁ f₁.contMDiff ω₁ = SmoothForm.mpullback f₀ f₀.contMDiff ω₀)
    {k : ℕ} (hk : ∀ q, finrank ℝ (LinearMap.ker
      ((SmoothForm.mpullback f₀ f₀.contMDiff ω₀).bilinFormAt q)) = k)
    (hdim : finrank ℝ E₀ = finrank ℝ E₁)
    (L : ∀ q, TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace I₁ (f₁ q))
    (hLs : ContMDiff J (J.prod 𝓘(ℝ, E₀ →L[ℝ] E₁)) ∞ (fun q ↦ TotalSpace.mk' (E₀ →L[ℝ] E₁)
      (E := fun q ↦ ((f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) q →L[ℝ]
        ((f₁ : Q → M₁) *ᵖ (TangentSpace I₁)) q) q (L q)))
    (hL : ∀ q, ∀ v ∈ (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
      (mfderiv J I₀ f₀ q).range,
        L q v ∈ (hω₁.isNondegenerate.symplecticFormAt (f₁ q)).orthogonal
          (mfderiv J I₁ f₁ q).range)
    (hLω : ∀ q, ∀ v ∈ (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
      (mfderiv J I₀ f₀ q).range, ∀ w ∈ (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
        (mfderiv J I₀ f₀ q).range,
        hω₁.isNondegenerate.symplecticFormAt (f₁ q) (L q v) (L q w) =
          hω₀.isNondegenerate.symplecticFormAt (f₀ q) v w) :
    ∃ A : ∀ q, TangentSpace I₀ (f₀ q) ≃L[ℝ] TangentSpace I₁ (f₁ q),
      ContMDiff J (J.prod 𝓘(ℝ, E₀ →L[ℝ] E₁)) ∞ (fun q ↦ TotalSpace.mk' (E₀ →L[ℝ] E₁)
        (E := fun q ↦ ((f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) q →L[ℝ]
          ((f₁ : Q → M₁) *ᵖ (TangentSpace I₁)) q) q
          (A q : TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace I₁ (f₁ q))) ∧
      (∀ q v, A q (mfderiv J I₀ f₀ q v) = mfderiv J I₁ f₁ q v) ∧
      (∀ q, (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).IsSymplectomorphism
        (hω₁.isNondegenerate.symplecticFormAt (f₁ q)) (A q).toLinearEquiv) ∧
      ∀ q, ∀ v ∈ (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
        (mfderiv J I₀ f₀ q).range, A q v - L q v ∈ (mfderiv J I₁ f₁ q).range := by
  have := Manifold.locallyCompact_of_finiteDimensional (M := M₀) I₀
  obtain ⟨Jc₀, hc₀⟩ := hω₀.isNondegenerate.exists_compatible
  -- `Q` embeds in `M₀`, so `f₁ (Q)` has a second countable open neighbourhood `U` in `M₁`, on
  -- which `ω₁` has a compatible almost complex structure.
  have : SecondCountableTopology Q := f₀.isEmbedding.secondCountableTopology
  have : SecondCountableTopology H₁ := I₁.secondCountableTopology
  obtain ⟨U, hfU, -, hU⟩ := (isLindelof_range f₁.contMDiff.continuous
    ).exists_opens_secondCountableTopology (H := H₁) isOpen_univ (Set.subset_univ _)
  have := Manifold.locallyCompact_of_finiteDimensional (M := U) I₁
  obtain ⟨Jc₁, hc₁⟩ := (hω₁.mpullback_subtype_val U).isNondegenerate.exists_compatible
  -- The data along `g`, which is `f₁` with image in `U`.
  let g := f₁.codRestrict U fun q ↦ hfU (Set.mem_range_self q)
  have hgd (q : Q) (v : TangentSpace J q) : mfderiv J I₁ g q v = mfderiv J I₁ f₁ q v := by
    rw [← TauCeti.Manifold.mfderiv_subtype_val_comp_apply, val_comp_codRestrict]
  have hform (q : Q) (v w : TangentSpace I₁ (f₁ q)) :
      hc₁.isNondegenerate.symplecticFormAt (g q) v w =
        hω₁.isNondegenerate.symplecticFormAt (f₁ q) v w :=
    (hω₁.isNondegenerate.symplecticFormAt_mpullback_subtypeVal_apply (g q) v w).trans
      (congrArg (fun y ↦ hω₁.isNondegenerate.symplecticFormAt y v w)
        (f₁.val_codRestrict_apply U _ q))
  have horth (q : Q) (v : TangentSpace I₁ (f₁ q)) :
      v ∈ (hc₁.isNondegenerate.symplecticFormAt (g q)).orthogonal (mfderiv J I₁ g q).range ↔
      v ∈ (hω₁.isNondegenerate.symplecticFormAt (f₁ q)).orthogonal (mfderiv J I₁ f₁ q).range := by
    refine ⟨fun h y ⟨u, hu⟩ ↦ ?_, fun h y ⟨u, hu⟩ ↦ ?_⟩
    · rw [← hu, ContinuousLinearMap.coe_coe, ← hgd]
      exact (hform q _ _).symm.trans (h _ ⟨u, rfl⟩)
    · rw [← hu, ContinuousLinearMap.coe_coe]
      refine (hform q _ _).trans ?_
      beta_reduce
      rw [hgd]
      exact h _ ⟨u, rfl⟩
  have hσU : SmoothForm.mpullback g g.contMDiff
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal ω₁) =
        SmoothForm.mpullback f₀ f₀.contMDiff ω₀ := by
    rw [SmoothForm.mpullback_mpullback]
    convert hσ
    exact f₁.val_comp_codRestrict U _
  let LU (q : Q) : TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace I₁ (g q) := L q
  have hLU : ∀ q, ∀ v ∈ (hc₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
      (mfderiv J I₀ f₀ q).range,
        LU q v ∈ (hc₁.isNondegenerate.symplecticFormAt (g q)).orthogonal
          (mfderiv J I₁ g q).range := fun q v hv ↦ (horth q _).2 (hL q v hv)
  have hLUω : ∀ q, ∀ v ∈ (hc₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
      (mfderiv J I₀ f₀ q).range, ∀ w ∈ (hc₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
        (mfderiv J I₀ f₀ q).range,
        hc₁.isNondegenerate.symplecticFormAt (g q) (LU q v) (LU q w) =
          hc₀.isNondegenerate.symplecticFormAt (f₀ q) v w := fun q v hv w hw ↦
    (hform q _ _).trans (hLω q v hv w hw)
  -- A family of maps is smooth as a section along `g` exactly when it is along `f₁`.
  have hsec (A : ∀ q, TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace I₁ (f₁ q)) (q : Q) :=
    Bundle.Pullback.contMDiffAt_hom_section_subtypeVal_iff (n := ∞) (IX := J) f₀ g f₁
      (f₁.val_codRestrict_apply U _) A (x₀ := q)
  -- The extension along `g`, read along `f₁`.
  refine ⟨fun q ↦ smoothExtendAlong hc₀ hc₁ hσU LU hLU hLUω hdim q, fun q ↦ (hsec _ q).1
    (contMDiff_smoothExtendAlong hc₀ hc₁ hσU LU hLU hLUω hdim hk (fun q ↦ (hsec L q).2 (hLs q)) q),
    fun q v ↦ (smoothExtendAlong_apply_mfderiv hc₀ hc₁ hσU LU hLU hLUω hdim q v).trans (hgd q v),
    fun q ↦ SymplecticForm.isSymplectomorphism_iff.2 fun v w ↦ (hform q _ _).symm.trans
      (SymplecticForm.isSymplectomorphism_iff.1
        (isSymplectomorphism_smoothExtendAlong hc₀ hc₁ hσU LU hLU hLUω hdim q) v w),
    fun q v hv ↦ ?_⟩
  obtain ⟨u, hu⟩ := smoothExtendAlong_sub_mem hc₀ hc₁ hσU LU hLU hLUω hdim q hv
  exact ⟨u, (hgd q u).symm.trans hu⟩

/-- **The comparison theorem for neighbourhoods of a submanifold.** Let `f₀ : Q → M₀` and
`f₁ : Q → M₁` be smooth embeddings into Hausdorff manifolds without boundary of the same
dimension, `M₀` second countable, with symplectic forms `ω₀` and `ω₁`, such that
`f₁^* ω₁ = f₀^* ω₀` and the kernels of this form all have dimension `k`. Let
`L q : T_{f₀ q} M₀ →L[ℝ] T_{f₁ q} M₁` be a smooth section over `Q` of the bundle of linear maps
between the pull-backs `f₀ *ᵖ TM₀` and `f₁ *ᵖ TM₁` which maps the symplectic complement of the
tangent image of `f₀` at `q` into that of `f₁`, and preserves the symplectic forms on it. Then
there are open sets `U₀ ⊆ M₀` and `U₁ ⊆ M₁` and a diffeomorphism `ψ : U₀ ≃ U₁` pulling the
restriction of `ω₁` back to that of `ω₀`, such that, for every `q`, `f₀ q ∈ U₀`,
`ψ (f₀ q) = f₁ q`, `dψ (df₀ v) = df₁ v`, and `dψ v - L q v` lies in the tangent image of `f₁` for
every `v` in the symplectic complement of the tangent image of `f₀`. Neither compactness of `Q`
nor closedness of the images is assumed. -/
theorem exists_symplectomorphism_opens_of_mpullback_eq [SecondCountableTopology M₀]
    (f₀ : SmoothEmbedding J I₀ ∞ Q M₀) (f₁ : SmoothEmbedding J I₁ ∞ Q M₁)
    {ω₀ : SmoothTwoForm I₀ M₀} {ω₁ : SmoothTwoForm I₁ M₁}
    (hω₀ : ω₀.IsSymplectic) (hω₁ : ω₁.IsSymplectic)
    (hσ : SmoothForm.mpullback f₁ f₁.contMDiff ω₁ = SmoothForm.mpullback f₀ f₀.contMDiff ω₀)
    {k : ℕ} (hk : ∀ q, finrank ℝ (LinearMap.ker
      ((SmoothForm.mpullback f₀ f₀.contMDiff ω₀).bilinFormAt q)) = k)
    (hdim : finrank ℝ E₀ = finrank ℝ E₁)
    (L : ∀ q, TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace I₁ (f₁ q))
    (hLs : ContMDiff J (J.prod 𝓘(ℝ, E₀ →L[ℝ] E₁)) ∞ (fun q ↦ TotalSpace.mk' (E₀ →L[ℝ] E₁)
      (E := fun q ↦ ((f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) q →L[ℝ]
        ((f₁ : Q → M₁) *ᵖ (TangentSpace I₁)) q) q (L q)))
    (hL : ∀ q, ∀ v ∈ (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
      (mfderiv J I₀ f₀ q).range,
        L q v ∈ (hω₁.isNondegenerate.symplecticFormAt (f₁ q)).orthogonal
          (mfderiv J I₁ f₁ q).range)
    (hLω : ∀ q, ∀ v ∈ (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
      (mfderiv J I₀ f₀ q).range, ∀ w ∈ (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
        (mfderiv J I₀ f₀ q).range,
        hω₁.isNondegenerate.symplecticFormAt (f₁ q) (L q v) (L q w) =
          hω₀.isNondegenerate.symplecticFormAt (f₀ q) v w) :
    ∃ (U₀ : Opens M₀) (U₁ : Opens M₁) (ψ : U₀ ≃ₘ⟮I₀, I₁⟯ U₁),
      (∀ q, ∃ h : f₀ q ∈ U₀, (ψ ⟨f₀ q, h⟩ : M₁) = f₁ q ∧
        (∀ v, mfderiv I₀ I₁ ψ ⟨f₀ q, h⟩ (mfderiv J I₀ f₀ q v) = mfderiv J I₁ f₁ q v) ∧
        ∀ v ∈ (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
          (mfderiv J I₀ f₀ q).range,
          ∃ u, mfderiv I₀ I₁ ψ ⟨f₀ q, h⟩ v = L q v + mfderiv J I₁ f₁ q u) ∧
      SmoothForm.mpullback ψ ψ.contMDiff
          (SmoothForm.mpullback (Subtype.val : U₁ → M₁) contMDiff_subtypeVal ω₁) =
        SmoothForm.mpullback (Subtype.val : U₀ → M₀) contMDiff_subtypeVal ω₀ := by
  obtain ⟨A, hA, hAf, hAω, hAL⟩ :=
    exists_symplectomorphism_extension f₀ f₁ hω₀ hω₁ hσ hk hdim L hLs hL hLω
  obtain ⟨U₀, U₁, ψ, hψ, hψω⟩ :=
    exists_symplectomorphism_opens_mfderiv_eq f₀ f₁ hω₀ hω₁ A hA hAf hAω
  refine ⟨U₀, U₁, ψ, fun q ↦ ?_, hψω⟩
  obtain ⟨h, hf, hd⟩ := hψ q
  -- `dψ` at `f₀ q` is `A q`; its tangent spaces are those of `M₀` and `M₁` at `f₀ q`, `f₁ q`.
  have hdv (v) : mfderiv I₀ I₁ ψ ⟨f₀ q, h⟩ v = A q v := ContinuousLinearMap.ext_iff.1 hd v
  refine ⟨h, hf, fun v ↦ (hdv _).trans (hAf q v), fun v hv ↦ ?_⟩
  obtain ⟨u, hu⟩ := hAL q v hv
  exact ⟨u, (hdv v).trans (eq_add_of_sub_eq' hu.symm)⟩

end TauCeti.SmoothEmbedding

end
