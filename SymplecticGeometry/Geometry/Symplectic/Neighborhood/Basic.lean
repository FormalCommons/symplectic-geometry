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
structures `J₀`, `J₁` compatible with `ω₀`, `ω₁`. With them,
`TauCeti.SmoothEmbedding.smoothExtendAlong` is a smooth family of linear symplectomorphisms
`A q` with `A q ∘ df₀ = df₁` that agrees with `L` modulo `W₁` on `W₀^ω`
(`TauCeti.SmoothEmbedding.contMDiff_smoothExtendAlong`). Then
`TauCeti.SmoothEmbedding.exists_symplectomorphism_opens_mfderiv_eq` gives `ψ` with derivative
`A q` at each `f₀ q`.

## Main results

* `TauCeti.SmoothEmbedding.exists_symplectomorphism_opens_of_mpullback_eq`: the comparison
  theorem.

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

/-- **The comparison theorem for neighbourhoods of a submanifold.** Let `f₀ : Q → M₀` and
`f₁ : Q → M₁` be smooth embeddings into second countable Hausdorff manifolds without boundary of
the same dimension, with symplectic forms `ω₀` and `ω₁`, such that `f₁^* ω₁ = f₀^* ω₀` and the
kernels of this form all have dimension `k`. Let `L q : T_{f₀ q} M₀ →L[ℝ] T_{f₁ q} M₁` be a
smooth section over `Q` of the bundle of linear maps between the pull-backs `f₀ *ᵖ TM₀` and
`f₁ *ᵖ TM₁` which maps the symplectic complement of the tangent image of `f₀` at `q` into that of
`f₁`, and preserves the symplectic forms on it. Then there are open sets `U₀ ⊆ M₀` and
`U₁ ⊆ M₁` and a diffeomorphism `ψ : U₀ ≃ U₁` pulling the restriction of `ω₁` back to that of
`ω₀`, such that, for every `q`, `f₀ q ∈ U₀`, `ψ (f₀ q) = f₁ q`, `dψ (df₀ v) = df₁ v`, and
`dψ v - L q v` lies in the tangent image of `f₁` for every `v` in the symplectic complement of the
tangent image of `f₀`. Neither compactness of `Q` nor closedness of the images is assumed. -/
theorem exists_symplectomorphism_opens_of_mpullback_eq [SecondCountableTopology M₀]
    [SecondCountableTopology M₁]
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
  -- Second countable manifolds on finite-dimensional models are σ-compact.
  have := Manifold.locallyCompact_of_finiteDimensional (M := M₀) I₀
  have := Manifold.locallyCompact_of_finiteDimensional (M := M₁) I₁
  obtain ⟨Jc₀, hc₀⟩ := hω₀.isNondegenerate.exists_compatible
  obtain ⟨Jc₁, hc₁⟩ := hω₁.isNondegenerate.exists_compatible
  let A := smoothExtendAlong hc₀ hc₁ hσ L hL hLω hdim
  obtain ⟨U₀, U₁, ψ, hψ, hψω⟩ := exists_symplectomorphism_opens_mfderiv_eq f₀ f₁ hω₀ hω₁ A
    (contMDiff_smoothExtendAlong hc₀ hc₁ hσ L hL hLω hdim hk hLs)
    (smoothExtendAlong_apply_mfderiv hc₀ hc₁ hσ L hL hLω hdim)
    (isSymplectomorphism_smoothExtendAlong hc₀ hc₁ hσ L hL hLω hdim)
  refine ⟨U₀, U₁, ψ, fun q ↦ ?_, hψω⟩
  obtain ⟨h, hf, hd⟩ := hψ q
  -- `dψ` at `f₀ q` is `A q`; its tangent spaces are those of `M₀` and `M₁` at `f₀ q`, `f₁ q`.
  have hdv (v) : mfderiv I₀ I₁ ψ ⟨f₀ q, h⟩ v = A q v := ContinuousLinearMap.ext_iff.1 hd v
  refine ⟨h, hf, fun v ↦ ?_, fun v hv ↦ ?_⟩
  · exact (hdv _).trans (smoothExtendAlong_apply_mfderiv hc₀ hc₁ hσ L hL hLω hdim q v)
  · obtain ⟨u, hu⟩ := smoothExtendAlong_sub_mem hc₀ hc₁ hσ L hL hLω hdim q hv
    exact ⟨u, (hdv v).trans (eq_add_of_sub_eq' hu.symm)⟩

end TauCeti.SmoothEmbedding

end
