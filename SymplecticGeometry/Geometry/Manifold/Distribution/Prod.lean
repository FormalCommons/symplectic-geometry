/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import TauCeti.Geometry.Manifold.Distribution
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod

/-!
# A distribution on the first factor of a product

A distribution `D` on `M` gives the distribution on `M × M'` whose space at `(x, y)` is the image
of `D x` under the derivative of `x' ↦ (x', y)`, that is, `D x × 0`. A local frame `X` of `D` on
`U` pushes forward to the local frame `(x, y) ↦ (X i x, 0)` of it on `U × M'`. So this
distribution is `C^n` of rank `k` when `D` is.

## Main results

* `TauCeti.IsDistributionFrameOn.map_mfderiv_prod_left`: the local frame `(X i ∘ Prod.fst, 0)`.
* `TauCeti.IsContMDiffDistribution.map_mfderiv_prod_left`: the distribution `D x × 0` on `M × M'`
  is `C^n` of rank `k` when `D` is.

## Implementation notes

The fields `(x, y) ↦ (X i x, 0)` are Tau Ceti's product fields
`TauCeti.Manifold.prodVectorField (X i) 0`, but Tau Ceti proves their smoothness only at a
point (`TauCeti.Manifold.contMDiffAt_prodVectorField`), while a frame on `U × M'` needs it on
that set. The proof here is that of `contMDiffAt_prodVectorField` on a set: the field is
`(X i ∘ Prod.fst, 0 ∘ Prod.snd)` read through Mathlib's `equivTangentBundleProd`. The frame is
written as the image of `X i` under the derivative of `x' ↦ (x', y)`, the form in which the
distribution is stated.
-/

public section

open Set Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 1 M']
  {n : ℕ∞ω} {k : ℕ} {ι : Type*}
  {D : Π x : M, Submodule 𝕜 (TangentSpace I x)} {X : ι → Π x : M, TangentSpace I x} {U : Set M}

variable (I') in
/-- A local frame `X` of a distribution `D` on `U ⊆ M` gives the local frame
`(x, y) ↦ (X i x, 0)` on `U × M'` of the distribution whose space at `(x, y)` is the image of
`D x` under the derivative of `x' ↦ (x', y)`. -/
theorem IsDistributionFrameOn.map_mfderiv_prod_left (hX : IsDistributionFrameOn I n D X U) :
    IsDistributionFrameOn (I.prod I') n
      (fun p : M × M' ↦ (D p.1).map (mfderiv I (I.prod I') (fun x ↦ (x, p.2)) p.1).toLinearMap)
      (fun i p ↦ mfderiv I (I.prod I') (fun x ↦ (x, p.2)) p.1 (X i p.1)) (U ×ˢ univ) where
  contMDiffOn i := by
    -- The section `p ↦ (X i p.1, 0_{p.2})`, read through `TM × TM' ≃ T (M × M')`.
    have h : CMDiff[U ×ˢ univ] n fun p : M × M' ↦
        (equivTangentBundleProd I M I' M').symm
          ((⟨p.1, X i p.1⟩ : TangentBundle I M),
            zeroSection E' (TangentSpace I' : M' → Type _) p.2) :=
      contMDiff_equivTangentBundleProd_symm.comp_contMDiffOn
        (((hX.contMDiffOn i).comp contMDiffOn_fst fun _ hp ↦ (mem_prod.1 hp).1).prodMk
          ((contMDiff_zeroSection 𝕜 (TangentSpace I' : M' → Type _)).comp
            contMDiff_snd).contMDiffOn)
    refine h.congr fun p _ ↦ ?_
    rw [mfderiv_prodMk_left_apply]
    -- Both sides are `⟨p, (X i p.1, 0)⟩`, once `equivTangentBundleProd` is unfolded.
    rfl
  linearIndependent hp := by
    rw [mfderiv_prod_left]
    exact (hX.linearIndependent hp.1).map' _
      (LinearMap.ker_eq_bot_of_injective LinearMap.inl_injective)
  span_eq hp := by
    rw [← hX.span_eq hp.1, Submodule.map_span, ← range_comp]
    rfl

/-- If `D` is a `C^n` distribution of rank `k` on `M`, then so is the distribution on `M × M'`
whose space at `(x, y)` is the image of `D x` under the derivative of `x' ↦ (x', y)`, that is,
`D x × 0`. -/
theorem IsContMDiffDistribution.map_mfderiv_prod_left (hD : IsContMDiffDistribution I n k D) :
    IsContMDiffDistribution (I.prod I') n k
      (fun p : M × M' ↦
        (D p.1).map (mfderiv I (I.prod I') (fun x ↦ (x, p.2)) p.1).toLinearMap) := by
  refine isContMDiffDistribution_iff.2 fun p ↦ ?_
  obtain ⟨U, hU, hpU, X, hX⟩ := isContMDiffDistribution_iff.1 hD p.1
  exact ⟨U ×ˢ univ, hU.prod isOpen_univ, ⟨hpU, mem_univ _⟩, _, hX.map_mfderiv_prod_left I'⟩

end TauCeti

end
