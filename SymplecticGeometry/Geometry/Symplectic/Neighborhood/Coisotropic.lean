/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Neighborhood.Basic
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Basic
import SymplecticGeometry.Topology.Sets.Opens.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Presymplectic
import SymplecticGeometry.LinearAlgebra.Symplectic.Subspace
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Diffeomorph

/-!
# The coisotropic neighbourhood theorem

Let `f₀ : Q₀ → M₀` and `f₁ : Q₁ → M₁` be coisotropic embeddings into symplectic manifolds
`(M₀, ω₀)` and `(M₁, ω₁)`, and let `φ : Q₀ ≃ Q₁` be a diffeomorphism with
`φ^* (f₁^* ω₁) = f₀^* ω₀`. Then `φ` extends to a symplectomorphism between open neighbourhoods of
the images (Gotay's theorem). Neither compactness of `Q₀` nor closedness of the images is needed.

## Proof

The comparison theorem `TauCeti.SmoothEmbedding.exists_symplectomorphism_opens_of_mpullback_eq`
applies to `f₀` and `f₁ ∘ φ` with `L = 0`: for a coisotropic subspace `W`, the complement `W^ω`
lies in `W`, so `ω` vanishes on it and `0` preserves it. The kernel of `f₀^* ω₀` has constant
rank, the codimension of `Q₀` (Tau Ceti's
`TauCeti.SmoothTwoForm.IsNondegenerate.IsCoisotropicMap.finrank_ker_bilinFormAt_mpullback_add`),
and the same holds for `f₁ ∘ φ`; since both embeddings pull back the same form, the ambient
dimensions agree as soon as `Q₀` is nonempty. When `Q₀` is empty, empty open sets will do.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.IsCoisotropicMap.exists_symplectomorphism_opens`: the
  coisotropic neighbourhood theorem.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Exercise 3.4.18 and the remarks on non-compact submanifolds on p. 124.
* [K. Cieliebak, *Symplectic Geometry*, lecture notes][Cieliebak2010], Theorem 6.10 and
  Corollary 6.14.
* [Y.-G. Oh and J.-S. Park, *Deformations of coisotropic submanifolds and strong homotopy Lie
  algebroids*][OhPark2005], §3.
-/

public section

open Bundle Manifold Module TopologicalSpace
open scoped ContDiff Manifold Bundle

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {EQ₀ EQ₁ E₀ E₁ HQ₀ HQ₁ H₀ H₁ Q₀ Q₁ M₀ M₁ : Type*}
  [NormedAddCommGroup EQ₀] [NormedSpace ℝ EQ₀] [FiniteDimensional ℝ EQ₀]
  [NormedAddCommGroup EQ₁] [NormedSpace ℝ EQ₁]
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace HQ₀] [TopologicalSpace HQ₁] [TopologicalSpace H₀] [TopologicalSpace H₁]
  {J₀ : ModelWithCorners ℝ EQ₀ HQ₀} {J₁ : ModelWithCorners ℝ EQ₁ HQ₁}
  {I₀ : ModelWithCorners ℝ E₀ H₀} {I₁ : ModelWithCorners ℝ E₁ H₁}
  [J₀.Boundaryless] [I₀.Boundaryless] [I₁.Boundaryless]
  [TopologicalSpace Q₀] [ChartedSpace HQ₀ Q₀] [IsManifold J₀ ∞ Q₀]
  [TopologicalSpace Q₁] [ChartedSpace HQ₁ Q₁] [IsManifold J₁ ∞ Q₁]
  [TopologicalSpace M₀] [ChartedSpace H₀ M₀] [IsManifold I₀ ∞ M₀] [T2Space M₀]
  [SecondCountableTopology M₀]
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁] [T2Space M₁]
  [SecondCountableTopology M₁]

/-- **The coisotropic neighbourhood theorem.** Let `f₀ : Q₀ → M₀` and `f₁ : Q₁ → M₁` be
coisotropic smooth embeddings into second countable Hausdorff symplectic manifolds `(M₀, ω₀)` and
`(M₁, ω₁)` without boundary, and let `φ : Q₀ ≃ Q₁` be a diffeomorphism with
`φ^* (f₁^* ω₁) = f₀^* ω₀`. Then there are open sets `U₀ ⊆ M₀` and `U₁ ⊆ M₁` and a diffeomorphism
`ψ : U₀ ≃ U₁` pulling the restriction of `ω₁` back to that of `ω₀`, such that `f₀ q ∈ U₀` and
`ψ (f₀ q) = f₁ (φ q)` for every `q`; as `φ` is onto, `U₁` contains the image of `f₁` too.
Neither compactness of `Q₀` nor closedness of the images is assumed, and the two submanifolds
may be modelled on different spaces `J₀` and `J₁`.

Milestone: *Coisotropic neighbourhood theorem*. -/
theorem IsCoisotropicMap.exists_symplectomorphism_opens {ω₀ : SmoothTwoForm I₀ M₀}
    {ω₁ : SmoothTwoForm I₁ M₁} (hω₀ : ω₀.IsSymplectic) (hω₁ : ω₁.IsSymplectic)
    {f₀ : SmoothEmbedding J₀ I₀ ∞ Q₀ M₀} {f₁ : SmoothEmbedding J₁ I₁ ∞ Q₁ M₁}
    (h₀ : hω₀.isNondegenerate.IsCoisotropicMap J₀ f₀)
    (h₁ : hω₁.isNondegenerate.IsCoisotropicMap J₁ f₁) (φ : Q₀ ≃ₘ⟮J₀, J₁⟯ Q₁)
    (hφ : SmoothForm.mpullback φ φ.contMDiff (SmoothForm.mpullback f₁ f₁.contMDiff ω₁) =
      SmoothForm.mpullback f₀ f₀.contMDiff ω₀) :
    ∃ (U₀ : Opens M₀) (U₁ : Opens M₁) (ψ : U₀ ≃ₘ⟮I₀, I₁⟯ U₁),
      (∀ q, ∃ h : f₀ q ∈ U₀, (ψ ⟨f₀ q, h⟩ : M₁) = f₁ (φ q)) ∧
      SmoothForm.mpullback ψ ψ.contMDiff
          (SmoothForm.mpullback (Subtype.val : U₁ → M₁) contMDiff_subtypeVal ω₁) =
        SmoothForm.mpullback (Subtype.val : U₀ → M₀) contMDiff_subtypeVal ω₀ := by
  rcases isEmpty_or_nonempty Q₀ with hQ | ⟨⟨q₀⟩⟩
  · -- Without points to work along, the empty open sets will do.
    exact ⟨⊥, ⊥, Diffeomorph.ofIsEmpty, fun q ↦ (hQ.false q).elim, Subsingleton.elim _ _⟩
  -- The comparison theorem applies to `f₀` and `g = f₁ ∘ φ`.
  set g := f₁.compDiffeomorphOfBoundaryless φ (by simp)
  have hg : ⇑g = f₁ ∘ φ := f₁.coe_compDiffeomorphOfBoundaryless φ (by simp)
  have hgc : hω₁.isNondegenerate.IsCoisotropicMap J₀ g := by
    rw [hg]
    exact (isCoisotropicMap_comp_diffeomorph_iff φ (by simp)).2 h₁
  have hσ : SmoothForm.mpullback g g.contMDiff ω₁ = SmoothForm.mpullback f₀ f₀.contMDiff ω₀ := by
    rw [← hφ, SmoothForm.mpullback_mpullback]
    simp only [hg]
  have hk₀ (q) := h₀.finrank_ker_bilinFormAt_mpullback_add f₀.contMDiff
    (f₀.isImmersion.mfderiv_injective (by simp) q)
  have hk₁ := hgc.finrank_ker_bilinFormAt_mpullback_add g.contMDiff
    (g.isImmersion.mfderiv_injective (by simp) q₀)
  rw [hσ] at hk₁
  -- On the complement of a coisotropic subspace, `ω` vanishes.
  have hW (q) : ∀ v ∈ (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
      (mfderiv J₀ I₀ f₀ q).range, ∀ w ∈ (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
        (mfderiv J₀ I₀ f₀ q).range, hω₀.isNondegenerate.symplecticFormAt (f₀ q) v w = 0 :=
    SymplecticForm.isIsotropic_iff.1 (isCoisotropicMap_iff.1 h₀ q).isIsotropic_orthogonal
  obtain ⟨U₀, U₁, ψ, hψ, hψω⟩ := SmoothEmbedding.exists_symplectomorphism_opens_of_mpullback_eq
    f₀ g hω₀ hω₁ hσ (k := finrank ℝ E₀ - finrank ℝ EQ₀) (fun q ↦ by have := hk₀ q; omega)
    (by have := hk₀ q₀; omega) (fun _ ↦ 0) (contMDiff_zeroSection ℝ _)
    (fun _ _ _ ↦ Submodule.zero_mem _)
    (fun q v hv w hw ↦ by simp [hW q v hv w hw])
  refine ⟨U₀, U₁, ψ, fun q ↦ ?_, hψω⟩
  obtain ⟨h, hf, -⟩ := hψ q
  exact ⟨h, hf.trans (f₁.compDiffeomorphOfBoundaryless_apply φ (by simp) q)⟩

end TauCeti.SmoothTwoForm.IsNondegenerate

end
