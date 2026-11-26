/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Neighborhood.Basic
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Basic
import SymplecticGeometry.Topology.Sets.Opens.Basic
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
public import TauCeti.Geometry.Symplectic.Lagrangian.Manifold
public import SymplecticGeometry.Geometry.Symplectic.Cotangent.Bundle.WeinsteinChart
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ZeroSection
import SymplecticGeometry.Geometry.Symplectic.Manifold.SymplecticMap
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Chern
import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Graph
import TauCeti.Topology.FiberBundle.Countable
import TauCeti.Topology.FiberBundle.Separation

/-!
# Neighbourhoods of Lagrangian submanifolds

Let `f : L → M` be a Lagrangian embedding into a symplectic manifold `(M, σ)`. Then a
neighbourhood of the zero section of the cotangent bundle `T^*L`, with its canonical symplectic
form `TauCeti.CotangentBundle.symplecticForm`, which is `-dλ` for the Liouville form `λ`, is
symplectomorphic to a neighbourhood of `f (L)` by a map `ψ` with `ψ (0_q) = f q`
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.exists_symplectomorphism_cotangent`).
Neither compactness of `L` nor closedness of its image is needed. Composed with the fibrewise
negation of `T^*L`, such a `ψ` becomes a diffeomorphism `ι` with `ι (0_q) = f q` that pulls `σ`
back to `-CotangentBundle.symplecticForm = dλ`, the form that the sources of the Dehn twist
(Seidel) take as canonical
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.exists_symplectomorphism_cotangent_neg`).

## Proof

The zero section of `T^*L` is a smooth embedding
(`SymplecticGeometry.Bundle.zeroSectionEmbedding`), and it is Lagrangian (Tau Ceti's
`TauCeti.CotangentBundle.isLagrangianMap_zeroSection`). Both embeddings pull their symplectic
forms back to `0`, and `T^*L` and `M` have the same dimension, twice that of `L`. The
symplectic complement of a Lagrangian tangent space is the tangent space itself, so the
comparison theorem `TauCeti.SmoothEmbedding.exists_symplectomorphism_opens_of_mpullback_eq` applies
to the zero section and `f`, with the zero map as the prescribed linear map.

The fibrewise negation `N` of `T^*L` is Tau Ceti's `TauCeti.CotangentBundle.fiberNeg`. It pulls
the canonical form back to its negative
(`TauCeti.CotangentBundle.mpullback_fiberNeg_symplecticForm`) and fixes the zero section
(`TauCeti.CotangentBundle.fiberNeg_apply`), so `ψ ∘ N` is the diffeomorphism for the form `dλ`.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.exists_symplectomorphism_cotangent`: the
  Lagrangian neighbourhood theorem.
* `TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.exists_symplectomorphism_cotangent_neg`:
  a diffeomorphism from an open set of `T^*L` onto an open set of `M` that pulls `σ` back to
  `-CotangentBundle.symplecticForm = dλ` and maps the zero covector at `q` to `f q`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 3.4.13, and the remarks on non-compact submanifolds on p. 124.
-/

public section

open Bundle Manifold Module TopologicalSpace
open scoped ContDiff Manifold Bundle

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {EL E HL H L M : Type*}
  [NormedAddCommGroup EL] [NormedSpace ℝ EL] [FiniteDimensional ℝ EL]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace HL] [TopologicalSpace H]
  {J : ModelWithCorners ℝ EL HL} {I : ModelWithCorners ℝ E H}
  [J.Boundaryless] [I.Boundaryless]
  [TopologicalSpace L] [ChartedSpace HL L] [IsManifold J ∞ L]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M]

/-- **The Lagrangian neighbourhood theorem.** Let `f : L → M` be a smooth Lagrangian embedding into
a second countable Hausdorff manifold without boundary with a symplectic form `σ`. Then there are
open sets `U` of the cotangent bundle `T^*L` and `V ⊆ M` and a diffeomorphism `ψ : U ≃ V` pulling
the restriction of `σ` back to that of the canonical symplectic form
`TauCeti.CotangentBundle.symplecticForm`, which is `-dλ`, such that for every `q`, the zero
covector at `q` lies in `U`, `ψ` maps it to `f q`, and `dψ` composed with the differential of the
zero section at `q` is `df` at `q`. Neither compactness of `L` nor closedness of `f (L)` is
assumed.

Milestone: *Lagrangian neighbourhood theorem*. -/
theorem IsLagrangianMap.exists_symplectomorphism_cotangent {σ : SmoothTwoForm I M}
    (hσ : σ.IsSymplectic) {f : SmoothEmbedding J I ∞ L M}
    (hf : hσ.isNondegenerate.IsLagrangianMap J f) :
    ∃ (U : Opens (CotangentBundle J L)) (V : Opens M)
      (ψ : U ≃ₘ⟮J.prod 𝓘(ℝ, EL →L[ℝ] ℝ), I⟯ V),
      (∀ q, ∃ h : zeroSection (EL →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) q ∈ U,
        (ψ ⟨_, h⟩ : M) = f q ∧
        ∀ v, mfderiv (J.prod 𝓘(ℝ, EL →L[ℝ] ℝ)) I ψ ⟨_, h⟩
          (mfderiv J (J.prod 𝓘(ℝ, EL →L[ℝ] ℝ))
            (zeroSection (EL →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ)) q v) =
            mfderiv J I f q v) ∧
      SmoothForm.mpullback ψ ψ.contMDiff
          (SmoothForm.mpullback (Subtype.val : V → M) contMDiff_subtypeVal σ) =
        SmoothForm.mpullback (Subtype.val : U → CotangentBundle J L) contMDiff_subtypeVal
          (CotangentBundle.symplecticForm J L) := by
  -- `L` embeds in `M`, so it is Hausdorff and second countable, and so is `T^*L`.
  have := f.isEmbedding.t2Space
  have := f.isEmbedding.isInducing.secondCountableTopology
  rcases isEmpty_or_nonempty L with hL | ⟨⟨q₀⟩⟩
  · exact ⟨⊥, ⊥, Diffeomorph.ofIsEmpty, fun q ↦ (hL.false q).elim, Subsingleton.elim _ _⟩
  have hcoe := SymplecticGeometry.Bundle.coe_zeroSectionEmbedding J (EL →L[ℝ] ℝ)
    (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ)
  generalize SymplecticGeometry.Bundle.zeroSectionEmbedding J (EL →L[ℝ] ℝ)
    (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) = f₀ at hcoe
  have hω₀ := CotangentBundle.isSymplectic_symplecticForm (I := J) (M := L)
  have hf₀ : hω₀.isNondegenerate.IsLagrangianMap J f₀ := by
    rw [hcoe]
    exact CotangentBundle.isLagrangianMap_zeroSection
  -- Both restricted forms vanish, so their kernels are the whole tangent spaces of `L`.
  have h₀ := (isIsotropicMap_iff_mpullback_eq_zero f₀.contMDiff).1 hf₀.isIsotropicMap
  have h₁ := (isIsotropicMap_iff_mpullback_eq_zero f.contMDiff).1 hf.isIsotropicMap
  have hk (q : L) : finrank ℝ (LinearMap.ker
      ((SmoothForm.mpullback f₀ f₀.contMDiff (CotangentBundle.symplecticForm J L)).bilinFormAt q))
      = finrank ℝ EL := by
    rw [(SmoothForm.bilinFormAt_eq_zero_iff _ q).2 (by simp [h₀]), LinearMap.ker_zero,
      finrank_top, finrank_tangentSpace]
  have hdim : finrank ℝ (EL × (EL →L[ℝ] ℝ)) = finrank ℝ E := by
    rw [finrank_prod, ContinuousLinearMap.dual_finrank_eq, ← two_mul]
    exact hf.two_mul_finrank (f.isImmersion.mfderiv_injective (by simp) q₀)
  -- With the zero map as the prescribed linear map: the symplectic complement of a Lagrangian
  -- tangent space is itself, on which the form vanishes.
  have hLω (q : L) : ∀ v ∈ (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
      (mfderiv J (J.prod 𝓘(ℝ, EL →L[ℝ] ℝ)) f₀ q).range,
      ∀ w ∈ (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
        (mfderiv J (J.prod 𝓘(ℝ, EL →L[ℝ] ℝ)) f₀ q).range,
      hσ.isNondegenerate.symplecticFormAt (f q) ((0 : TangentSpace _ (f₀ q) →L[ℝ]
        TangentSpace I (f q)) v) ((0 : TangentSpace _ (f₀ q) →L[ℝ] TangentSpace I (f q)) w) =
        hω₀.isNondegenerate.symplecticFormAt (f₀ q) v w := by
    intro v hv w hw
    have hq := isLagrangianMap_iff_forall.1 hf₀ q
    have hc := SymplecticForm.isCoisotropic_iff.1 hq.isCoisotropic
    simpa using (hq.symplecticForm_apply_eq_zero (hc v hv) (hc w hw)).symm
  have := Pullback.contMDiffVectorBundle (F := EL × (EL →L[ℝ] ℝ))
    (E := TangentSpace (J.prod 𝓘(ℝ, EL →L[ℝ] ℝ))) f₀.contMDiff
  have := Pullback.contMDiffVectorBundle (F := E) (E := TangentSpace I) f.contMDiff
  obtain ⟨U, V, ψ, hψ, hψσ⟩ := SmoothEmbedding.exists_symplectomorphism_opens_of_mpullback_eq f₀ f
    hω₀ hσ (h₁.trans h₀.symm) hk hdim (fun _ ↦ 0) (contMDiff_zeroSection ℝ _)
    (fun _ _ _ ↦ zero_mem _) hLω
  rw [hcoe] at hψ
  refine ⟨U, V, ψ, fun q ↦ ?_, hψσ⟩
  obtain ⟨h, hψq, hdψ, -⟩ := hψ q
  exact ⟨h, hψq, hdψ⟩

/-- **The Lagrangian neighbourhood theorem, for the form `dλ`.** Let `f : L → M` be a smooth
Lagrangian embedding into a second countable Hausdorff manifold without boundary with a symplectic
form `σ`. Then there are open sets `U` of the cotangent bundle `T^*L` and `V ⊆ M` and a
diffeomorphism `ι : U ≃ V` that is a Weinstein chart of `f` for `σ`
(`SymplecticGeometry.CotangentBundle.IsWeinsteinChart`): it is a symplectomorphism from the
restriction of `-TauCeti.CotangentBundle.symplecticForm`, which is `dλ` for the Liouville form
`λ`, to that of `σ`, and for every `q`, the zero covector at `q` lies in `U` and `ι` maps it to
`f q`. -/
theorem IsLagrangianMap.exists_symplectomorphism_cotangent_neg {σ : SmoothTwoForm I M}
    (hσ : σ.IsSymplectic) {f : SmoothEmbedding J I ∞ L M}
    (hf : hσ.isNondegenerate.IsLagrangianMap J f) :
    ∃ (U : Opens (CotangentBundle J L)) (V : Opens M)
      (ι : U ≃ₘ⟮J.prod 𝓘(ℝ, EL →L[ℝ] ℝ), I⟯ V),
      SymplecticGeometry.CotangentBundle.IsWeinsteinChart σ f ι := by
  obtain ⟨U, V, ψ, hψ0, hψσ⟩ := hf.exists_symplectomorphism_cotangent hσ
  -- The fibrewise negation `N` of `T^*L`, which fixes the zero section.
  let N := CotangentBundle.fiberNeg J L
  have hN0 (q : L) : N (zeroSection _ _ q) = zeroSection _ _ q := by
    simp [N, zeroSection]
  let U' : Opens (CotangentBundle J L) := ⟨N ⁻¹' U, U.isOpen.preimage N.continuous⟩
  let N' : U' ≃ₘ⟮J.prod 𝓘(ℝ, EL →L[ℝ] ℝ), J.prod 𝓘(ℝ, EL →L[ℝ] ℝ)⟯ U :=
    N.subtype fun _ ↦ Iff.rfl
  have hψ : SymplecticGeometry.CotangentBundle.AgreesOnZeroSection f ψ :=
    ⟨fun q ↦ (hψ0 q).imp fun _ h ↦ h.1⟩
  refine ⟨U', V, N'.trans ψ, hψ.subtype_trans (a := id) (fun _ ↦ Iff.rfl) hN0, ?_⟩
  exact ((isSymplectomorphism_iff_mpullback_eq.2
    (CotangentBundle.mpullback_fiberNeg_symplecticForm (I := J) (M := L))).subtype
    fun _ ↦ Iff.rfl).trans (isSymplectomorphism_iff_mpullback_eq.2 hψσ) (by simp)

end TauCeti.SmoothTwoForm.IsNondegenerate

end
