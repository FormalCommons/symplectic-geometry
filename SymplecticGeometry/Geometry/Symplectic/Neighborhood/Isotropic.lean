/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Neighborhood.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import TauCeti.Geometry.Symplectic.Lagrangian.Manifold
public import TauCeti.Geometry.Symplectic.LinearReduction

/-!
# The isotropic neighbourhood theorem

Let `f₀ : Q₀ → M₀` and `f₁ : Q₁ → M₁` be isotropic embeddings into symplectic manifolds
`(M₀, ω₀)` and `(M₁, ω₁)`, and write `Wⱼ` for the tangent image of `fⱼ`. Over each point, the
symplectic normal space of `fⱼ` is the reduced space `Wⱼ^ω ⧸ Wⱼ` of `Wⱼ^ω`, whose radical is
`Wⱼ` since `Wⱼ ⊆ Wⱼ^ω`; Tau Ceti's `SymplecticForm.reduction` is its symplectic form. A
diffeomorphism `φ : Q₀ ≃ Q₁` together with a symplectic isomorphism `Φ` of these normal spaces
over `φ` extends to a symplectomorphism `ψ` between open neighbourhoods of the images whose
derivative induces `Φ`.

No bundle structure on the quotients `Wⱼ^ω ⧸ Wⱼ` is built: `Φ` is given together with a smooth
family of linear maps `L q : T_{f₀ q} M₀ → T_{f₁ (φ q)} M₁` that induces it, in the sense that
`L` maps `W₀^ω` into `W₁^ω` and `Φ q [v] = [L q v]`. Smoothness of `Φ` is read through `L`;
smooth complements lift every smooth isomorphism of the quotient bundles to such an `L`.

## Main results

All in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `IsIsotropicMap.finrank_reducedSpace_orthogonal_add`: the symplectic normal space of an
  isotropic immersion has dimension `dim M - 2 dim Q`.
* `IsIsotropicMap.exists_symplectomorphism_opens_of_finrank_eq`: for ambient manifolds of the
  same dimension, a smooth `L` that carries `W₀^ω` into `W₁^ω` and preserves `ω` there agrees
  modulo `W₁` with the derivative of a symplectomorphism `ψ` extending `φ`.
* `IsIsotropicMap.exists_symplectomorphism_opens`: the isotropic neighbourhood theorem, with the
  isomorphism `Φ` of normal spaces that `dψ` induces. The ambient dimensions agree because of
  `Φ` and `dφ` when `Q₀` is nonempty, and empty open sets will do when it is empty.

Both follow from the comparison theorem
`TauCeti.SmoothEmbedding.exists_symplectomorphism_opens_of_mpullback_eq`, applied to `f₀` and
`f₁ ∘ φ`, whose restricted forms both vanish.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Exercise 3.4.18 and the remarks on non-compact submanifolds on p. 124.
* [K. Cieliebak, *Symplectic Geometry*, lecture notes][Cieliebak2010], Theorem 6.10 and
  Corollary 6.13.
-/

public section

open Bundle Manifold Module TopologicalSpace
open scoped ContDiff Manifold Bundle

namespace TauCeti.SmoothTwoForm.IsNondegenerate

section Dimension

variable {E H M EQ HQ Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
  {J : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {f : Q → M}

/-- At a point where the derivative of an isotropic map `f : Q → M` is injective, the symplectic
normal space `W^ω ⧸ W` of its tangent image `W` has dimension `dim M - 2 dim Q`. -/
theorem IsIsotropicMap.finrank_reducedSpace_orthogonal_add (h : hσ.IsIsotropicMap J f) {q : Q}
    (hq : Function.Injective (mfderiv J I f q)) :
    finrank ℝ ((hσ.symplecticFormAt (f q)).ReducedSpace
      ((hσ.symplecticFormAt (f q)).orthogonal (mfderiv J I f q).range)) + 2 * finrank ℝ EQ =
      finrank ℝ E := by
  have := (hσ.symplecticFormAt (f q)).finrank_reducedSpace_orthogonal_add (mfderiv J I f q).range
  rw [inf_eq_left.2 (SymplecticForm.isIsotropic_iff_le.1 (isIsotropicMap_iff_forall.1 h q)),
    LinearMap.finrank_range_of_inj hq, finrank_tangentSpace,
    finrank_tangentSpace] at this
  omega

end Dimension

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
  [TopologicalSpace Q₁] [ChartedSpace HQ₁ Q₁]
  [TopologicalSpace M₀] [ChartedSpace H₀ M₀] [IsManifold I₀ ∞ M₀] [T2Space M₀]
  [SecondCountableTopology M₀]
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁] [T2Space M₁]
  [SecondCountableTopology M₁]
  {ω₀ : SmoothTwoForm I₀ M₀} {ω₁ : SmoothTwoForm I₁ M₁}
  (hω₀ : ω₀.IsSymplectic) (hω₁ : ω₁.IsSymplectic)
  {f₀ : SmoothEmbedding J₀ I₀ ∞ Q₀ M₀} {f₁ : SmoothEmbedding J₁ I₁ ∞ Q₁ M₁}

/-- **Isotropic neighbourhoods with a prescribed normal map.** Let `f₀ : Q₀ → M₀` and
`f₁ : Q₁ → M₁` be isotropic smooth embeddings into second countable Hausdorff symplectic
manifolds `(M₀, ω₀)` and `(M₁, ω₁)` without boundary of the same dimension, let `φ : Q₀ ≃ Q₁` be
a diffeomorphism, and let `L q : T_{f₀ q} M₀ →L[ℝ] T_{f₁ (φ q)} M₁` be a smooth section over
`Q₀` of the bundle of linear maps between the pull-backs `f₀ *ᵖ TM₀` and `(f₁ ∘ φ) *ᵖ TM₁` that
maps the symplectic complement `W₀^ω` of the tangent image `W₀` of `f₀` at `q` into the
complement `W₁^ω` of the tangent image `W₁` of `f₁` at `φ q`, and preserves the symplectic forms
on it. Then there are open sets `U₀ ⊆ M₀` and `U₁ ⊆ M₁` and a diffeomorphism `ψ : U₀ ≃ U₁`
pulling the restriction of `ω₁` back to that of `ω₀`, such that, for every `q`, `f₀ q ∈ U₀`,
`ψ (f₀ q) = f₁ (φ q)`, and `dψ v - L q v ∈ W₁` for every `v ∈ W₀^ω`. The two submanifolds may
be modelled on different spaces `J₀` and `J₁`. -/
theorem IsIsotropicMap.exists_symplectomorphism_opens_of_finrank_eq
    (h₀ : hω₀.isNondegenerate.IsIsotropicMap J₀ f₀)
    (h₁ : hω₁.isNondegenerate.IsIsotropicMap J₁ f₁) (φ : Q₀ ≃ₘ⟮J₀, J₁⟯ Q₁)
    (hdim : finrank ℝ E₀ = finrank ℝ E₁)
    (L : ∀ q, TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace I₁ (f₁ (φ q)))
    (hLs : ContMDiff J₀ (J₀.prod 𝓘(ℝ, E₀ →L[ℝ] E₁)) ∞ (fun q ↦ TotalSpace.mk' (E₀ →L[ℝ] E₁)
      (E := fun q ↦ ((f₀ : Q₀ → M₀) *ᵖ (TangentSpace I₀)) q →L[ℝ]
        ((f₁.compDiffeomorphOfBoundaryless φ (by simp) : Q₀ → M₁) *ᵖ (TangentSpace I₁)) q) q (L q)))
    (hL : ∀ q, ∀ v ∈ (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
      (mfderiv J₀ I₀ f₀ q).range,
        L q v ∈ (hω₁.isNondegenerate.symplecticFormAt (f₁ (φ q))).orthogonal
          (mfderiv J₁ I₁ f₁ (φ q)).range)
    (hLω : ∀ q, ∀ v ∈ (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
      (mfderiv J₀ I₀ f₀ q).range, ∀ w ∈ (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
        (mfderiv J₀ I₀ f₀ q).range,
        hω₁.isNondegenerate.symplecticFormAt (f₁ (φ q)) (L q v) (L q w) =
          hω₀.isNondegenerate.symplecticFormAt (f₀ q) v w) :
    ∃ (U₀ : Opens M₀) (U₁ : Opens M₁) (ψ : U₀ ≃ₘ⟮I₀, I₁⟯ U₁),
      (∀ q, ∃ h : f₀ q ∈ U₀, (ψ ⟨f₀ q, h⟩ : M₁) = f₁ (φ q) ∧
        ∀ v ∈ (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
          (mfderiv J₀ I₀ f₀ q).range,
          ∃ u, mfderiv I₀ I₁ ψ ⟨f₀ q, h⟩ v = L q v + mfderiv J₁ I₁ f₁ (φ q) u) ∧
      SmoothForm.mpullback ψ ψ.contMDiff
          (SmoothForm.mpullback (Subtype.val : U₁ → M₁) contMDiff_subtypeVal ω₁) =
        SmoothForm.mpullback (Subtype.val : U₀ → M₀) contMDiff_subtypeVal ω₀ := by
  -- The comparison theorem applies to `f₀` and `g = f₁ ∘ φ`.
  set g := f₁.compDiffeomorphOfBoundaryless φ (by simp)
  have hg : ⇑g = f₁ ∘ φ := f₁.coe_compDiffeomorphOfBoundaryless φ (by simp)
  have hgq (q) : g q = f₁ (φ q) := f₁.compDiffeomorphOfBoundaryless_apply φ (by simp) q
  have hgi : hω₁.isNondegenerate.IsIsotropicMap J₀ g := by
    rw [hg]
    exact (isIsotropicMap_comp_diffeomorph_iff φ (by simp)).2 h₁
  have hz₀ := (isIsotropicMap_iff_mpullback_eq_zero f₀.contMDiff).1 h₀
  have hz₁ := (isIsotropicMap_iff_mpullback_eq_zero g.contMDiff).1 hgi
  -- The restricted form vanishes, so its kernel is the whole tangent space.
  have hk (q) : finrank ℝ (LinearMap.ker
      ((SmoothForm.mpullback f₀ f₀.contMDiff ω₀).bilinFormAt q)) = finrank ℝ EQ₀ := by
    rw [(SmoothForm.bilinFormAt_eq_zero_iff _ q).2 (by simp [hz₀]), LinearMap.ker_zero,
      finrank_top, finrank_tangentSpace]
  obtain ⟨U₀, U₁, ψ, hψ, hψω⟩ := SmoothEmbedding.exists_symplectomorphism_opens_of_mpullback_eq
    f₀ g hω₀ hω₁ (hz₁.trans hz₀.symm) (k := finrank ℝ EQ₀) hk hdim L
    hLs (fun q v hv ↦ by
      rw [f₁.range_mfderiv_compDiffeomorphOfBoundaryless φ (by simp) q, hgq]; exact hL q v hv)
    (fun q v hv w hw ↦ by rw [hgq]; exact hLω q v hv w hw)
  refine ⟨U₀, U₁, ψ, fun q ↦ ?_, hψω⟩
  obtain ⟨h, hf, -, hd⟩ := hψ q
  refine ⟨h, hf.trans (hgq q), fun v hv ↦ ?_⟩
  obtain ⟨u, hu⟩ := hd v hv
  obtain ⟨u', hu'⟩ : mfderiv J₀ I₁ g q u ∈ (mfderiv J₁ I₁ f₁ (φ q)).range :=
    f₁.range_mfderiv_compDiffeomorphOfBoundaryless φ (by simp) q ▸ ⟨u, rfl⟩
  exact ⟨u', hu.trans (congrArg (L q v + ·) hu'.symm)⟩

/-- **The isotropic neighbourhood theorem.** Let `f₀ : Q₀ → M₀` and `f₁ : Q₁ → M₁` be isotropic
smooth embeddings into second countable Hausdorff symplectic manifolds `(M₀, ω₀)` and `(M₁, ω₁)`
without boundary, and write `Wⱼ` for the tangent image of `fⱼ`. Let `φ : Q₀ ≃ Q₁` be a
diffeomorphism, covered by linear symplectomorphisms `Φ q` from the symplectic normal space
`W₀^ω ⧸ W₀` of `f₀` at `q` onto that of `f₁` at `φ q` (the reduced spaces of `W^ω`, with the
reduced forms). Let `Φ` be smooth in the sense that it is induced by a smooth section
`L q : T_{f₀ q} M₀ →L[ℝ] T_{f₁ (φ q)} M₁` over `Q₀` of the bundle of linear maps between the
pull-backs `f₀ *ᵖ TM₀` and `(f₁ ∘ φ) *ᵖ TM₁`: `L q` maps `W₀^ω` into `W₁^ω` and
`Φ q [v] = [L q v]`. Then there are open sets `U₀ ⊆ M₀` and `U₁ ⊆ M₁` and a diffeomorphism
`ψ : U₀ ≃ U₁` pulling the restriction of `ω₁` back to that of `ω₀`, such that, for every `q`,
`f₀ q ∈ U₀`, `ψ (f₀ q) = f₁ (φ q)`, and `dψ` maps `W₀^ω` into `W₁^ω` and induces `Φ q`:
`Φ q [v] = [dψ v]`. As `φ` is onto, `U₁` contains the image of `f₁` too. Neither compactness of
`Q₀` nor closedness of the images is assumed, and the ambient dimensions are not assumed equal:
`Φ` forces it when `Q₀` is nonempty. The two submanifolds may be modelled on different spaces
`J₀` and `J₁`.

Milestone: *Isotropic neighbourhood theorem*. -/
theorem IsIsotropicMap.exists_symplectomorphism_opens
    (h₀ : hω₀.isNondegenerate.IsIsotropicMap J₀ f₀)
    (h₁ : hω₁.isNondegenerate.IsIsotropicMap J₁ f₁) (φ : Q₀ ≃ₘ⟮J₀, J₁⟯ Q₁)
    (Φ : ∀ q, (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).ReducedSpace
        ((hω₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal (mfderiv J₀ I₀ f₀ q).range) ≃ₗ[ℝ]
      (hω₁.isNondegenerate.symplecticFormAt (f₁ (φ q))).ReducedSpace
        ((hω₁.isNondegenerate.symplecticFormAt (f₁ (φ q))).orthogonal
          (mfderiv J₁ I₁ f₁ (φ q)).range))
    (hΦ : ∀ q, SymplecticForm.IsSymplectomorphism
      ((hω₀.isNondegenerate.symplecticFormAt (f₀ q)).reduction _)
      ((hω₁.isNondegenerate.symplecticFormAt (f₁ (φ q))).reduction _) (Φ q))
    (L : ∀ q, TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace I₁ (f₁ (φ q)))
    (hLs : ContMDiff J₀ (J₀.prod 𝓘(ℝ, E₀ →L[ℝ] E₁)) ∞ (fun q ↦ TotalSpace.mk' (E₀ →L[ℝ] E₁)
      (E := fun q ↦ ((f₀ : Q₀ → M₀) *ᵖ (TangentSpace I₀)) q →L[ℝ]
        ((f₁.compDiffeomorphOfBoundaryless φ (by simp) : Q₀ → M₁) *ᵖ (TangentSpace I₁)) q) q (L q)))
    (hL : ∀ q, ∀ v ∈ (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
      (mfderiv J₀ I₀ f₀ q).range,
        L q v ∈ (hω₁.isNondegenerate.symplecticFormAt (f₁ (φ q))).orthogonal
          (mfderiv J₁ I₁ f₁ (φ q)).range)
    (hLΦ : ∀ q v (hv : v ∈ (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
      (mfderiv J₀ I₀ f₀ q).range),
        Φ q (Submodule.Quotient.mk ⟨v, hv⟩) = Submodule.Quotient.mk ⟨L q v, hL q v hv⟩) :
    ∃ (U₀ : Opens M₀) (U₁ : Opens M₁) (ψ : U₀ ≃ₘ⟮I₀, I₁⟯ U₁),
      (∀ q, ∃ h : f₀ q ∈ U₀, (ψ ⟨f₀ q, h⟩ : M₁) = f₁ (φ q) ∧
        ∀ v (hv : v ∈ (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
          (mfderiv J₀ I₀ f₀ q).range),
          ∃ hψv : mfderiv I₀ I₁ ψ ⟨f₀ q, h⟩ v ∈
              (hω₁.isNondegenerate.symplecticFormAt (f₁ (φ q))).orthogonal
                (mfderiv J₁ I₁ f₁ (φ q)).range,
            Φ q (Submodule.Quotient.mk ⟨v, hv⟩) =
              Submodule.Quotient.mk ⟨mfderiv I₀ I₁ ψ ⟨f₀ q, h⟩ v, hψv⟩) ∧
      SmoothForm.mpullback ψ ψ.contMDiff
          (SmoothForm.mpullback (Subtype.val : U₁ → M₁) contMDiff_subtypeVal ω₁) =
        SmoothForm.mpullback (Subtype.val : U₀ → M₀) contMDiff_subtypeVal ω₀ := by
  rcases isEmpty_or_nonempty Q₀ with hQ | ⟨⟨q₀⟩⟩
  · -- Without points to work along, the empty open sets will do.
    obtain ⟨ψ, hψ⟩ := SmoothTwoForm.exists_diffeomorph_bot_mpullback_eq ω₀ ω₁
    exact ⟨⊥, ⊥, ψ, fun q ↦ (hQ.false q).elim, hψ⟩
  -- `L` preserves `ω` on `W₀^ω`, since `Φ` preserves the reduced forms.
  have hLω (q) : ∀ v ∈ (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
      (mfderiv J₀ I₀ f₀ q).range, ∀ w ∈ (hω₀.isNondegenerate.symplecticFormAt (f₀ q)).orthogonal
        (mfderiv J₀ I₀ f₀ q).range,
        hω₁.isNondegenerate.symplecticFormAt (f₁ (φ q)) (L q v) (L q w) =
          hω₀.isNondegenerate.symplecticFormAt (f₀ q) v w := fun v hv w hw ↦ by
    have := (hΦ q).apply (Submodule.Quotient.mk ⟨v, hv⟩) (Submodule.Quotient.mk ⟨w, hw⟩)
    rwa [hLΦ, hLΦ, SymplecticForm.reduction_mk, SymplecticForm.reduction_mk] at this
  -- At a point of `Q₀`, the normal spaces `W^ω ⧸ W` have dimension `dim M - 2 dim Q`.
  have hdim : finrank ℝ E₀ = finrank ℝ E₁ := by
    have h₀' := h₀.finrank_reducedSpace_orthogonal_add
      (f₀.isImmersion.mfderiv_injective (by simp) q₀)
    have h₁' := h₁.finrank_reducedSpace_orthogonal_add
      (f₁.isImmersion.mfderiv_injective (by simp) (φ q₀))
    have := (Φ q₀).finrank_eq
    -- The diffeomorphism `φ` forces `Q₀` and `Q₁` to have models of equal dimension.
    have hQ := (φ.isLocalDiffeomorph q₀).finrank_eq (by simp)
    omega
  obtain ⟨U₀, U₁, ψ, hψ, hψω⟩ :=
    h₀.exists_symplectomorphism_opens_of_finrank_eq hω₀ hω₁ h₁ φ hdim L hLs hL hLω
  refine ⟨U₀, U₁, ψ, fun q ↦ ?_, hψω⟩
  obtain ⟨h, hf, hd⟩ := hψ q
  refine ⟨h, hf, fun v hv ↦ ?_⟩
  obtain ⟨u, hu⟩ := hd v hv
  -- `dψ v` differs from `L q v` by a vector of `W₁ ⊆ W₁^ω`, so both have the same class.
  have hW₁ : mfderiv J₁ I₁ f₁ (φ q) u ∈ (hω₁.isNondegenerate.symplecticFormAt (f₁ (φ q))).orthogonal
      (mfderiv J₁ I₁ f₁ (φ q)).range :=
    SymplecticForm.isIsotropic_iff_le.1 (isIsotropicMap_iff_forall.1 h₁ (φ q)) ⟨u, rfl⟩
  refine ⟨hu ▸ Submodule.add_mem _ (hL q v hv) hW₁, ?_⟩
  rw [hLΦ, SymplecticForm.ReducedSpace.mk_eq_mk_iff, SymplecticForm.orthogonal_orthogonal]
  exact ⟨-u, by simp [hu]⟩

end TauCeti.SmoothTwoForm.IsNondegenerate

end
