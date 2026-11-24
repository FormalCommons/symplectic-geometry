/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Moser.Field
public import SymplecticGeometry.Geometry.Manifold.Flow.TimeDependent
public import TauCeti.Geometry.Manifold.Algebra.SMul
public import SymplecticGeometry.Geometry.Symplectic.Moser.Relative
import SymplecticGeometry.Geometry.Symplectic.Manifold.Flat

/-!
# The equivariant Moser flow

Let `σ` be a two-form and `β` a one-form on `N × M`, with slices `σ_t` and `β_t` on `M`, and let
`ρ : N × M → ℝ` be a cutoff. If a diffeomorphism `g` of `M` preserves every slice `σ_t` and `β_t`
and every function `ρ(t, ·)`, then the cut-off Moser field `X_t = ρ(t, ·) (σ_t♭)⁻¹(-β_t)` of
`SymplecticGeometry.moserField` is `g`-related to itself at every time: inverse flat maps are
natural under maps with invertible differential
(`TauCeti.SmoothTwoForm.mfderiv_flat_mpullback_inverse_apply`).

For `N = ℝ`, the time-dependent flow of a `C¹` Moser field then commutes with `g`, by the
naturality of time-dependent flows (`Diffeomorph.apply_timeDependentFlowOf`, which applies Tau
Ceti's `Diffeomorph.apply_flowOf` to the suspended field on `ℝ × M`). For a group acting on `M` by
diffeomorphisms that preserve the data, the Moser isotopy is therefore equivariant. This is the
step of the equivariant Moser argument in which invariant forms, an invariant primitive and an
invariant cutoff give an equivariant isotopy ([GuilleminSternberg1990], Theorem 22.1;
[McDuffSalamon2017], §3.2).

The same applies to Moser's argument along the local flow, which need not be complete
(`TauCeti.SmoothTwoForm.exists_partialDiffeomorph_mpullback_eq_of_mextDeriv_eq_sub`). Its partial
diffeomorphism is the time-one map of the Moser field of the path `σ₀ + c(t) (σ₁ - σ₀)` and the
one-forms `c'(t) β` with no cutoff
(`TauCeti.SmoothTwoForm.exists_partialDiffeomorph_eq_timeDependentFlowOf_moserField`). When the
action preserves `σ₀`, `σ₁` and `β`, it preserves these slices, so the time-one map commutes with
the action. Its source, the set of points whose trajectory reaches time one, is invariant, since
a diffeomorphism relating two fields maps the domain of one flow onto that of the other
(`Diffeomorph.mem_timeDependentFlowDomain_apply_iff`).

## Main results

* `SymplecticGeometry.mfderiv_moserField`: a diffeomorphism preserving the slices of `σ` and `β`
  and the cutoff carries the Moser field to itself.
* `SymplecticGeometry.timeDependentFlowOf_moserField_comp`: the time-dependent flow of the Moser
  field then commutes with the diffeomorphism.
* `SymplecticGeometry.timeDependentFlowOf_moserField_smul`: for a group acting by such
  diffeomorphisms, the time-dependent flow of the Moser field is equivariant.
* `TauCeti.SmoothTwoForm.exists_partialDiffeomorph_mpullback_eq_of_mextDeriv_eq_sub_of_smul`:
  Moser's argument along the local flow for invariant forms and an invariant primitive gives an
  equivariant partial diffeomorphism with invariant source.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.2.
* [V. Guillemin and S. Sternberg, *Symplectic Techniques in Physics*][GuilleminSternberg1990],
  Theorem 22.1.
-/

public section

noncomputable section

open TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Field

variable {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold J ∞ N]
  {σ : SmoothForm (J.prod I) (N × M) ℝ 2} {β : SmoothForm (J.prod I) (N × M) ℝ 1}
  {ρ : N × M → ℝ}

/-- **The Moser field of invariant data is invariant.** If a diffeomorphism `g` of `M` preserves
the slice `σ_t` of the two-form `σ`, the slice `β_t` of the one-form `β` and the cutoff
`ρ(t, ·)`, then its differential carries the cut-off Moser field `X_t` at `x` to `X_t` at
`g x`. -/
theorem mfderiv_moserField (g : M ≃ₘ⟮I, I⟯ M) {t : N}
    (hσ : SmoothForm.mpullback g g.contMDiff
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ) =
      SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ)
    (hβ : SmoothForm.mpullback g g.contMDiff
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β) =
      SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β)
    (hρ : ∀ x, ρ (t, g x) = ρ (t, x)) (x : M) :
    mfderiv I I g x (moserField σ β ρ t x) = moserField σ β ρ t (g x) := by
  set σt := SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ
  set βt := SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β
  -- The covector `-β_t` at `x` is the one at `g x` composed with the differential of `g`.
  have hc : -SmoothForm.degreeOneEquiv βt x =
      (-SmoothForm.degreeOneEquiv βt (g x)) ∘L mfderiv I I g x := by
    ext v
    conv_lhs => rw [← hβ]
    rw [neg_apply, ContinuousLinearMap.comp_apply, neg_apply,
      SmoothForm.degreeOneEquiv_mpullback_apply]
  have key : mfderiv I I g x ((SmoothTwoForm.flat σt x).inverse (-SmoothForm.degreeOneEquiv βt x)) =
      (SmoothTwoForm.flat σt (g x)).inverse (-SmoothForm.degreeOneEquiv βt (g x)) := by
    conv_lhs => rw [← hσ]
    rw [hc, SmoothTwoForm.mfderiv_flat_mpullback_inverse_apply g.contMDiff σt
      (g.isInvertible_mfderiv (by simp))]
  rw [moserField_def, moserField_def, map_smul, hρ]
  exact congrArg _ key

end Field

variable [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 2} {β : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1}
  {ρ : ℝ × M → ℝ}

/-- **The Moser flow of invariant data commutes with the symmetry.** If a diffeomorphism `g` of
`M` preserves every slice `σ_t` of the two-form `σ` and `β_t` of the one-form `β` on `ℝ × M`, and
every function `ρ(t, ·)`, and the cut-off Moser field is jointly `C¹`, then its time-dependent
flow from `s` to `t` commutes with `g`. -/
theorem timeDependentFlowOf_moserField_comp (g : M ≃ₘ⟮I, I⟯ M)
    (hσ : ∀ t, SmoothForm.mpullback g g.contMDiff
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ) =
      SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ)
    (hβ : ∀ t, SmoothForm.mpullback g g.contMDiff
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β) =
      SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β)
    (hρ : ∀ t x, ρ (t, g x) = ρ (t, x))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, moserField σ β ρ p.1 p.2⟩ : TangentBundle I M))) (s t : ℝ) :
    timeDependentFlowOf (moserField σ β ρ) s t ∘ g =
      g ∘ timeDependentFlowOf (moserField σ β ρ) s t :=
  funext fun x ↦ (g.apply_timeDependentFlowOf (by simp) hX
    (fun u y ↦ mfderiv_moserField g (hσ u) (hβ u) (hρ u) y) s t x).symm

/-- **The equivariant Moser isotopy.** Let a group `G` act on `M` by smooth maps preserving every
slice `σ_t` of the two-form `σ` and `β_t` of the one-form `β` on `ℝ × M`, and every function
`ρ(t, ·)`. If the cut-off Moser field is jointly `C¹`, then its time-dependent flow from `s` to
`t` is `G`-equivariant. -/
theorem timeDependentFlowOf_moserField_smul {G : Type*} [Group G] [MulAction G M]
    [ContMDiffConstSMul I ∞ G M]
    (hσ : ∀ (g : G) t, SmoothForm.mpullback (fun x : M ↦ g • x) (contMDiff_const_smul g)
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ) =
      SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ)
    (hβ : ∀ (g : G) t, SmoothForm.mpullback (fun x : M ↦ g • x) (contMDiff_const_smul g)
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β) =
      SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β)
    (hρ : ∀ (g : G) t x, ρ (t, g • x) = ρ (t, x))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, moserField σ β ρ p.1 p.2⟩ : TangentBundle I M)))
    (g : G) (s t : ℝ) (x : M) :
    timeDependentFlowOf (moserField σ β ρ) s t (g • x) =
      g • timeDependentFlowOf (moserField σ β ρ) s t x := by
  have h := congrFun (timeDependentFlowOf_moserField_comp (Diffeomorph.constSmul I ∞ g)
    (by simpa only [Diffeomorph.coe_constSmul] using hσ g)
    (by simpa only [Diffeomorph.coe_constSmul] using hβ g)
    (by simpa only [Diffeomorph.constSmul_apply] using hρ g) hX s t) x
  simpa only [Function.comp_apply, Diffeomorph.constSmul_apply] using h
end SymplecticGeometry

namespace TauCeti.SmoothTwoForm

open Set

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- **Moser's argument along the local flow, equivariantly.** Let a group `G` act on `M` by smooth
maps, let `σ₀` be closed, `β` a primitive of `σ₁ - σ₀`, and let every form
`σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, be nondegenerate. If `σ₀`, `σ₁` and `β` are invariant under
every `g : G`, then the partial diffeomorphism `Φ` of
`TauCeti.SmoothTwoForm.exists_partialDiffeomorph_mpullback_eq_of_mextDeriv_eq_sub` can be chosen
`G`-equivariant: besides fixing the zeros of `β`, with identity differential where `β` also has
zero first jet, and pulling `σ₁` back to `σ₀` on its source, it has a `G`-invariant source and
satisfies `Φ (g • x) = g • Φ x` for every `g` and `x`. -/
theorem exists_partialDiffeomorph_mpullback_eq_of_mextDeriv_eq_sub_of_smul
    {G : Type*} [Group G] [MulAction G M] [ContMDiffConstSMul I ∞ G M]
    {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed) {β : SmoothForm I M ℝ 1}
    (hβ : mextDeriv β.val = (σ₁ - σ₀).val)
    (hnd : ∀ x, ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt x).Nondegenerate)
    (hσ₀ : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x) (contMDiff_const_smul g) σ₀ = σ₀)
    (hσ₁ : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x) (contMDiff_const_smul g) σ₁ = σ₁)
    (hβG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x) (contMDiff_const_smul g) β = β) :
    ∃ Φ : PartialDiffeomorph I I M M ∞,
      (∀ x, β.val x = 0 → x ∈ Φ.source ∧ Φ x = x ∧
        (HasFDerivAt (RoughForm.inChartAt β.val x) (0 : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ)
          (extChartAt I x x) → mfderiv I I Φ x = ContinuousLinearMap.id ℝ (TangentSpace I x))) ∧
      (∀ x ∈ Φ.source, mpullback I I Φ σ₁.val x = σ₀.val x) ∧
      (∀ (g : G) x, g • x ∈ Φ.source ↔ x ∈ Φ.source) ∧
      ∀ (g : G) x, Φ (g • x) = g • Φ x := by
  obtain ⟨α, hα, hX, Φ, hsrc, hΦ, hfix, hpull⟩ :=
    exists_partialDiffeomorph_eq_timeDependentFlowOf_moserField h₀ hβ hnd
  set σ := SmoothForm.lineMapFamily σ₀ σ₁ Real.smoothTransition.contDiff
  -- The slices `σ₀ + c(t) (σ₁ - σ₀)` and `c'(t) β` are invariant, hence so is the Moser field.
  have hσG (g : G) (t : ℝ) : SmoothForm.mpullback (fun x : M ↦ g • x) (contMDiff_const_smul g)
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ) =
        SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ := by
    rw [SmoothForm.mpullback_prodMk_lineMapFamily, map_add, map_smul, map_sub, hσ₀, hσ₁]
  have hαG (g : G) (t : ℝ) : SmoothForm.mpullback (fun x : M ↦ g • x) (contMDiff_const_smul g)
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α) =
        SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α := by
    rw [hα, map_smul, hβG]
  have hρG (g : G) (t : ℝ) (x : M) : (1 : ℝ × M → ℝ) (t, g • x) = (1 : ℝ × M → ℝ) (t, x) := by
    rw [Pi.one_apply, Pi.one_apply]
  have hrel (g : G) (t : ℝ) (x : M) :
      mfderiv I I (Diffeomorph.constSmul I ∞ g) x (SymplecticGeometry.moserField σ α 1 t x) =
        SymplecticGeometry.moserField σ α 1 t (Diffeomorph.constSmul I ∞ g x) :=
    SymplecticGeometry.mfderiv_moserField (Diffeomorph.constSmul I ∞ g)
      (by simpa only [Diffeomorph.coe_constSmul] using hσG g t)
      (by simpa only [Diffeomorph.coe_constSmul] using hαG g t)
      (fun _ ↦ by rw [Pi.one_apply, Pi.one_apply]) x
  refine ⟨Φ, hfix, hpull, fun g x ↦ ?_, fun g x ↦ ?_⟩
  · have h := (Diffeomorph.constSmul I ∞ g).mem_timeDependentFlowDomain_apply_iff (by simp)
      (hrel g) (s := 0) (t := 1) (x := x)
    rwa [Diffeomorph.constSmul_apply, ← hsrc, ← hsrc] at h
  · rw [hΦ, hΦ]
    exact SymplecticGeometry.timeDependentFlowOf_moserField_smul hσG hαG hρG (hX.of_le (by simp))
      g 0 1 x

end TauCeti.SmoothTwoForm

end
