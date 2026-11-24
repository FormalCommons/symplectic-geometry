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
import SymplecticGeometry.Geometry.Manifold.GroupAction.Opens
import SymplecticGeometry.Geometry.Manifold.GroupAction.InvariantPrimitive
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Logic.Equiv.PartialEquiv
import SymplecticGeometry.Geometry.Symplectic.Manifold.Family
import TauCeti.Geometry.Symplectic.Manifold.Opens
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Basic
import SymplecticGeometry.Topology.Sets.Opens.Basic

/-!
# The equivariant Moser flow and the equivariant relative Moser theorem

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

For a compact group `G` acting smoothly, this gives the equivariant form of the relative Moser
theorem of `Moser/Relative.lean`
(`TauCeti.SmoothEmbedding.exists_equivariant_diffeomorph_opens_of_eq_along`). Its proof adapts
that of `TauCeti.SmoothEmbedding.exists_diffeomorph_opens_of_eq_along`, with two more steps
between the relative primitive and Moser's argument.

1. The relative Poincaré lemma gives a primitive `β` of `σ₁ - σ₀` on a tube `W` around `f(Q)`,
   vanishing with its first jet along `f(Q)`. Since `f(Q)` is invariant and `G` is compact,
   `f(Q)` lies in the invariant core `V` of `W` (`TopologicalSpace.Opens.invariantCore`), an
   open set on which `G` acts smoothly.
2. The average over the normalized Haar measure (`TauCeti.SmoothForm.measureAverage`) of the
   restriction of `β` to `V` is an invariant primitive of `σ₁ - σ₀` on `V`
   (`TauCeti.SmoothForm.mextDerivₗ_measureAverage_of_invariant`). As `f(Q)` is invariant, the
   average still vanishes with its first jet along `f(Q)`
   (`TauCeti.SmoothForm.measureAverage_eq_zero_of_forall_smul`,
   `TauCeti.SmoothForm.hasFDerivAt_inChartAt_measureAverage_of_forall_smul`).
3. Moser's argument along the local flow on `V`, done equivariantly as above, gives an
   equivariant partial diffeomorphism of `V` with invariant source and target, which is read in
   `M` as in `Moser/Relative.lean`.

Since the local flow needs no cutoff, no invariant cutoff is needed, and `Q` need not be compact.

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
* `TauCeti.SmoothEmbedding.exists_equivariant_diffeomorph_opens_of_eq_along`: the equivariant
  relative Moser theorem with prescribed first derivative.

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
      (hρG g t) x
  refine ⟨Φ, hfix, hpull, fun g x ↦ ?_, fun g x ↦ ?_⟩
  · have h := (Diffeomorph.constSmul I ∞ g).mem_timeDependentFlowDomain_apply_iff (by simp)
      (hrel g) (s := 0) (t := 1) (x := x)
    rwa [Diffeomorph.constSmul_apply, ← hsrc, ← hsrc] at h
  · rw [hΦ, hΦ]
    exact SymplecticGeometry.timeDependentFlowOf_moserField_smul hσG hαG hρG (hX.of_le (by simp))
      g 0 1 x

end TauCeti.SmoothTwoForm

namespace TauCeti.SmoothEmbedding

open Set TopologicalSpace MeasureTheory SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M]
  {E' H' Q : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q]
  {EG HG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  (IG : ModelWithCorners ℝ EG HG) [TopologicalSpace G] [ChartedSpace HG G] [IsManifold IG ∞ G]
  [Group G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MulAction G M]
  [ContMDiffSMul IG I ∞ G M]


omit [IsTopologicalGroup G] [T2Space G] in
/-- The first step of the equivariant relative Moser theorem: a tube `W` around `f(Q)` on which
the segment from `σ₀` to `σ₁` is nondegenerate, whose invariant core contains `f(Q)`, and a
primitive on that invariant core of the restriction of `σ₁ - σ₀`, vanishing with its first jet
along `f(Q)`. -/
private theorem exists_primitive_invariantCore_of_eq_along [ContinuousSMul G M]
    (f : SmoothEmbedding J I ∞ Q M) (hfG : ∀ (g : G) q, g • f q ∈ range f)
    {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed) (h₁ : σ₁.IsClosed)
    (hnd : ∀ q, (σ₀.bilinFormAt (f q)).Nondegenerate)
    (heq : ∀ q, σ₁.val (f q) = σ₀.val (f q)) :
    ∃ (W : Opens M) (_ : (W : Set M) ⊆
        {x | ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt x).Nondegenerate})
      (hfV : range f ⊆ W.invariantCore G) (β : SmoothForm I (W.invariantCore G) ℝ 1),
      mextDeriv β.val =
        (SmoothForm.mpullback (Subtype.val : W.invariantCore G → M) contMDiff_subtypeVal σ₁ -
          SmoothForm.mpullback (Subtype.val : W.invariantCore G → M) contMDiff_subtypeVal σ₀).val ∧
      (∀ q, β.val ⟨f q, hfV (mem_range_self q)⟩ = 0) ∧
      ∀ q, HasFDerivAt (RoughForm.inChartAt β.val ⟨f q, hfV (mem_range_self q)⟩)
        (0 : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ)
        (extChartAt I (⟨f q, hfV (mem_range_self q)⟩ : W.invariantCore G)
          ⟨f q, hfV (mem_range_self q)⟩) := by
  have hη (q : Q) : (σ₁ - σ₀).val (f q) = 0 := by
    rw [AddSubgroupClass.coe_sub, Pi.sub_apply, heq q, sub_self]
  -- Along `f(Q)`, every form of the segment from `σ₀` to `σ₁` is `σ₀`.
  have hfO : range f ⊆
      {x | ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt x).Nondegenerate} := by
    rintro _ ⟨q, rfl⟩ s -
    exact nondegenerate_bilinFormAt_add_smul_sub_of_eq (hη q) (hnd q) s
  have hf : SmoothForm.mpullback f f.contMDiff σ₁ = SmoothForm.mpullback f f.contMDiff σ₀ :=
    Subtype.ext (funext fun q ↦ by
      ext v
      rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback, mpullback_apply, mpullback_apply,
        heq q])
  -- A primitive of `σ₁ - σ₀` on a tube `W`, vanishing with its first jet along `f(Q)`.
  obtain ⟨W, hWO, hfW, βW, hdβW, hβW0, hβW1⟩ := f.exists_smoothForm_relative_primitive_sub h₀ h₁
    hf (isOpen_setOf_forall_mem_Icc_nondegenerate σ₀ σ₁) hfO
  -- Its restriction to the invariant core `V` of `W`, which still contains `f(Q)`.
  set V := W.invariantCore G
  have hVW : V ≤ W := Opens.invariantCore_le W
  have hfV : range f ⊆ V := Opens.subset_invariantCore (by
    rintro g _ ⟨q, rfl⟩
    exact hfW (hfG g q))
  refine ⟨W, hWO, hfV, SmoothForm.mpullback (Opens.inclusion hVW) (contMDiff_inclusion hVW) βW,
    ?_, fun q ↦ ?_, fun q ↦ ?_⟩
  · rw [SmoothForm.coe_mpullback, ← mpullback_inclusion_mextDeriv, hdβW,
      ← SmoothForm.coe_mpullback _ (contMDiff_inclusion hVW), map_sub,
      SmoothForm.mpullback_inclusion_mpullback_subtype_val,
      SmoothForm.mpullback_inclusion_mpullback_subtype_val]
  · rw [SmoothForm.coe_mpullback, mpullback_inclusion_apply]
    exact hβW0 q
  · have h := RoughForm.inChartAt_mpullback_inclusion_eventuallyEq hVW βW.val
      ⟨f q, hfV (mem_range_self q)⟩
    rw [I.range_eq_univ, nhdsWithin_univ] at h
    rw [SmoothForm.coe_mpullback]
    refine HasFDerivAt.congr_of_eventuallyEq ?_ h
    rw [← extChartAt_inclusion_self hVW]
    exact hβW1 q (heq q)

include IG in
/-- The equivariant relative Moser theorem before it is read in `M`: on the invariant core of a tube
around `f(Q)`, an equivariant partial diffeomorphism `Φ` with invariant source, whose source
contains `f(Q)`, which fixes `f(Q)` with identity differential there, and which pulls `σ₁` back
to `σ₀` at every point of its source. -/
private theorem exists_partialDiffeomorph_invariantCore_of_eq_along [ContinuousSMul G M]
    (f : SmoothEmbedding J I ∞ Q M) (hfG : ∀ (g : G) q, g • f q ∈ range f)
    {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed) (h₁ : σ₁.IsClosed)
    (hσ₀ : ∀ g : G, TauCeti.mpullback I I (g • ·) σ₀.val = σ₀.val)
    (hσ₁ : ∀ g : G, TauCeti.mpullback I I (g • ·) σ₁.val = σ₁.val)
    (hnd : ∀ q, (σ₀.bilinFormAt (f q)).Nondegenerate)
    (heq : ∀ q, σ₁.val (f q) = σ₀.val (f q)) :
    ∃ (W : Opens M) (Φ : PartialDiffeomorph I I (W.invariantCore G) (W.invariantCore G) ∞),
      (∀ q, ∃ h : f q ∈ W.invariantCore G, ⟨f q, h⟩ ∈ Φ.source ∧ Φ ⟨f q, h⟩ = ⟨f q, h⟩ ∧
        mfderiv I I Φ ⟨f q, h⟩ =
          ContinuousLinearMap.id ℝ (TangentSpace I (⟨f q, h⟩ : W.invariantCore G))) ∧
      (∀ x ∈ Φ.source, mpullback I I Φ
        (mpullback I I (Subtype.val : W.invariantCore G → M) σ₁.val) x = σ₀.val x) ∧
      (∀ (g : G) x, g • x ∈ Φ.source ↔ x ∈ Φ.source) ∧ ∀ (g : G) x, Φ (g • x) = g • Φ x := by
  have : ContMDiffConstSMul I ∞ G M := ContMDiffSMul.contMDiffConstSMul IG
  borelize G
  obtain ⟨W, hWO, hfV, β, hdβ, hβ0, hβ1⟩ :=
    exists_primitive_invariantCore_of_eq_along (G := G) f hfG h₀ h₁ hnd heq
  set τ₀ := SmoothForm.mpullback (Subtype.val : W.invariantCore G → M) contMDiff_subtypeVal σ₀
  set τ₁ := SmoothForm.mpullback (Subtype.val : W.invariantCore G → M) contMDiff_subtypeVal σ₁
  have hτ (σ : SmoothTwoForm I M) (hσ : ∀ g : G, TauCeti.mpullback I I (g • ·) σ.val = σ.val)
      (g : G) : SmoothForm.mpullback (fun x : W.invariantCore G ↦ g • x) (contMDiff_const_smul g)
        (SmoothForm.mpullback (Subtype.val : W.invariantCore G → M) contMDiff_subtypeVal σ) =
      SmoothForm.mpullback (Subtype.val : W.invariantCore G → M) contMDiff_subtypeVal σ :=
    Subtype.ext ((SmoothForm.coe_mpullback _ _ _).trans
      (SmoothForm.mpullback_smul_mpullback_subtypeVal Opens.coe_smul_invariantCore hσ g))
  -- The average `γ` of `β` over `G` is an invariant primitive, still vanishing with its first jet
  -- along the invariant set `f(Q)`.
  set γ := SmoothForm.measureAverage IG (haarProb G) β
  have horb (g : G) (q : Q) :
      ∃ q', g • (⟨f q, hfV (mem_range_self q)⟩ : W.invariantCore G) =
        ⟨f q', hfV (mem_range_self q')⟩ := by
    obtain ⟨q', hq'⟩ := hfG g q
    exact ⟨q', Subtype.ext ((Opens.coe_smul_invariantCore g _).trans hq'.symm)⟩
  have hdγ : mextDeriv γ.val = (τ₁ - τ₀).val := by
    have hβₗ : mextDerivₗ I 1 β = τ₁ - τ₀ := Subtype.ext (by rw [mextDerivₗ_apply, hdβ])
    have hτG (g : G) : TauCeti.mpullback I I (g • ·) (τ₁ - τ₀).val = (τ₁ - τ₀).val := by
      rw [← SmoothForm.coe_mpullback _ (contMDiff_const_smul g), map_sub, hτ σ₀ hσ₀ g,
        hτ σ₁ hσ₁ g]
    rw [← mextDerivₗ_apply,
      SmoothForm.mextDerivₗ_measureAverage_of_invariant IG (haarProb G) hβₗ hτG]
  have hγG (g : G) : SmoothForm.mpullback (fun x : W.invariantCore G ↦ g • x)
      (contMDiff_const_smul g) γ = γ :=
    Subtype.ext ((SmoothForm.coe_mpullback _ _ _).trans
      (SmoothForm.mpullback_smul_measureAverage IG _ β g))
  -- Moser's argument on the invariant core, equivariantly.
  obtain ⟨Φ, hΦf, hΦ, hsrc, hΦG⟩ :=
    SmoothTwoForm.exists_partialDiffeomorph_mpullback_eq_of_mextDeriv_eq_sub_of_smul
      (h₀.mpullback _ _) hdγ
      (fun x s hs ↦ by
        rw [← map_sub, ← map_smul, ← map_add]
        exact (nondegenerate_bilinFormAt_mpullback_subtype_val_iff x).2
          (hWO (Opens.invariantCore_le W x.property) s hs))
      (hτ σ₀ hσ₀) (hτ σ₁ hσ₁) hγG
  refine ⟨W, Φ, fun q ↦ ?_, fun x hx ↦ ?_, hsrc, hΦG⟩
  · have hγ0 : γ.val ⟨f q, hfV (mem_range_self q)⟩ = 0 :=
      SmoothForm.measureAverage_eq_zero_of_forall_smul IG _ β fun g ↦ by
        obtain ⟨q', hq'⟩ := horb g q
        rw [hq']
        exact hβ0 q'
    have hγ1 := SmoothForm.hasFDerivAt_inChartAt_measureAverage_of_forall_smul IG (haarProb G) β
      (x := ⟨f q, hfV (mem_range_self q)⟩)
      (fun g ↦ by
        obtain ⟨q', hq'⟩ := horb g q
        rw [hq']
        exact hβ0 q')
      (fun g ↦ by
        obtain ⟨q', hq'⟩ := horb g q
        rw [hq']
        exact hβ1 q')
    obtain ⟨hq, hfix, hjet⟩ := hΦf _ hγ0
    exact ⟨hfV (mem_range_self q), hq, hfix, hjet hγ1⟩
  · rw [← SmoothForm.coe_mpullback _ contMDiff_subtypeVal, hΦ x hx,
      SmoothForm.coe_mpullback_subtype_val_apply]

include IG in
/-- **The equivariant relative Moser theorem.** Let a compact Hausdorff topological group `G`,
which is a smooth manifold, act smoothly on a boundaryless Hausdorff second-countable manifold
`M`, and let `f : Q → M` be a smooth embedding whose image is `G`-invariant. Let `σ₀`, `σ₁` be
closed two-forms on `M`, invariant under every element of `G`, which agree on the whole tangent
space `T_{f q} M` at every point `f q`, with `σ₀` nondegenerate there. Then there are `G`-invariant
open sets `U₀`, `U₁` of `M` containing `f(Q)` and a `G`-equivariant diffeomorphism
`φ : U₀ → U₁`, which pulls the restriction of `σ₁` to `U₁` back to the restriction of `σ₀` to
`U₀`, fixes every point `f q`, and has the identity of `T_{f q} M` as its differential there.

This is the equivariant form of `TauCeti.SmoothEmbedding.exists_diffeomorph_opens_of_eq_along`;
as there, `Q` need not be compact and `f(Q)` need not be closed. -/
theorem exists_equivariant_diffeomorph_opens_of_eq_along (f : SmoothEmbedding J I ∞ Q M)
    (hfG : ∀ (g : G) q, g • f q ∈ range f)
    {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed) (h₁ : σ₁.IsClosed)
    (hσ₀ : ∀ g : G, TauCeti.mpullback I I (g • ·) σ₀.val = σ₀.val)
    (hσ₁ : ∀ g : G, TauCeti.mpullback I I (g • ·) σ₁.val = σ₁.val)
    (hnd : ∀ q, (σ₀.bilinFormAt (f q)).Nondegenerate)
    (heq : ∀ q, σ₁.val (f q) = σ₀.val (f q)) :
    ∃ (U₀ U₁ : Opens M) (φ : U₀ ≃ₘ⟮I, I⟯ U₁),
      (∀ g : G, ∀ x ∈ U₀, g • x ∈ U₀) ∧ (∀ g : G, ∀ x ∈ U₁, g • x ∈ U₁) ∧
      (∀ (g : G) (x : U₀) (hx : g • (x : M) ∈ U₀), (φ ⟨g • (x : M), hx⟩ : M) = g • (φ x : M)) ∧
      (∀ q, ∃ h : f q ∈ U₀, (φ ⟨f q, h⟩ : M) = f q ∧
        mfderiv I I φ ⟨f q, h⟩ = ContinuousLinearMap.id ℝ (TangentSpace I (⟨f q, h⟩ : U₀))) ∧
      SmoothForm.mpullback φ φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : U₁ → M) contMDiff_subtypeVal σ₁) =
        SmoothForm.mpullback (Subtype.val : U₀ → M) contMDiff_subtypeVal σ₀ := by
  have : ContinuousSMul G M := ContMDiffSMul.continuousSMul (I := IG) (I' := I) ∞
  obtain ⟨W, Φ, hΦf, hΦ, hsrc, hΦG⟩ :=
    exists_partialDiffeomorph_invariantCore_of_eq_along IG f hfG h₀ h₁ hσ₀ hσ₁ hnd heq
  rcases isEmpty_or_nonempty (W.invariantCore G) with hV | hV
  · -- If the invariant core is empty, so is `Q`, and the empty opens will do.
    have : IsEmpty Q := ⟨fun q ↦ hV.false ⟨f q, (hΦf q).1⟩⟩
    refine ⟨⊥, ⊥, Diffeomorph.ofIsEmpty, by simp, by simp, fun _ x ↦ isEmptyElim x, isEmptyElim,
      Subsingleton.elim _ _⟩
  -- Read `Φ` in `M`, as a partial diffeomorphism `Ψ`, and then as a diffeomorphism between the
  -- source and the target of `Ψ`; both are invariant, and `Ψ` is equivariant.
  set Ψ := Φ.liftOpens hV hV
  have hsrcG (g : G) : ∀ x ∈ Ψ.source, g • x ∈ Ψ.source := fun _ ↦
    Φ.smul_mem_liftOpens_source Opens.coe_smul_invariantCore hV hV (fun g x ↦ (hsrc g x).2) g
  have hΨG (g : G) : ∀ x ∈ Ψ.source, Ψ (g • x) = g • Ψ x :=
    Φ.liftOpens_smul Opens.coe_smul_invariantCore Opens.coe_smul_invariantCore hV hV
      (fun g x _ ↦ hΦG g x) g
  refine ⟨_, _, Ψ.toDiffeomorphSourceTarget, hsrcG,
    fun g _ hy ↦ (Ψ.toPartialEquiv.symm_map_of_intertwines (f := (g • ·)) (A := (g • ·))
      (fun x hx ↦ ⟨hsrcG g x hx, hΨG g x hx⟩) hy).1, fun g x hx ↦ ?_, fun q ↦ ?_,
    Φ.mpullback_toDiffeomorphSourceTarget_liftOpens hV hV hΦ⟩
  · rw [Ψ.toDiffeomorphSourceTarget_apply_coe, Ψ.toDiffeomorphSourceTarget_apply_coe]
    exact hΨG g x x.property
  · obtain ⟨_, hq, hfix, hjet⟩ := hΦf q
    exact Φ.exists_toDiffeomorphSourceTarget_liftOpens_eq_and_mfderiv_eq_id hV hq hfix hjet

end TauCeti.SmoothEmbedding

end
