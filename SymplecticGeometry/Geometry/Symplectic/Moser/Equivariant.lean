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
import TauCeti.Geometry.Symplectic.Hamiltonian.CanonicalTransformation
import SymplecticGeometry.Geometry.Manifold.GroupAction.Opens
import SymplecticGeometry.Geometry.Manifold.GroupAction.InvariantPrimitive
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Logic.Equiv.PartialEquiv
import SymplecticGeometry.Geometry.Symplectic.Manifold.Family
import TauCeti.Geometry.Symplectic.Manifold.Opens
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Basic
import SymplecticGeometry.Topology.Sets.Opens.Basic
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph

/-!
# The equivariant Moser flow and the equivariant relative Moser theorem

Let `σ` be a two-form and `β` a one-form on `N × M`, with slices `σ_t` and `β_t` on `M`, and let
`ρ : N × M → ℝ` be a cutoff. If a diffeomorphism `g` of `M` preserves every slice `σ_t` and `β_t`
and every function `ρ(t, ·)`, then the cut-off Moser field `X_t = ρ(t, ·) (σ_t♭)⁻¹(-β_t)` of
`SymplecticGeometry.moserField` is `g`-related to itself at every time: inverse flat maps are
natural under symplectic maps with invertible differential, and `g` is one from `g^* σ_t` to `σ_t`
(`TauCeti.SmoothTwoForm.IsSymplecticMap.mfderiv_inverse_flat_comp`).

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

The theorem also holds for forms given only on an open set `W` of `M` containing `f(Q)`, on which
`G` acts smoothly with equivariant inclusion
(`TauCeti.SmoothEmbedding.exists_equivariant_diffeomorph_opens_le_of_eq_along`). It is the
theorem for the manifold `W` and the embedding `TauCeti.SmoothEmbedding.codRestrict f W`, whose
open sets `V` of `W` are carried to open sets of `M` by Tau Ceti's
`IsLocalDiffeomorph.diffeomorphOfInjective`, applied to the composite of the inclusions
`V → W → M`; this diffeomorphism has identity differential, as both inclusions have
(`IsLocalDiffeomorph.mfderiv_diffeomorphOfInjective_apply`).

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
* `TauCeti.SmoothEmbedding.exists_equivariant_diffeomorph_opens_le_of_eq_along`: the same for
  forms on an open set around `f(Q)`.

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
    rw [hc, (SmoothTwoForm.isSymplecticMap_mpullback σt g.contMDiff).mfderiv_inverse_flat_comp
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
  -- A primitive of `σ₁ - σ₀` on a tube `W`, vanishing with its first jet along `f(Q)`.
  obtain ⟨W, hWO, hfW, βW, hdβW, hβW0, hβW1⟩ :=
    f.exists_smoothForm_relative_primitive_sub_of_eq_along h₀ h₁ hnd heq
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
    exact hβW1 q

include IG in
/-- The equivariant relative Moser theorem before it is read in `M`: on the invariant core of a tube
around `f(Q)`, an equivariant partial diffeomorphism `Φ` with invariant source, whose source
contains `f(Q)`, which fixes `f(Q)` with identity differential there, and which pulls `σ₁` back
to `σ₀` at every point of its source. -/
private theorem exists_partialDiffeomorph_invariantCore_of_eq_along [ContinuousSMul G M]
    (f : SmoothEmbedding J I ∞ Q M) (hfG : ∀ (g : G) q, g • f q ∈ range f)
    {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed) (h₁ : σ₁.IsClosed)
    (hσ₀ : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) (I' := I) g) σ₀ = σ₀)
    (hσ₁ : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) (I' := I) g) σ₁ = σ₁)
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
  have hτ (σ : SmoothTwoForm I M)
      (hσ : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x) (contMDiff_const_smul g) σ = σ)
      (g : G) : SmoothForm.mpullback (fun x : W.invariantCore G ↦ g • x) (contMDiff_const_smul g)
        (SmoothForm.mpullback (Subtype.val : W.invariantCore G → M) contMDiff_subtypeVal σ) =
      SmoothForm.mpullback (Subtype.val : W.invariantCore G → M) contMDiff_subtypeVal σ :=
    SmoothForm.mpullback_smul_mpullback contMDiff_subtypeVal (Opens.coe_smul_invariantCore g)
      (hσ g)
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
    (hσ₀ : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) (I' := I) g) σ₀ = σ₀)
    (hσ₁ : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) (I' := I) g) σ₁ = σ₁)
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

omit [ContMDiffSMul IG I ∞ G M] in
include IG in
/-- **The equivariant relative Moser theorem for forms on an open set.** Let a compact Hausdorff
topological group `G`, which is a smooth manifold, act on a boundaryless Hausdorff
second-countable manifold `M`, and let `f : Q → M` be a smooth embedding whose image is
`G`-invariant. Let `W` be an open set of `M` containing `f(Q)`, on which `G` acts smoothly so
that the inclusion `W → M` is equivariant, such as an invariant `W` with the restricted action
(`TopologicalSpace.Opens.mulActionOfForallSMulMem`, smooth by
`TopologicalSpace.Opens.contMDiffSMul_of_coe_smul` when the action on `M` is). Let `σ₀`, `σ₁`
be closed two-forms on `W`, invariant under every element of `G`, which agree on the whole
tangent space at every point `f q`, with `σ₀` nondegenerate there. Then there are
`G`-invariant open sets `U₀, U₁ ≤ W` of `M` containing `f(Q)` and a `G`-equivariant
diffeomorphism `φ : U₀ → U₁`, which pulls the restriction of `σ₁` to `U₁` back to the
restriction of `σ₀` to `U₀`, fixes every point `f q`, and has the identity of `T_{f q} M` as
its differential there.

This is `TauCeti.SmoothEmbedding.exists_equivariant_diffeomorph_opens_of_eq_along` for the
manifold `W` and the embedding `f` with codomain restricted to `W`, read in `M`. -/
theorem exists_equivariant_diffeomorph_opens_le_of_eq_along (f : SmoothEmbedding J I ∞ Q M)
    (hfG : ∀ (g : G) q, g • f q ∈ range f) {W : Opens M} (hfW : range f ⊆ W)
    [MulAction G W] [ContMDiffSMul IG I ∞ G W]
    (hcW : ∀ (g : G) (x : W), ((g • x : W) : M) = g • (x : M))
    {σ₀ σ₁ : SmoothTwoForm I W} (h₀ : σ₀.IsClosed) (h₁ : σ₁.IsClosed)
    (hσ₀ : ∀ g : G, SmoothForm.mpullback (fun x : W ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) (I' := I) g) σ₀ = σ₀)
    (hσ₁ : ∀ g : G, SmoothForm.mpullback (fun x : W ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) (I' := I) g) σ₁ = σ₁)
    (hnd : ∀ q, (σ₀.bilinFormAt ⟨f q, hfW (mem_range_self q)⟩).Nondegenerate)
    (heq : ∀ q, σ₁.val ⟨f q, hfW (mem_range_self q)⟩ = σ₀.val ⟨f q, hfW (mem_range_self q)⟩) :
    ∃ (U₀ U₁ : Opens M) (hU₀ : U₀ ≤ W) (hU₁ : U₁ ≤ W) (φ : U₀ ≃ₘ⟮I, I⟯ U₁),
      (∀ g : G, ∀ x ∈ U₀, g • x ∈ U₀) ∧ (∀ g : G, ∀ x ∈ U₁, g • x ∈ U₁) ∧
      (∀ (g : G) (x : U₀) (hx : g • (x : M) ∈ U₀), (φ ⟨g • (x : M), hx⟩ : M) = g • (φ x : M)) ∧
      (∀ q, ∃ h : f q ∈ U₀, (φ ⟨f q, h⟩ : M) = f q ∧
        mfderiv I I φ ⟨f q, h⟩ = ContinuousLinearMap.id ℝ (TangentSpace I (⟨f q, h⟩ : U₀))) ∧
      SmoothForm.mpullback φ φ.contMDiff
          (SmoothForm.mpullback (Opens.inclusion hU₁) (contMDiff_inclusion hU₁) σ₁) =
        SmoothForm.mpullback (Opens.inclusion hU₀) (contMDiff_inclusion hU₀) σ₀ := by
  have hfW' (q : Q) : f q ∈ W := hfW (mem_range_self q)
  set f' := f.codRestrict W hfW'
  have hf' (q : Q) : f' q = ⟨f q, hfW' q⟩ := Subtype.ext (f.val_codRestrict_apply W hfW' q)
  -- The equivariant relative Moser theorem on the manifold `W`.
  obtain ⟨V₀, V₁, ψ, hV₀, hV₁, hψG, hψf, hψσ⟩ :=
    exists_equivariant_diffeomorph_opens_of_eq_along IG f'
      (fun g q ↦ by
        obtain ⟨q', hq'⟩ := hfG g q
        exact ⟨q', Subtype.ext (by
          rw [hcW, f.val_codRestrict_apply, f.val_codRestrict_apply]; exact hq')⟩)
      h₀ h₁ hσ₀ hσ₁ (fun q ↦ hf' q ▸ hnd q) (fun q ↦ hf' q ▸ heq q)
  -- An open set `V` of `W` is diffeomorphic to its image in `M`, by a map with identity
  -- differential.
  have hl (V : Opens W) :
      IsLocalDiffeomorph I I ∞ ((Subtype.val : W → M) ∘ (Subtype.val : V → W)) :=
    isLocalDiffeomorph_subtypeVal_comp_iff.2 isLocalDiffeomorph_subtype_val
  have hi (V : Opens W) : Function.Injective ((Subtype.val : W → M) ∘ (Subtype.val : V → W)) :=
    Subtype.val_injective.comp Subtype.val_injective
  have hmem {V : Opens W} {x : M} :
      x ∈ (hl V).image ↔ x ∈ range ((Subtype.val : W → M) ∘ (Subtype.val : V → W)) :=
    Set.ext_iff.1 (hl V).image_coe x
  have hle (V : Opens W) : (hl V).image ≤ W := fun x hx ↦ by
    obtain ⟨y, rfl⟩ := hmem.1 hx
    exact (y : W).property
  have hsmul {V : Opens W} (hV : ∀ g : G, ∀ x ∈ V, g • x ∈ V) (g : G) (x : M)
      (hx : x ∈ (hl V).image) : g • x ∈ (hl V).image := by
    obtain ⟨y, rfl⟩ := hmem.1 hx
    exact hmem.2 ⟨⟨g • (y : W), hV g _ y.property⟩, hcW g _⟩
  have hincl (V : Opens W) : Opens.inclusion (hle V) ∘ (hl V).diffeomorphOfInjective (hi V) =
      Subtype.val :=
    funext fun y ↦ Subtype.ext ((hl V).coe_diffeomorphOfInjective_apply (hi V) y)
  have hincl' (V : Opens W) : Subtype.val ∘ ((hl V).diffeomorphOfInjective (hi V)).symm =
      Opens.inclusion (hle V) :=
    funext fun x ↦ Subtype.ext ((hl V).apply_diffeomorphOfInjective_symm (hi V) x)
  have hde (V : Opens W) (y : V) (v : TangentSpace I y) :
      mfderiv I I ((hl V).diffeomorphOfInjective (hi V)) y v = v := by
    rw [(hl V).mfderiv_diffeomorphOfInjective_apply,
      TauCeti.Manifold.mfderiv_subtype_val_comp_apply]
    exact TauCeti.Manifold.mfderiv_subtype_val_apply _ _
  have hde' (V : Opens W) (x : (hl V).image) (v : TangentSpace I x) :
      mfderiv I I ((hl V).diffeomorphOfInjective (hi V)).symm x v = v := by
    rw [← TauCeti.Manifold.mfderiv_subtype_val_comp_apply, hincl',
      TauCeti.Manifold.mfderiv_inclusion_apply]
  set e₀ := (hl V₀).diffeomorphOfInjective (hi V₀)
  set e₁ := (hl V₁).diffeomorphOfInjective (hi V₁)
  -- The diffeomorphism `ψ` read in `M`.
  set φ := e₀.symm.trans (ψ.trans e₁) with hφdef
  have hincl₀ : Subtype.val ∘ e₀.symm = Opens.inclusion (hle V₀) := hincl' V₀
  have hde₁ (y : V₁) (v : TangentSpace I y) : mfderiv I I e₁ y v = v := hde V₁ y v
  have hde₀' (x : (hl V₀).image) (v : TangentSpace I x) : mfderiv I I e₀.symm x v = v :=
    hde' V₀ x v
  have hφ (y : V₀) : (φ (e₀ y) : M) = ((ψ y : W) : M) := by
    rw [hφdef, Diffeomorph.coe_trans, Diffeomorph.coe_trans, Function.comp_apply,
      Function.comp_apply, Diffeomorph.symm_apply_apply]
    exact (hl V₁).coe_diffeomorphOfInjective_apply (hi V₁) (ψ y)
  refine ⟨_, _, hle V₀, hle V₁, φ, hsmul hV₀, hsmul hV₁, fun g x hx ↦ ?_, fun q ↦ ?_, ?_⟩
  · obtain ⟨y, rfl⟩ : ∃ y, e₀ y = x := ⟨e₀.symm x, e₀.apply_symm_apply x⟩
    have hy : g • (y : W) ∈ V₀ := hV₀ g _ y.property
    have hgy : (⟨g • ((e₀ y : (hl V₀).image) : M), hx⟩ : (hl V₀).image) =
        e₀ ⟨g • (y : W), hy⟩ :=
      Subtype.ext (by simp [e₀, hcW])
    rw [hgy, hφ, hφ, hψG g y hy, hcW]
  · obtain ⟨hq, hfix, hjet⟩ := hψf q
    have hx : f q ∈ (hl V₀).image := hmem.2 ⟨⟨f' q, hq⟩, f.val_codRestrict_apply W hfW' q⟩
    have hex : (⟨f q, hx⟩ : (hl V₀).image) = e₀ ⟨f' q, hq⟩ :=
      Subtype.ext ((f.val_codRestrict_apply W hfW' q).symm.trans
        ((hl V₀).coe_diffeomorphOfInjective_apply (hi V₀) ⟨f' q, hq⟩).symm)
    refine ⟨hx, by rw [hex, hφ, hfix]; exact f.val_codRestrict_apply W hfW' q, ?_⟩
    have hd (x : (hl V₀).image)
        (hψd : mfderiv I I ψ (e₀.symm x) = ContinuousLinearMap.id ℝ (TangentSpace I (e₀.symm x))) :
        mfderiv I I φ x = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
      ext v
      rw [hφdef, Diffeomorph.coe_trans, Diffeomorph.coe_trans,
        mfderiv_comp_apply x
          (((e₁.mdifferentiable (by simp)) _).comp _ ((ψ.mdifferentiable (by simp)) _))
          ((e₀.symm.mdifferentiable (by simp)) x),
        mfderiv_comp_apply (e₀.symm x) ((e₁.mdifferentiable (by simp)) _)
          ((ψ.mdifferentiable (by simp)) _),
        hde₁, hde₀']
      exact DFunLike.congr_fun hψd v
    refine hd _ ?_
    rw [hex, Diffeomorph.symm_apply_apply]
    exact hjet
  · have hcomp : Opens.inclusion (hle V₁) ∘ φ = (Subtype.val ∘ ψ) ∘ e₀.symm := by
      rw [hφdef, Diffeomorph.coe_trans, Diffeomorph.coe_trans]
      exact funext fun x ↦ congrFun (hincl V₁) (ψ (e₀.symm x))
    rw [SmoothForm.mpullback_mpullback_of_comp_eq φ.contMDiff (contMDiff_inclusion (hle V₁))
      e₀.symm.contMDiff (contMDiff_subtypeVal.comp ψ.contMDiff) hcomp,
      ← SmoothForm.mpullback_mpullback ψ Subtype.val ψ.contMDiff contMDiff_subtypeVal, hψσ]
    simp only [SmoothForm.mpullback_mpullback, hincl₀]

end TauCeti.SmoothEmbedding

end
