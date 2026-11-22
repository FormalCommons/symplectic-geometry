/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Liouville.Collar
public import SymplecticGeometry.Geometry.Symplectic.Liouville.ContactType
public import SymplecticGeometry.Topology.Sets.Strip
import Mathlib.Geometry.Manifold.Metrizable
import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective

/-!
# Liouville collars of hypersurfaces

Let `σ` be a symplectic form on `M`, `i : Q → M` a smooth embedding of codimension one, and `Y` a
vector field, smooth on an open neighbourhood `U` of the image of `i`, with `L_Y σ = σ` on `U` and
transverse along `i`. In McDuff–Salamon's signs the Liouville primitive is `λ = -ι_Y σ`, and the
hypersurface carries the contact form `α = i^*λ = -i^*(ι_Y σ)`
(`TauCeti.SmoothEmbedding.exists_isContactForm_eq_neg_mpullback_interior`). This file shows that
the flow of `Y` out of the hypersurface is a *Liouville collar*: the map `Φ(t, q) = φₜ(i q)` is a
diffeomorphism from an open neighbourhood `D` of `{0} × Q` in `ℝ × Q` onto an open neighbourhood
`V ⊆ U` of the image of `i`, with `Φ(0, q) = i q`, and it pulls `σ` back to the symplectization
form `-d(eˢ α)` and `λ` back to `eˢ α`. For compact `Q` the domain may be taken to be a strip
`(-ε, ε) × Q`. Together with `TauCeti.SmoothEmbedding.exists_liouville_of_isContactForm` this gives
McDuff–Salamon's Proposition 3.5.31, without its compactness assumption.

The forms appear in Tau Ceti's signs (see `design/liouville-structures.md`): Tau Ceti's primitive
is `ι_Y σ = -λ`, its symplectization of a one-form `β` on `Q` is `eˢ β`, so the book's `-d(eˢ α)`
is `mextDerivₗ _ 1 (-α).symplectization`.

The field `Y` is Liouville only on `U`, while Tau Ceti's collar theorems
(`TauCeti.exists_continuous_pos_injOn_flowOf_comp` and its formulas
`TauCeti.mpullback_flowOf_comp_mextDeriv_apply`,
`TauCeti.mpullback_flowOf_comp_apply_eq_symplectization`) ask for a field and a primitive on the
whole manifold. They are therefore applied on the open submanifold `U`, to the restriction of `Y`
(Mathlib's pullback `VectorField.mpullback` along the inclusion) and of `ι_Y σ`, which is
Liouville there by `TauCeti.interior_mextDeriv_mpullback_subtypeVal_interior`, and the
resulting injective local diffeomorphism is made a diffeomorphism onto its image with Tau Ceti's
`IsLocalDiffeomorph.diffeomorphOfInjective`.

## Main definitions

* `TauCeti.IsLiouvilleCollar σ Y i α Φ φ`: the diffeomorphism `Φ : D ≃ₘ V`, given by `φ`, is a
  Liouville collar of `i` for `σ`, `Y` and `α`: `V` contains the image of `i`, `φ (0, q) = i q`,
  the lines of `φ` are integral curves of `Y`, and `Φ` pulls `σ` and `ι_Y σ` back to
  `d(eˢ (-α))` and `eˢ (-α)`, both stated as pullbacks of rough forms to `D`.

## Main results

* `TauCeti.SmoothEmbedding.exists_pos_forall_liouvilleCollar`: there is a positive continuous
  width `ε` on `Q` such that every open `D` with `{0} × Q ⊆ D ⊆ {|t| < ε q}` is the domain of a
  Liouville collar.
* `TauCeti.SmoothEmbedding.exists_liouvilleCollar`: a Liouville collar of variable width.
* `TauCeti.SmoothEmbedding.exists_liouvilleCollar_of_compactSpace`: for compact `Q`, a Liouville
  collar on a strip `(-ε, ε) × Q`.
* `TauCeti.SmoothEmbedding.exists_isContactForm_iff_exists_liouville` and
  `TauCeti.SmoothEmbedding.exists_liouvilleCollar_of_isContactForm`: a hypersurface carries a
  contact form `α` with `dα = -i^*σ` exactly when it has a transverse Liouville field nearby;
  and for each such `α` there is such a field inducing `α`, whose flow is a Liouville collar.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.5,
  Definition 3.5.27 and Proposition 3.5.31.
-/

public section

open Bundle Module Set Function TopologicalSpace SymplecticGeometry
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {E' H' Q : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless] [TopologicalSpace Q]
  [ChartedSpace H' Q] [IsManifold J ∞ Q]
  {σ : SmoothTwoForm I M} {U : Set M} {Y : (x : M) → TangentSpace I x}

/-- A **Liouville collar** of `i : Q → M` for the two-form `σ`, the vector field `Y` and the
one-form `α` on `Q`: a diffeomorphism `Φ` from an open set `D ⊆ ℝ × Q` onto an open set `V ⊆ M`
containing the image of `i`, which agrees on `D` with a map `φ : ℝ × Q → M` such that
`φ (0, q) = i q` and each `t ↦ φ (t, q)` is an integral curve of `Y` on the slice of `D` over `q`,
and which pulls `σ` back to `d(eˢ (-α))` and `ι_Y σ` back to `eˢ (-α)` on `D`. In McDuff–Salamon's
signs, with the primitive `λ = -ι_Y σ`, these say `Φ^*σ = -d(eˢ α)` and `Φ^*λ = eˢ α`. -/
structure IsLiouvilleCollar (σ : SmoothTwoForm I M) (Y : (x : M) → TangentSpace I x)
    (i : Q → M) (α : SmoothForm J Q ℝ 1) {D : Opens (ℝ × Q)} {V : Opens M}
    (Φ : D ≃ₘ⟮𝓘(ℝ).prod J, I⟯ V) (φ : ℝ × Q → M) : Prop where
  /-- The image of `V` contains the hypersurface. -/
  range_subset : range i ⊆ V
  /-- On `D`, the collar is given by `φ`. -/
  coe_apply : ∀ p, (Φ p : M) = φ p
  /-- The map `φ` starts on the hypersurface. -/
  apply_zero : ∀ q, φ (0, q) = i q
  /-- The lines of `φ` are integral curves of `Y` on the slices of `D`. -/
  isMIntegralCurveOn : ∀ q, IsMIntegralCurveOn (fun t ↦ φ (t, q)) Y {t | (t, q) ∈ D}
  /-- The collar pulls `σ` back to `d(eˢ (-α))`. -/
  mpullback_eq : mpullback (𝓘(ℝ).prod J) I (fun p ↦ (Φ p : M)) σ.val =
    mpullback (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) (Subtype.val : D → ℝ × Q)
      (mextDerivₗ (𝓘(ℝ).prod J) 1 (-α).symplectization).val
  /-- The collar pulls `ι_Y σ` back to `eˢ (-α)`. -/
  mpullback_interior_eq :
    mpullback (𝓘(ℝ).prod J) I (fun p ↦ (Φ p : M)) (RoughForm.interior Y σ.val) =
      mpullback (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) (Subtype.val : D → ℝ × Q)
        (-α).symplectization.val

omit [FiniteDimensional ℝ E'] [J.Boundaryless] in
/-- The assembly of the collar from Tau Ceti's local Liouville flow on an open submanifold `U'`:
if the flow map `Ψ(t, q) = φₜ(ι q)` of the restricted field `Z` is injective and a local
diffeomorphism on an open `D ⊇ {0} × Q` inside its domain, then `Ψ`, read in `M`, is a Liouville
collar on `D`. -/
private theorem liouvilleCollar_of_injOn {U' : Opens M}
    {Z : (x : U') → TangentSpace I x} (hZ : ContMDiff I I.tangent ∞ (T% Z))
    (hZY : ∀ x, mfderiv I I Subtype.val x (Z x) = Y x) {β : SmoothForm I U' ℝ 1}
    (hβ : β.val = mpullback I I Subtype.val (RoughForm.interior Y σ.val))
    (hdβ : mextDeriv β.val = mpullback I I Subtype.val σ.val)
    (hZβ : (mextDeriv β.val).interior Z = β.val) {i : Q → M} {ι : Q → U'}
    (hι : ContMDiff J I ∞ ι) (hιi : ∀ q, (ι q : M) = i q) {α : SmoothForm J Q ℝ 1}
    (hια : SmoothForm.mpullback ι hι β = -α) (D : Opens (ℝ × Q))
    (hD0 : ({0} ×ˢ univ : Set (ℝ × Q)) ⊆ D)
    (hDZ : (D : Set (ℝ × Q)) ⊆ {p | (p.1, ι p.2) ∈ flowDomain Z})
    (hinj : InjOn (fun p : ℝ × Q ↦ flowOf Z p.1 (ι p.2)) D)
    (hloc : IsLocalDiffeomorphOn (𝓘(ℝ).prod J) I ∞ (fun p : ℝ × Q ↦ flowOf Z p.1 (ι p.2)) D) :
    ∃ (V : Opens M) (Φ : D ≃ₘ⟮𝓘(ℝ).prod J, I⟯ V) (φ : ℝ × Q → M),
      V ≤ U' ∧ IsLiouvilleCollar σ Y i α Φ φ := by
  let Ψ : ℝ × Q → U' := fun p ↦ flowOf Z p.1 (ι p.2)
  let g : D → U' := Ψ ∘ Subtype.val
  have hg : IsLocalDiffeomorph (𝓘(ℝ).prod J) I ∞ g := fun p ↦
    IsLocalDiffeomorphAt.comp I U' (isLocalDiffeomorph_subtype_val p) (hloc ⟨p.val, p.property⟩)
  have hf : IsLocalDiffeomorph (𝓘(ℝ).prod J) I ∞ (Subtype.val ∘ g) := fun p ↦
    IsLocalDiffeomorphAt.comp I M (hg p) (isLocalDiffeomorph_subtype_val (g p))
  have hfinj : Injective (Subtype.val ∘ g) := fun p p' h ↦
    Subtype.ext (hinj p.property p'.property (Subtype.ext h))
  have hΦ : (fun p ↦ (hf.diffeomorphOfInjective hfinj p : M)) = Subtype.val ∘ g :=
    funext (hf.coe_diffeomorphOfInjective_apply hfinj)
  -- Pulling back along `g` is pulling back along `Ψ`, then restricting to `D`.
  have hgpb {k : ℕ} (γ : RoughForm I U' ℝ k) :
      mpullback (𝓘(ℝ).prod J) I g γ = mpullback (𝓘(ℝ).prod J) (𝓘(ℝ).prod J)
        (Subtype.val : D → ℝ × Q) (mpullback (𝓘(ℝ).prod J) I Ψ γ) := by
    funext p
    exact mpullback_comp_at ((contMDiff_subtypeVal p).mdifferentiableAt one_ne_zero)
      ((hloc ⟨p.val, p.property⟩).mdifferentiableAt (by simp)) γ
  -- Pulling back along `Φ` into `M` is pulling back along `g`, then along the inclusion of `U'`.
  have hΦpb {k : ℕ} (γ : RoughForm I M ℝ k) (p : D) :
      mpullback (𝓘(ℝ).prod J) I (fun p ↦ (hf.diffeomorphOfInjective hfinj p : M)) γ p =
        mpullback (𝓘(ℝ).prod J) I g (mpullback I I (Subtype.val : U' → M) γ) p := by
    rw [hΦ, mpullback_comp_at (hg.contMDiff.mdifferentiableAt (by simp))
      ((contMDiff_subtypeVal _).mdifferentiableAt one_ne_zero)]
  have hpb {k : ℕ} (γ : RoughForm (𝓘(ℝ).prod J) (ℝ × Q) ℝ k) (p : D) :
      mpullback (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) (Subtype.val : D → ℝ × Q) γ p = γ p.val :=
    mpullback_subtype_val_apply γ p
  refine ⟨hf.image, hf.diffeomorphOfInjective hfinj, fun p ↦ (Ψ p : M), ?_,
    ⟨?_, hf.coe_diffeomorphOfInjective_apply hfinj, fun q ↦ ?_, fun q ↦ ?_, ?_, ?_⟩⟩
  · rintro _ ⟨p, rfl⟩
    exact (g p).property
  · rintro _ ⟨q, rfl⟩
    exact ⟨⟨(0, q), hD0 ⟨rfl, mem_univ q⟩⟩, by simp [g, Ψ, hιi]⟩
  · simp [Ψ, hιi]
  · exact ((isMIntegralCurveOn_flowOf (hZ.of_le (by simp)) (ι q)).mono
      fun t ht ↦ hDZ ht).map_of_mfderiv_eq
      (fun _ _ ↦ (contMDiff_subtypeVal _).mdifferentiableAt one_ne_zero) (fun _ _ ↦ hZY _)
  · funext p
    rw [hΦpb, ← hdβ, hgpb, hpb, hpb, mpullback_flowOf_comp_mextDeriv_apply hZ hι hZβ
      (hDZ p.property), hια, mextDerivₗ_apply]
  · funext p
    rw [hΦpb, ← hβ, hgpb, hpb, hpb,
      mpullback_flowOf_comp_apply_eq_symplectization hZ hι hZβ (hDZ p.property), hια]

/-- **Liouville collars of every small width.** Let `σ` be a symplectic form on `M`, `i : Q → M` a
smooth embedding of codimension one, `Y` a vector field, smooth and Liouville (`L_Y σ = σ`) on an
open neighbourhood `U` of the image of `i` and transverse along `i`, and `α = -i^*(ι_Y σ)` the
induced contact form. Then there is a positive continuous function `ε` on `Q` such that every open
`D` with `{0} × Q ⊆ D ⊆ {(t, q) | |t| < ε q}` is the domain of a Liouville collar
(`TauCeti.IsLiouvilleCollar`) of `i` for `σ`, `Y` and `α`, given by the flow of `Y` out of the
hypersurface, onto an open set `V ⊆ U`. -/
theorem SmoothEmbedding.exists_pos_forall_liouvilleCollar [SecondCountableTopology M]
    (hσ : σ.IsSymplectic) (i : SmoothEmbedding J I ∞ Q M) (hdim : finrank ℝ E' + 1 = finrank ℝ E)
    (hU : IsOpen U) (hiU : range i ⊆ U) (hY : ContMDiffOn I I.tangent (⊤ : ℕ∞) (T% Y) U)
    (hYσ : ∀ x ∈ U, mlieDerivForm Y σ.val x = σ.val x) (hYi : IsTransverseAlong J Y i)
    {α : SmoothForm J Q ℝ 1} (hα : α.val = -mpullback J I i (RoughForm.interior Y σ.val)) :
    ∃ ε : C(Q, ℝ), (∀ q, 0 < ε q) ∧ ∀ D : Opens (ℝ × Q),
      ({0} ×ˢ univ : Set (ℝ × Q)) ⊆ D → (D : Set (ℝ × Q)) ⊆ {p | |p.1| < ε p.2} →
      ∃ (V : Opens M) (Φ : D ≃ₘ⟮𝓘(ℝ).prod J, I⟯ V) (φ : ℝ × Q → M),
        (V : Set M) ⊆ U ∧ IsLiouvilleCollar σ Y i α Φ φ := by
  set U' : Opens M := ⟨U, hU⟩
  -- The field `Y` and the primitive `ι_Y σ`, restricted to `U'`.
  let Z : (x : U') → TangentSpace I x := VectorField.mpullback I I Subtype.val Y
  have hZ : ContMDiff I I.tangent ∞ (T% Z) := VectorField.contMDiff_mpullback_subtypeVal hY
  let β : SmoothForm I U' ℝ 1 :=
    ⟨_, (isSmoothForm_mpullback_subtypeVal_interior (σ := σ) (U := U') hY).mem_smoothBundleForms⟩
  have hβ : β.val = mpullback I I Subtype.val (RoughForm.interior Y σ.val) := rfl
  have hdβ : mextDeriv β.val = mpullback I I Subtype.val σ.val := by
    rw [hβ]
    exact mextDeriv_mpullback_subtypeVal_interior hσ.isClosed hY hYσ
  have hZβ : (mextDeriv β.val).interior Z = β.val := by
    rw [hβ]
    exact interior_mextDeriv_mpullback_subtypeVal_interior hσ.isClosed hY hYσ
  -- The hypersurface, as a map into `U'`.
  let ι : Q → U' := fun q ↦ ⟨i q, hiU (mem_range_self q)⟩
  have hι : ContMDiff J I ∞ ι := (ContMDiff.subtypeVal_comp_iff _ ι).1 i.contMDiff
  have hιi : (Subtype.val ∘ ι : Q → M) = i := rfl
  have hια : SmoothForm.mpullback ι hι β = -α := by
    refine Subtype.ext (funext fun q ↦ ?_)
    rw [SmoothForm.coe_mpullback, SmoothForm.neg_toRoughForm, Pi.neg_apply, hα, Pi.neg_apply,
      neg_neg, hβ, ← mpullback_comp_at ((hι q).mdifferentiableAt (by simp))
        ((contMDiff_subtypeVal _).mdifferentiableAt one_ne_zero), hιi]
  have hcontact : (SmoothForm.mpullback ι hι β).IsContactForm := by
    obtain ⟨α₀, hα₀, hα₀c, -⟩ :=
      i.exists_isContactForm_eq_neg_mpullback_interior hσ hdim hU hiU hY hYσ hYi
    rw [hια, Subtype.ext (hα.trans hα₀.symm), SmoothForm.isContactForm_neg_iff]
    exact hα₀c
  -- Second countable Hausdorff manifolds are metrizable, as Tau Ceti's variable width needs.
  have := I.locallyCompactSpace
  have := ChartedSpace.locallyCompactSpace H M
  have := Manifold.metrizableSpace I M
  have : PseudoMetrizableSpace U' := Topology.IsInducing.subtypeVal.pseudoMetrizableSpace
  have : PseudoMetrizableSpace Q := i.isEmbedding.isInducing.pseudoMetrizableSpace
  obtain ⟨ε, hε, hεD, hinj, hloc⟩ := exists_continuous_pos_injOn_flowOf_comp hZ hι hdim hZβ
    hcontact (i.isEmbedding.isInducing.codRestrict _)
  refine ⟨ε, hε, fun D hD0 hDε ↦ ?_⟩
  exact liouvilleCollar_of_injOn hZ (VectorField.mfderiv_subtypeVal_mpullback_subtypeVal Y) hβ
    hdβ hZβ hι (fun _ ↦ rfl) hια D hD0 (hDε.trans hεD) (hinj.mono hDε)
    fun p ↦ hloc ⟨p, hDε p.property⟩

/-- **The Liouville collar of a hypersurface.** Let `σ` be a symplectic form on `M`, `i : Q → M` a
smooth embedding of codimension one, `Y` a vector field, smooth and Liouville (`L_Y σ = σ`) on an
open neighbourhood `U` of the image of `i` and transverse along `i`, and `α = -i^*(ι_Y σ)` the
induced contact form. Then some open neighbourhood `D` of `{0} × Q` in `ℝ × Q` is the domain of a
Liouville collar (`TauCeti.IsLiouvilleCollar`) of `i` for `σ`, `Y` and `α` onto an open set
`V ⊆ U`. -/
theorem SmoothEmbedding.exists_liouvilleCollar [SecondCountableTopology M]
    (hσ : σ.IsSymplectic) (i : SmoothEmbedding J I ∞ Q M) (hdim : finrank ℝ E' + 1 = finrank ℝ E)
    (hU : IsOpen U) (hiU : range i ⊆ U) (hY : ContMDiffOn I I.tangent (⊤ : ℕ∞) (T% Y) U)
    (hYσ : ∀ x ∈ U, mlieDerivForm Y σ.val x = σ.val x) (hYi : IsTransverseAlong J Y i)
    {α : SmoothForm J Q ℝ 1} (hα : α.val = -mpullback J I i (RoughForm.interior Y σ.val)) :
    ∃ D : Opens (ℝ × Q), ({0} ×ˢ univ : Set (ℝ × Q)) ⊆ D ∧
      ∃ (V : Opens M) (Φ : D ≃ₘ⟮𝓘(ℝ).prod J, I⟯ V) (φ : ℝ × Q → M),
        (V : Set M) ⊆ U ∧ IsLiouvilleCollar σ Y i α Φ φ := by
  obtain ⟨ε, hε, h⟩ := i.exists_pos_forall_liouvilleCollar hσ hdim hU hiU hY hYσ hYi hα
  let D : Opens (ℝ × Q) := ⟨{p | |p.1| < ε p.2},
    isOpen_lt (continuous_abs.comp continuous_fst) (ε.continuous.comp continuous_snd)⟩
  have hD0 : ({0} ×ˢ univ : Set (ℝ × Q)) ⊆ D := by
    rintro ⟨_, q⟩ ⟨rfl, -⟩
    simpa [D] using hε q
  exact ⟨D, hD0, h D hD0 subset_rfl⟩

/-- **The Liouville collar of a compact hypersurface.** In the setting of
`TauCeti.SmoothEmbedding.exists_liouvilleCollar`, for compact `Q` the domain of the collar may be
taken to be a strip `(-ε, ε) × Q` for some `ε > 0`. -/
theorem SmoothEmbedding.exists_liouvilleCollar_of_compactSpace [SecondCountableTopology M]
    [CompactSpace Q] (hσ : σ.IsSymplectic) (i : SmoothEmbedding J I ∞ Q M)
    (hdim : finrank ℝ E' + 1 = finrank ℝ E) (hU : IsOpen U) (hiU : range i ⊆ U)
    (hY : ContMDiffOn I I.tangent (⊤ : ℕ∞) (T% Y) U)
    (hYσ : ∀ x ∈ U, mlieDerivForm Y σ.val x = σ.val x) (hYi : IsTransverseAlong J Y i)
    {α : SmoothForm J Q ℝ 1} (hα : α.val = -mpullback J I i (RoughForm.interior Y σ.val)) :
    ∃ ε > 0, ∃ (V : Opens M) (Φ : symmStrip Q ε ≃ₘ⟮𝓘(ℝ).prod J, I⟯ V) (φ : ℝ × Q → M),
      (V : Set M) ⊆ U ∧ IsLiouvilleCollar σ Y i α Φ φ := by
  obtain ⟨ε, hε, h⟩ := i.exists_pos_forall_liouvilleCollar hσ hdim hU hiU hY hYσ hYi hα
  let D : Opens (ℝ × Q) := ⟨{p | |p.1| < ε p.2},
    isOpen_lt (continuous_abs.comp continuous_fst) (ε.continuous.comp continuous_snd)⟩
  obtain ⟨δ, hδ, hδD⟩ := exists_symmStrip_le (U := D) fun q ↦ by simpa [D] using hε q
  refine ⟨δ, hδ, h _ ?_ hδD⟩
  rintro ⟨_, q⟩ ⟨rfl, -⟩
  exact zero_mk_mem_symmStrip hδ q

/-- **Contact type through Liouville fields.** Let `σ` be a symplectic form on `M` and `i : Q → M`
a smooth embedding of codimension one. Then `Q` carries a contact form `α` with `dα = -i^*σ` if and
only if some vector field, smooth and Liouville (`L_Y σ = σ`) on an open neighbourhood of the image
of `i`, is transverse along `i`. The contact forms and the fields are related by
`α = -i^*(ι_Y σ)` (`TauCeti.SmoothEmbedding.exists_liouvilleCollar_of_isContactForm`).

Milestone: *Contact-type hypersurfaces and Liouville collars*. -/
theorem SmoothEmbedding.exists_isContactForm_iff_exists_liouville [SecondCountableTopology M]
    (hσ : σ.IsSymplectic) (i : SmoothEmbedding J I ∞ Q M)
    (hdim : finrank ℝ E' + 1 = finrank ℝ E) :
    (∃ α : SmoothForm J Q ℝ 1, α.IsContactForm ∧
        mextDerivₗ J 1 α = -SmoothForm.mpullback i i.contMDiff σ) ↔
      ∃ U : Set M, IsOpen U ∧ range i ⊆ U ∧ ∃ Y : (x : M) → TangentSpace I x,
        ContMDiffOn I I.tangent (⊤ : ℕ∞) (T% Y) U ∧
          (∀ x ∈ U, mlieDerivForm Y σ.val x = σ.val x) ∧ IsTransverseAlong J Y i := by
  constructor
  · rintro ⟨α, hα, hdα⟩
    obtain ⟨U, hU, hiU, Y, hY, hYσ, hYi, -⟩ := i.exists_liouville_of_isContactForm hσ hα hdα
    exact ⟨U, hU, hiU, Y, hY, hYσ, hYi⟩
  · rintro ⟨U, hU, hiU, Y, hY, hYσ, hYi⟩
    obtain ⟨α, -, hα, hdα⟩ :=
      i.exists_isContactForm_eq_neg_mpullback_interior hσ hdim hU hiU hY hYσ hYi
    exact ⟨α, hα, hdα⟩

/-- **The Liouville collar of a prescribed contact form.** Let `σ` be a symplectic form on `M`,
`i : Q → M` a smooth embedding of codimension one, and `α` a contact form on `Q` with
`dα = -i^*σ`. Then there are an open neighbourhood `U` of the image of `i` and a vector field `Y`,
smooth and Liouville (`L_Y σ = σ`) on `U` and transverse along `i`, with `-i^*(ι_Y σ) = α`, whose
flow gives a Liouville collar (`TauCeti.IsLiouvilleCollar`) of `i` for `σ`, `Y` and `α`, from an
open neighbourhood `D` of `{0} × Q` onto an open set `V ⊆ U`. If `Q` is compact, `D` may be taken
to be a strip `(-ε, ε) × Q`.

Milestone: *Contact-type hypersurfaces and Liouville collars*. -/
theorem SmoothEmbedding.exists_liouvilleCollar_of_isContactForm [SecondCountableTopology M]
    (hσ : σ.IsSymplectic) (i : SmoothEmbedding J I ∞ Q M)
    (hdim : finrank ℝ E' + 1 = finrank ℝ E) {α : SmoothForm J Q ℝ 1} (hα : α.IsContactForm)
    (hdα : mextDerivₗ J 1 α = -SmoothForm.mpullback i i.contMDiff σ) :
    ∃ U : Set M, IsOpen U ∧ range i ⊆ U ∧ ∃ Y : (x : M) → TangentSpace I x,
      ContMDiffOn I I.tangent (⊤ : ℕ∞) (T% Y) U ∧
      (∀ x ∈ U, mlieDerivForm Y σ.val x = σ.val x) ∧ IsTransverseAlong J Y i ∧
      -mpullback J I i (RoughForm.interior Y σ.val) = α.val ∧
      (∃ D : Opens (ℝ × Q), ({0} ×ˢ univ : Set (ℝ × Q)) ⊆ D ∧
        ∃ (V : Opens M) (Φ : D ≃ₘ⟮𝓘(ℝ).prod J, I⟯ V) (φ : ℝ × Q → M),
          (V : Set M) ⊆ U ∧ IsLiouvilleCollar σ Y i α Φ φ) ∧
      (CompactSpace Q → ∃ ε > 0,
        ∃ (V : Opens M) (Φ : symmStrip Q ε ≃ₘ⟮𝓘(ℝ).prod J, I⟯ V) (φ : ℝ × Q → M),
          (V : Set M) ⊆ U ∧ IsLiouvilleCollar σ Y i α Φ φ) := by
  obtain ⟨U, hU, hiU, Y, hY, hYσ, hYi, hYα⟩ := i.exists_liouville_of_isContactForm hσ hα hdα
  exact ⟨U, hU, hiU, Y, hY, hYσ, hYi, hYα,
    i.exists_liouvilleCollar hσ hdim hU hiU hY hYσ hYi hYα.symm,
    fun _ ↦ i.exists_liouvilleCollar_of_compactSpace hσ hdim hU hiU hY hYσ hYi hYα.symm⟩

end TauCeti

end
