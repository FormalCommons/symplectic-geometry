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
import Mathlib.Geometry.Manifold.VectorField.Pullback
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.DifferentialForm.Interior
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

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
(Mathlib's pullback `VectorField.mpullback` along the inclusion) and of `ι_Y σ`, and the
resulting injective local diffeomorphism is made a diffeomorphism onto its image with Tau Ceti's
`IsLocalDiffeomorph.diffeomorphOfInjective`.

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

omit [I.Boundaryless] [T2Space M] in
/-- On the open submanifold `U`, the restriction `Z` of a field `Y` that is smooth and Liouville
on `U` is a smooth Liouville field of the restriction `β` of `ι_Y σ`, in Tau Ceti's sense
`ι_Z dβ = β`, and `dβ` is the restriction of `σ`. -/
private theorem exists_restrict_liouville (hσ : σ.IsClosed) (hU : IsOpen U)
    (hY : ContMDiffOn I I.tangent (⊤ : ℕ∞) (T% Y) U)
    (hYσ : ∀ x ∈ U, mlieDerivForm Y σ.val x = σ.val x) :
    ∃ (Z : (x : (⟨U, hU⟩ : Opens M)) → TangentSpace I x)
      (β : SmoothForm I (⟨U, hU⟩ : Opens M) ℝ 1), ContMDiff I I.tangent ∞ (T% Z) ∧
      (∀ x, mfderiv I I Subtype.val x (Z x) = Y x) ∧
      β.val = mpullback I I Subtype.val (RoughForm.interior Y σ.val) ∧
      mextDeriv β.val = mpullback I I Subtype.val σ.val ∧ (mextDeriv β.val).interior Z = β.val := by
  set U' : Opens M := ⟨U, hU⟩
  -- The field `Y` restricted to `U'`.
  let Z : (x : U') → TangentSpace I x := VectorField.mpullback I I Subtype.val Y
  have hval (x : U') : (mfderiv I I (Subtype.val : U' → M) x).IsInvertible :=
    ⟨_, (Manifold.mfderiv_subtype_val x).symm⟩
  have hZY (x : U') : mfderiv I I (Subtype.val : U' → M) x (Z x) = Y x := by
    simp only [Z, VectorField.mpullback_apply]
    exact (hval x).self_apply_inverse _
  have hZ : ContMDiff I I.tangent ∞ (T% Z) := fun x ↦ by
    have := ContMDiffWithinAt.mpullback_vectorField_preimage (n := ⊤) (hY x x.property)
      (contMDiff_subtypeVal x) (hval x) le_top
    rwa [show (Subtype.val : U' → M) ⁻¹' U = univ from eq_univ_of_forall fun y ↦ y.property,
      contMDiffWithinAt_univ] at this
  -- The primitive `ι_Y σ`, restricted to `U'`.
  have hβs : IsSmoothForm I ∞ (mpullback I I (Subtype.val : U' → M)
      (RoughForm.interior Y σ.val)) :=
    (isSmoothForm_def ∞ _).mpr fun x ↦ (RoughForm.contMDiffAt_interior
      (hY.contMDiffAt (hU.mem_nhds x.property)) (σ.contMDiff x)).mpullback_form
        (contMDiff_subtypeVal (n := ⊤) x) le_top
  let β : SmoothForm I U' ℝ 1 := ⟨_, hβs.mem_smoothBundleForms⟩
  -- Cartan's formula at each point of `U`: `d(ι_Y σ) = L_Y σ = σ`.
  have hdβ : mextDeriv β.val = mpullback I I (Subtype.val : U' → M) σ.val := by
    funext x
    have hYx := hY.contMDiffAt (hU.mem_nhds x.property)
    rw [← mpullback_mextDeriv_at ((contMDiff_subtypeVal x).of_le le_top)
      ((RoughForm.contMDiffAt_interior hYx (σ.contMDiff x)).of_le (by simp)),
      mpullback_subtype_val_apply, mpullback_subtype_val_apply,
      ← mlieDerivForm_eq_mextDeriv_interior_apply
        (σ.isSmoothForm.contMDiff.mdifferentiable (by simp) x)
        (hYx.mdifferentiableAt (by simp))
        (congrFun ((SmoothForm.isClosed_def σ).1 hσ) x), hYσ x x.property]
  refine ⟨Z, β, hZ, hZY, rfl, hdβ, funext fun x ↦ ?_⟩
  ext v
  rw [RoughForm.interior_apply, hdβ, mpullback_apply]
  simp only [β, mpullback_apply, RoughForm.interior_apply]
  congr 1
  ext k
  refine Fin.cases ?_ (fun j ↦ ?_) k
  · simpa [Manifold.mfderiv_subtype_val] using hZY x
  · simp only [Matrix.cons_val_succ]

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
      range i ⊆ V ∧ V ≤ U' ∧ (∀ p, (Φ p : M) = φ p) ∧ (∀ q, φ (0, q) = i q) ∧
      (∀ q, IsMIntegralCurveOn (fun t ↦ φ (t, q)) Y {t | (t, q) ∈ D}) ∧
      SmoothForm.mpullback Φ Φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : V → M) contMDiff_subtypeVal σ) =
        SmoothForm.mpullback (Subtype.val : D → ℝ × Q) contMDiff_subtypeVal
          (mextDerivₗ (𝓘(ℝ).prod J) 1 (-α).symplectization) ∧
      mpullback (𝓘(ℝ).prod J) I (fun p ↦ (Φ p : M)) (RoughForm.interior Y σ.val) =
        mpullback (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) (Subtype.val : D → ℝ × Q)
          (-α).symplectization.val := by
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
    ext v
    simp only [mpullback_apply, Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
      Manifold.tangentSpaceOpenEquiv_apply]
    exact (congrArg (γ (Ψ p.val))
      (funext fun j ↦ Manifold.mfderiv_comp_subtype_val_apply (v j))).trans
        (TauCeti.mpullback_apply Ψ γ p.val _).symm
  have hpb {k : ℕ} (γ : RoughForm (𝓘(ℝ).prod J) (ℝ × Q) ℝ k) (p : D) :
      mpullback (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) (Subtype.val : D → ℝ × Q) γ p = γ p.val :=
    mpullback_subtype_val_apply γ p
  refine ⟨hf.image, hf.diffeomorphOfInjective hfinj, fun p ↦ (Ψ p : M), ?_, ?_,
    hf.coe_diffeomorphOfInjective_apply hfinj, fun q ↦ ?_, fun q ↦ ?_, ?_, ?_⟩
  · rintro _ ⟨q, rfl⟩
    exact ⟨⟨(0, q), hD0 ⟨rfl, mem_univ q⟩⟩, by simp [g, Ψ, hιi]⟩
  · rintro _ ⟨p, rfl⟩
    exact (g p).property
  · simp [Ψ, hιi]
  · exact ((isMIntegralCurveOn_flowOf (hZ.of_le (by simp)) (ι q)).mono
      fun t ht ↦ hDZ ht).map_of_mfderiv_eq
      (fun _ _ ↦ (contMDiff_subtypeVal _).mdifferentiableAt one_ne_zero) (fun _ _ ↦ hZY _)
  · rw [SmoothForm.mpullback_mpullback_of_comp_eq _ _ hg.contMDiff contMDiff_subtypeVal hΦ]
    refine Subtype.ext (funext fun p ↦ ?_)
    simp only [SmoothForm.coe_mpullback]
    rw [← hdβ, hgpb, hpb, hpb, mpullback_flowOf_comp_mextDeriv_apply hZ hι hZβ (hDZ p.property),
      hια, mextDerivₗ_apply]
  · funext p
    rw [hpb, hΦ, mpullback_comp_at (hg.contMDiff.mdifferentiableAt (by simp))
      ((contMDiff_subtypeVal _).mdifferentiableAt one_ne_zero), ← hβ, hgpb, hpb,
      mpullback_flowOf_comp_apply_eq_symplectization hZ hι hZβ (hDZ p.property), hια]

/-- **Liouville collars of every small width.** Let `σ` be a symplectic form on `M`, `i : Q → M` a
smooth embedding of codimension one, `Y` a vector field, smooth and Liouville (`L_Y σ = σ`) on an
open neighbourhood `U` of the image of `i` and transverse along `i`, and `α = -i^*(ι_Y σ)` the
induced contact form. Then there is a positive continuous function `ε` on `Q` such that for every
open `D` with `{0} × Q ⊆ D ⊆ {(t, q) | |t| < ε q}` the flow of `Y` out of the hypersurface is a
diffeomorphism `Φ` from `D` onto an open `V` with `i(Q) ⊆ V ⊆ U`: there is `φ : ℝ × Q → M` with
`Φ = φ` on `D` and `φ(0, q) = i q`, each `t ↦ φ(t, q)` is an integral curve of `Y` on the slice of
`D` over `q`, `Φ` pulls `σ` back to `-d(eˢ α)`, and it pulls `ι_Y σ` back to `eˢ (-α)`, that is,
the primitive `λ = -ι_Y σ` to `eˢ α`. -/
theorem SmoothEmbedding.exists_pos_forall_liouvilleCollar [SecondCountableTopology M]
    (hσ : σ.IsSymplectic) (i : SmoothEmbedding J I ∞ Q M) (hdim : finrank ℝ E' + 1 = finrank ℝ E)
    (hU : IsOpen U) (hiU : range i ⊆ U) (hY : ContMDiffOn I I.tangent (⊤ : ℕ∞) (T% Y) U)
    (hYσ : ∀ x ∈ U, mlieDerivForm Y σ.val x = σ.val x) (hYi : IsTransverseAlong J Y i)
    {α : SmoothForm J Q ℝ 1} (hα : α.val = -mpullback J I i (RoughForm.interior Y σ.val)) :
    ∃ ε : C(Q, ℝ), (∀ q, 0 < ε q) ∧ ∀ D : Opens (ℝ × Q),
      ({0} ×ˢ univ : Set (ℝ × Q)) ⊆ D → (D : Set (ℝ × Q)) ⊆ {p | |p.1| < ε p.2} →
      ∃ (V : Opens M) (Φ : D ≃ₘ⟮𝓘(ℝ).prod J, I⟯ V) (φ : ℝ × Q → M),
        range i ⊆ V ∧ (V : Set M) ⊆ U ∧ (∀ p, (Φ p : M) = φ p) ∧ (∀ q, φ (0, q) = i q) ∧
        (∀ q, IsMIntegralCurveOn (fun t ↦ φ (t, q)) Y {t | (t, q) ∈ D}) ∧
        SmoothForm.mpullback Φ Φ.contMDiff
            (SmoothForm.mpullback (Subtype.val : V → M) contMDiff_subtypeVal σ) =
          SmoothForm.mpullback (Subtype.val : D → ℝ × Q) contMDiff_subtypeVal
            (mextDerivₗ (𝓘(ℝ).prod J) 1 (-α).symplectization) ∧
        mpullback (𝓘(ℝ).prod J) I (fun p ↦ (Φ p : M)) (RoughForm.interior Y σ.val) =
          mpullback (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) (Subtype.val : D → ℝ × Q)
            (-α).symplectization.val := by
  obtain ⟨Z, β, hZ, hZY, hβ, hdβ, hZβ⟩ := exists_restrict_liouville hσ.isClosed hU hY hYσ
  -- The hypersurface, as a map into `U`.
  let ι : Q → (⟨U, hU⟩ : Opens M) := fun q ↦ ⟨i q, hiU (mem_range_self q)⟩
  have hι : ContMDiff J I ∞ ι := (ContMDiff.subtypeVal_comp_iff _ ι).1 i.contMDiff
  have hια : SmoothForm.mpullback ι hι β = -α := by
    refine Subtype.ext (funext fun q ↦ ?_)
    ext v
    rw [SmoothForm.mpullback_apply, SmoothForm.neg_toRoughForm, Pi.neg_apply, hα, Pi.neg_apply,
      neg_neg, hβ, mpullback_apply, mpullback_apply]
    congr 1
    ext k
    rw [Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
      Manifold.tangentSpaceOpenEquiv_apply]
    exact (Manifold.mfderiv_subtype_val_comp_apply (I := I) (J := J) (f := ι) (v k)).symm
  have hcontact : (SmoothForm.mpullback ι hι β).IsContactForm := by
    obtain ⟨α₀, hα₀, hα₀c, -⟩ :=
      i.exists_isContactForm_eq_neg_mpullback_interior hσ hdim hU hiU hY hYσ hYi
    rw [hια, Subtype.ext (hα.trans hα₀.symm), SmoothForm.isContactForm_neg_iff]
    exact hα₀c
  -- Second countable Hausdorff manifolds are metrizable, as Tau Ceti's variable width needs.
  have := I.locallyCompactSpace
  have := ChartedSpace.locallyCompactSpace H M
  have := Manifold.metrizableSpace I M
  have : PseudoMetrizableSpace (⟨U, hU⟩ : Opens M) :=
    Topology.IsInducing.subtypeVal.pseudoMetrizableSpace
  have : PseudoMetrizableSpace Q := i.isEmbedding.isInducing.pseudoMetrizableSpace
  obtain ⟨ε, hε, hεD, hinj, hloc⟩ := exists_continuous_pos_injOn_flowOf_comp hZ hι hdim hZβ
    hcontact (i.isEmbedding.isInducing.codRestrict _)
  refine ⟨ε, hε, fun D hD0 hDε ↦ ?_⟩
  exact liouvilleCollar_of_injOn hZ hZY hβ hdβ hZβ hι (fun _ ↦ rfl) hια D hD0 (hDε.trans hεD)
    (hinj.mono hDε) fun p ↦ hloc ⟨p, hDε p.property⟩

/-- **The Liouville collar of a hypersurface.** Let `σ` be a symplectic form on `M`, `i : Q → M` a
smooth embedding of codimension one, `Y` a vector field, smooth and Liouville (`L_Y σ = σ`) on an
open neighbourhood `U` of the image of `i` and transverse along `i`, and `α = -i^*(ι_Y σ)` the
induced contact form. Then the flow of `Y` out of the hypersurface is a diffeomorphism `Φ` from an
open neighbourhood `D` of `{0} × Q` in `ℝ × Q` onto an open `V` with `i(Q) ⊆ V ⊆ U`: there is
`φ : ℝ × Q → M` with `Φ = φ` on `D` and `φ(0, q) = i q`, each `t ↦ φ(t, q)` is an integral curve of
`Y` on the slice of `D` over `q`, `Φ` pulls `σ` back to `-d(eˢ α)`, and it pulls `ι_Y σ` back to
`eˢ (-α)`, that is, the primitive `λ = -ι_Y σ` to `eˢ α`. -/
theorem SmoothEmbedding.exists_liouvilleCollar [SecondCountableTopology M]
    (hσ : σ.IsSymplectic) (i : SmoothEmbedding J I ∞ Q M) (hdim : finrank ℝ E' + 1 = finrank ℝ E)
    (hU : IsOpen U) (hiU : range i ⊆ U) (hY : ContMDiffOn I I.tangent (⊤ : ℕ∞) (T% Y) U)
    (hYσ : ∀ x ∈ U, mlieDerivForm Y σ.val x = σ.val x) (hYi : IsTransverseAlong J Y i)
    {α : SmoothForm J Q ℝ 1} (hα : α.val = -mpullback J I i (RoughForm.interior Y σ.val)) :
    ∃ D : Opens (ℝ × Q), ({0} ×ˢ univ : Set (ℝ × Q)) ⊆ D ∧
      ∃ (V : Opens M) (Φ : D ≃ₘ⟮𝓘(ℝ).prod J, I⟯ V) (φ : ℝ × Q → M),
        range i ⊆ V ∧ (V : Set M) ⊆ U ∧ (∀ p, (Φ p : M) = φ p) ∧ (∀ q, φ (0, q) = i q) ∧
        (∀ q, IsMIntegralCurveOn (fun t ↦ φ (t, q)) Y {t | (t, q) ∈ D}) ∧
        SmoothForm.mpullback Φ Φ.contMDiff
            (SmoothForm.mpullback (Subtype.val : V → M) contMDiff_subtypeVal σ) =
          SmoothForm.mpullback (Subtype.val : D → ℝ × Q) contMDiff_subtypeVal
            (mextDerivₗ (𝓘(ℝ).prod J) 1 (-α).symplectization) ∧
        mpullback (𝓘(ℝ).prod J) I (fun p ↦ (Φ p : M)) (RoughForm.interior Y σ.val) =
          mpullback (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) (Subtype.val : D → ℝ × Q)
            (-α).symplectization.val := by
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
      range i ⊆ V ∧ (V : Set M) ⊆ U ∧ (∀ p, (Φ p : M) = φ p) ∧ (∀ q, φ (0, q) = i q) ∧
      (∀ q, IsMIntegralCurveOn (fun t ↦ φ (t, q)) Y {t | (t, q) ∈ symmStrip Q ε}) ∧
      SmoothForm.mpullback Φ Φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : V → M) contMDiff_subtypeVal σ) =
        SmoothForm.mpullback (Subtype.val : symmStrip Q ε → ℝ × Q) contMDiff_subtypeVal
          (mextDerivₗ (𝓘(ℝ).prod J) 1 (-α).symplectization) ∧
      mpullback (𝓘(ℝ).prod J) I (fun p ↦ (Φ p : M)) (RoughForm.interior Y σ.val) =
        mpullback (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) (Subtype.val : symmStrip Q ε → ℝ × Q)
          (-α).symplectization.val := by
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
flow is a Liouville collar: a diffeomorphism `Φ` from an open neighbourhood `D` of `{0} × Q` onto
an open `V` with `i(Q) ⊆ V ⊆ U`, given by a map `φ` with `φ(0, q) = i q` whose lines
`t ↦ φ(t, q)` are integral curves of `Y`, pulling `σ` back to `-d(eˢ α)` and `ι_Y σ` back to
`eˢ (-α)`. If `Q` is compact, `D` may be taken to be a strip `(-ε, ε) × Q`.

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
          range i ⊆ V ∧ (V : Set M) ⊆ U ∧ (∀ p, (Φ p : M) = φ p) ∧ (∀ q, φ (0, q) = i q) ∧
          (∀ q, IsMIntegralCurveOn (fun t ↦ φ (t, q)) Y {t | (t, q) ∈ D}) ∧
          SmoothForm.mpullback Φ Φ.contMDiff
              (SmoothForm.mpullback (Subtype.val : V → M) contMDiff_subtypeVal σ) =
            SmoothForm.mpullback (Subtype.val : D → ℝ × Q) contMDiff_subtypeVal
              (mextDerivₗ (𝓘(ℝ).prod J) 1 (-α).symplectization) ∧
          mpullback (𝓘(ℝ).prod J) I (fun p ↦ (Φ p : M)) (RoughForm.interior Y σ.val) =
            mpullback (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) (Subtype.val : D → ℝ × Q)
              (-α).symplectization.val) ∧
      (CompactSpace Q → ∃ ε > 0,
        ∃ (V : Opens M) (Φ : symmStrip Q ε ≃ₘ⟮𝓘(ℝ).prod J, I⟯ V) (φ : ℝ × Q → M),
          range i ⊆ V ∧ (V : Set M) ⊆ U ∧ (∀ p, (Φ p : M) = φ p) ∧ (∀ q, φ (0, q) = i q) ∧
          (∀ q, IsMIntegralCurveOn (fun t ↦ φ (t, q)) Y {t | (t, q) ∈ symmStrip Q ε}) ∧
          SmoothForm.mpullback Φ Φ.contMDiff
              (SmoothForm.mpullback (Subtype.val : V → M) contMDiff_subtypeVal σ) =
            SmoothForm.mpullback (Subtype.val : symmStrip Q ε → ℝ × Q) contMDiff_subtypeVal
              (mextDerivₗ (𝓘(ℝ).prod J) 1 (-α).symplectization) ∧
          mpullback (𝓘(ℝ).prod J) I (fun p ↦ (Φ p : M)) (RoughForm.interior Y σ.val) =
            mpullback (𝓘(ℝ).prod J) (𝓘(ℝ).prod J) (Subtype.val : symmStrip Q ε → ℝ × Q)
              (-α).symplectization.val) := by
  obtain ⟨U, hU, hiU, Y, hY, hYσ, hYi, hYα⟩ := i.exists_liouville_of_isContactForm hσ hα hdα
  exact ⟨U, hU, hiU, Y, hY, hYσ, hYi, hYα,
    i.exists_liouvilleCollar hσ hdim hU hiU hY hYσ hYi hYα.symm,
    fun _ ↦ i.exists_liouvilleCollar_of_compactSpace hσ hdim hU hiU hY hYσ hYi hYα.symm⟩

end TauCeti

end
