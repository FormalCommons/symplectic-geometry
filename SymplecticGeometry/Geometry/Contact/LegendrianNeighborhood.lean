/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Immersion.Transverse
public import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.Riemannian.Injective
public import TauCeti.Geometry.Contact.Contactization
public import TauCeti.Geometry.Contact.Flat
public import TauCeti.Geometry.Contact.Isotropic
public import TauCeti.Geometry.Contact.Pullback
public import TauCeti.Geometry.Contact.Reeb
public import TauCeti.Geometry.Manifold.Flow.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.ZeroSection
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Normal
import SymplecticGeometry.Geometry.Contact.Contactization
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.IsManifold.Basic
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Opens
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ZeroSection
import SymplecticGeometry.Geometry.Symplectic.Neighborhood.Lagrangian
import SymplecticGeometry.Topology.Sets.Opens.Basic
import TauCeti.Geometry.Contact.LegendrianNormal
import TauCeti.Geometry.Contact.Slice
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Section
import TauCeti.Geometry.Manifold.TubularNeighborhood.RelativePoincare
import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Graph
import TauCeti.Geometry.Symplectic.Manifold.Opens
import TauCeti.Topology.FiberBundle.Countable
import TauCeti.Topology.FiberBundle.Separation

/-!
# The Legendrian neighbourhood theorem

Let `α` be a contact form on `M` and `f : L → M` a Legendrian embedding, so that
`dim M = 2 n + 1` and `dim L = n`. This file proves that a neighbourhood of `f(L)` is strictly
contactomorphic to an open set around the zero section of `T^* L × ℝ`, with the form
`λ_can - dz`, by a diffeomorphism that is `f` on the zero section
(`TauCeti.IsLegendrianEmbedding.exists_diffeomorph_opens_mpullback_eq_neg_contactization`). It
follows the route through a hypersurface of McDuff–Salamon, Exercise 3.5.22(i). Neither
compactness of `L` nor closedness of `f(L)` is assumed. Nor is `α` assumed to be a contact
form: a one-form whose kernel has a Legendrian immersion is one
(`TauCeti.IsLegendrianImmersion.isContactForm`).

## A slice through `f(L)`

The first step builds a hypersurface through `f(L)`, tangent to `ker α` along `f(L)` and
transverse to the Reeb field near it, parametrized by the cotangent bundle `T^* L`
(`TauCeti.IsLegendrianEmbedding.exists_contactSlice`).

The construction:

* At `q ∈ L`, Tau Ceti identifies the normal space `ν_q = T_(f q) M ⧸ df_q(T_q L)` with
  `T_q^* L × ℝ` by `[w] ↦ (dα(df_q ·, w), α w)`
  (`TauCeti.SmoothEmbedding.normalSpaceEquivOfIsLegendrianImmersion`), smoothly in `q`
  (`TauCeti.SmoothEmbedding.contMDiff_normalSpaceEquivOfIsLegendrianImmersion`). Composing its
  inverse with `p ↦ (p, 0)` gives a smooth fibrewise injection `j : T^* L → ν` whose image lies in
  `ker α ⧸ df(T L)`.
* A smooth injective map `T : ν → M`, equal to `f` on the zero section, whose differential
  sends the vertical vector `v` at `0_q` to a vector of normal class `c q • v` with `c q > 0`,
  comes from `TauCeti.SmoothEmbedding.exists_contMDiff_injective_normalBundle`.
* The slice is `ι = T ∘ j`. At `0_q` its differential is `df_q` horizontally and lands in
  `ker α` vertically, and it is injective; as `T_(0_q)(T^* L)` and `ker α_(f q)` both have
  dimension `2 n`, its range is `ker α_(f q)`. So the Reeb field is not in it, and the set where
  the differential of `ι` is injective with the Reeb field outside its range is an open
  neighbourhood of the zero section (`ContMDiffAt.eventually_injective_mfderiv_and_notMem_range`).

The identification of the normal bundle with `T^* L × ℝ` is taken from Tau Ceti's file
`TauCeti/Geometry/Contact/LegendrianNormal.lean`.
The splitting of the differential of `T ∘ j` along the zero section into a horizontal and a
vertical part follows the proof of Tau Ceti's
`TauCeti.SmoothEmbedding.mfderiv_normalExp_zeroSection_apply`.

## The neighbourhood theorem

On the open set `N` where the slice `ι` is an immersion transverse to the Reeb field, `-d(ι^* α)`
is symplectic (`TauCeti.SmoothForm.IsContactForm.isSymplectic_neg_mextDerivₗ_mpullback`), and
the zero section is Lagrangian for it, since `f^* α = 0`. Then:

* the Lagrangian neighbourhood theorem
  `TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.exists_symplectomorphism_cotangent`,
  applied on `N`, gives a map `κ` from an open set around the zero section of `T^* L` into `M`,
  equal to `f` on the zero section, with `d(κ^* α) = dλ_can`;
* the closed form `κ^* α - λ_can` vanishes along the zero section, so the relative Poincaré lemma
  `TauCeti.SmoothEmbedding.exists_isSmoothForm_relative_primitive` writes it as `dg` near the zero
  section, with `g = 0` there;
* the map `Φ (a, z) = φ^R_{-z - g a} (κ a)`, with `φ^R` the local Reeb flow, pulls `α` back to
  `λ_can - dz` wherever it is defined
  (`TauCeti.SmoothForm.IsContactForm.mpullback_flowOf_neg_sub_apply`, for any map `κ` with
  `κ^* α = β + dg`), since the Reeb flow out of `κ` pulls `α` back to `dt + κ^* α`
  (`TauCeti.mpullback_flowOf_comp_apply_eq_contactization`); and it is a local diffeomorphism
  there, since `d(κ^* α)` is nondegenerate
  (`TauCeti.isLocalDiffeomorphAt_flowOf_comp_of_nondegenerate`);
* `Φ` is `f` on the zero section, which `f` embeds, so it restricts to a diffeomorphism from a
  neighbourhood of the zero section onto an open set
  (`IsLocalDiffeomorphOn.exists_partialDiffeomorph_near_section`). Its source is an open subset
  of `W × ℝ`, with `W` an open subset of an open subset of `T^* L`. The map `(w, z) ↦ (w, z)`,
  an injective local diffeomorphism, moves it to an open subset of `T^* L × ℝ`
  (`PartialDiffeomorph.exists_diffeomorph_opens_mpullback_eq`), and pulls
  `-λ_can.contactization` back to minus the contactization form of `λ_can` restricted to `W`
  (`TauCeti.SmoothForm.mpullback_prodMap_contactization`).

The last two steps adapt the proof of Tau Ceti's
`TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart`, which straightens a contact form
along the Reeb flow out of a symplectic slice after a change of the time coordinate, here along a
whole Legendrian submanifold instead of near a point. The flow identity
`TauCeti.SmoothForm.IsContactForm.mpullback_flowOf_neg_sub_apply` follows the steps of the private
lemma `mpullback_flowOf_comp_contactizationShift_comp_reassoc` of that proof. An empty `L` is
handled with the empty open sets (`TopologicalSpace.Opens.isEmpty_bot`).

## Main results

* `TauCeti.IsLegendrianImmersion.finrank_prod_dual_add_one`: the model of `T^* L` has one
  dimension less than that of `M`.
* `TauCeti.IsLegendrianEmbedding.exists_contactSlice`: a smooth injective map `ι : T^* L → M`
  with `ι (0_q) = f q`, which is an immersion transverse to the Reeb field on some open set
  containing the zero section, and whose differential at `0_q` has range `ker α_(f q)`.
* `TauCeti.SmoothForm.IsContactForm.isSymplectic_neg_mextDerivₗ_mpullback`: on a hypersurface
  that is everywhere an immersion transverse to the Reeb field, `-d(ι^* α)` is symplectic.
* `TauCeti.SmoothForm.IsContactForm.mpullback_flowOf_neg_sub_apply`: if `κ^* α = β + dg`, the map
  `(s, z) ↦ φ^R_{-z - g s} (κ s)` pulls `α` back to minus the contactization form of `β`.
* `TauCeti.IsLegendrianEmbedding.exists_diffeomorph_opens_mpullback_eq_neg_contactization`: the
  Legendrian neighbourhood theorem.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §3.5, Example 3.5.6 and Exercise 3.5.22(i).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics
  109, Cambridge University Press, 2008, §2.5 (cited by Tau Ceti's proof that the last steps
  adapt).
-/

public section

noncomputable section

open Bundle Function Module Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace TauCeti.IsLegendrianEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {E' H' L : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace L] [ChartedSpace H' L]
  [IsManifold J ∞ L]
  {α : SmoothForm I M ℝ 1}

private theorem infty_ne_zero : (∞ : ℕ∞ω) ≠ 0 := by simp

omit [IsManifold J ∞ L] in
/-- For a Legendrian immersion `f : L → M`, the model `E' × E'^*` of the cotangent bundle of `L`
has dimension one less than the model `E` of `M`. -/
theorem _root_.TauCeti.IsLegendrianImmersion.finrank_prod_dual_add_one
    {D : Π x : M, Submodule ℝ (TangentSpace I x)} {f : L → M}
    (hf : IsLegendrianImmersion J D f) : finrank ℝ (E' × (E' →L[ℝ] ℝ)) + 1 = finrank ℝ E := by
  rw [finrank_prod, ContinuousLinearMap.dual_finrank_eq, ← hf.two_mul_finrank_add_one]
  ring

variable {g : SmoothEmbedding J I ∞ L M}

/-- The fibrewise injection `p ↦ e⁻¹ (p, 0)` of `T_q^* L` into the normal space, for `e` the
identification `TauCeti.SmoothEmbedding.normalSpaceEquivOfIsLegendrianImmersion`. -/
private def cotangentToNormal (hf : IsLegendrianEmbedding J α.kerDistribution g) (q : L) :
    (TangentSpace J q →L[ℝ] ℝ) →L[ℝ] g.NormalSpace q infty_ne_zero :=
  (g.normalSpaceEquivOfIsLegendrianImmersion hf.toIsLegendrianImmersion infty_ne_zero
    q).symm.toContinuousLinearMap ∘L ContinuousLinearMap.inl ℝ _ ℝ

omit [FiniteDimensional ℝ E'] in
private theorem normalSpaceEquivOfIsLegendrianImmersion_cotangentToNormal
    (hf : IsLegendrianEmbedding J α.kerDistribution g) (q : L) (p : TangentSpace J q →L[ℝ] ℝ) :
    g.normalSpaceEquivOfIsLegendrianImmersion hf.toIsLegendrianImmersion infty_ne_zero q
      (cotangentToNormal hf q p) = (p, 0) := by
  simp [cotangentToNormal]

omit [FiniteDimensional ℝ E'] in
private theorem cotangentToNormal_injective (hf : IsLegendrianEmbedding J α.kerDistribution g)
    (q : L) : Injective (cotangentToNormal hf q) := fun p p' h ↦ by
  have := congrArg (fun v ↦ (g.normalSpaceEquivOfIsLegendrianImmersion
    hf.toIsLegendrianImmersion infty_ne_zero q v).1) h
  simpa only [normalSpaceEquivOfIsLegendrianImmersion_cotangentToNormal] using this

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The bundle map `T^* L → ν` induced by `cotangentToNormal` is smooth. -/
private theorem contMDiff_cotangentToNormal (hf : IsLegendrianEmbedding J α.kerDistribution g)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') :
    letI := g.normalSpaceFiberBundle infty_ne_zero hdim
    ContMDiff (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, P)) ∞
      (fun p : CotangentBundle J L ↦ TotalSpace.mk' P
        (E := fun q ↦ g.NormalSpace q infty_ne_zero) p.proj
        (cotangentToNormal hf p.proj p.snd)) := by
  let := g.normalSpaceFiberBundle infty_ne_zero hdim
  let := g.normalSpaceVectorBundle infty_ne_zero hdim
  have := g.normalSpaceContMDiffVectorBundle (m := ∞) infty_ne_zero (by simp) hdim
  exact (contMDiff_bundle_symm _
    (g.contMDiff_normalSpaceEquivOfIsLegendrianImmersion hf.toIsLegendrianImmersion
      infty_ne_zero (by simp) (by simp) hdim)).comp
    (Bundle.Prod.contMDiff_inl (E₂ := Trivial L ℝ))

/-- The differential of `T ∘ j` along the zero section, for a smooth map `T` of the normal bundle
which is `g` on its zero section and `j` the bundle map of `cotangentToNormal`: horizontally
it is `dg`, vertically it is the vertical differential of `T`. -/
private theorem mfderiv_comp_cotangentToNormal (hf : IsLegendrianEmbedding J α.kerDistribution g)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') :
    letI := g.normalSpaceFiberBundle infty_ne_zero hdim
    letI := g.normalSpaceVectorBundle infty_ne_zero hdim
    ∀ T : TotalSpace P (fun q ↦ g.NormalSpace q infty_ne_zero) → M,
      ContMDiff (J.prod 𝓘(ℝ, P)) I ∞ T → (∀ q, T (zeroSection P _ q) = g q) →
      ∀ (q : L) (u : TangentSpace J q) (p : TangentSpace J q →L[ℝ] ℝ),
        mfderiv (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I
            (fun p : CotangentBundle J L ↦ T ⟨p.proj, cotangentToNormal hf p.proj p.snd⟩)
            (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q)
            ((Bundle.zeroSectionTangentEquiv (I := J) q).symm (u, 0)) = mfderiv J I g q u ∧
        mfderiv (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I
            (fun p : CotangentBundle J L ↦ T ⟨p.proj, cotangentToNormal hf p.proj p.snd⟩)
            (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q)
            ((Bundle.zeroSectionTangentEquiv (I := J) q).symm (0, p)) =
          mfderiv (J.prod 𝓘(ℝ, P)) I T (zeroSection P _ q)
            ((Bundle.zeroSectionTangentEquiv (I := J) q).symm
              (0, cotangentToNormal hf q p)) := by
  let := g.normalSpaceFiberBundle infty_ne_zero hdim
  let := g.normalSpaceVectorBundle infty_ne_zero hdim
  intro T hT hT0 q u p
  have hι : ContMDiff (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I ∞
      (fun p : CotangentBundle J L ↦ T ⟨p.proj, cotangentToNormal hf p.proj p.snd⟩) :=
    hT.comp (contMDiff_cotangentToNormal hf hdim)
  refine ⟨?_, ?_⟩
  · -- Horizontally: the composite is `g` on the zero section.
    have hfun : (fun p : CotangentBundle J L ↦ T ⟨p.proj, cotangentToNormal hf p.proj p.snd⟩) ∘
        zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) = g := by
      funext q
      rw [Function.comp_apply, ← hT0 q]
      exact congrArg T (congrArg (TotalSpace.mk' P q) (map_zero _))
    have h := mfderiv_comp_apply q ((hι _).mdifferentiableAt (by simp))
      (mdifferentiableAt_zeroSection ℝ _) u
    rw [hfun] at h
    rw [Bundle.zeroSectionTangentEquiv_symm_inl, h]
  · -- Vertically: the composite maps the line `t ↦ t • p` to the line `t ↦ t • j p`.
    rw [Bundle.zeroSectionTangentEquiv_symm_inr, Bundle.zeroSectionTangentEquiv_symm_inr]
    let line : ℝ → CotangentBundle J L := fun t ↦ ⟨q, t • p⟩
    let line' : ℝ → TotalSpace P (fun q ↦ g.NormalSpace q infty_ne_zero) :=
      fun t ↦ ⟨q, t • cotangentToNormal hf q p⟩
    have hl : ContMDiff 𝓘(ℝ) (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) 1 line :=
      contMDiff_id.smul_totalSpace (contMDiff_const (c := (⟨q, p⟩ : CotangentBundle J L)))
    have hl' : ContMDiff 𝓘(ℝ) (J.prod 𝓘(ℝ, P)) 1 line' :=
      contMDiff_id.smul_totalSpace (contMDiff_const (c := (⟨q, cotangentToNormal hf q p⟩ :
        TotalSpace P (fun q ↦ g.NormalSpace q infty_ne_zero))))
    have h1 := mfderiv_comp_apply_of_eq (0 : ℝ)
      ((hι (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q)).mdifferentiableAt
        (by simp)) (hl.mdifferentiableAt one_ne_zero) (by simp [line, zeroSection]) (1 : ℝ)
    have h2 := mfderiv_comp_apply_of_eq (0 : ℝ)
      ((hT (zeroSection P (fun q ↦ g.NormalSpace q infty_ne_zero) q)).mdifferentiableAt
        (by simp)) (hl'.mdifferentiableAt one_ne_zero) (by simp [line', zeroSection]) (1 : ℝ)
    have hfun : (fun p : CotangentBundle J L ↦ T ⟨p.proj, cotangentToNormal hf p.proj p.snd⟩) ∘
        line = T ∘ line' := by
      funext t
      exact congrArg T (congrArg (TotalSpace.mk' P q) (map_smul _ t p))
    rw [← h1, hfun, h2]

/-- The differential at `0_q` of `T ∘ j`, for a map `T` of the normal bundle and `j` the bundle
map of `cotangentToNormal`, with its values read in the tangent space of `M` at `g q`. When `T` is
`g` on the zero section, as below, this is the tangent space at the base point of the image. -/
private def sliceDeriv (hf : IsLegendrianEmbedding J α.kerDistribution g)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') :
    letI := g.normalSpaceFiberBundle infty_ne_zero hdim
    letI := g.normalSpaceVectorBundle infty_ne_zero hdim
    (TotalSpace P (fun q ↦ g.NormalSpace q infty_ne_zero) → M) → ∀ q : L,
      TangentSpace (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ))
          (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q) →L[ℝ]
        TangentSpace I (g q) :=
  letI := g.normalSpaceFiberBundle infty_ne_zero hdim
  letI := g.normalSpaceVectorBundle infty_ne_zero hdim
  fun T q ↦ mfderiv (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I
    (fun p : CotangentBundle J L ↦ T ⟨p.proj, cotangentToNormal hf p.proj p.snd⟩)
    (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q)

omit [FiniteDimensional ℝ E'] [FiniteDimensional ℝ P] in
private theorem sliceDeriv_apply (hf : IsLegendrianEmbedding J α.kerDistribution g)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') :
    letI := g.normalSpaceFiberBundle infty_ne_zero hdim
    letI := g.normalSpaceVectorBundle infty_ne_zero hdim
    ∀ (T : TotalSpace P (fun q ↦ g.NormalSpace q infty_ne_zero) → M) (q : L) (X),
      sliceDeriv hf hdim T q X = mfderiv (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I
        (fun p : CotangentBundle J L ↦ T ⟨p.proj, cotangentToNormal hf p.proj p.snd⟩)
        (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q) X :=
  fun _ _ _ ↦ rfl

/-- For a map `T` as in `TauCeti.SmoothEmbedding.exists_contMDiff_injective_normalBundle`, the
differential of `T ∘ j` at `0_q` takes values in `ker α` and is injective. -/
private theorem sliceDeriv_mem_kerDistribution_and_injective
    (hf : IsLegendrianEmbedding J α.kerDistribution g)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') :
    letI := g.normalSpaceFiberBundle infty_ne_zero hdim
    letI := g.normalSpaceVectorBundle infty_ne_zero hdim
    ∀ T : TotalSpace P (fun q ↦ g.NormalSpace q infty_ne_zero) → M,
      ContMDiff (J.prod 𝓘(ℝ, P)) I ∞ T → (∀ q, T (zeroSection P _ q) = g q) →
      ∀ c : L → ℝ, (∀ q, 0 < c q) → (∀ q (v : g.NormalSpace q infty_ne_zero),
        g.normalClass q infty_ne_zero (mfderiv (J.prod 𝓘(ℝ, P)) I T (zeroSection P _ q)
          ((Bundle.zeroSectionTangentEquiv (I := J) q).symm (0, v))) = c q • v) →
      ∀ q, (∀ X, sliceDeriv hf hdim T q X ∈ α.kerDistribution (g q)) ∧
        Injective (sliceDeriv hf hdim T q) := by
  let := g.normalSpaceFiberBundle infty_ne_zero hdim
  let := g.normalSpaceVectorBundle infty_ne_zero hdim
  intro T hT hT0 c hc hTd q
  set D := sliceDeriv hf hdim T q
  set e := (Bundle.zeroSectionTangentEquiv (I := J)
    (F := E' →L[ℝ] ℝ) (V := fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q).symm
  set e' := (Bundle.zeroSectionTangentEquiv (I := J) (F := P)
    (V := fun q ↦ g.NormalSpace q infty_ne_zero) q).symm
  have hd := mfderiv_comp_cotangentToNormal hf hdim T hT hT0 q
  have hhor (u : TangentSpace J q) : D (e (u, 0)) = mfderiv J I g q u :=
    (sliceDeriv_apply hf hdim T q _).trans (hd u 0).1
  have hver (p : TangentSpace J q →L[ℝ] ℝ) : D (e (0, p)) = mfderiv (J.prod 𝓘(ℝ, P)) I T
      (zeroSection P _ q) (e' (0, cotangentToNormal hf q p)) :=
    (sliceDeriv_apply hf hdim T q _).trans (hd 0 p).2
  -- `D` splits into `dg` horizontally and a vertical part of normal class `c q • j p`.
  have hsplit (u : TangentSpace J q) (p : TangentSpace J q →L[ℝ] ℝ) :
      D (e (u, p)) = mfderiv J I g q u + D (e (0, p)) := by
    rw [← hhor, ← map_add, ← map_add, Prod.mk_add_mk,
      add_zero, zero_add]
  have hvert (p : TangentSpace J q →L[ℝ] ℝ) :
      g.normalClass q infty_ne_zero (D (e (0, p))) = c q • cotangentToNormal hf q p := by
    rw [hver, hTd]
  have hαvert (p : TangentSpace J q →L[ℝ] ℝ) : α.val (g q) ![D (e (0, p))] = 0 := by
    have h := g.normalSpaceEquivOfIsLegendrianImmersion_normalClass hf.toIsLegendrianImmersion
      infty_ne_zero q (D (e (0, p)))
    rw [hvert, map_smul, normalSpaceEquivOfIsLegendrianImmersion_cotangentToNormal] at h
    simpa using (congrArg Prod.snd h).symm
  refine ⟨fun X ↦ ?_, (injective_iff_map_eq_zero D).2 fun X hX ↦ ?_⟩
  · obtain ⟨⟨u, p⟩, rfl⟩ := e.surjective X
    rw [SmoothForm.mem_kerDistribution, hsplit, ← SmoothForm.degreeOneEquiv_apply_apply_vec,
      map_add, SmoothForm.degreeOneEquiv_apply_apply_vec,
      SmoothForm.degreeOneEquiv_apply_apply_vec, hαvert,
      SmoothForm.mem_kerDistribution.1 (hf.isHorizontalMap.mfderiv_mem q u), add_zero]
  · obtain ⟨⟨u, p⟩, rfl⟩ := e.surjective X
    rw [hsplit] at hX
    have hcl := congrArg (g.normalClass q infty_ne_zero) hX
    rw [map_add, hvert, SmoothEmbedding.normalClass_mfderiv, zero_add, map_zero,
      smul_eq_zero] at hcl
    obtain rfl : p = 0 := cotangentToNormal_injective hf q
      ((hcl.resolve_left (hc q).ne').trans (map_zero _).symm)
    rw [Prod.mk_zero_zero, map_zero, map_zero, add_zero] at hX
    obtain rfl : u = 0 := g.isImmersion.mfderiv_injective infty_ne_zero q
      (hX.trans (map_zero _).symm)
    rw [Prod.mk_zero_zero, map_zero]

/-- **A slice through a Legendrian submanifold.** Let `f : L → M` be a Legendrian embedding for
the kernel of a one-form `α`, which is then a contact form, between boundaryless manifolds, `M`
Hausdorff and second countable. There are a smooth injective map `ι : T^* L → M` with
`ι (0_q) = f q`, and an open neighbourhood `N` of the zero section, such that at each point of
`N` the differential of `ι` is injective and the Reeb vector field of `α` is not in its range,
and at `0_q` the range of the differential is the contact hyperplane `ker α` at `f q`. -/
theorem exists_contactSlice [I.Boundaryless] [J.Boundaryless] [T2Space M]
    [SecondCountableTopology M] {f : L → M}
    (hf : IsLegendrianEmbedding J α.kerDistribution f) :
    ∃ (ι : CotangentBundle J L → M) (N : Set (CotangentBundle J L)),
      ContMDiff (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I ∞ ι ∧ Injective ι ∧ IsOpen N ∧
      (∀ q, zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q ∈ N) ∧
      (∀ q, ι (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q) = f q) ∧
      (∀ p ∈ N, Injective (mfderiv (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I ι p) ∧
        α.reebVectorField (ι p) ∉ (mfderiv (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I ι p).range) ∧
      ∀ q, (mfderiv (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I ι
        (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q)).range =
          α.kerDistribution (f q) := by
  have hα := hf.isContactForm
  let g : SmoothEmbedding J I ∞ L M := .ofIsSmoothEmbedding f hf.isSmoothEmbedding
  have hg : ⇑g = f := SmoothEmbedding.coe_ofIsSmoothEmbedding f _
  have hf' : IsLegendrianEmbedding J α.kerDistribution g := hg ▸ hf
  let P := EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ E'))
  have hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E' := finrank_euclideanSpace_fin
  let := g.normalSpaceFiberBundle infty_ne_zero hdim
  let := g.normalSpaceVectorBundle infty_ne_zero hdim
  obtain ⟨T, hT, hTinj, hT0, c, hc, hTd⟩ := g.exists_contMDiff_injective_normalBundle hdim
  let ι : CotangentBundle J L → M := fun p ↦ T ⟨p.proj, cotangentToNormal hf' p.proj p.snd⟩
  have hι : ContMDiff (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I ∞ ι :=
    hT.comp (contMDiff_cotangentToNormal hf' hdim)
  set Z0 := zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ)
  have hιinj : Injective ι := by
    rintro ⟨q, a⟩ ⟨q', a'⟩ h
    obtain ⟨rfl, h2⟩ := TotalSpace.mk.inj (hTinj h)
    cases cotangentToNormal_injective hf' q (eq_of_heq h2)
    rfl
  have hι0 (q : L) : ι (Z0 q) = g q := by
    rw [← hT0 q]
    exact congrArg T (congrArg (TotalSpace.mk' P q) (map_zero _))
  have hD := sliceDeriv_mem_kerDistribution_and_injective hf' hdim T hT hT0 c hc hTd
  -- The differential of `ι` at `0_q`, with values in the tangent space at `g q = ι 0_q`, so that
  -- its range and `ker α` are subspaces of the same type.
  have hrange (q : L) : (sliceDeriv hf' hdim T q).range = α.kerDistribution (g q) := by
    have : FiniteDimensional ℝ (TangentSpace I (g q)) := inferInstanceAs (FiniteDimensional ℝ E)
    refine Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨X, rfl⟩; exact (hD q).1 X) ?_
    rw [LinearMap.finrank_range_of_inj (hD q).2, finrank_tangentSpace]
    have h1 := hα.finrank_kerDistribution_add_one (g q)
    have h2 := hf.finrank_prod_dual_add_one
    omega
  let N := {p | Injective (mfderiv (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I ι p) ∧
    α.reebVectorField (ι p) ∉ (mfderiv (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I ι p).range}
  have hN : IsOpen N := isOpen_iff_mem_nhds.2 fun p hp ↦
    (hι p).eventually_injective_mfderiv_and_notMem_range (by simp)
      hα.contMDiff_reebVectorField.continuous.continuousAt hp.1 hp.2
  refine ⟨ι, N, hι, hιinj, hN, fun q ↦ ⟨(hD q).2, fun h ↦ ?_⟩,
    fun q ↦ (hι0 q).trans (congrFun hg q), fun p hp ↦ hp, fun q ↦ (hrange q).trans (hg ▸ rfl)⟩
  obtain ⟨X, hX⟩ := h
  have h := (hD q).1 X
  rw [show sliceDeriv hf' hdim T q X = α.reebVectorField (ι (Z0 q)) from
    (sliceDeriv_apply hf' hdim T q X).trans hX, hι0 q] at h
  exact hα.reebVectorField_notMem_kerDistribution (g q) h

end TauCeti.IsLegendrianEmbedding

namespace TauCeti.SmoothForm.IsContactForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  [IsManifold J ∞ S]
  {α : SmoothForm I M ℝ 1}

/-- Let `ι : S → M` be a smooth map from a manifold of one dimension less which is, at every point,
an immersion whose image does not contain the Reeb vector of a contact form `α`. Then the two-form
`-d(ι^* α)` on `S` is symplectic. -/
theorem isSymplectic_neg_mextDerivₗ_mpullback (hα : α.IsContactForm)
    (hdim : finrank ℝ E' + 1 = finrank ℝ E) {ι : S → M} (hι : ContMDiff J I ∞ ι)
    (hιs : ∀ s, Injective (mfderiv J I ι s) ∧ α.reebVectorField (ι s) ∉ (mfderiv J I ι s).range) :
    SmoothTwoForm.IsSymplectic (-mextDerivₗ J 1 (SmoothForm.mpullback ι hι α)) :=
  ⟨(SmoothForm.isClosed_mextDerivₗ _).neg, SmoothTwoForm.IsNondegenerate.neg <|
    SmoothTwoForm.isNondegenerate_iff_separatingLeft.2 fun s v hv ↦
      (hα.nondegenerate_bilinFormAt_mextDerivₗ_mpullback hι hdim (hιs s).1 (hιs s).2).1 v
        fun w ↦ by rw [SmoothForm.bilinFormAt_apply]; exact hv w⟩

variable {ES HS S : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [TopologicalSpace HS]
  {IS : ModelWithCorners ℝ ES HS} [TopologicalSpace S] [ChartedSpace HS S] [IsManifold IS ∞ S]

/-- Let `κ : S → M` be a smooth map and `g` a smooth function on `S` with `κ^* α = β + dg`, for a
contact form `α` and a one-form `β` on `S`. At each point `(s, z)` of `S × ℝ` where the Reeb flow
`φ^R` of `α` is defined for the time `-z - g s` from `κ s`, the map `(s, z) ↦ φ^R_{-z - g s} (κ s)`
pulls `α` back to `-(dz - β)`, minus the contactization form of `β`. -/
theorem mpullback_flowOf_neg_sub_apply [I.Boundaryless] [T2Space M] (hα : α.IsContactForm)
    {κ : S → M} (hκ : ContMDiff IS I ∞ κ) {g : S → ℝ} (hg : ContMDiff IS 𝓘(ℝ) ∞ g)
    {β : SmoothForm IS S ℝ 1}
    (hκα : SmoothForm.mpullback κ hκ α = β + mextDerivₗ IS 0
      ⟨RoughForm.ofFunction _ g, (isSmoothForm_ofFunction_iff.2 hg).mem_smoothBundleForms⟩)
    {p : S × ℝ} (hp : (-p.2 - g p.1, κ p.1) ∈ flowDomain α.reebVectorField) :
    TauCeti.mpullback (IS.prod 𝓘(ℝ)) I
        (fun p : S × ℝ ↦ flowOf α.reebVectorField (-p.2 - g p.1) (κ p.1)) α.val p =
      (-β.contactization).val p := by
  have hR := hα.contMDiff_reebVectorField
  have hh : ContMDiff (IS.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ (fun p : S × ℝ ↦ -p.2 - g p.1) :=
    contMDiff_snd.neg.sub (hg.comp contMDiff_fst)
  have hχ := (contMDiff_fst (M := S) (N := ℝ)).prodMk hh
  have hFd : MDifferentiableAt _ I (fun q : S × ℝ ↦ flowOf α.reebVectorField q.2 (κ q.1))
      (p.1, -p.2 - g p.1) :=
    (contMDiffAt_flowOf_comp le_top hR contMDiffAt_snd (hκ.contMDiffAt.comp _ contMDiffAt_fst)
      hp).mdifferentiableAt (by simp)
  have hflow := mpullback_flowOf_comp_apply_eq_contactization hR hκ hα.apply_reebVectorField
    hα.interior_mextDeriv_reebVectorField (p := (p.1, -p.2 - g p.1)) hp
  have h1 : TauCeti.mpullback _ I
      (fun p : S × ℝ ↦ flowOf α.reebVectorField (-p.2 - g p.1) (κ p.1)) α.val p =
      (SmoothForm.mpullback (fun p : S × ℝ ↦ (p.1, -p.2 - g p.1)) hχ
        (-SmoothForm.mpullback κ hκ α).contactization).val p := by
    rw [show (fun p : S × ℝ ↦ flowOf α.reebVectorField (-p.2 - g p.1) (κ p.1)) =
        (fun q : S × ℝ ↦ flowOf α.reebVectorField q.2 (κ q.1)) ∘
          (fun p : S × ℝ ↦ (p.1, -p.2 - g p.1)) from rfl,
      mpullback_comp_at (hχ.mdifferentiableAt (by simp)) hFd, SmoothForm.coe_mpullback]
    exact ContinuousAlternatingMap.ext fun u ↦ by
      rw [TauCeti.mpullback_apply (fun p : S × ℝ ↦ (p.1, -p.2 - g p.1)),
        TauCeti.mpullback_apply (fun p : S × ℝ ↦ (p.1, -p.2 - g p.1)), hflow]
  have hfst : MDifferentiable (IS.prod 𝓘(ℝ)) 𝓘(ℝ) (fun p : S × ℝ ↦ g p.1) :=
    (hg.comp (contMDiff_fst (n := ∞))).mdifferentiable (by simp)
  have hsnd : MDifferentiable (IS.prod 𝓘(ℝ)) 𝓘(ℝ) (fun p : S × ℝ ↦ p.2) :=
    (contMDiff_snd (n := ∞)).mdifferentiable (by simp)
  -- `d(-z - g) = -dz - dg`.
  have hdh : mextDeriv (RoughForm.ofFunction (IS.prod 𝓘(ℝ)) (fun p : S × ℝ ↦ -p.2 - g p.1)) =
      -(mextDeriv (RoughForm.ofFunction _ (fun p : S × ℝ ↦ p.2)) +
        mextDeriv (RoughForm.ofFunction _ (fun p : S × ℝ ↦ g p.1))) := by
    rw [← mextDeriv_ofFunction_add hsnd hfst, eq_neg_iff_add_eq_zero,
      ← mextDeriv_ofFunction_add (hh.mdifferentiable (by simp)) (hsnd.add hfst)]
    convert mextDeriv_ofFunction_zero using 3
    ext p
    simp only [Pi.add_apply, Pi.zero_apply]
    ring
  have hfstα : (SmoothForm.mpullback (Prod.fst : S × ℝ → S) (contMDiff_fst (J := 𝓘(ℝ)))
      (SmoothForm.mpullback κ hκ α)).val =
      (SmoothForm.mpullback (Prod.fst : S × ℝ → S) contMDiff_fst β).val +
      mextDeriv (RoughForm.ofFunction _ (fun p : S × ℝ ↦ g p.1)) := by
    rw [hκα, map_add, Submodule.coe_add, ← SmoothForm.mextDerivₗ_mpullback, mextDerivₗ_apply,
      SmoothForm.coe_mpullback Prod.fst _ ⟨RoughForm.ofFunction _ g,
        (isSmoothForm_ofFunction_iff.2 hg).mem_smoothBundleForms⟩]
    exact congrArg₂ (· + ·) rfl (congrArg mextDeriv (mpullback_ofFunction _ _))
  rw [h1]
  refine congrFun ?_ p
  rw [SmoothForm.mpullback_prodMk_contactization _ contMDiff_fst hh, NegMemClass.coe_neg,
    SmoothForm.coe_contactization, map_neg, NegMemClass.coe_neg, hfstα, hdh]
  abel

end TauCeti.SmoothForm.IsContactForm

namespace TauCeti.IsLegendrianEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {E' H' L : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace L] [ChartedSpace H' L]
  [IsManifold J ∞ L]
  {α : SmoothForm I M ℝ 1}

/-- The zero section of `T^* L`, as a smooth embedding into an open set `N` that contains it. -/
private def zeroSectionOpens [J.Boundaryless] (N : Opens (CotangentBundle J L))
    (hN : ∀ q, zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q ∈ N) :
    SmoothEmbedding J (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) ∞ L N :=
  (SymplecticGeometry.Bundle.zeroSectionEmbedding J (E' →L[ℝ] ℝ)
    (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ)).codRestrict
    N fun q ↦ by rw [SymplecticGeometry.Bundle.coe_zeroSectionEmbedding]; exact hN q

private theorem coe_zeroSectionOpens_apply [J.Boundaryless] (N : Opens (CotangentBundle J L))
    (hN : ∀ q, zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q ∈ N) (q : L) :
    ((zeroSectionOpens N hN q : N) : CotangentBundle J L) =
      zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q := by
  rw [zeroSectionOpens, SmoothEmbedding.val_codRestrict_apply,
    SymplecticGeometry.Bundle.coe_zeroSectionEmbedding]

/-- Step 2 of the proof: given a map `κ` from an open neighbourhood `N` of the zero section of
`T^* L` into `M`, which is `f` on the zero section and for which `-d(κ^* α)` is symplectic, the
Lagrangian neighbourhood theorem reparametrizes it near the zero section so that `d(κ^* α)` becomes
`dλ`. -/
private theorem exists_mextDerivₗ_eq_of_isSymplectic [I.Boundaryless] [J.Boundaryless]
    [T2Space L] [SecondCountableTopology L] {f : L → M}
    (hf : IsLegendrianEmbedding J α.kerDistribution f) {N : Opens (CotangentBundle J L)}
    (hN : ∀ q, zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q ∈ N)
    {κ : N → M} (hκ : ContMDiff (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I ∞ κ)
    (hκ0 : ∀ q, κ ⟨_, hN q⟩ = f q)
    (hσ : SmoothTwoForm.IsSymplectic (-mextDerivₗ _ 1 (SmoothForm.mpullback κ hκ α))) :
    ∃ (U : Opens (CotangentBundle J L)) (κ' : U → M)
      (hκ' : ContMDiff (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I ∞ κ'),
      (∀ q, ∃ h : zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q ∈ U,
        κ' ⟨_, h⟩ = f q) ∧
      mextDerivₗ _ 1 (SmoothForm.mpullback κ' hκ' α) = mextDerivₗ _ 1
        (SmoothForm.mpullback (Subtype.val : U → CotangentBundle J L) contMDiff_subtypeVal
          (CotangentBundle.liouvilleForm J L)) := by
  -- The zero section is Lagrangian for `-d(κ^* α)`, since `f^* α = 0`.
  let z₀ := zeroSectionOpens N hN
  have hκz₀ : κ ∘ z₀ = f ∘ id :=
    funext fun q ↦ (congrArg κ (Subtype.ext (coe_zeroSectionOpens_apply N hN q))).trans (hκ0 q)
  have h0 : SmoothForm.mpullback z₀ z₀.contMDiff (SmoothForm.mpullback κ hκ α) = 0 := by
    rw [SmoothForm.mpullback_mpullback_of_comp_eq _ _ contMDiff_id hf.isImmersion.contMDiff hκz₀,
      (SmoothForm.isHorizontalMap_kerDistribution_iff_mpullback_eq_zero α _).1
        hf.isHorizontalMap, map_zero]
  have hLag : hσ.isNondegenerate.IsLagrangianMap J z₀ := by
    refine SmoothTwoForm.IsNondegenerate.IsIsotropicMap.isLagrangianMap_of_finrank ?_
      (fun q ↦ z₀.isImmersion.mfderiv_injective (by simp) q) ?_
    · rw [SmoothTwoForm.IsNondegenerate.isIsotropicMap_iff_mpullback_eq_zero z₀.contMDiff,
        map_neg, ← SmoothForm.mextDerivₗ_mpullback, h0, map_zero, neg_zero]
    · rw [finrank_prod, ContinuousLinearMap.dual_finrank_eq]; ring
  -- The Lagrangian neighbourhood theorem gives `ψ`; the map sought is `κ ∘ ψ`.
  obtain ⟨U, V, ψ, hψ0, hψσ⟩ :=
    SmoothTwoForm.IsNondegenerate.IsLagrangianMap.exists_symplectomorphism_cotangent
      (hσ := hσ) hLag
  refine ⟨U, κ ∘ (Subtype.val ∘ ψ), hκ.comp (contMDiff_subtypeVal.comp ψ.contMDiff),
    fun q ↦ ?_, ?_⟩
  · obtain ⟨h, hq, -⟩ := hψ0 q
    refine ⟨h, ?_⟩
    rw [Function.comp_apply, Function.comp_apply, hq]
    exact (congrFun hκz₀ q)
  · have hκ' : SmoothForm.mpullback ψ ψ.contMDiff (SmoothForm.mpullback (Subtype.val : V → N)
        contMDiff_subtypeVal (SmoothForm.mpullback κ hκ α)) =
        SmoothForm.mpullback _ (hκ.comp (contMDiff_subtypeVal.comp ψ.contMDiff)) α := by
      rw [SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback]
    have h2 : SmoothForm.mpullback ψ ψ.contMDiff (SmoothForm.mpullback (Subtype.val : V → N)
        contMDiff_subtypeVal (mextDerivₗ _ 1 (SmoothForm.mpullback κ hκ α))) =
        -SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
          (CotangentBundle.symplecticForm J L) := by
      rw [← hψσ, ← map_neg, ← map_neg, neg_neg]
    rw [← hκ', SmoothForm.mextDerivₗ_mpullback, SmoothForm.mextDerivₗ_mpullback, h2,
      CotangentBundle.symplecticForm_eq_neg_mextDerivₗ, map_neg, neg_neg,
      SmoothForm.mextDerivₗ_mpullback]

/-- Steps 1 and 2 of the proof: a map `κ` from an open set of `T^* L` containing its zero
section into `M`, equal to `f` on the zero section, with `d(κ^* α) = dλ`. -/
private theorem exists_slice_mextDerivₗ_eq [I.Boundaryless] [J.Boundaryless] [T2Space M]
    [SecondCountableTopology M] [T2Space L] [SecondCountableTopology L] {f : L → M}
    (hf : IsLegendrianEmbedding J α.kerDistribution f) :
    ∃ (U : Opens (CotangentBundle J L)) (κ : U → M)
      (hκ : ContMDiff (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I ∞ κ),
      (∀ q, ∃ h : zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q ∈ U,
        κ ⟨_, h⟩ = f q) ∧
      mextDerivₗ _ 1 (SmoothForm.mpullback κ hκ α) = mextDerivₗ _ 1
        (SmoothForm.mpullback (Subtype.val : U → CotangentBundle J L) contMDiff_subtypeVal
          (CotangentBundle.liouvilleForm J L)) := by
  have hα := hf.isContactForm
  obtain ⟨ι, N, hι, -, hN, hzN, hι0, hNι, -⟩ := exists_contactSlice hf
  -- On `N`, `-d(ι^* α)` is symplectic, since `ι` is an immersion transverse to the Reeb field.
  refine exists_mextDerivₗ_eq_of_isSymplectic (N := ⟨N, hN⟩) hf hzN (hι.comp contMDiff_subtypeVal)
    (fun q ↦ hι0 q) (hα.isSymplectic_neg_mextDerivₗ_mpullback hf.finrank_prod_dual_add_one _
      fun x ↦ ?_)
  rw [mfderiv_comp x ((hι _).mdifferentiableAt (by simp))
    SymplecticGeometry.mdifferentiableAt_subtypeVal, Manifold.mfderiv_subtype_val]
  refine ⟨(hNι x x.property).1.comp (Manifold.tangentSpaceOpenEquiv x).injective, ?_⟩
  rintro ⟨v, hv⟩
  exact (hNι x x.property).2 ⟨_, hv⟩

/-- Step 3 of the proof: for `κ` as in step 2, the closed form `κ^* α - λ` has a primitive `g` near
the zero section of `T^* L`, which vanishes on it. The zero section of the open set `W` where `g`
is defined is `s₀`. -/
private theorem exists_primitive [I.Boundaryless] [J.Boundaryless] [T2Space L]
    [SecondCountableTopology L] {f : L → M} (hf : IsLegendrianEmbedding J α.kerDistribution f)
    {U : Opens (CotangentBundle J L)} {κ : U → M}
    (hκ : ContMDiff (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I ∞ κ)
    (hκ0 : ∀ q, ∃ h : zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q ∈ U,
        κ ⟨_, h⟩ = f q)
    (hdκ : mextDerivₗ _ 1 (SmoothForm.mpullback κ hκ α) = mextDerivₗ _ 1
        (SmoothForm.mpullback (Subtype.val : U → CotangentBundle J L) contMDiff_subtypeVal
          (CotangentBundle.liouvilleForm J L))) :
    ∃ (W : Opens U) (g : W → ℝ) (_ : ContMDiff (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) 𝓘(ℝ) ∞ g)
      (s₀ : L → W), Continuous s₀ ∧
      (∀ q, ((s₀ q : U) : CotangentBundle J L) =
        zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q) ∧
      (∀ q, κ (s₀ q) = f q) ∧ (∀ q, g (s₀ q) = 0) ∧
      TauCeti.mpullback _ I (κ ∘ Subtype.val) α.val =
        TauCeti.mpullback _ _ ((Subtype.val : U → CotangentBundle J L) ∘ Subtype.val)
          (CotangentBundle.liouvilleForm J L).val +
        mextDeriv (RoughForm.ofFunction (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) g) := by
  set lam := CotangentBundle.liouvilleForm J L
  obtain ⟨lamU, hlamU⟩ : ∃ l, l =
      SmoothForm.mpullback (Subtype.val : U → CotangentBundle J L) contMDiff_subtypeVal lam :=
    ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = SmoothForm.mpullback κ hκ α - lamU := ⟨_, rfl⟩
  have hγc : mextDeriv γ.val = 0 := by
    rw [hγ, ← mextDerivₗ_apply, map_sub, hlamU, hdκ, sub_self, ZeroMemClass.coe_zero]
  let z₀ := zeroSectionOpens U fun q ↦ (hκ0 q).1
  have hz₀ := coe_zeroSectionOpens_apply U fun q ↦ (hκ0 q).1
  have hκz₀ (q : L) : κ (z₀ q) = f q := by
    obtain ⟨h, hq⟩ := hκ0 q
    rw [← hq]
    exact congrArg κ (Subtype.ext (hz₀ q))
  -- Along the zero section, `κ^* α` and `λ` both vanish.
  have hγ0 : TauCeti.mpullback J _ z₀ γ.val = 0 := by
    have h1 : SmoothForm.mpullback z₀ z₀.contMDiff (SmoothForm.mpullback κ hκ α) = 0 := by
      rw [SmoothForm.mpullback_mpullback_of_comp_eq _ _ contMDiff_id hf.isImmersion.contMDiff
        (funext hκz₀ : κ ∘ z₀ = f ∘ id)]
      simp [(SmoothForm.isHorizontalMap_kerDistribution_iff_mpullback_eq_zero α _).1
        hf.isHorizontalMap]
    have h2 : SmoothForm.mpullback z₀ z₀.contMDiff lamU = 0 := by
      refine Subtype.ext ?_
      rw [hlamU, SmoothForm.mpullback_mpullback, SmoothForm.coe_mpullback]
      have : (Subtype.val ∘ z₀ : L → CotangentBundle J L) =
          zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) := funext hz₀
      rw [this, CotangentBundle.isExactLagrangianMap_zeroSection.mpullback_eq,
        mextDeriv_ofFunction_zero, ZeroMemClass.coe_zero]
    have := congrArg Subtype.val (show SmoothForm.mpullback z₀ z₀.contMDiff γ = 0 by
      rw [hγ, map_sub, h1, h2, sub_zero])
    rwa [SmoothForm.coe_mpullback, ZeroMemClass.coe_zero] at this
  obtain ⟨W, -, hz₀W, hprim⟩ := z₀.exists_isSmoothForm_relative_primitive (F := ℝ) isOpen_univ
    (subset_univ _)
  obtain ⟨b, hb, hdb, hb0, -⟩ := hprim (k := 0) (r := ⊤) le_top γ.isSmoothForm hγc hγ0
  have hbg : b = RoughForm.ofFunction _ (fun w ↦ b w 0) := RoughForm.eq_ofFunction b
  have hgs : ContMDiff (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) 𝓘(ℝ) ∞ (fun w : W ↦ b w 0) :=
    SmoothForm.contMDiff_apply_zero ⟨b, hb.mem_smoothBundleForms⟩
  have hfin : TauCeti.mpullback _ I (κ ∘ Subtype.val) α.val =
      TauCeti.mpullback _ _ ((Subtype.val : U → CotangentBundle J L) ∘ Subtype.val) lam.val +
      mextDeriv (RoughForm.ofFunction (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) fun w : W ↦ b w 0) := by
    rw [← hbg, hdb, hγ, hlamU, Submodule.coe_sub, TauCeti.mpullback_sub, SmoothForm.coe_mpullback,
      SmoothForm.coe_mpullback,
      ← TauCeti.mpullback_comp SymplecticGeometry.mdifferentiable_subtypeVal
        (hκ.mdifferentiable (by simp)),
      ← TauCeti.mpullback_comp SymplecticGeometry.mdifferentiable_subtypeVal
        SymplecticGeometry.mdifferentiable_subtypeVal,
      add_sub_cancel]
  exact ⟨W, fun w ↦ b w 0, hgs, fun q ↦ ⟨z₀ q, hz₀W (mem_range_self q)⟩,
    z₀.contMDiff.continuous.subtype_mk _, hz₀, hκz₀,
    fun q ↦ (congrFun (congrArg DFunLike.coe (hb0 q)) 0 : _), hfin⟩

section Flow

variable {S : Type*} [TopologicalSpace S] [ChartedSpace (ModelProd H' (E' →L[ℝ] ℝ)) S]
  [IsManifold (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) ∞ S]

/-- Step 4 of the proof: from a local diffeomorphism `e : S → T^* L`, a map `κ : S → M` and a
function `g` on `S` with `κ^* α = e^* λ + dg`, all compatible with `f` along a section `s₀` of `e`
over the zero section, the map `(s, z) ↦ φ^R_{-z - g s} (κ s)` restricts to a partial
diffeomorphism near the points `(s₀ q, 0)`, which sends them to `f q` and pulls `α` back to minus
the contactization form of `e^* λ`, that is to `e^* λ - dz`. -/
private theorem exists_partialDiffeomorph_of_primitive [I.Boundaryless] [J.Boundaryless]
    [T2Space M] [SecondCountableTopology M] [Nonempty L] {f : L → M}
    (hf : IsLegendrianEmbedding J α.kerDistribution f) [T2Space S] [SecondCountableTopology S]
    {e : S → CotangentBundle J L}
    (he : IsLocalDiffeomorph (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) ∞ e)
    {κ : S → M} (hκ : ContMDiff (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I ∞ κ)
    {g : S → ℝ} (hg : ContMDiff (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) 𝓘(ℝ) ∞ g)
    {s₀ : L → S} (hs₀ : Continuous s₀)
    (hes₀ : ∀ q, e (s₀ q) = zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q)
    (hκs₀ : ∀ q, κ (s₀ q) = f q) (hgs₀ : ∀ q, g (s₀ q) = 0)
    (hκα : SmoothForm.mpullback κ hκ α = SmoothForm.mpullback e he.contMDiff
      (CotangentBundle.liouvilleForm J L) +
        mextDerivₗ (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) 0
          ⟨RoughForm.ofFunction _ g, (isSmoothForm_ofFunction_iff.2 hg).mem_smoothBundleForms⟩) :
    ∃ Φ : PartialDiffeomorph ((J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)).prod 𝓘(ℝ)) I (S × ℝ) M ∞,
      (∀ q, (s₀ q, 0) ∈ Φ.source) ∧ (∀ q, Φ (s₀ q, 0) = f q) ∧
      ∀ x ∈ Φ.source, TauCeti.mpullback _ I Φ α.val x =
        (-(SmoothForm.mpullback e he.contMDiff
          (CotangentBundle.liouvilleForm J L)).contactization).val x := by
  have hα := hf.isContactForm
  have hR := hα.contMDiff_reebVectorField
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have := ChartedSpace.locallyCompactSpace H M
  have : LocallyCompactSpace (ModelProd (ModelProd H' (E' →L[ℝ] ℝ)) ℝ) :=
    ((J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)).prod 𝓘(ℝ)).locallyCompactSpace
  have := ChartedSpace.locallyCompactSpace (ModelProd (ModelProd H' (E' →L[ℝ] ℝ)) ℝ) (S × ℝ)
  have := Manifold.metrizableSpace ((J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)).prod 𝓘(ℝ)) (S × ℝ)
  have := Manifold.metrizableSpace I M
  have : Nonempty (S × ℝ) := ⟨(s₀ (Classical.arbitrary L), 0)⟩
  -- `d(κ^* α) = d(e^* λ) = -e^* ω` is nondegenerate.
  have hdκ : mextDerivₗ _ 1 (SmoothForm.mpullback κ hκ α) =
      -SmoothForm.mpullback e he.contMDiff (CotangentBundle.symplecticForm J L) := by
    have hdd : mextDerivₗ (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) 1
        (mextDerivₗ (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) 0
          ⟨RoughForm.ofFunction _ g, (isSmoothForm_ofFunction_iff.2 hg).mem_smoothBundleForms⟩) =
          0 :=
      LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ _ 0) _
    rw [hκα, map_add, hdd, add_zero, SmoothForm.mextDerivₗ_mpullback,
      CotangentBundle.symplecticForm_eq_neg_mextDerivₗ, map_neg, neg_neg]
  have hω := CotangentBundle.isSymplectic_symplecticForm.isNondegenerate
    |>.isNondegenerate_mpullback_of_isLocalDiffeomorph (I := J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) he
  have hnd : SmoothTwoForm.IsNondegenerate (mextDerivₗ _ 1 (SmoothForm.mpullback κ hκ α)) := by
    rw [hdκ]
    exact hω.neg
  -- The change of time `χ (s, z) = (s, -z - g s)`, an involution.
  have hh : ContMDiff ((J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun p : S × ℝ ↦ -p.2 - g p.1) := contMDiff_snd.neg.sub (hg.comp contMDiff_fst)
  have hχinv (p : S × ℝ) : (p.1, -(-p.2 - g p.1) - g p.1) = p := Prod.ext rfl (by ring)
  let χ : (S × ℝ) ≃ₘ⟮(J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)).prod 𝓘(ℝ),
      (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)).prod 𝓘(ℝ)⟯ (S × ℝ) :=
    { toFun p := (p.1, -p.2 - g p.1)
      invFun p := (p.1, -p.2 - g p.1)
      left_inv := hχinv
      right_inv := hχinv
      contMDiff_toFun := contMDiff_fst.prodMk hh
      contMDiff_invFun := contMDiff_fst.prodMk hh }
  -- `Φ₀ (s, z) = φ^R_{-z - g s} (κ s)` is a local diffeomorphism where it is defined.
  let Φ₀ : S × ℝ → M := fun p ↦ flowOf α.reebVectorField (-p.2 - g p.1) (κ p.1)
  let O : Set (S × ℝ) := {p | (-p.2 - g p.1, κ p.1) ∈ flowDomain α.reebVectorField}
  have hO : IsOpen O := isOpen_setOf_mem_flowDomain (hR.of_le (by simp)) hh.continuous
    (hκ.continuous.comp continuous_fst)
  have hloc : IsLocalDiffeomorphOn _ I ∞ Φ₀ O := fun p ↦
    (χ.isLocalDiffeomorph p).comp I M (isLocalDiffeomorphAt_flowOf_comp_of_nondegenerate hR hκ
      hf.finrank_prod_dual_add_one hα.apply_reebVectorField hα.interior_mextDeriv_reebVectorField
      (hnd.nondegenerate_bilinFormAt p.val.1) p.property)
  -- It is `f` on the zero section, so it is a diffeomorphism near it.
  let s : L → S × ℝ := fun q ↦ (s₀ q, 0)
  have hΦ₀s : Φ₀ ∘ s = f := funext fun q ↦ by simp [Φ₀, s, hgs₀, hκs₀]
  have hsO : range s ⊆ O := by
    rintro _ ⟨q, rfl⟩
    simpa [O, s, hgs₀] using mem_flowDomain_zero (hR.of_le (by simp)) (κ (s₀ q))
  obtain ⟨Φ', hsΦ', hΦ'O, -, hΦ'⟩ := hloc.exists_partialDiffeomorph_near_section hO hsO
    (hs₀.prodMk continuous_const) (fun p ↦ (e p.1).proj)
    ((FiberBundle.continuous_proj _ _).comp (he.contMDiff.continuous.comp continuous_fst))
    (fun q ↦ by simp [s, hes₀]) (by rw [hΦ₀s]; exact hf.isEmbedding.isInducing)
  refine ⟨Φ', fun q ↦ hsΦ' ⟨q, rfl⟩, fun q ↦ by rw [hΦ']; exact congrFun hΦ₀s q,
    fun x hx ↦ ?_⟩
  rw [hΦ']
  exact hα.mpullback_flowOf_neg_sub_apply hκ hg hκα (hΦ'O hx)

/-- Step 5 of the proof: under the hypotheses of step 4, and with `e` injective, an open set of
`T^* L × ℝ` containing the points `(0_q, 0)` is diffeomorphic to an open set of `M` by a map
that sends `(0_q, 0)` to `f q` and pulls `α` back to minus the contactization form of `λ`. The
partial diffeomorphism of step 4 is moved to `T^* L × ℝ` along `(s, z) ↦ (e s, z)`. -/
private theorem exists_diffeomorph_opens_of_primitive [I.Boundaryless] [J.Boundaryless]
    [T2Space M] [SecondCountableTopology M] [Nonempty L] {f : L → M}
    (hf : IsLegendrianEmbedding J α.kerDistribution f) [T2Space S] [SecondCountableTopology S]
    {e : S → CotangentBundle J L}
    (he : IsLocalDiffeomorph (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) ∞ e)
    (heinj : Injective e)
    {κ : S → M} (hκ : ContMDiff (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I ∞ κ)
    {g : S → ℝ} (hg : ContMDiff (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) 𝓘(ℝ) ∞ g)
    {s₀ : L → S} (hs₀ : Continuous s₀)
    (hes₀ : ∀ q, e (s₀ q) = zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q)
    (hκs₀ : ∀ q, κ (s₀ q) = f q) (hgs₀ : ∀ q, g (s₀ q) = 0)
    (hκα : SmoothForm.mpullback κ hκ α = SmoothForm.mpullback e he.contMDiff
      (CotangentBundle.liouvilleForm J L) +
        mextDerivₗ (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) 0
          ⟨RoughForm.ofFunction _ g, (isSmoothForm_ofFunction_iff.2 hg).mem_smoothBundleForms⟩) :
    ∃ (U : Opens (CotangentBundle J L × ℝ)) (V : Opens M)
      (Φ : U ≃ₘ⟮(J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)).prod 𝓘(ℝ), I⟯ V),
      (∀ q, ∃ h : (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q,
        (0 : ℝ)) ∈ U, (Φ ⟨_, h⟩ : M) = f q) ∧
      SmoothForm.mpullback Φ Φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : V → M) contMDiff_subtypeVal α) =
        -SmoothForm.mpullback (Subtype.val : U → CotangentBundle J L × ℝ) contMDiff_subtypeVal
          (CotangentBundle.liouvilleForm J L).contactization := by
  obtain ⟨Φ, hsΦ, hΦs, hΦα⟩ :=
    exists_partialDiffeomorph_of_primitive hf he hκ hg hs₀ hes₀ hκs₀ hgs₀ hκα
  have hk : IsLocalDiffeomorph ((J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)).prod 𝓘(ℝ))
      ((J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)).prod 𝓘(ℝ)) ∞ (Prod.map e id) :=
    he.prodMap (by
      rw [← Diffeomorph.coe_refl 𝓘(ℝ) ℝ ∞]
      exact (Diffeomorph.refl 𝓘(ℝ) ℝ ∞).isLocalDiffeomorph)
  obtain ⟨U, V, Ψ, hΨ, hΨα⟩ := PartialDiffeomorph.exists_diffeomorph_opens_mpullback_eq hk
    (heinj.prodMap injective_id) Φ (τ := -(CotangentBundle.liouvilleForm J L).contactization)
    fun x hx ↦ by rw [hΦα x hx, map_neg, SmoothForm.mpullback_prodMap_contactization]
  refine ⟨U, V, Ψ, fun q ↦ ?_, by rw [hΨα, map_neg]⟩
  obtain ⟨h, hq⟩ := hΨ _ (hsΦ q)
  have hq0 : Prod.map e id (s₀ q, (0 : ℝ)) =
      (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q, (0 : ℝ)) := by
    rw [Prod.map_apply, hes₀, id_eq]
  exact ⟨hq0 ▸ h, (congrArg (fun y ↦ (Ψ y : M)) (Subtype.ext hq0.symm)).trans (hq.trans (hΦs q))⟩

end Flow

/-- **The Legendrian neighbourhood theorem.** Let `f : L → M` be a Legendrian embedding for the
kernel of a one-form `α`, which is then a contact form, between boundaryless manifolds, `M`
Hausdorff and second countable. Then an open set around the zero section of `T^* L × ℝ` is
diffeomorphic to an open set around `f (L)` by a map `Φ` with `Φ (0_q, 0) = f q` that pulls `α`
back to `λ_can - dz`, minus the contactization form `dz - λ_can` of the Liouville form. Neither
compactness of `L` nor closedness of `f (L)` is assumed.

Milestone: *Legendrian neighbourhood theorem*. -/
theorem exists_diffeomorph_opens_mpullback_eq_neg_contactization [I.Boundaryless]
    [J.Boundaryless] [T2Space M] [SecondCountableTopology M] {f : L → M}
    (hf : IsLegendrianEmbedding J α.kerDistribution f) :
    ∃ (U : Opens (CotangentBundle J L × ℝ)) (V : Opens M)
      (Φ : U ≃ₘ⟮(J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)).prod 𝓘(ℝ), I⟯ V),
      (∀ q, ∃ h : (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q,
        (0 : ℝ)) ∈ U, (Φ ⟨_, h⟩ : M) = f q) ∧
      SmoothForm.mpullback Φ Φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : V → M) contMDiff_subtypeVal α) =
        -SmoothForm.mpullback (Subtype.val : U → CotangentBundle J L × ℝ) contMDiff_subtypeVal
          (CotangentBundle.liouvilleForm J L).contactization := by
  rcases isEmpty_or_nonempty L with hL | hL
  · exact ⟨⊥, ⊥, Diffeomorph.ofIsEmpty, fun q ↦ (hL.false q).elim,
      Subtype.ext (funext fun x ↦ (IsEmpty.false x).elim)⟩
  have := hf.isEmbedding.t2Space
  have := hf.isEmbedding.isInducing.secondCountableTopology
  obtain ⟨U, κ, hκ, hκ0, hdκ⟩ := exists_slice_mextDerivₗ_eq hf
  obtain ⟨W, g, hg, s₀, hs₀, hes₀, hκs₀, hgs₀, hκα⟩ := exists_primitive hf hκ hκ0 hdκ
  let e := (Subtype.val : U → CotangentBundle J L) ∘ (Subtype.val : W → U)
  have he : IsLocalDiffeomorph (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) ∞ e :=
    fun x ↦ (isLocalDiffeomorph_subtype_val x).comp _ _ (isLocalDiffeomorph_subtype_val _)
  have hκα' : SmoothForm.mpullback (κ ∘ Subtype.val) (hκ.comp contMDiff_subtypeVal) α =
      SmoothForm.mpullback e he.contMDiff (CotangentBundle.liouvilleForm J L) +
        mextDerivₗ (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) 0
          ⟨RoughForm.ofFunction _ g, (isSmoothForm_ofFunction_iff.2 hg).mem_smoothBundleForms⟩ := by
    refine Subtype.ext ?_
    rw [Submodule.coe_add, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback, mextDerivₗ_apply]
    exact hκα
  exact exists_diffeomorph_opens_of_primitive hf he
    (Subtype.val_injective.comp Subtype.val_injective) (hκ.comp contMDiff_subtypeVal) hg hs₀ hes₀
    hκs₀ hgs₀ hκα'

end TauCeti.IsLegendrianEmbedding
