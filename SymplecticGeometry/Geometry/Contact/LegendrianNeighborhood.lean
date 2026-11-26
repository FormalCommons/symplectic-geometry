/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Immersion.Transverse
public import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.Riemannian.Injective
public import TauCeti.Geometry.Contact.Legendrian.Neighborhood
public import TauCeti.Geometry.Manifold.Flow.Basic
import SymplecticGeometry.Geometry.Contact.Contactization
import TauCeti.Geometry.Contact.OneJet.Connection
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ZeroSection
import SymplecticGeometry.Topology.Sets.Opens.Basic
import TauCeti.Geometry.Contact.Slice

/-!
# The Legendrian neighbourhood theorem

Let `α` be a contact form on `M` and `f : L → M` a Legendrian embedding, so that
`dim M = 2 n + 1` and `dim L = n`. This file states the Legendrian neighbourhood theorem in the
form of a diffeomorphism between open sets: an open set around the zero section of `T^* L × ℝ` is
diffeomorphic to an open set around `f(L)` by a map that is `f` on the zero section and pulls `α`
back to `λ_can - dz`
(`TauCeti.IsLegendrianEmbedding.exists_diffeomorph_opens_mpullback_eq_neg_contactization`).
Neither compactness of `L` nor closedness of `f(L)` is assumed. Nor is `α` assumed to be a
contact form: a one-form whose kernel has a Legendrian immersion is one
(`TauCeti.IsLegendrianImmersion.isContactForm`). The file also keeps the hypersurface through
`f(L)` and the two facts about contact forms of the route through a hypersurface of
McDuff–Salamon, Exercise 3.5.22(i), which later neighbourhood theorems can use.

## A slice through `f(L)`

The first step of that route builds a hypersurface through `f(L)`, tangent to `ker α` along
`f(L)` and transverse to the Reeb field near it, parametrized by the cotangent bundle `T^* L`
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
`TauCeti/Geometry/Contact/Legendrian/Normal.lean`.
The splitting of the differential of `T ∘ j` along the zero section into a horizontal and a
vertical part follows the proof of Tau Ceti's
`TauCeti.SmoothEmbedding.mfderiv_normalExp_zeroSection_apply`.

## The neighbourhood theorem

Tau Ceti proves the theorem as
`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_mpullback_eq_contactization`: for a nonempty
`L`, a partial diffeomorphism `φ` from `T^* L × ℝ` to `M`, whose source contains the points
`(0_q, 0)`, with `φ (0_q, 0) = f q` and `φ^* α = dz - λ_can` on its source. The theorem here is
deduced from it:

* the involution `σ (q, p, z) = (q, -p, -z)` of `T^* L × ℝ` is Tau Ceti's frame change
  `TauCeti.CotangentBundle.connectionFrameChange` by the constant function `-1`. It fixes the
  points `(0_q, 0)` and pulls `dz - λ_can` back to `λ_can - dz`, by
  `TauCeti.CotangentBundle.mpullback_connectionFrameChange_connectionOneJetForm` for the zero
  connection (`TauCeti.CotangentBundle.connectionOneJetForm_zero`);
* so `φ` pulls `α` back to `σ^* (λ_can - dz)`, and
  `PartialDiffeomorph.exists_diffeomorph_opens_mpullback_eq`, applied with `e = σ`, gives a
  diffeomorphism `Ψ` between open sets with `Ψ (σ x) = φ x` that pulls `α` back to
  `λ_can - dz`;
* an empty `L` is handled with the empty open sets (`TopologicalSpace.Opens.isEmpty_bot`).

## Two facts about contact forms

* On a hypersurface `ι : S → M` that is everywhere an immersion transverse to the Reeb field,
  `-d(ι^* α)` is symplectic
  (`TauCeti.SmoothForm.IsContactForm.isSymplectic_neg_mextDerivₗ_mpullback`).
* If `κ^* α = β + dg`, the map `(s, z) ↦ φ^R_{-z - g s} (κ s)`, with `φ^R` the local Reeb flow,
  pulls `α` back to `-(dz - β)` wherever it is defined
  (`TauCeti.SmoothForm.IsContactForm.mpullback_flowOf_neg_sub_apply`), since the Reeb flow out of
  `κ` pulls `α` back to `dt + κ^* α` (`TauCeti.mpullback_flowOf_comp_apply_eq_contactization`).
  Its proof follows the steps of the private lemma
  `mpullback_flowOf_comp_contactizationShift_comp_reassoc` of the proof of Tau Ceti's
  `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart`.

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
* A. Kriegl, P. W. Michor, *The Convenient Setting of Global Analysis*, Mathematical Surveys and
  Monographs 53, AMS (1997), Proposition 43.18 (cited by Tau Ceti's proof of the theorem).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics
  109, Cambridge University Press, 2008, §2.5 (cited by Tau Ceti's proofs that this file uses
  and adapts).
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
    refine Bundle.mfderiv_zeroSectionTangentEquiv_symm_inl ((hι _).mdifferentiableAt (by simp))
      (.of_forall fun q ↦ ?_) u
    rw [Function.comp_apply, ← hT0 q]
    exact congrArg T (congrArg (TotalSpace.mk' P q) (map_zero _))
  · -- Vertically: the composite maps the line `t ↦ t • p` to the line `t ↦ t • j p`.
    rw [Bundle.mfderiv_zeroSectionTangentEquiv_symm_inr ((hι _).mdifferentiableAt (by simp)),
      Bundle.mfderiv_zeroSectionTangentEquiv_symm_inr ((hT _).mdifferentiableAt (by simp))]
    congr 2 with t
    exact congrArg T (congrArg (TotalSpace.mk' P q) (map_smul _ t p))

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
        g.normalFiberDeriv infty_ne_zero hdim T q v = c q • v) →
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
    have h := hTd q (cotangentToNormal hf q p)
    rw [SmoothEmbedding.normalFiberDeriv_apply] at h
    rw [hver]
    -- `exact`, not `rw`: the vector lies in the tangent space at `T 0_q`, which `rw` does not
    -- identify with the tangent space at `g q` that `normalClassL_apply` expects.
    exact (SmoothEmbedding.normalClassL_apply ..).symm.trans h
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
    exact TauCeti.mpullback_apply_congr hflow
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
    SmoothForm.contactization_def, Submodule.coe_sub, SmoothForm.coe_mpullback Prod.snd,
    SmoothForm.mpullback_realLineCoordForm, map_neg, NegMemClass.coe_neg, hfstα, hdh]
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
  let g : SmoothEmbedding J I ∞ L M := .ofIsSmoothEmbedding f hf.isSmoothEmbedding
  have hg : ⇑g = f := SmoothEmbedding.coe_ofIsSmoothEmbedding f _
  obtain ⟨φ, hφs, hφ0, hφα⟩ := g.exists_partialDiffeomorph_mpullback_eq_contactization
    (hg ▸ hf.toIsLegendrianImmersion)
  -- The frame change by `-1`, `(q, p, z) ↦ (q, -p, -z)`, pulls `dz - λ` back to `λ - dz`.
  let σ := CotangentBundle.connectionFrameChange J (M := L) (contMDiff_const (c := (-1 : ℝ)))
    fun _ ↦ by norm_num
  have hd : mextDeriv (RoughForm.ofFunction J (fun _ : L ↦ (-1 : ℝ))) = 0 := by
    funext x
    exact mextDeriv_ofFunction_apply_eq_zero_iff.2 (mfderiv_const ..)
  obtain ⟨U, V, Ψ, hΨ, hΨα⟩ := PartialDiffeomorph.exists_diffeomorph_opens_mpullback_eq
    σ.isLocalDiffeomorph σ.injective φ
    (τ := -(CotangentBundle.liouvilleForm J L).contactization) fun x hx ↦ by
      rw [hφα x hx, map_neg, NegMemClass.coe_neg, Pi.neg_apply,
        ← CotangentBundle.connectionOneJetForm_zero,
        CotangentBundle.mpullback_connectionFrameChange_connectionOneJetForm _ _
          (a := 0) (by simp [hd, Pi.zero_def]), neg_one_smul, neg_neg]
  refine ⟨U, V, Ψ, fun q ↦ ?_, by rw [hΨα, map_neg]⟩
  obtain ⟨h, hq⟩ := hΨ _ (hφs q)
  have hq0 : σ (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q, (0 : ℝ)) =
      (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q, (0 : ℝ)) := by
    simp only [σ, CotangentBundle.connectionFrameChange_apply, zeroSection_proj, zeroSection_snd,
      mul_zero]
    -- `zeroSection q` is `⟨q, 0⟩` by definition, which Mathlib states by no lemma.
    exact congrArg (fun v ↦ (TotalSpace.mk' (E' →L[ℝ] ℝ) q v, (0 : ℝ))) (smul_zero (-1 : ℝ))
  exact ⟨hq0 ▸ h, (congrArg (fun y ↦ (Ψ y : M)) (Subtype.ext hq0.symm)).trans
    (hq.trans ((hφ0 q).trans (congrFun hg q)))⟩

end TauCeti.IsLegendrianEmbedding
