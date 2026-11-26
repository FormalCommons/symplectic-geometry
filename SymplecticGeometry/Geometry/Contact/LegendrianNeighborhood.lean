/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Immersion.Transverse
public import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.Riemannian.Injective
public import TauCeti.Geometry.Contact.Legendrian.Neighborhood
import TauCeti.Geometry.Contact.Family
import TauCeti.Geometry.Contact.OneJet.Connection
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ZeroSection
import SymplecticGeometry.Topology.Sets.Opens.Basic
import SymplecticGeometry.Topology.VectorBundle.Basic

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
`f(L)` of the route through a hypersurface of McDuff–Salamon, Exercise 3.5.22(i), which later
neighbourhood theorems can use; the two facts about contact forms of that route are in
`SymplecticGeometry/Geometry/Contact/Slice.lean`.

## A slice through `f(L)`

The first step of that route builds a hypersurface through `f(L)`, tangent to `ker α` along
`f(L)` and transverse to the Reeb field near it, parametrized by the cotangent bundle `T^* L`
(`TauCeti.IsLegendrianEmbedding.exists_contactSlice`).

The construction:

* Tau Ceti's diffeomorphism `Φ : ν → T^* L × ℝ` of the normal bundle, over the identity of `L`
  (`TauCeti.SmoothEmbedding.normalBundleDiffeomorphOfIsLegendrianImmersion`), is on the fibre
  over `q` the map `[w] ↦ (dα(df_q ·, w), α w)` from `ν_q = T_(f q) M ⧸ df_q(T_q L)`
  (`TauCeti.SmoothEmbedding.normalSpaceEquivOfIsLegendrianImmersion`). So
  `j p = Φ⁻¹ (p, 0)` is a smooth injective bundle map `j : T^* L → ν`, linear on each fibre,
  whose image lies in `ker α ⧸ df(T L)`.
* A smooth injective map `T : ν → M`, equal to `f` on the zero section, whose differential
  sends the vertical vector `v` at `0_q` to a vector of normal class `c q • v` with `c q > 0`,
  comes from `TauCeti.SmoothEmbedding.exists_contMDiff_injective_normalBundle`.
* The slice is `ι = T ∘ j`. At `0_q` its differential is `df_q` horizontally and lands in
  `ker α` vertically, and it is injective; as `T_(0_q)(T^* L)` and `ker α_(f q)` both have
  dimension `2 n`, its range is `ker α_(f q)`. So the Reeb field is not in it, and the set where
  the differential of `ι` is injective with the Reeb field outside its range is an open
  neighbourhood of the zero section (`ContMDiffAt.eventually_injective_mfderiv_and_notMem_range`).

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

## Main results

* `TauCeti.IsLegendrianImmersion.finrank_prod_dual_add_one`: the model of `T^* L` has one
  dimension less than that of `M`.
* `TauCeti.IsLegendrianEmbedding.exists_contactSlice`: a smooth injective map `ι : T^* L → M`
  with `ι (0_q) = f q`, which is an immersion transverse to the Reeb field on some open set
  containing the zero section, and whose differential at `0_q` has range `ker α_(f q)`.
* `TauCeti.IsLegendrianEmbedding.exists_diffeomorph_opens_mpullback_eq_neg_contactization`: the
  Legendrian neighbourhood theorem.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §3.5, Example 3.5.6 and Exercise 3.5.22(i).
* A. Kriegl, P. W. Michor, *The Convenient Setting of Global Analysis*, Mathematical Surveys and
  Monographs 53, AMS (1997), Proposition 43.18 (cited by Tau Ceti's proof of the theorem).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics
  109, Cambridge University Press, 2008, §2.5 (cited by Tau Ceti's proofs that this file
  uses).
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
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The bundle map `j : T^* L → ν`, `p ↦ Φ⁻¹ (p, 0)`, for `Φ` Tau Ceti's diffeomorphism
`TauCeti.SmoothEmbedding.normalBundleDiffeomorphOfIsLegendrianImmersion` of the normal bundle `ν`
with `T^* L × ℝ`. -/
private def cotangentToNormal (hf : IsLegendrianEmbedding J α.kerDistribution g)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') :
    CotangentBundle J L → TotalSpace P (fun q ↦ g.isImmersion.NormalSpace q infty_ne_zero) :=
  letI := g.normalSpaceFiberBundle infty_ne_zero hdim
  fun p ↦ (g.normalBundleDiffeomorphOfIsLegendrianImmersion hf.toIsLegendrianImmersion
    (m := ∞) infty_ne_zero (by simp) (by simp) hdim).symm (p, 0)

private theorem cotangentToNormal_mk (hf : IsLegendrianEmbedding J α.kerDistribution g)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') (q : L) (p : TangentSpace J q →L[ℝ] ℝ) :
    cotangentToNormal hf hdim ⟨q, p⟩ = ⟨q, (g.normalSpaceEquivOfIsLegendrianImmersion
      hf.toIsLegendrianImmersion infty_ne_zero q).symm (p, 0)⟩ := by
  let := g.normalSpaceFiberBundle infty_ne_zero hdim
  unfold cotangentToNormal
  exact g.normalBundleDiffeomorphOfIsLegendrianImmersion_symm_apply ..

private theorem contMDiff_cotangentToNormal (hf : IsLegendrianEmbedding J α.kerDistribution g)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') :
    letI := g.normalSpaceFiberBundle infty_ne_zero hdim
    ContMDiff (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, P)) ∞ (cotangentToNormal hf hdim) := by
  let := g.normalSpaceFiberBundle infty_ne_zero hdim
  unfold cotangentToNormal
  exact (Diffeomorph.contMDiff _).comp (contMDiff_id.prodMk contMDiff_const)

private theorem injective_cotangentToNormal (hf : IsLegendrianEmbedding J α.kerDistribution g)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') : Injective (cotangentToNormal hf hdim) := by
  unfold cotangentToNormal
  exact (EquivLike.injective _).comp fun _ _ h ↦ (Prod.mk.inj h).1

private theorem cotangentToNormal_zeroSection (hf : IsLegendrianEmbedding J α.kerDistribution g)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') (q : L) :
    cotangentToNormal hf hdim
        (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q) =
      zeroSection P _ q := by
  rw [zeroSection_def, zeroSection_def]
  exact (cotangentToNormal_mk hf hdim q 0).trans
    (congrArg (TotalSpace.mk' P q) (by rw [Prod.mk_zero_zero, map_zero]))

/-- The differential of `T ∘ j` along the zero section, for a smooth map `T` of the normal bundle
which is `g` on its zero section and `j` the bundle map `cotangentToNormal`: horizontally it is
`dg`, vertically it is the vertical differential of `T` on `e⁻¹ (p, 0)`, for `e` the
identification `TauCeti.SmoothEmbedding.normalSpaceEquivOfIsLegendrianImmersion`. -/
private theorem mfderiv_comp_cotangentToNormal (hf : IsLegendrianEmbedding J α.kerDistribution g)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') :
    letI := g.normalSpaceFiberBundle infty_ne_zero hdim
    letI := g.normalSpaceVectorBundle infty_ne_zero hdim
    ∀ T : TotalSpace P (fun q ↦ g.isImmersion.NormalSpace q infty_ne_zero) → M,
      ContMDiff (J.prod 𝓘(ℝ, P)) I ∞ T → (∀ q, T (zeroSection P _ q) = g q) →
      ∀ (q : L) (u : TangentSpace J q) (p : TangentSpace J q →L[ℝ] ℝ),
        mfderiv (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I (T ∘ cotangentToNormal hf hdim)
            (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q)
            ((Bundle.zeroSectionTangentEquiv (I := J) q).symm (u, 0)) = mfderiv J I g q u ∧
        mfderiv (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I (T ∘ cotangentToNormal hf hdim)
            (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q)
            ((Bundle.zeroSectionTangentEquiv (I := J) q).symm (0, p)) =
          mfderiv (J.prod 𝓘(ℝ, P)) I T (zeroSection P _ q)
            ((Bundle.zeroSectionTangentEquiv (I := J) q).symm
              (0, (g.normalSpaceEquivOfIsLegendrianImmersion hf.toIsLegendrianImmersion
                infty_ne_zero q).symm (p, 0))) := by
  let := g.normalSpaceFiberBundle infty_ne_zero hdim
  let := g.normalSpaceVectorBundle infty_ne_zero hdim
  intro T hT hT0 q u p
  have hι : ContMDiff (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I ∞ (T ∘ cotangentToNormal hf hdim) :=
    hT.comp (contMDiff_cotangentToNormal hf hdim)
  refine ⟨?_, ?_⟩
  · -- Horizontally: the composite is `g` on the zero section.
    refine Bundle.mfderiv_zeroSectionTangentEquiv_symm_inl ((hι _).mdifferentiableAt (by simp))
      (.of_forall fun q ↦ ?_) u
    rw [Function.comp_apply, Function.comp_apply, cotangentToNormal_zeroSection, hT0]
  · -- Vertically: the composite maps the line `t ↦ t • p` to the line `t ↦ t • e⁻¹ (p, 0)`.
    rw [Bundle.mfderiv_zeroSectionTangentEquiv_symm_inr ((hι _).mdifferentiableAt (by simp)),
      Bundle.mfderiv_zeroSectionTangentEquiv_symm_inr ((hT _).mdifferentiableAt (by simp))]
    congr 2 with t
    rw [Function.comp_apply, cotangentToNormal_mk, ← map_smul, Prod.smul_mk, smul_zero]

/-- The differential at `0_q` of `T ∘ j`, for a map `T` of the normal bundle and `j` the bundle
map `cotangentToNormal`, with its values read in the tangent space of `M` at `g q`. When `T` is
`g` on the zero section, as below, this is the tangent space at the base point of the image. -/
private def sliceDeriv (hf : IsLegendrianEmbedding J α.kerDistribution g)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') :
    letI := g.normalSpaceFiberBundle infty_ne_zero hdim
    letI := g.normalSpaceVectorBundle infty_ne_zero hdim
    (TotalSpace P (fun q ↦ g.isImmersion.NormalSpace q infty_ne_zero) → M) → ∀ q : L,
      TangentSpace (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ))
          (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q) →L[ℝ]
        TangentSpace I (g q) :=
  letI := g.normalSpaceFiberBundle infty_ne_zero hdim
  letI := g.normalSpaceVectorBundle infty_ne_zero hdim
  fun T q ↦ mfderiv (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I
    (T ∘ cotangentToNormal hf hdim)
    (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q)

private theorem sliceDeriv_apply (hf : IsLegendrianEmbedding J α.kerDistribution g)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') :
    letI := g.normalSpaceFiberBundle infty_ne_zero hdim
    letI := g.normalSpaceVectorBundle infty_ne_zero hdim
    ∀ (T : TotalSpace P (fun q ↦ g.isImmersion.NormalSpace q infty_ne_zero) → M) (q : L) (X),
      sliceDeriv hf hdim T q X = mfderiv (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I
        (T ∘ cotangentToNormal hf hdim)
        (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q) X :=
  fun _ _ _ ↦ rfl

/-- For a map `T` as in `TauCeti.SmoothEmbedding.exists_contMDiff_injective_normalBundle`, the
differential of `T ∘ j` at `0_q` takes values in `ker α` and is injective. -/
private theorem sliceDeriv_mem_kerDistribution_and_injective
    (hf : IsLegendrianEmbedding J α.kerDistribution g)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') :
    letI := g.normalSpaceFiberBundle infty_ne_zero hdim
    letI := g.normalSpaceVectorBundle infty_ne_zero hdim
    ∀ T : TotalSpace P (fun q ↦ g.isImmersion.NormalSpace q infty_ne_zero) → M,
      ContMDiff (J.prod 𝓘(ℝ, P)) I ∞ T → (∀ q, T (zeroSection P _ q) = g q) →
      ∀ c : L → ℝ, (∀ q, 0 < c q) → (∀ q (v : g.isImmersion.NormalSpace q infty_ne_zero),
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
    (V := fun q ↦ g.isImmersion.NormalSpace q infty_ne_zero) q).symm
  set en := g.normalSpaceEquivOfIsLegendrianImmersion hf.toIsLegendrianImmersion infty_ne_zero q
  have hd := mfderiv_comp_cotangentToNormal hf hdim T hT hT0 q
  have hhor (u : TangentSpace J q) : D (e (u, 0)) = mfderiv J I g q u :=
    (sliceDeriv_apply hf hdim T q _).trans (hd u 0).1
  have hver (p : TangentSpace J q →L[ℝ] ℝ) : D (e (0, p)) = mfderiv (J.prod 𝓘(ℝ, P)) I T
      (zeroSection P _ q) (e' (0, en.symm (p, 0))) :=
    (sliceDeriv_apply hf hdim T q _).trans (hd 0 p).2
  -- `D` splits into `dg` horizontally and a vertical part of normal class `c q • j p`.
  have hsplit (u : TangentSpace J q) (p : TangentSpace J q →L[ℝ] ℝ) :
      D (e (u, p)) = mfderiv J I g q u + D (e (0, p)) := by
    rw [← hhor, ← map_add, ← map_add, Prod.mk_add_mk,
      add_zero, zero_add]
  have hvert (p : TangentSpace J q →L[ℝ] ℝ) :
      g.isImmersion.normalClass q infty_ne_zero (D (e (0, p))) = c q • en.symm (p, 0) := by
    have h := hTd q (en.symm (p, 0))
    rw [SmoothEmbedding.normalFiberDeriv_apply] at h
    rw [hver]
    -- `exact`, not `rw`: the vector lies in the tangent space at `T 0_q`, which `rw` does not
    -- identify with the tangent space at `g q` that `Manifold.IsImmersion.normalClassL_apply`
    -- expects.
    exact (Manifold.IsImmersion.normalClassL_apply ..).symm.trans h
  have hαvert (p : TangentSpace J q →L[ℝ] ℝ) : α.val (g q) ![D (e (0, p))] = 0 := by
    have h := g.normalSpaceEquivOfIsLegendrianImmersion_normalClass hf.toIsLegendrianImmersion
      infty_ne_zero q (D (e (0, p)))
    rw [hvert, map_smul, en.apply_symm_apply] at h
    simpa using (congrArg Prod.snd h).symm
  refine ⟨fun X ↦ ?_, (injective_iff_map_eq_zero D).2 fun X hX ↦ ?_⟩
  · obtain ⟨⟨u, p⟩, rfl⟩ := e.surjective X
    rw [SmoothForm.mem_kerDistribution, hsplit, ← SmoothForm.degreeOneEquiv_apply_apply_vec,
      map_add, SmoothForm.degreeOneEquiv_apply_apply_vec,
      SmoothForm.degreeOneEquiv_apply_apply_vec, hαvert,
      SmoothForm.mem_kerDistribution.1 (hf.isHorizontalMap.mfderiv_mem q u), add_zero]
  · obtain ⟨⟨u, p⟩, rfl⟩ := e.surjective X
    rw [hsplit] at hX
    have hcl := congrArg (g.isImmersion.normalClass q infty_ne_zero) hX
    rw [map_add, hvert, Manifold.IsImmersion.normalClass_mfderiv, zero_add, map_zero,
      smul_eq_zero] at hcl
    obtain rfl : p = 0 := congrArg Prod.fst (en.symm.injective
      ((hcl.resolve_left (hc q).ne').trans (map_zero _).symm))
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
  let ι : CotangentBundle J L → M := T ∘ cotangentToNormal hf' hdim
  have hι : ContMDiff (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I ∞ ι :=
    hT.comp (contMDiff_cotangentToNormal hf' hdim)
  set Z0 := zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ)
  have hιinj : Injective ι := hTinj.comp (injective_cotangentToNormal hf' hdim)
  have hι0 (q : L) : ι (Z0 q) = g q :=
    (congrArg T (cotangentToNormal_zeroSection hf' hdim q)).trans (hT0 q)
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
    simp only [σ, CotangentBundle.connectionFrameChange_apply, mul_zero, zeroSection_def,
      smul_zero]
  exact ⟨hq0 ▸ h, (congrArg (fun y ↦ (Ψ y : M)) (Subtype.ext hq0.symm)).trans
    (hq.trans ((hφ0 q).trans (congrFun hg q)))⟩

end TauCeti.IsLegendrianEmbedding
