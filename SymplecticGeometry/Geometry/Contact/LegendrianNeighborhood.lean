/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Immersion.Transverse
public import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.Riemannian.Injective
public import TauCeti.Geometry.Contact.Flat
public import TauCeti.Geometry.Contact.Isotropic
public import TauCeti.Geometry.Contact.Levi
public import TauCeti.Geometry.Contact.Pullback
public import TauCeti.Geometry.Contact.Reeb
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.Trivial
public import TauCeti.Geometry.Manifold.VectorBundle.ZeroSection
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Normal

/-!
# A slice through a Legendrian submanifold

Let `α` be a contact form on `M` and `f : L → M` a Legendrian embedding, so that
`dim M = 2 n + 1` and `dim L = n`. This file builds a hypersurface through `f(L)`, tangent to
`ker α` along `f(L)` and transverse to the Reeb field near it, parametrized by the cotangent
bundle `T^* L` (`TauCeti.IsLegendrianEmbedding.exists_contactSlice`). It is the first step of the
proof of the Legendrian neighbourhood theorem through a hypersurface, as in McDuff–Salamon,
Exercise 3.5.22(i): on the slice, `d` of the pulled-back form is symplectic and the zero section
is Lagrangian for it.

The construction:

* At `q ∈ L`, the normal space `ν_q = T_(f q) M ⧸ df_q(T_q L)` is identified with
  `T_q^* L × ℝ` by `[w] ↦ (dα(df_q ·, w), α w)`. This is well defined because `f` pulls `α` and
  `dα` back to zero, and injective because a vector of `ker α` that is `dα`-orthogonal to
  `df_q(T_q L)` lies in `df_q(T_q L)`, by the maximality of Legendrian tangent spaces
  (`TauCeti.IsLegendrianImmersion.mem_range_mfderiv_of_distributionLeviForm_eq_zero`); the two
  sides have dimension `n + 1`. These identifications form a smooth bundle isomorphism, and
  `p ↦ (p, 0)` gives a smooth fibrewise injection `j : T^* L → ν` whose image lies in
  `ker α ⧸ df(T L)`.
* A smooth injective map `T : ν → M`, equal to `f` on the zero section, whose differential
  sends the vertical vector `v` at `0_q` to a vector of normal class `c q • v` with `c q > 0`,
  comes from `TauCeti.SmoothEmbedding.exists_contMDiff_injective_normalBundle`.
* The slice is `ι = T ∘ j`. At `0_q` its differential is `df_q` horizontally and lands in
  `ker α` vertically, and it is injective; as `T_(0_q)(T^* L)` and `ker α_(f q)` both have
  dimension `2 n`, its range is `ker α_(f q)`. So the Reeb field is not in it, and the set where
  the differential of `ι` is injective with the Reeb field outside its range is an open
  neighbourhood of the zero section (`ContMDiffAt.eventually_injective_mfderiv_and_notMem_range`).

The fibrewise identification of the normal bundle with a bundle built from `T^* L`, its smoothness
through `TauCeti.SmoothEmbedding.contMDiff_normalBundle_iff` and the smoothness of its inverse
adapt Tau Ceti's `TauCeti.SmoothEmbedding.normalBundleDiffeomorphOfIsLagrangianMap`, with the
covector `dα(df ·, w)` of `TauCeti.SmoothEmbedding.pairingCovector` completed by the value `α w`.
The splitting of the differential of `T ∘ j` along the zero section into a horizontal and a
vertical part follows the proof of Tau Ceti's
`TauCeti.SmoothEmbedding.mfderiv_normalExp_zeroSection_apply`.

## Main results

* `TauCeti.IsLegendrianEmbedding.exists_contactSlice`: a smooth injective map `ι : T^* L → M`
  with `ι (0_q) = f q`, which is an immersion transverse to the Reeb field on some open set
  containing the zero section, and whose differential at `0_q` has range `ker α_(f q)`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §3.5, Exercise 3.5.22(i).
-/

public section

noncomputable section

open Bundle Function Module Set Filter
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

/-- The map `w ↦ (dα(dg ·, w), α w)` from the tangent space of `M` at `g q`. -/
private def normalMap (g : SmoothEmbedding J I ∞ L M) (α : SmoothForm I M ℝ 1) (q : L) :
    TangentSpace I (g q) →L[ℝ] (TangentSpace J q →L[ℝ] ℝ) × ℝ :=
  (g.pairingCovector (mextDerivₗ I 1 α) q).prod (SmoothForm.degreeOneEquiv α (g q))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold J ∞ L] in
private theorem normalMap_apply (g : SmoothEmbedding J I ∞ L M) (q : L)
    (w : TangentSpace I (g q)) :
    normalMap g α q w = (g.pairingCovector (mextDerivₗ I 1 α) q w, α.val (g q) ![w]) := by
  simp [normalMap]

variable {g : SmoothEmbedding J I ∞ L M}

omit [FiniteDimensional ℝ E'] in
private theorem normalMap_eq_zero_of_mem (hf : IsLegendrianEmbedding J α.kerDistribution g)
    (q : L) (w : TangentSpace I (g q)) (hw : w ∈ g.tangentRange q infty_ne_zero) :
    normalMap g α q w = 0 := by
  obtain ⟨u', rfl⟩ := hw
  have h0 := congr($(SmoothForm.mpullback_mextDerivₗ_eq_zero_of_isHorizontalMap g.contMDiff
    hf.isHorizontalMap).val q)
  rw [normalMap_apply, Prod.mk_eq_zero]
  refine ⟨ContinuousLinearMap.ext fun u ↦ ?_, ?_⟩
  · have := congr($h0 ![u, u'])
    rw [SmoothForm.mpullback_apply] at this
    simp only [SmoothBundleForm.eval₂_apply, SmoothEmbedding.pairingCovector_apply_apply]
    convert this using 2
    ext i
    fin_cases i <;> rfl
  · exact SmoothForm.mem_kerDistribution.1 (hf.isHorizontalMap.mfderiv_mem q u')

omit [FiniteDimensional ℝ E'] in
private theorem mem_of_normalMap_eq_zero (hα : α.IsContactForm)
    (hf : IsLegendrianEmbedding J α.kerDistribution g) (q : L) (w : TangentSpace I (g q))
    (hw : normalMap g α q w = 0) : w ∈ g.tangentRange q infty_ne_zero := by
  rw [normalMap_apply, Prod.mk_eq_zero] at hw
  obtain ⟨h1, h2⟩ := hw
  have hwξ : w ∈ α.kerDistribution (g q) := SmoothForm.mem_kerDistribution.2 h2
  have hx : α.val (g q) ≠ 0 :=
    (SmoothForm.isContactForm_iff_forall_isContactFormAt.1 hα (g q)).ne_zero
  have hker := Submodule.ker_liftQ_eq_bot _ _ (SmoothForm.kerDistribution_def α (g q)).le
    (SmoothForm.kerDistribution_def α (g q)).ge
  have h := hf.toIsLegendrianImmersion.mem_range_mfderiv_of_distributionLeviForm_eq_zero
    (a := ⟨w, hwξ⟩) fun u ↦ ?_
  · exact (g.mem_tangentRange_iff q infty_ne_zero w).2 h
  rw [← Submodule.mem_bot ℝ, ← hker, LinearMap.mem_ker,
    SmoothForm.liftQ_distributionLeviForm_kerDistribution hx]
  have := congr($h1 u)
  rw [SmoothEmbedding.pairingCovector_apply_apply, SmoothBundleForm.eval₂_apply] at this
  rw [ContinuousAlternatingMap.apply_vecCons_swap]
  simpa using this

/-- The normal space of a Legendrian embedding at `q`, identified with `T_q^* L × ℝ` by
`[w] ↦ (dα(dg ·, w), α w)`. -/
private def normalEquiv (hα : α.IsContactForm) (hf : IsLegendrianEmbedding J α.kerDistribution g)
    (q : L) : g.NormalSpace q infty_ne_zero ≃L[ℝ] (TangentSpace J q →L[ℝ] ℝ) × ℝ :=
  let φ := g.normalLiftL q infty_ne_zero (normalMap g α q) (normalMap_eq_zero_of_mem hf q)
  have hφ (w) : φ (g.normalClass q infty_ne_zero w) = normalMap g α q w :=
    g.normalLiftL_normalClass q infty_ne_zero _ _ w
  have hinj : Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun v hv ↦ ?_
    obtain ⟨w, rfl⟩ := g.normalClass_surjective q infty_ne_zero v
    rw [hφ] at hv
    exact (g.normalClass_eq_zero_iff q infty_ne_zero w).2 (mem_of_normalMap_eq_zero hα hf q w hv)
  have hdim : finrank ℝ (g.NormalSpace q infty_ne_zero) =
      finrank ℝ ((TangentSpace J q →L[ℝ] ℝ) × ℝ) := by
    have h2 := hf.two_mul_finrank_add_one
    rw [g.finrank_normalSpace q infty_ne_zero, Module.finrank_prod,
      ← LinearMap.toContinuousLinearMap.finrank_eq, Subspace.dual_finrank_eq,
      finrank_tangentSpace, finrank_tangentSpace, Module.finrank_self]
    omega
  (φ.toLinearMap.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv

private theorem normalEquiv_normalClass (hα : α.IsContactForm)
    (hf : IsLegendrianEmbedding J α.kerDistribution g) (q : L) (w : TangentSpace I (g q)) :
    normalEquiv hα hf q (g.normalClass q infty_ne_zero w) = normalMap g α q w := by
  rw [normalEquiv, LinearEquiv.coe_toContinuousLinearEquiv',
    LinearMap.linearEquivOfInjective_apply, ContinuousLinearMap.coe_coe,
    SmoothEmbedding.normalLiftL_normalClass]

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The identification `normalEquiv` is smooth as a map of total spaces. -/
private theorem contMDiff_normalEquiv (hα : α.IsContactForm)
    (hf : IsLegendrianEmbedding J α.kerDistribution g)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') :
    letI := g.normalSpaceFiberBundle infty_ne_zero hdim
    ContMDiff (J.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, (E' →L[ℝ] ℝ) × ℝ)) ∞
      (fun p : TotalSpace P (fun q ↦ g.NormalSpace q infty_ne_zero) ↦
        TotalSpace.mk' ((E' →L[ℝ] ℝ) × ℝ)
          (E := (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) ×ᵇ Trivial L ℝ) p.proj
          (normalEquiv hα hf p.proj p.snd)) := by
  let := g.normalSpaceFiberBundle infty_ne_zero hdim
  have : IsManifold J (∞ + 1) L := by simpa using (inferInstance : IsManifold J ∞ L)
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  rw [g.contMDiff_normalBundle_iff infty_ne_zero (m := ∞) (by simp) hdim]
  have heq : ((fun p : TotalSpace P (fun q ↦ g.NormalSpace q infty_ne_zero) ↦
      TotalSpace.mk' ((E' →L[ℝ] ℝ) × ℝ)
        (E := (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) ×ᵇ Trivial L ℝ) p.proj
        (normalEquiv hα hf p.proj p.snd)) ∘ g.normalQuotientMap infty_ne_zero) =
      fun p ↦ TotalSpace.mk' ((E' →L[ℝ] ℝ) × ℝ)
        (E := (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) ×ᵇ Trivial L ℝ) p.proj
        (normalMap g α p.proj p.snd) := by
    funext p
    rw [Function.comp_apply, SmoothEmbedding.normalQuotientMap_apply]
    exact congrArg (TotalSpace.mk' _ p.proj) (normalEquiv_normalClass hα hf p.proj p.snd)
  rw [heq]
  -- Evaluating `α` on ambient tangent vectors along `g` is smooth.
  have hαg : ContMDiff (J.prod 𝓘(ℝ, E)) 𝓘(ℝ) ∞
      (fun p : TotalSpace E ((g : L → M) *ᵖ (TangentSpace I)) ↦ α.val (g p.proj) ![p.snd]) := by
    have hsec : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun x : M ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun y : M ↦ TangentSpace I y →L[ℝ] Trivial M ℝ y) x
          (SmoothForm.degreeOneEquiv α x)) :=
      (SmoothForm.degreeOneEquiv α).contMDiff
    have h := ContMDiff.clm_bundle_apply (F₁ := E) (F₂ := ℝ) (E₁ := TangentSpace I)
      (E₂ := Trivial M ℝ) (hsec.comp (g.contMDiff.comp (Bundle.contMDiff_proj (F := E)
        ((g : L → M) *ᵖ (TangentSpace I)))))
      (Bundle.Pullback.contMDiff_lift (E := TangentSpace I) g g.contMDiff)
    refine (Bundle.Trivial.contMDiff_mk_iff.1 h).2.congr fun p ↦ ?_
    exact (SmoothForm.degreeOneEquiv_apply_apply_vec α (g p.proj) p.snd).symm
  refine fun p ↦ Bundle.contMDiffAt_totalSpace_prod_iff.2 ⟨?_, ?_⟩
  · refine (g.contMDiff_pairingCovector (mextDerivₗ I 1 α) (m := ∞) (by simp) (by simp)
      p).congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
    dsimp only
    rw [normalMap_apply (α := α) g y.proj y.snd]
  · refine (Bundle.Trivial.contMDiffAt_mk_iff.2
      ⟨(Bundle.contMDiff_proj (F := E) ((g : L → M) *ᵖ (TangentSpace I))).contMDiffAt,
        hαg p⟩).congr_of_eventuallyEq
        (Eventually.of_forall fun y ↦ ?_)
    dsimp only
    rw [normalMap_apply (α := α) g y.proj y.snd]

/-- The fibrewise injection `p ↦ (normalEquiv)⁻¹ (p, 0)` of `T_q^* L` into the normal space. -/
private def cotangentToNormal (hα : α.IsContactForm)
    (hf : IsLegendrianEmbedding J α.kerDistribution g) (q : L) :
    (TangentSpace J q →L[ℝ] ℝ) →L[ℝ] g.NormalSpace q infty_ne_zero :=
  (normalEquiv hα hf q).symm.toContinuousLinearMap ∘L ContinuousLinearMap.inl ℝ _ ℝ

private theorem normalEquiv_cotangentToNormal (hα : α.IsContactForm)
    (hf : IsLegendrianEmbedding J α.kerDistribution g) (q : L) (p : TangentSpace J q →L[ℝ] ℝ) :
    normalEquiv hα hf q (cotangentToNormal hα hf q p) = (p, 0) := by
  simp [cotangentToNormal]

private theorem cotangentToNormal_injective (hα : α.IsContactForm)
    (hf : IsLegendrianEmbedding J α.kerDistribution g) (q : L) :
    Injective (cotangentToNormal hα hf q) := fun p p' h ↦ by
  have := congrArg (fun v ↦ (normalEquiv hα hf q v).1) h
  simpa only [normalEquiv_cotangentToNormal] using this

/-- The bundle map `T^* L → ν` induced by `cotangentToNormal` is smooth. -/
private theorem contMDiff_cotangentToNormal (hα : α.IsContactForm)
    (hf : IsLegendrianEmbedding J α.kerDistribution g)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') :
    letI := g.normalSpaceFiberBundle infty_ne_zero hdim
    ContMDiff (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, P)) ∞
      (fun p : CotangentBundle J L ↦ TotalSpace.mk' P
        (E := fun q ↦ g.NormalSpace q infty_ne_zero) p.proj
        (cotangentToNormal hα hf p.proj p.snd)) := by
  let := g.normalSpaceFiberBundle infty_ne_zero hdim
  have : IsManifold J (∞ + 1) L := by simpa using (inferInstance : IsManifold J ∞ L)
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let := g.normalSpaceVectorBundle infty_ne_zero hdim
  have := g.normalSpaceContMDiffVectorBundle (m := ∞) infty_ne_zero (by simp) hdim
  exact (contMDiff_bundle_symm (normalEquiv hα hf) (contMDiff_normalEquiv hα hf hdim)).comp
    (Bundle.Prod.contMDiff_inl (E₂ := Trivial L ℝ))

/-- The differential of `T ∘ j` along the zero section, for a smooth map `T` of the normal bundle
which is `g` on its zero section and `j` the bundle map of `cotangentToNormal`: horizontally
it is `dg`, vertically it is the vertical differential of `T`. -/
private theorem mfderiv_comp_cotangentToNormal (hα : α.IsContactForm)
    (hf : IsLegendrianEmbedding J α.kerDistribution g)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') :
    letI := g.normalSpaceFiberBundle infty_ne_zero hdim
    letI := g.normalSpaceVectorBundle infty_ne_zero hdim
    ∀ T : TotalSpace P (fun q ↦ g.NormalSpace q infty_ne_zero) → M,
      ContMDiff (J.prod 𝓘(ℝ, P)) I ∞ T → (∀ q, T (zeroSection P _ q) = g q) →
      ∀ (q : L) (u : TangentSpace J q) (p : TangentSpace J q →L[ℝ] ℝ),
        mfderiv (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I
            (fun p : CotangentBundle J L ↦ T ⟨p.proj, cotangentToNormal hα hf p.proj p.snd⟩)
            (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q)
            ((Bundle.zeroSectionTangentEquiv (I := J) q).symm (u, 0)) = mfderiv J I g q u ∧
        mfderiv (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I
            (fun p : CotangentBundle J L ↦ T ⟨p.proj, cotangentToNormal hα hf p.proj p.snd⟩)
            (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q)
            ((Bundle.zeroSectionTangentEquiv (I := J) q).symm (0, p)) =
          mfderiv (J.prod 𝓘(ℝ, P)) I T (zeroSection P _ q)
            ((Bundle.zeroSectionTangentEquiv (I := J) q).symm
              (0, cotangentToNormal hα hf q p)) := by
  let := g.normalSpaceFiberBundle infty_ne_zero hdim
  let := g.normalSpaceVectorBundle infty_ne_zero hdim
  intro T hT hT0 q u p
  have hι : ContMDiff (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I ∞
      (fun p : CotangentBundle J L ↦ T ⟨p.proj, cotangentToNormal hα hf p.proj p.snd⟩) :=
    hT.comp (contMDiff_cotangentToNormal hα hf hdim)
  refine ⟨?_, ?_⟩
  · -- Horizontally: the composite is `g` on the zero section.
    have hfun : (fun p : CotangentBundle J L ↦ T ⟨p.proj, cotangentToNormal hα hf p.proj p.snd⟩) ∘
        zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) = g := by
      funext q
      rw [Function.comp_apply, ← hT0 q]
      exact congrArg T (congrArg (TotalSpace.mk' P q) (map_zero _))
    have h := mfderiv_comp_apply q ((hι _).mdifferentiableAt (by simp))
      (mdifferentiableAt_zeroSection ℝ _) u
    rw [hfun] at h
    rw [Bundle.zeroSectionTangentEquiv_symm_eq, map_add, h, Prod.mk_zero_zero, map_zero, map_zero,
      add_zero]
  · -- Vertically: the composite maps the line `t ↦ t • p` to the line `t ↦ t • j p`.
    rw [Bundle.zeroSectionTangentEquiv_symm_inr, Bundle.zeroSectionTangentEquiv_symm_inr]
    let line : ℝ → CotangentBundle J L := fun t ↦ ⟨q, t • p⟩
    let line' : ℝ → TotalSpace P (fun q ↦ g.NormalSpace q infty_ne_zero) :=
      fun t ↦ ⟨q, t • cotangentToNormal hα hf q p⟩
    have hl : ContMDiff 𝓘(ℝ) (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) 1 line :=
      contMDiff_id.smul_totalSpace (contMDiff_const (c := (⟨q, p⟩ : CotangentBundle J L)))
    have hl' : ContMDiff 𝓘(ℝ) (J.prod 𝓘(ℝ, P)) 1 line' :=
      contMDiff_id.smul_totalSpace (contMDiff_const (c := (⟨q, cotangentToNormal hα hf q p⟩ :
        TotalSpace P (fun q ↦ g.NormalSpace q infty_ne_zero))))
    have h1 := mfderiv_comp_apply_of_eq (0 : ℝ)
      ((hι (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q)).mdifferentiableAt
        (by simp)) (hl.mdifferentiableAt one_ne_zero) (by simp [line, zeroSection]) (1 : ℝ)
    have h2 := mfderiv_comp_apply_of_eq (0 : ℝ)
      ((hT (zeroSection P (fun q ↦ g.NormalSpace q infty_ne_zero) q)).mdifferentiableAt
        (by simp)) (hl'.mdifferentiableAt one_ne_zero) (by simp [line', zeroSection]) (1 : ℝ)
    have hfun : (fun p : CotangentBundle J L ↦ T ⟨p.proj, cotangentToNormal hα hf p.proj p.snd⟩) ∘
        line = T ∘ line' := by
      funext t
      exact congrArg T (congrArg (TotalSpace.mk' P q) (map_smul _ t p))
    rw [← h1, hfun, h2]

/-- The differential at `0_q` of `T ∘ j`, for a map `T` of the normal bundle and `j` the bundle
map of `cotangentToNormal`, with its values read in the tangent space of `M` at `g q`. When `T` is
`g` on the zero section, as below, this is the tangent space at the base point of the image. -/
private def sliceDeriv (hα : α.IsContactForm) (hf : IsLegendrianEmbedding J α.kerDistribution g)
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
    (fun p : CotangentBundle J L ↦ T ⟨p.proj, cotangentToNormal hα hf p.proj p.snd⟩)
    (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q)

omit [FiniteDimensional ℝ P] in
private theorem sliceDeriv_apply (hα : α.IsContactForm)
    (hf : IsLegendrianEmbedding J α.kerDistribution g)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') :
    letI := g.normalSpaceFiberBundle infty_ne_zero hdim
    letI := g.normalSpaceVectorBundle infty_ne_zero hdim
    ∀ (T : TotalSpace P (fun q ↦ g.NormalSpace q infty_ne_zero) → M) (q : L) (X),
      sliceDeriv hα hf hdim T q X = mfderiv (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I
        (fun p : CotangentBundle J L ↦ T ⟨p.proj, cotangentToNormal hα hf p.proj p.snd⟩)
        (zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q) X :=
  fun _ _ _ ↦ rfl

/-- For a map `T` as in `TauCeti.SmoothEmbedding.exists_contMDiff_injective_normalBundle`, the
differential of `T ∘ j` at `0_q` takes values in `ker α` and is injective. -/
private theorem sliceDeriv_mem_kerDistribution_and_injective (hα : α.IsContactForm)
    (hf : IsLegendrianEmbedding J α.kerDistribution g)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') :
    letI := g.normalSpaceFiberBundle infty_ne_zero hdim
    letI := g.normalSpaceVectorBundle infty_ne_zero hdim
    ∀ T : TotalSpace P (fun q ↦ g.NormalSpace q infty_ne_zero) → M,
      ContMDiff (J.prod 𝓘(ℝ, P)) I ∞ T → (∀ q, T (zeroSection P _ q) = g q) →
      ∀ c : L → ℝ, (∀ q, 0 < c q) → (∀ q (v : g.NormalSpace q infty_ne_zero),
        g.normalClass q infty_ne_zero (mfderiv (J.prod 𝓘(ℝ, P)) I T (zeroSection P _ q)
          ((Bundle.zeroSectionTangentEquiv (I := J) q).symm (0, v))) = c q • v) →
      ∀ q, (∀ X, sliceDeriv hα hf hdim T q X ∈ α.kerDistribution (g q)) ∧
        Injective (sliceDeriv hα hf hdim T q) := by
  let := g.normalSpaceFiberBundle infty_ne_zero hdim
  let := g.normalSpaceVectorBundle infty_ne_zero hdim
  intro T hT hT0 c hc hTd q
  set D := sliceDeriv hα hf hdim T q
  set e := (Bundle.zeroSectionTangentEquiv (I := J)
    (F := E' →L[ℝ] ℝ) (V := fun q : L ↦ TangentSpace J q →L[ℝ] ℝ) q).symm
  set e' := (Bundle.zeroSectionTangentEquiv (I := J) (F := P)
    (V := fun q ↦ g.NormalSpace q infty_ne_zero) q).symm
  have hd := mfderiv_comp_cotangentToNormal hα hf hdim T hT hT0 q
  have hhor (u : TangentSpace J q) : D (e (u, 0)) = mfderiv J I g q u :=
    (sliceDeriv_apply hα hf hdim T q _).trans (hd u 0).1
  have hver (p : TangentSpace J q →L[ℝ] ℝ) : D (e (0, p)) = mfderiv (J.prod 𝓘(ℝ, P)) I T
      (zeroSection P _ q) (e' (0, cotangentToNormal hα hf q p)) :=
    (sliceDeriv_apply hα hf hdim T q _).trans (hd 0 p).2
  -- `D` splits into `dg` horizontally and a vertical part of normal class `c q • j p`.
  have hsplit (u : TangentSpace J q) (p : TangentSpace J q →L[ℝ] ℝ) :
      D (e (u, p)) = mfderiv J I g q u + D (e (0, p)) := by
    rw [← hhor, ← map_add, ← map_add, Prod.mk_add_mk,
      add_zero, zero_add]
  have hvert (p : TangentSpace J q →L[ℝ] ℝ) :
      g.normalClass q infty_ne_zero (D (e (0, p))) = c q • cotangentToNormal hα hf q p := by
    rw [hver, hTd]
  have hαvert (p : TangentSpace J q →L[ℝ] ℝ) : α.val (g q) ![D (e (0, p))] = 0 := by
    have h := normalEquiv_normalClass hα hf q (D (e (0, p)))
    rw [hvert, map_smul, normalEquiv_cotangentToNormal, normalMap_apply] at h
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
    obtain rfl : p = 0 := cotangentToNormal_injective hα hf q
      ((hcl.resolve_left (hc q).ne').trans (map_zero _).symm)
    rw [Prod.mk_zero_zero, map_zero, map_zero, add_zero] at hX
    obtain rfl : u = 0 := g.isImmersion.mfderiv_injective infty_ne_zero q
      (hX.trans (map_zero _).symm)
    rw [Prod.mk_zero_zero, map_zero]

/-- **A slice through a Legendrian submanifold.** Let `f : L → M` be a Legendrian embedding for a
contact form `α`, between boundaryless manifolds, `M` Hausdorff and second countable. There are a
smooth injective map `ι : T^* L → M` with `ι (0_q) = f q`, and an open neighbourhood `N` of the
zero section, such that at each point of `N` the differential of `ι` is injective and the Reeb
vector field of `α` is not in its range, and at `0_q` the range of the differential is the
contact hyperplane `ker α` at `f q`. -/
theorem exists_contactSlice [I.Boundaryless] [J.Boundaryless] [T2Space M]
    [SecondCountableTopology M] {f : L → M} (hα : α.IsContactForm)
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
  let g : SmoothEmbedding J I ∞ L M := .ofIsSmoothEmbedding f hf.isSmoothEmbedding
  have hg : ⇑g = f := SmoothEmbedding.coe_ofIsSmoothEmbedding f _
  have hf' : IsLegendrianEmbedding J α.kerDistribution g := hg ▸ hf
  let P := EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ E'))
  have hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E' := finrank_euclideanSpace_fin
  let := g.normalSpaceFiberBundle infty_ne_zero hdim
  let := g.normalSpaceVectorBundle infty_ne_zero hdim
  obtain ⟨T, hT, hTinj, hT0, c, hc, hTd⟩ := g.exists_contMDiff_injective_normalBundle hdim
  let ι : CotangentBundle J L → M := fun p ↦ T ⟨p.proj, cotangentToNormal hα hf' p.proj p.snd⟩
  have hι : ContMDiff (J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) I ∞ ι :=
    hT.comp (contMDiff_cotangentToNormal hα hf' hdim)
  set Z0 := zeroSection (E' →L[ℝ] ℝ) (fun q : L ↦ TangentSpace J q →L[ℝ] ℝ)
  have hιinj : Injective ι := by
    rintro ⟨q, a⟩ ⟨q', a'⟩ h
    obtain ⟨rfl, h2⟩ := TotalSpace.mk.inj (hTinj h)
    cases cotangentToNormal_injective hα hf' q (eq_of_heq h2)
    rfl
  have hι0 (q : L) : ι (Z0 q) = g q := by
    rw [← hT0 q]
    exact congrArg T (congrArg (TotalSpace.mk' P q) (map_zero _))
  have hD := sliceDeriv_mem_kerDistribution_and_injective hα hf' hdim T hT hT0 c hc hTd
  -- The differential of `ι` at `0_q`, with values in the tangent space at `g q = ι 0_q`, so that
  -- its range and `ker α` are subspaces of the same type.
  have hrange (q : L) : (sliceDeriv hα hf' hdim T q).range = α.kerDistribution (g q) := by
    have : FiniteDimensional ℝ (TangentSpace I (g q)) := inferInstanceAs (FiniteDimensional ℝ E)
    refine Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨X, rfl⟩; exact (hD q).1 X) ?_
    rw [LinearMap.finrank_range_of_inj (hD q).2, finrank_tangentSpace, Module.finrank_prod,
      ← LinearMap.toContinuousLinearMap.finrank_eq, Subspace.dual_finrank_eq]
    have h1 := hα.finrank_kerDistribution_add_one (g q)
    have h2 := hf.two_mul_finrank_add_one
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
  rw [show sliceDeriv hα hf' hdim T q X = α.reebVectorField (ι (Z0 q)) from
    (sliceDeriv_apply hα hf' hdim T q X).trans hX, hι0 q] at h
  exact hα.reebVectorField_notMem_kerDistribution (g q) h

end TauCeti.IsLegendrianEmbedding
