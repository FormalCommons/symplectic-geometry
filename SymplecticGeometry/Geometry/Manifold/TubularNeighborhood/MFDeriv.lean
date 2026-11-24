/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Coordinates
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Basic
import SymplecticGeometry.Topology.Sets.Opens.Basic
import SymplecticGeometry.Geometry.Manifold.IsManifold.Basic
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ZeroSection

/-!
# Diffeomorphisms of neighbourhoods with a prescribed derivative

Let `f₀ : Q → M₀` and `f₁ : Q → M₁` be smooth embeddings of the same manifold, and let `A` be a
smooth family of linear isomorphisms `A q : T_{f₀ q} M₀ ≃ T_{f₁ q} M₁`, a section over `Q` of the
bundle of linear maps between the pull-backs `f₀ *ᵖ TM₀` and `f₁ *ᵖ TM₁`, with
`A q ∘ df₀ q = df₁ q`. Then `exists_diffeomorph_opens_mfderiv_eq` gives a diffeomorphism `ψ`
between open neighbourhoods of `f₀ (Q)` and of `f₁ (Q)` with `ψ ∘ f₀ = f₁` and derivative `A q` at
every `f₀ q`. Neither compactness of `Q` nor closedness of the images is assumed.

This is the step of the proofs of the neighbourhood theorems of McDuff–Salamon, §3.4, in which a
bundle isomorphism along the submanifold is realized as the derivative of a diffeomorphism of
neighbourhoods, before the relative Moser theorem corrects the symplectic forms.

## Construction

Choose Riemannian metrics on `M₀` and `M₁`, and let `rep₀` send a normal vector of `f₀` to its
orthogonal representative. On the normal bundle `N` of `f₀`, consider the map
`Θ (q, v) = exp_{f₁ q} (A q (rep₀ v))`. It is smooth where the exponential map is defined, it is
`f₁` on the zero section, and at the zero vector over `q` its derivative is
`(u, v) ↦ df₁ u + A q (rep₀ v) = A q (df₀ u + rep₀ v)`, that is, `A q` composed with the derivative
of the normal exponential `normalExp` of `f₀`. Hence `Θ` is a local diffeomorphism along the zero
section, and Tau Ceti's `IsLocalDiffeomorphOn.exists_partialDiffeomorph_near_section` makes it a
partial diffeomorphism on a neighbourhood of the zero section. Composed with the inverse of the
normal exponential of `f₀`, it gives `ψ`.

The computation of the derivative of `Θ` follows Tau Ceti's
`TauCeti.SmoothEmbedding.mfderiv_normalExp_zeroSection_apply`, and the assembly near the zero
section follows Tau Ceti's `TauCeti.SmoothEmbedding.exists_partialDiffeomorph_normalExp_subset`,
both with `rep₀` replaced by `A ∘ rep₀` and the exponential map of `M₀` by that of `M₁`.

## Main results

* `TauCeti.SmoothEmbedding.exists_diffeomorph_opens_mfderiv_eq`: the diffeomorphism of open
  neighbourhoods with prescribed derivative along the embedded manifold.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.4.
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
-/

public section

noncomputable section

open Bundle Manifold Set Function TopologicalSpace
open scoped ContDiff Manifold Bundle

namespace TauCeti.SmoothEmbedding

variable {EQ E₀ E₁ HQ H₀ H₁ Q M₀ M₁ P : Type*}
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [FiniteDimensional ℝ EQ]
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace HQ] [TopologicalSpace H₀] [TopologicalSpace H₁]
  {J : ModelWithCorners ℝ EQ HQ} {I₀ : ModelWithCorners ℝ E₀ H₀}
  {I₁ : ModelWithCorners ℝ E₁ H₁}
  [J.Boundaryless] [I₀.Boundaryless] [I₁.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold J ∞ Q]
  [TopologicalSpace M₀] [ChartedSpace H₀ M₀] [IsManifold I₀ ∞ M₀] [T2Space M₀]
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁] [T2Space M₁]

/-- The smoothness exponent `∞` is nonzero; it names the normal bundles below. -/
private theorem infty_ne_zero : (∞ : ℕ∞ω) ≠ 0 := by simp

section Metric

variable [RiemannianBundle (fun y : M₀ ↦ TangentSpace I₀ y)]
  [IsContMDiffRiemannianBundle I₀ ∞ E₀ (fun y : M₀ ↦ TangentSpace I₀ y)]
  [RiemannianBundle (fun y : M₁ ↦ TangentSpace I₁ y)]
  [IsContMDiffRiemannianBundle I₁ ∞ E₁ (fun y : M₁ ↦ TangentSpace I₁ y)]
  (f₀ : SmoothEmbedding J I₀ ∞ Q M₀) (f₁ : SmoothEmbedding J I₁ ∞ Q M₁)
  (A : ∀ q, TangentSpace I₀ (f₀ q) ≃L[ℝ] TangentSpace I₁ (f₁ q))

/-- The twisted normal exponential `(q, v) ↦ exp_{f₁ q} (A q (rep₀ v))` on the normal bundle of
`f₀`, with `rep₀` the orthogonal representative of a normal vector. -/
private def twistedExp (p : TotalSpace P (fun q ↦ f₀.NormalSpace q infty_ne_zero)) : M₁ :=
  Manifold.riemannianExp I₁ M₁ (f₁ p.proj)
    (A p.proj (f₀.normalRepresentative p.proj infty_ne_zero p.snd))

/-- The normal vectors whose image under `A ∘ rep₀` lies in the domain of the exponential map. -/
private def twistedExpDomain : Set (TotalSpace P (fun q ↦ f₀.NormalSpace q infty_ne_zero)) :=
  {p | A p.proj (f₀.normalRepresentative p.proj infty_ne_zero p.snd) ∈
    Manifold.expDomain I₁ M₁ (f₁ p.proj)}

omit [FiniteDimensional ℝ EQ] [J.Boundaryless] [I₀.Boundaryless] [IsManifold J ∞ Q]
  [IsManifold I₀ ∞ M₀] [T2Space M₀]
  [IsContMDiffRiemannianBundle I₀ ∞ E₀ (fun y : M₀ ↦ TangentSpace I₀ y)] in
private theorem twistedExp_zeroSection (q : Q) :
    twistedExp (P := P) f₀ f₁ A (zeroSection P (fun q ↦ f₀.NormalSpace q infty_ne_zero) q) =
      f₁ q := by
  -- The fibre value of the zero section is the zero of the fibre over its projection, which is
  -- only definitionally the fibre over `q`; restate it over `q` so that `map_zero` applies.
  change Manifold.riemannianExp I₁ M₁ (f₁ q)
    (A q (f₀.normalRepresentative q infty_ne_zero 0)) = f₁ q
  rw [map_zero, map_zero, Manifold.riemannianExp_zero]

omit [FiniteDimensional ℝ EQ] [J.Boundaryless] [I₀.Boundaryless] [I₁.Boundaryless]
  [IsManifold J ∞ Q] [IsManifold I₀ ∞ M₀] [T2Space M₀] [T2Space M₁]
  [IsContMDiffRiemannianBundle I₀ ∞ E₀ (fun y : M₀ ↦ TangentSpace I₀ y)] in
private theorem zeroSection_mem_twistedExpDomain (q : Q) :
    zeroSection P (fun q ↦ f₀.NormalSpace q infty_ne_zero) q ∈ twistedExpDomain f₀ f₁ A := by
  -- As in `twistedExp_zeroSection`, restate the fibre value over `q`.
  change A q (f₀.normalRepresentative q infty_ne_zero 0) ∈ Manifold.expDomain I₁ M₁ (f₁ q)
  rw [map_zero, map_zero]
  exact Manifold.zero_mem_expDomain (f₁ q)

variable [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  (hA : ContMDiff J (J.prod 𝓘(ℝ, E₀ →L[ℝ] E₁)) ∞ (fun q ↦ TotalSpace.mk' (E₀ →L[ℝ] E₁)
      (E := fun q ↦ ((f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) q →L[ℝ]
        ((f₁ : Q → M₁) *ᵖ (TangentSpace I₁)) q) q
      (A q : TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace I₁ (f₁ q))))
  (hdim : Module.finrank ℝ P = Module.finrank ℝ E₀ - Module.finrank ℝ EQ)

omit [FiniteDimensional ℝ E₁] [J.Boundaryless] [I₀.Boundaryless] [I₁.Boundaryless]
  [T2Space M₀] [T2Space M₁] [RiemannianBundle (fun y : M₁ ↦ TangentSpace I₁ y)]
  [IsContMDiffRiemannianBundle I₁ ∞ E₁ (fun y : M₁ ↦ TangentSpace I₁ y)] in
include hA in
/-- The tangent vector `A q (rep₀ v)` at `f₁ q` depends smoothly on the normal vector `(q, v)`. -/
private theorem contMDiff_twistedExpVector :
    letI := f₀.normalSpaceFiberBundle infty_ne_zero hdim
    ContMDiff (J.prod 𝓘(ℝ, P)) I₁.tangent ∞
      (fun p : TotalSpace P (fun q ↦ f₀.NormalSpace q infty_ne_zero) ↦
        (⟨f₁ p.proj, A p.proj (f₀.normalRepresentative p.proj infty_ne_zero p.snd)⟩ :
          TangentBundle I₁ M₁)) := by
  let := f₀.normalSpaceFiberBundle infty_ne_zero hdim
  have hv : ContMDiff (J.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, E₀)) ∞
      (fun p : TotalSpace P (fun q ↦ f₀.NormalSpace q infty_ne_zero) ↦
        TotalSpace.mk' E₀ (E := (f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) p.proj
          (f₀.normalRepresentative p.proj infty_ne_zero p.snd)) :=
    (Pullback.contMDiff_iff f₀ f₀.contMDiff).2 ⟨contMDiff_proj _,
      f₀.contMDiff_normalRepresentative (m := ∞) infty_ne_zero (by simp) hdim⟩
  have hϕ := hA.comp (contMDiff_proj (F := P) (fun q ↦ f₀.NormalSpace q infty_ne_zero))
  exact (Pullback.contMDiff_lift (E := TangentSpace I₁) f₁ f₁.contMDiff).comp
    (ContMDiff.clm_bundle_apply hϕ hv)

omit [J.Boundaryless] [I₀.Boundaryless] [T2Space M₀] in
include hA hdim in
private theorem isOpen_twistedExpDomain :
    letI := f₀.normalSpaceFiberBundle infty_ne_zero hdim
    IsOpen (twistedExpDomain (P := P) f₀ f₁ A) :=
  letI := f₀.normalSpaceFiberBundle infty_ne_zero hdim
  Manifold.isOpen_setOfPred_mem_expDomain.preimage
    (contMDiff_twistedExpVector f₀ f₁ A hA hdim).continuous

omit [J.Boundaryless] [I₀.Boundaryless] [T2Space M₀] in
include hA in
private theorem contMDiffOn_twistedExp :
    letI := f₀.normalSpaceFiberBundle infty_ne_zero hdim
    ContMDiffOn (J.prod 𝓘(ℝ, P)) I₁ ∞ (twistedExp (P := P) f₀ f₁ A)
      (twistedExpDomain f₀ f₁ A) :=
  letI := f₀.normalSpaceFiberBundle infty_ne_zero hdim
  Manifold.contMDiffOn_riemannianExp_tangentBundle.comp
    (contMDiff_twistedExpVector f₀ f₁ A hA hdim).contMDiffOn fun _ hp ↦ hp

omit [J.Boundaryless] [I₀.Boundaryless] [T2Space M₀] in
include hA in
/-- In the splitting of the tangent space of the normal bundle at a zero vector, the derivative
of the twisted exponential is `(u, v) ↦ df₁ u + A q (rep₀ v)`. -/
private theorem mfderiv_twistedExp_zeroSection_apply
    (q : Q) (u : TangentSpace J q) (v : f₀.NormalSpace q infty_ne_zero) :
    letI := f₀.normalSpaceFiberBundle infty_ne_zero hdim
    letI := f₀.normalSpaceVectorBundle infty_ne_zero hdim
    mfderiv (J.prod 𝓘(ℝ, P)) I₁ (twistedExp (P := P) f₀ f₁ A)
        (zeroSection P (fun q ↦ f₀.NormalSpace q infty_ne_zero) q)
        ((Bundle.zeroSectionTangentEquiv (I := J) q).symm (u, v)) =
      mfderiv J I₁ f₁ q u + A q (f₀.normalRepresentative q infty_ne_zero v) := by
  let := f₀.normalSpaceFiberBundle infty_ne_zero hdim
  let := f₀.normalSpaceVectorBundle infty_ne_zero hdim
  let := f₀.normalSpaceContMDiffVectorBundle (m := ∞) infty_ne_zero (by simp) hdim
  have he : MDifferentiableAt (J.prod 𝓘(ℝ, P)) I₁ (twistedExp (P := P) f₀ f₁ A)
      (zeroSection P (fun q ↦ f₀.NormalSpace q infty_ne_zero) q) :=
    ((contMDiffOn_twistedExp f₀ f₁ A hA hdim).contMDiffAt
      ((isOpen_twistedExpDomain f₀ f₁ A hA hdim).mem_nhds
        (zeroSection_mem_twistedExpDomain f₀ f₁ A q))).mdifferentiableAt (by simp)
  rw [show (u, v) = (u, 0) + (0, v) from Prod.ext (add_zero u).symm (zero_add v).symm, map_add,
    map_add]
  congr 1
  · -- On the zero section the twisted exponential is `f₁`.
    exact Bundle.mfderiv_zeroSectionTangentEquiv_symm_inl he
      (.of_eq (funext (twistedExp_zeroSection f₀ f₁ A))) u
  · -- On the fibre line `t ↦ t • v` it is `t ↦ exp_{f₁ q} (t • A q (rep₀ v))`.
    rw [Bundle.zeroSectionTangentEquiv_symm_inr]
    let line : ℝ → TotalSpace P (fun q ↦ f₀.NormalSpace q infty_ne_zero) := fun t ↦ ⟨q, t • v⟩
    have hl : ContMDiff 𝓘(ℝ) (J.prod 𝓘(ℝ, P)) 1 line :=
      contMDiff_id.smul_totalSpace (contMDiff_const (c := (⟨q, v⟩ :
        TotalSpace P (fun q ↦ f₀.NormalSpace q infty_ne_zero))))
    have h := mfderiv_comp_apply_of_eq (0 : ℝ) he
      (hl.mdifferentiableAt one_ne_zero) (by simp [line, zeroSection]) (1 : ℝ)
    set w := A q (f₀.normalRepresentative q infty_ne_zero v)
    have hfun : twistedExp (P := P) f₀ f₁ A ∘ line =
        Manifold.riemannianExp I₁ M₁ (f₁ q) ∘ (fun t : ℝ ↦ t • w) := by
      funext t
      simp only [Function.comp_apply, line, twistedExp, map_smul, w]
    rw [hfun] at h
    have hexp₀ := Manifold.hasMFDerivAt_riemannianExp_zero (I := I₁) (f₁ q)
    have hvec : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, TangentSpace I₁ (f₁ q)) (fun t : ℝ ↦ t • w) 0
        (ContinuousLinearMap.toSpanSingleton ℝ w) :=
      (ContinuousLinearMap.toSpanSingleton ℝ w).hasMFDerivAt
    have hc := mfderiv_comp_apply_of_eq (0 : ℝ) hexp₀.mdifferentiableAt
      hvec.mdifferentiableAt (by simp) (1 : ℝ)
    -- `hc` evaluates at the zero of the model space `E₁`, the lemma at the zero of the tangent
    -- space; they agree only up to unfolding `TangentSpace`.
    erw [Manifold.mfderiv_riemannianExp_apply_zero (I := I₁) (f₁ q), hvec.mfderiv] at hc
    exact h.symm.trans (hc.trans (ContinuousLinearMap.toSpanSingleton_apply_one ℝ w))

omit [J.Boundaryless] in
include hA in
/-- At a zero vector, the derivative of the twisted exponential is `A q` composed with the
derivative of the normal exponential of `f₀`. -/
private theorem mfderiv_twistedExp_zeroSection_apply_eq_apply_mfderiv_normalExp
    (hAf : ∀ q v, A q (mfderiv J I₀ f₀ q v) = mfderiv J I₁ f₁ q v) (q : Q) :
    letI := f₀.normalSpaceFiberBundle infty_ne_zero hdim
    ∀ w, mfderiv (J.prod 𝓘(ℝ, P)) I₁ (twistedExp (P := P) f₀ f₁ A)
        (zeroSection P (fun q ↦ f₀.NormalSpace q infty_ne_zero) q) w =
      A q (mfderiv (J.prod 𝓘(ℝ, P)) I₀ (f₀.normalExp (P := P) infty_ne_zero)
        (zeroSection P (fun q ↦ f₀.NormalSpace q infty_ne_zero) q) w) := by
  intro w
  let := f₀.normalSpaceFiberBundle infty_ne_zero hdim
  let := f₀.normalSpaceVectorBundle infty_ne_zero hdim
  obtain ⟨⟨u, v⟩, rfl⟩ := (Bundle.zeroSectionTangentEquiv (I := J) (F := P)
    (V := fun q ↦ f₀.NormalSpace q infty_ne_zero) q).symm.surjective w
  rw [f₀.mfderiv_normalExp_zeroSection_apply infty_ne_zero (by simp) hdim, map_add, hAf]
  exact mfderiv_twistedExp_zeroSection_apply f₀ f₁ A hA hdim q u v

include hA in
/-- The twisted exponential is a partial diffeomorphism on a neighbourhood of the zero
section. -/
private theorem exists_partialDiffeomorph_twistedExp [SecondCountableTopology M₀]
    [SecondCountableTopology M₁] [Nonempty Q]
    (hAf : ∀ q v, A q (mfderiv J I₀ f₀ q v) = mfderiv J I₁ f₁ q v) :
    letI := f₀.normalSpaceFiberBundle infty_ne_zero hdim
    ∃ Φ : PartialDiffeomorph (J.prod 𝓘(ℝ, P)) I₁
        (TotalSpace P (fun q ↦ f₀.NormalSpace q infty_ne_zero)) M₁ ∞,
      (∀ q, zeroSection P (fun q ↦ f₀.NormalSpace q infty_ne_zero) q ∈ Φ.source) ∧
        ⇑Φ = twistedExp f₀ f₁ A := by
  let := f₀.normalSpaceFiberBundle infty_ne_zero hdim
  let := f₀.normalSpaceVectorBundle infty_ne_zero hdim
  let := f₀.normalSpaceContMDiffVectorBundle (m := ∞) infty_ne_zero (by simp) hdim
  let N := TotalSpace P (fun q ↦ f₀.NormalSpace q infty_ne_zero)
  let z := zeroSection P (fun q ↦ f₀.NormalSpace q infty_ne_zero)
  let Θ := twistedExp (P := P) f₀ f₁ A
  have hΘz (q : Q) : IsLocalDiffeomorphAt (J.prod 𝓘(ℝ, P)) I₁ ∞ Θ (z q) := by
    obtain ⟨e, he⟩ := f₀.isInvertible_mfderiv_normalExp_zeroSection (P := P) infty_ne_zero
      (by simp) hdim q
    refine isLocalDiffeomorphAt_of_mfderiv_eq (contMDiffOn_twistedExp f₀ f₁ A hA hdim)
      (isOpen_twistedExpDomain f₀ f₁ A hA hdim) (zeroSection_mem_twistedExpDomain f₀ f₁ A q)
      BoundarylessManifold.isInteriorPoint (by simp) (e := e.trans (A q)) ?_
    refine ContinuousLinearMap.ext fun w ↦ ?_
    rw [mfderiv_twistedExp_zeroSection_apply_eq_apply_mfderiv_normalExp f₀ f₁ A hA hdim hAf,
      ← he, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe]
    exact e.trans_apply (A q) w
  let U : Set N := {p | IsLocalDiffeomorphAt (J.prod 𝓘(ℝ, P)) I₁ ∞ Θ p}
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr fun _ hp ↦ hp.eventually
  let S : Set N := U ∩ twistedExpDomain f₀ f₁ A
  have hS : IsOpen S := hU.inter (isOpen_twistedExpDomain f₀ f₁ A hA hdim)
  have hzS : range z ⊆ S := by
    rintro _ ⟨q, rfl⟩
    exact ⟨hΘz q, zeroSection_mem_twistedExpDomain f₀ f₁ A q⟩
  have : T2Space Q := f₀.isEmbedding.t2Space
  have : SecondCountableTopology Q := f₀.isEmbedding.isInducing.secondCountableTopology
  have := Manifold.locallyCompact_of_finiteDimensional (M := N) (J.prod 𝓘(ℝ, P))
  have := Manifold.locallyCompact_of_finiteDimensional (M := M₁) I₁
  have : MetrizableSpace M₁ := Manifold.metrizableSpace I₁ M₁
  have : MetrizableSpace N := Manifold.metrizableSpace (J.prod 𝓘(ℝ, P)) _
  have : Nonempty N := Nonempty.map z inferInstance
  have hΘf : Θ ∘ z = f₁ := funext (twistedExp_zeroSection f₀ f₁ A)
  obtain ⟨Φ, hzΦ, -, -, hΦ⟩ := IsLocalDiffeomorphOn.exists_partialDiffeomorph_near_section
    (fun p : S ↦ p.property.1) hS hzS (Bundle.Trivialization.continuous_zeroSection ℝ)
    (π P (fun q ↦ f₀.NormalSpace q infty_ne_zero)) (FiberBundle.continuous_proj _ _)
    (fun _ ↦ rfl) (hΘf ▸ f₁.isEmbedding.isInducing)
  exact ⟨Φ, fun q ↦ hzΦ (mem_range_self q), hΦ⟩

include hA hdim in
/-- The theorem `exists_diffeomorph_opens_mfderiv_eq` for given metrics on `M₀` and `M₁` and
nonempty `Q`: `ψ` is the twisted exponential composed with the inverse of the normal
exponential of `f₀`. -/
private theorem exists_diffeomorph_opens_mfderiv_eq_of_riemannian [SecondCountableTopology M₀]
    [SecondCountableTopology M₁] [Nonempty Q]
    (hAf : ∀ q v, A q (mfderiv J I₀ f₀ q v) = mfderiv J I₁ f₁ q v) :
    ∃ (U₀ : Opens M₀) (U₁ : Opens M₁) (ψ : U₀ ≃ₘ⟮I₀, I₁⟯ U₁),
      ∀ q, ∃ h : f₀ q ∈ U₀, (ψ ⟨f₀ q, h⟩ : M₁) = f₁ q ∧
        mfderiv I₀ I₁ ψ ⟨f₀ q, h⟩ =
          (A q : TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace I₁ (f₁ q)) := by
  let := f₀.normalSpaceFiberBundle infty_ne_zero hdim
  let := f₀.normalSpaceVectorBundle infty_ne_zero hdim
  let := f₀.normalSpaceContMDiffVectorBundle (m := ∞) infty_ne_zero (by simp) hdim
  let z := zeroSection P (fun q ↦ f₀.NormalSpace q infty_ne_zero)
  obtain ⟨Φ₀, hz₀, -, -, -, hΦ₀⟩ := f₀.exists_partialDiffeomorph_normalExp_subset (m := ∞)
    (P := P) infty_ne_zero (by simp) (by simp) hdim isOpen_univ (subset_univ _)
  obtain ⟨Φ₁, hz₁, hΦ₁⟩ := exists_partialDiffeomorph_twistedExp f₀ f₁ A hA hdim hAf
  let Ψ := Φ₀.symm.trans Φ₁
  have hΦ₀z (q : Q) : Φ₀ (z q) = f₀ q := by
    rw [hΦ₀]
    exact f₀.normalExp_zeroSection infty_ne_zero q
  have hsymm (q : Q) : Φ₀.symm (f₀ q) = z q := by
    rw [← hΦ₀z]
    exact Φ₀.left_inv (hz₀ q)
  have hmem (q : Q) : f₀ q ∈ Ψ.source := by
    rw [PartialDiffeomorph.trans_source, mem_inter_iff, mem_preimage, hsymm]
    refine ⟨?_, hz₁ q⟩
    rw [PartialDiffeomorph.symm_toPartialEquiv, PartialEquiv.symm_source, ← hΦ₀z]
    exact Φ₀.map_source (hz₀ q)
  refine ⟨⟨Ψ.source, Ψ.open_source⟩, ⟨Ψ.target, Ψ.open_target⟩, Ψ.toDiffeomorphSourceTarget,
    fun q ↦ ⟨hmem q, ?_, ?_⟩⟩
  · rw [PartialDiffeomorph.toDiffeomorphSourceTarget_apply_coe, PartialDiffeomorph.coe_trans,
      Function.comp_apply, hsymm, hΦ₁]
    exact twistedExp_zeroSection f₀ f₁ A q
  · refine ContinuousLinearMap.ext fun v ↦ ?_
    -- The derivative of `ψ` is that of `Ψ = Φ₁ ∘ Φ₀⁻¹`, read through the inclusions.
    have h := Manifold.mfderiv_apply_of_subtype_val_comp_eq (I := I₀) (I' := I₁)
      (f := Ψ.toDiffeomorphSourceTarget) (A := Ψ) (x := ⟨f₀ q, hmem q⟩)
      (funext Ψ.toDiffeomorphSourceTarget_apply_coe) v
    have hd₀ : MDifferentiableAt I₀ (J.prod 𝓘(ℝ, P)) Φ₀.symm (f₀ q) :=
      Φ₀.symm.mdifferentiableAt infty_ne_zero (hmem q).1
    have hd₁ : MDifferentiableAt (J.prod 𝓘(ℝ, P)) I₁ Φ₁ (Φ₀.symm (f₀ q)) :=
      Φ₁.mdifferentiableAt infty_ne_zero (hmem q).2
    have hv : mfderiv (J.prod 𝓘(ℝ, P)) I₀ Φ₀ (Φ₀.symm (f₀ q))
        (mfderiv I₀ (J.prod 𝓘(ℝ, P)) Φ₀.symm (f₀ q) v) = v :=
      Φ₀.mfderiv_apply_mfderiv_symm_apply infty_ne_zero (hmem q).1 v
    -- The base point `Φ₀⁻¹ (f₀ q)` is only propositionally the zero vector `z q`, and the
    -- tangent vectors there depend on it, so the derivative of `Φ₁` is computed at every point
    -- equal to `z q`.
    have hΘ : ∀ x, x = z q → ∀ w, mfderiv (J.prod 𝓘(ℝ, P)) I₁ Φ₁ x w =
        A q (mfderiv (J.prod 𝓘(ℝ, P)) I₀ Φ₀ x w) := by
      rintro x rfl w
      rw [hΦ₁, hΦ₀]
      exact mfderiv_twistedExp_zeroSection_apply_eq_apply_mfderiv_normalExp f₀ f₁ A hA hdim
        hAf q w
    refine h.trans ((mfderiv_comp_apply (f₀ q) hd₁ hd₀ v).trans ?_)
    rw [hΘ _ (hsymm q), hv]
    exact (ContinuousLinearEquiv.coe_apply (A q) v).symm

end Metric

/-- **Diffeomorphisms of neighbourhoods with a prescribed derivative.** Let `f₀ : Q → M₀` and
`f₁ : Q → M₁` be smooth embeddings into second countable Hausdorff manifolds without boundary,
and let `A q : T_{f₀ q} M₀ ≃L[ℝ] T_{f₁ q} M₁` be linear isomorphisms forming a smooth section over
`Q` of the bundle of linear maps between the pull-backs `f₀ *ᵖ TM₀` and `f₁ *ᵖ TM₁`, with
`A q (df₀ q v) = df₁ q v`. Then there are open sets `U₀ ⊆ M₀` and `U₁ ⊆ M₁` and a diffeomorphism
`ψ : U₀ ≃ U₁` such that, for every `q`, `f₀ q ∈ U₀`, `ψ (f₀ q) = f₁ q` and the derivative of `ψ`
at `f₀ q` is `A q`. Neither compactness of `Q` nor closedness of the images is assumed. -/
theorem exists_diffeomorph_opens_mfderiv_eq [SecondCountableTopology M₀]
    [SecondCountableTopology M₁]
    (f₀ : SmoothEmbedding J I₀ ∞ Q M₀) (f₁ : SmoothEmbedding J I₁ ∞ Q M₁)
    (A : ∀ q, TangentSpace I₀ (f₀ q) ≃L[ℝ] TangentSpace I₁ (f₁ q))
    (hA : ContMDiff J (J.prod 𝓘(ℝ, E₀ →L[ℝ] E₁)) ∞ (fun q ↦ TotalSpace.mk' (E₀ →L[ℝ] E₁)
      (E := fun q ↦ ((f₀ : Q → M₀) *ᵖ (TangentSpace I₀)) q →L[ℝ]
        ((f₁ : Q → M₁) *ᵖ (TangentSpace I₁)) q) q
        (A q : TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace I₁ (f₁ q))))
    (hAf : ∀ q v, A q (mfderiv J I₀ f₀ q v) = mfderiv J I₁ f₁ q v) :
    ∃ (U₀ : Opens M₀) (U₁ : Opens M₁) (ψ : U₀ ≃ₘ⟮I₀, I₁⟯ U₁),
      ∀ q, ∃ h : f₀ q ∈ U₀, (ψ ⟨f₀ q, h⟩ : M₁) = f₁ q ∧
        mfderiv I₀ I₁ ψ ⟨f₀ q, h⟩ =
          (A q : TangentSpace I₀ (f₀ q) →L[ℝ] TangentSpace I₁ (f₁ q)) := by
  cases isEmpty_or_nonempty Q with
  | inl hQ =>
    exact ⟨⊥, ⊥, Diffeomorph.ofIsEmpty, fun q ↦ (hQ.false q).elim⟩
  | inr hQ =>
    have := Manifold.locallyCompact_of_finiteDimensional (M := M₀) I₀
    have := Manifold.locallyCompact_of_finiteDimensional (M := M₁) I₁
    obtain ⟨g₀⟩ := nonempty_contMDiffRiemannianMetric (IB := I₀) (n := ⊤) (F := E₀)
      (E := fun y : M₀ ↦ TangentSpace I₀ y)
    let : RiemannianBundle (fun y : M₀ ↦ TangentSpace I₀ y) := ⟨g₀.toRiemannianMetric⟩
    let : IsContMDiffRiemannianBundle I₀ ∞ E₀ (fun y : M₀ ↦ TangentSpace I₀ y) :=
      Bundle.instIsContMDiffRiemannianBundle g₀
    obtain ⟨g₁⟩ := nonempty_contMDiffRiemannianMetric (IB := I₁) (n := ⊤) (F := E₁)
      (E := fun y : M₁ ↦ TangentSpace I₁ y)
    let : RiemannianBundle (fun y : M₁ ↦ TangentSpace I₁ y) := ⟨g₁.toRiemannianMetric⟩
    let : IsContMDiffRiemannianBundle I₁ ∞ E₁ (fun y : M₁ ↦ TangentSpace I₁ y) :=
      Bundle.instIsContMDiffRiemannianBundle g₁
    exact exists_diffeomorph_opens_mfderiv_eq_of_riemannian f₀ f₁ A hA
      (P := EuclideanSpace ℝ (Fin (Module.finrank ℝ E₀ - Module.finrank ℝ EQ)))
      finrank_euclideanSpace_fin hAf

end TauCeti.SmoothEmbedding
