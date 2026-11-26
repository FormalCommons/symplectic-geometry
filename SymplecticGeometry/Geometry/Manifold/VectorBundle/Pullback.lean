/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
public import SymplecticGeometry.Topology.VectorBundle.Pullback
import TauCeti.Analysis.Calculus.ContDiff.ContinuousAlternatingMap
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Topology.VectorBundle.ContinuousAlternatingMap

/-!
# Sections of the alternating and bilinear bundles of a pull-back

Let `V` be a vector bundle over `B` and `f : X → B` a `C^n` map. A family
`A x : V (f x) [⋀^ι]→L[𝕜] G` of alternating maps with values in a fixed normed space `G` can be
read in two ways: as a section of the bundle of alternating maps from `f *ᵖ V` to the trivial
bundle `Bundle.Trivial X G` over `X`, or as a map from `X` into the total space of the bundle of
alternating maps from `V` to `Bundle.Trivial B G`, lying over `f`. This file shows that the two
are `C^n` together (`Bundle.Pullback.contMDiff_continuousAlternatingMap_section_iff`), the
analogue for alternating maps of Tau Ceti's `Bundle.Pullback.contMDiff_hom_section_iff`. First,
the identity of each fibre is a `C^n` map from the total space of the pull-back of the bundle of
alternating maps on `V` to that of the bundle of alternating maps on `f *ᵖ V`
(`Bundle.Pullback.contMDiff_continuousAlternatingMap_totalSpace`): near a point, Mathlib's
`contMDiffAt_continuousAlternatingMap_bundle` and Tau Ceti's `Bundle.Pullback.contMDiffAt_lift`
reduce this to coordinate expressions, which agree on a neighbourhood by
`ContinuousAlternatingMap.inCoordinates_pullback_trivial_of_mem`
(`SymplecticGeometry.Topology.VectorBundle.Pullback`). The section of `f *ᵖ V` is then that map
composed with `x ↦ ⟨x, A x⟩`, which is `C^n` by Tau Ceti's `Bundle.Pullback.contMDiff_iff`.
The other direction follows Tau Ceti's proof, with the same comparison of coordinates.

In the same way, a family `β x` of continuous bilinear forms on `V (f x)` is a `C^n` section of
the bundle of bilinear forms on `f *ᵖ V` exactly when `x ↦ ⟨f x, β x⟩` is `C^n` into the bundle
of bilinear forms on `V` (`Bundle.Pullback.contMDiff_bilinear_section_iff`). The proof is again
that of Tau Ceti's `Bundle.Pullback.contMDiff_hom_section_iff`, the two coordinate expressions
agreeing near each point by Mathlib's `inCoordinates_apply_eq₂`.

Finally, for a `C^∞` map `f : Q → M`, the derivative `(q, v) ↦ (q, df_q v)` is a `C^∞` map from
the tangent bundle of `Q` to the pull-back `f *ᵖ TM`
(`Bundle.Pullback.contMDiff_totalSpace_mfderiv`), so the maps `df_q` form a `C^∞` section of the
bundle of linear maps from `TQ` to `f *ᵖ TM` (`Bundle.Pullback.contMDiff_mfderiv_hom`). When `f`
is moreover an immersion, the tangent
images `df_q(T_q Q)` have `C^∞` local frames in `f *ᵖ TM`
(`Bundle.Pullback.hasLocalContMDiffSubbundleFrames_range_mfderiv`), by Tau Ceti's constant-rank
criterion `TauCeti.hasLocalContMDiffSubbundleFrames_of_contMDiff_totalSpace_range`.

For a family of maps `f (p, ·) : M → M'` depending on a parameter `p ∈ P`, jointly `C^n` on
`P × M`, precomposition with the differentials `d(f (p, ·))ₓ` sends alternating maps on the tangent
space of `M'` at `f (p, x)` to alternating maps on that of `M` at `x`. For `m + 1 ≤ n`, the map
`(p, x, ξ) ↦ (x, ξ ∘ d(f (p, ·))ₓ)`, from the total space of the pull-back along `f` of the bundle
of alternating maps on `TM'` with values in a fixed normed space `G` to the total space of that
bundle on `TM`, is `C^m`
(`Bundle.Pullback.contMDiff_totalSpace_compContinuousLinearMap_mfderiv`). The proof adapts that
of Tau Ceti's `ContMDiffAt.mpullback_form_family`, which pulls back one fixed form along the
family, to an alternating map that varies with the point of the total space, and its last step,
the agreement of the two coordinate expressions near a point, adapts that of Tau Ceti's
`TauCeti.inCoordinates_mpullback_family`. In the trivializations at a point, the map is Tau
Ceti's `ContinuousAlternatingMap.compContinuousLinearMapCLM` applied to the tangent coordinates
of the differentials, which are `C^m` by Mathlib's `ContMDiffAt.mfderiv`, and to the coordinates
of `ξ`.

The file also gives, as continuous linear equivalences, the identity of the fibres of the
pull-backs along the identity and along a composite: `Bundle.Pullback.idFiberEquiv` from the fibre
of `id *ᵖ E` at `x` to `E x`, and `Bundle.Pullback.compFiberEquiv` from the fibre of
`(g ∘ f) *ᵖ E` at `z` to that of `f *ᵖ (g *ᵖ E)`. They are the maps that Tau Ceti's
`Bundle.Pullback.idDiffeomorph` and `Bundle.Pullback.compDiffeomorph` induce on the fibres, and
their types name both fibres as they are written, which `ContinuousLinearEquiv.refl` of one of
them does not: since `Bundle.Pullback` is not reducible, the lemmas about `refl` do not apply to it
when it is used as a map between the two.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 2 (induced bundles).
-/

public section

open Bundle
open scoped Manifold

variable {𝕜 B X F G K ι EB HB EX HX : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
  {IX : ModelWithCorners 𝕜 EX HX} [TopologicalSpace X] [ChartedSpace HX X]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {V : B → Type*}
  [∀ b, AddCommGroup (V b)] [∀ b, Module 𝕜 (V b)] [∀ b, TopologicalSpace (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [FunLike K X B] [ContinuousMapClass K X B] {n : WithTop ℕ∞}

namespace Bundle.Pullback

/-- Along a `C^n` map `f`, the identity of each fibre is a `C^n` map from the total space of the
pull-back along `f` of the bundle of alternating maps from `V` to `Bundle.Trivial B G`, to the
total space of the bundle of alternating maps from `f *ᵖ V` to `Bundle.Trivial X G`. No rank or
smooth-bundle assumption is needed. -/
theorem contMDiff_continuousAlternatingMap_totalSpace [Fintype ι] (f : K)
    (hf : ContMDiff IX IB n f) :
    ContMDiff (IX.prod 𝓘(𝕜, F [⋀^ι]→L[𝕜] G)) (IX.prod 𝓘(𝕜, F [⋀^ι]→L[𝕜] G)) n
      (fun p : TotalSpace (F [⋀^ι]→L[𝕜] G)
          ((f : X → B) *ᵖ (fun b ↦ V b [⋀^ι]→L[𝕜] Bundle.Trivial B G b)) ↦
        TotalSpace.mk' (F [⋀^ι]→L[𝕜] G)
          (E := fun x ↦ ((f : X → B) *ᵖ V) x [⋀^ι]→L[𝕜] Bundle.Trivial X G x) p.proj p.snd) := by
  intro p₀
  have hl := (contMDiffAt_continuousAlternatingMap_bundle _).mp
    (Pullback.contMDiffAt_lift f (hf p₀.proj))
  have hp₀ : (f ∘ TotalSpace.proj) ⁻¹' (trivializationAt F V (f p₀.proj)).baseSet ∈ nhds p₀ :=
    (hf.continuous.comp (FiberBundle.continuous_proj _ _)).continuousAt.preimage_mem_nhds
      ((trivializationAt F V (f p₀.proj)).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt F V (f p₀.proj)))
  rw [contMDiffAt_continuousAlternatingMap_bundle]
  refine ⟨(contMDiff_proj _).contMDiffAt, hl.2.congr_of_eventuallyEq ?_⟩
  filter_upwards [hp₀] with p hp
  exact ContinuousAlternatingMap.inCoordinates_pullback_trivial_of_mem f p₀.proj p.proj p.snd hp

/-- A family `A x` of alternating maps from `V (f x)` to `G`, along a `C^n` map `f`, is a `C^n`
section of the bundle of alternating maps from `f *ᵖ V` to the trivial bundle with fibre `G`
exactly when `x ↦ ⟨f x, A x⟩` is `C^n` into the bundle of alternating maps from `V` to the
trivial bundle with fibre `G`. No rank or smooth-bundle assumption is needed. -/
theorem contMDiff_continuousAlternatingMap_section_iff [Fintype ι] (f : K)
    (hf : ContMDiff IX IB n f) (A : ∀ x, V (f x) [⋀^ι]→L[𝕜] G) :
    ContMDiff IX (IX.prod 𝓘(𝕜, F [⋀^ι]→L[𝕜] G)) n
        (fun x ↦ TotalSpace.mk' (F [⋀^ι]→L[𝕜] G)
          (E := fun x ↦ ((f : X → B) *ᵖ V) x [⋀^ι]→L[𝕜] Bundle.Trivial X G x) x (A x)) ↔
      ContMDiff IX (IB.prod 𝓘(𝕜, F [⋀^ι]→L[𝕜] G)) n
        (fun x ↦ TotalSpace.mk' (F [⋀^ι]→L[𝕜] G)
          (E := fun b ↦ V b [⋀^ι]→L[𝕜] Bundle.Trivial B G b) (f x) (A x)) := by
  have heq (x : X) :
      (fun y ↦ ContinuousAlternatingMap.inCoordinates F G (E₁ := (f : X → B) *ᵖ V)
        (E₂ := Bundle.Trivial X G) x y x y (A y)) =ᶠ[nhds x]
      (fun y ↦ ContinuousAlternatingMap.inCoordinates F G (E₁ := V)
        (E₂ := Bundle.Trivial B G) (f x) (f y) (f x) (f y) (A y)) := by
    filter_upwards [hf.continuous.continuousAt.preimage_mem_nhds
      ((trivializationAt F V (f x)).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt F V (f x)))] with y hy
    exact ContinuousAlternatingMap.inCoordinates_pullback_trivial_of_mem f x y (A y) hy
  constructor
  · intro h x
    have hx := (contMDiffAt_continuousAlternatingMap_bundle _).mp (h x)
    rw [contMDiffAt_continuousAlternatingMap_bundle]
    exact ⟨hf x, hx.2.congr_of_eventuallyEq (heq x).symm⟩
  · intro h
    have hA : ContMDiff IX (IX.prod 𝓘(𝕜, F [⋀^ι]→L[𝕜] G)) n
        (fun x ↦ TotalSpace.mk' (F [⋀^ι]→L[𝕜] G)
          (E := (f : X → B) *ᵖ (fun b ↦ V b [⋀^ι]→L[𝕜] Bundle.Trivial B G b)) x (A x)) :=
      (Pullback.contMDiff_iff f hf).2 ⟨contMDiff_id, by simpa only [Pullback.lift_mk] using h⟩
    exact (contMDiff_continuousAlternatingMap_totalSpace f hf).comp hA

end Bundle.Pullback

section Bilinear

variable {𝕜 B X F K EB HB EX HX : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
  {IX : ModelWithCorners 𝕜 EX HX} [TopologicalSpace X] [ChartedSpace HX X]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {V : B → Type*}
  [∀ b, AddCommGroup (V b)] [∀ b, Module 𝕜 (V b)] [∀ b, TopologicalSpace (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [FunLike K X B] [ContinuousMapClass K X B] {n : WithTop ℕ∞}

namespace Bundle.Pullback

/-- A family `β x` of continuous bilinear forms on `V (f x)`, along a `C^n` map `f`, is a `C^n`
section of the bundle of bilinear forms on `f *ᵖ V` exactly when `x ↦ ⟨f x, β x⟩` is `C^n` into
the bundle of bilinear forms on `V`. No rank or smooth-bundle assumption is needed. -/
theorem contMDiff_bilinear_section_iff (f : K) (hf : ContMDiff IX IB n f)
    (β : ∀ x, V (f x) →L[𝕜] V (f x) →L[𝕜] 𝕜) :
    ContMDiff IX (IX.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] 𝕜)) n
        (fun x ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] 𝕜)
          (E := fun x ↦ ((f : X → B) *ᵖ V) x →L[𝕜] ((f : X → B) *ᵖ V) x →L[𝕜] 𝕜) x (β x)) ↔
      ContMDiff IX (IB.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] 𝕜)) n
        (fun x ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] 𝕜)
          (E := fun b ↦ V b →L[𝕜] V b →L[𝕜] 𝕜) (f x) (β x)) := by
  have heq (x : X) :
      (fun y ↦ ContinuousLinearMap.inCoordinates F ((f : X → B) *ᵖ V) (F →L[𝕜] 𝕜)
        (fun y ↦ ((f : X → B) *ᵖ V) y →L[𝕜] Trivial X 𝕜 y) x y x y (β y)) =ᶠ[nhds x]
      (fun y ↦ ContinuousLinearMap.inCoordinates F V (F →L[𝕜] 𝕜)
        (fun b ↦ V b →L[𝕜] Trivial B 𝕜 b) (f x) (f y) (f x) (f y) (β y)) := by
    filter_upwards [hf.continuous.continuousAt.preimage_mem_nhds
      ((trivializationAt F V (f x)).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt F V (f x)))] with y hy
    have hy' : y ∈ (trivializationAt F ((f : X → B) *ᵖ V) x).baseSet := hy
    have hs (u : F) : (trivializationAt F ((f : X → B) *ᵖ V) x).symm y u =
        (trivializationAt F V (f x)).symm (f y) u :=
      (trivializationAt F V (f x)).symm_pullback f hy u
    ext v w
    -- The fibres of the pull-back carry the module instances of `V` under other names; `erw`
    -- sees through them.
    erw [inCoordinates_apply_eq₂ (E₃ := Trivial X 𝕜) hy' hy' (Set.mem_univ _),
      inCoordinates_apply_eq₂ (E₃ := Trivial B 𝕜) hy hy (Set.mem_univ _)]
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization, hs]
    -- Both sides are now the same expression, up to those instances.
    rfl
  constructor
  · intro h x
    have hx := (contMDiffAt_hom_bundle _).mp (h x)
    rw [contMDiffAt_hom_bundle]
    exact ⟨hf x, hx.2.congr_of_eventuallyEq (heq x).symm⟩
  · intro h x
    have hx := (contMDiffAt_hom_bundle _).mp (h x)
    rw [contMDiffAt_hom_bundle]
    exact ⟨contMDiffAt_id, hx.2.congr_of_eventuallyEq (heq x)⟩

end Bundle.Pullback

end Bilinear

section FiberEquiv

/-! ### The identity of the fibres of pull-backs along the identity and along a composite -/

variable {𝕜 EM HM B EM' HM' B' EM'' HM'' B'' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM]
  {I : ModelWithCorners 𝕜 EM HM} [TopologicalSpace B] [ChartedSpace HM B]
  [NormedAddCommGroup EM'] [NormedSpace 𝕜 EM'] [TopologicalSpace HM']
  {I' : ModelWithCorners 𝕜 EM' HM'} [TopologicalSpace B'] [ChartedSpace HM' B']
  [NormedAddCommGroup EM''] [NormedSpace 𝕜 EM''] [TopologicalSpace HM'']
  {I'' : ModelWithCorners 𝕜 EM'' HM''} [TopologicalSpace B''] [ChartedSpace HM'' B'']
  {m : WithTop ℕ∞} {R : Type*} [Semiring R] (E : B → Type*) [∀ b, AddCommMonoid (E b)]
  [∀ b, Module R (E b)] [∀ b, TopologicalSpace (E b)]

namespace Bundle.Pullback

variable (I m R) in
/-- The fibre at `x` of the pull-back of `E` along the identity is `E x`: the identity of `E x`,
as a continuous linear equivalence from that fibre to `E x`. This is the map that Tau Ceti's
`Bundle.Pullback.idDiffeomorph` induces on the fibre at `x`. -/
def idFiberEquiv (x : B) : ((ContMDiffMap.id : C^m⟮I, B; I, B⟯) *ᵖ E) x ≃L[R] E x :=
  ContinuousLinearEquiv.refl R (E x)

/-- `idFiberEquiv` sends a vector to itself.

This is not `@[simp]`: the right-hand side is a vector of the pull-back fibre, so the lemmas
that evaluate a form or a map on `E x` no longer match it once it replaces
`idFiberEquiv I m R E x v`. -/
theorem idFiberEquiv_apply {x : B} (v : ((ContMDiffMap.id : C^m⟮I, B; I, B⟯) *ᵖ E) x) :
    idFiberEquiv I m R E x v = (v : E x) :=
  (rfl)

/-- The inverse of `idFiberEquiv` sends a vector to itself. It is not `@[simp]`, for the reason
given at `idFiberEquiv_apply`. -/
theorem idFiberEquiv_symm_apply {x : B} (v : E x) :
    (idFiberEquiv I m R E x).symm v = (v : ((ContMDiffMap.id : C^m⟮I, B; I, B⟯) *ᵖ E) x) :=
  (rfl)

variable (R) in
/-- The fibre at `z` of the pull-back of `E` along `g ∘ f` is that of the pull-back along `g` and
then along `f`: the identity of `E (g (f z))`, as a continuous linear equivalence between the two
fibres. This is the map that Tau Ceti's `Bundle.Pullback.compDiffeomorph` induces on the fibre
at `z`. -/
def compFiberEquiv (g : C^m⟮I', B'; I, B⟯) (f : C^m⟮I'', B''; I', B'⟯) (z : B'') :
    ((g.comp f : B'' → B) *ᵖ E) z ≃L[R] ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E)) z :=
  ContinuousLinearEquiv.refl R (E (g (f z)))

/-- `compFiberEquiv` sends a vector to itself. It is not `@[simp]`, for the reason given at
`idFiberEquiv_apply`. -/
theorem compFiberEquiv_apply (g : C^m⟮I', B'; I, B⟯) (f : C^m⟮I'', B''; I', B'⟯) {z : B''}
    (v : ((g.comp f : B'' → B) *ᵖ E) z) :
    compFiberEquiv R E g f z v = (v : ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E)) z) :=
  (rfl)

/-- The inverse of `compFiberEquiv` sends a vector to itself. It is not `@[simp]`, for the reason
given at `idFiberEquiv_apply`. -/
theorem compFiberEquiv_symm_apply (g : C^m⟮I', B'; I, B⟯) (f : C^m⟮I'', B''; I', B'⟯) {z : B''}
    (v : ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E)) z) :
    (compFiberEquiv R E g f z).symm v = (v : ((g.comp f : B'' → B) *ᵖ E) z) :=
  (rfl)

end Bundle.Pullback

end FiberEquiv

section MFDeriv

open scoped ContDiff

variable {E E' H H' M Q K : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace Q] [ChartedSpace H' Q]
  [IsManifold J ∞ Q]
  [FunLike K Q M] [ContinuousMapClass K Q M]

namespace Bundle.Pullback

open Module TauCeti

/-- The derivative of a `C^∞` map `f`, as the map `(q, v) ↦ (q, df_q v)` from the tangent bundle
of `Q` to the pull-back `f *ᵖ TM`, is `C^∞`. -/
theorem contMDiff_totalSpace_mfderiv (f : K) (hf : ContMDiff J I ∞ f) :
    ContMDiff (J.prod 𝓘(ℝ, E')) (J.prod 𝓘(ℝ, E)) ∞
      (fun p : TangentBundle J Q ↦
        (⟨p.proj, mfderiv J I f p.proj p.snd⟩ :
          TotalSpace E ((f : Q → M) *ᵖ (TangentSpace I)))) := by
  rw [Bundle.Pullback.contMDiff_iff f hf]
  exact ⟨contMDiff_proj _, hf.contMDiff_tangentMap (by simp)⟩

/-- The derivatives `df_q : T_q Q → T_{f q} M` of a `C^∞` map `f` form a `C^∞` section of the
bundle of continuous linear maps from `TQ` to the pull-back `f *ᵖ TM`. -/
theorem contMDiff_mfderiv_hom [FiniteDimensional ℝ E'] (f : K) (hf : ContMDiff J I ∞ f) :
    ContMDiff J (J.prod 𝓘(ℝ, E' →L[ℝ] E)) ∞
      (fun q ↦ TotalSpace.mk' (E' →L[ℝ] E)
        (E := fun q ↦ TangentSpace J q →L[ℝ] ((f : Q → M) *ᵖ (TangentSpace I)) q) q
        (mfderiv J I f q)) :=
  (contMDiff_hom_bundle_iff (E₁ := TangentSpace J) (E₂ := (f : Q → M) *ᵖ (TangentSpace I))
    fun q ↦ mfderiv J I f q).2 (contMDiff_totalSpace_mfderiv f hf)

/-- **Frames of the tangent image.** For a `C^∞` immersion `f`, the images `df_q(T_q Q)` of the
tangent spaces of `Q` have `C^∞` local frames of size `dim Q` in the pull-back `f *ᵖ TM`. -/
theorem hasLocalContMDiffSubbundleFrames_range_mfderiv [FiniteDimensional ℝ E] (f : K)
    (hi : Manifold.IsImmersion J I ∞ f) :
    HasLocalContMDiffSubbundleFrames J ∞ E (Fin (finrank ℝ E'))
      (E := (f : Q → M) *ᵖ (TangentSpace I)) fun q ↦ (mfderiv J I f q).range := by
  have : ContMDiffVectorBundle ∞ E' (TangentSpace J : Q → Type _) J :=
    TangentBundle.contMDiffVectorBundle
  refine hasLocalContMDiffSubbundleFrames_of_contMDiff_totalSpace_range
    (fun q ↦ (mfderiv J I f q : TangentSpace J q →ₗ[ℝ] TangentSpace I (f q)))
    (contMDiff_totalSpace_mfderiv f hi.contMDiff) (fun q ↦ rfl) fun q ↦ ?_
  -- The ranges are subspaces of the fibres of the pull-back, which are the tangent spaces of
  -- `M` under another name.
  have h : finrank ℝ (LinearMap.range
      (mfderiv J I f q : TangentSpace J q →ₗ[ℝ] TangentSpace I (f q))) = finrank ℝ E' :=
    LinearMap.finrank_range_of_inj (hi.mfderiv_injective (by simp) q)
  exact h

end Bundle.Pullback

end MFDeriv

section MFDerivFamily

variable {E E' EP H H' HP M M' P K ι : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' 1 M']
  [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  [IsManifold IP 1 P]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FunLike K (P × M) M'] [ContinuousMapClass K (P × M) M'] {m n : WithTop ℕ∞}

namespace Bundle.Pullback

/-- Pulling back alternating maps along the differentials of a `C^n` family of maps
`f (p, ·) : M → M'` is `C^m` for `m + 1 ≤ n`: the map `(p, x, ξ) ↦ (x, ξ ∘ d(f (p, ·))ₓ)`, from
the total space of the pull-back along `f` of the bundle of alternating maps on `TM'` to the total
space of the bundle of alternating maps on `TM`, both with values in `G`, is `C^m`. -/
theorem contMDiff_totalSpace_compContinuousLinearMap_mfderiv (f : K)
    (hf : ContMDiff (IP.prod I) I' n f) (hmn : m + 1 ≤ n) :
    ContMDiff ((IP.prod I).prod 𝓘(ℝ, E' [⋀^ι]→L[ℝ] G)) (I.prod 𝓘(ℝ, E [⋀^ι]→L[ℝ] G)) m
      fun q : TotalSpace (E' [⋀^ι]→L[ℝ] G)
          ((f : P × M → M') *ᵖ fun y ↦ TangentSpace I' y [⋀^ι]→L[ℝ] Trivial M' G y) ↦
        TotalSpace.mk' (E [⋀^ι]→L[ℝ] G) (E := fun x ↦ TangentSpace I x [⋀^ι]→L[ℝ] Trivial M G x)
          q.proj.2 (q.snd.compContinuousLinearMap
            (mfderiv I I' (fun y ↦ f (q.proj.1, y)) q.proj.2)) := by
  intro q₀
  have hfm : ContMDiff (IP.prod I) I' m f := hf.of_le (le_trans le_self_add hmn)
  rw [contMDiffAt_continuousAlternatingMap_bundle]
  refine ⟨contMDiffAt_snd.comp q₀ (contMDiff_proj _).contMDiffAt, ?_⟩
  -- The alternating map `q.snd`, read in the trivialization at `f q₀.proj`.
  have hp := (contMDiffAt_continuousAlternatingMap_bundle (IB := I') (ι := ι)
    (F₁ := E') (F₂ := G) (E₁ := TangentSpace I') (E₂ := Trivial M' G) (n := m)
    (fun q ↦ TotalSpace.mk' (E' [⋀^ι]→L[ℝ] G)
      (E := fun y ↦ TangentSpace I' y [⋀^ι]→L[ℝ] Trivial M' G y) (f q.proj) q.snd)
    (x₀ := q₀)).1 (contMDiffAt_lift f (hfm q₀.proj))
  -- The differential `d(f (p, ·))ₓ`, read in tangent coordinates.
  have hl := (ContMDiffAt.mfderiv (fun a : P × M ↦ fun y ↦ f (a.1, y)) Prod.snd
    ((hf _).comp _ (contMDiffAt_fst.fst.prodMk contMDiffAt_snd)) contMDiffAt_snd hmn
    (x₀ := q₀.proj)).comp q₀ (contMDiff_proj _).contMDiffAt
  have hc := ((ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM (𝕜 := ℝ)
    (E := E) (F := E') (G := G) (ι := ι) m).contMDiff.contMDiffAt.comp q₀ hl).clm_apply hp.2
  refine hc.congr_of_eventuallyEq ?_
  have hmem : (trivializationAt E' (TangentSpace I') (f q₀.proj)).baseSet ∈ nhds (f q₀.proj) :=
    (trivializationAt E' (TangentSpace I') (f q₀.proj)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E' (TangentSpace I') (f q₀.proj))
  filter_upwards [hp.1.continuousAt.preimage_mem_nhds hmem] with q hq
  have h := ContinuousAlternatingMap.inCoordinates_compContinuousLinearMap
    (F₁ := E) (F₂ := E') (F₃ := G) (V₁ := TangentSpace I) (V₂ := TangentSpace I')
    (V₃ := Trivial M' G) (x₀ := q₀.proj.2) (y₀ := f q₀.proj) (z₀ := f q₀.proj) (y := f q.proj)
    q.snd (mfderiv I I' (fun y ↦ f (q.proj.1, y)) q.proj.2) hq
  ext v
  simpa only [ContinuousAlternatingMap.inCoordinates,
    Bundle.Trivial.eq_trivialization M G (trivializationAt G (Trivial M G) q₀.proj.2),
    Bundle.Trivial.eq_trivialization M' G (trivializationAt G (Trivial M' G) (f q₀.proj)),
    Bundle.Trivial.continuousLinearMapAt_trivialization,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_def,
    ContinuousLinearMap.id_apply, inTangentCoordinates, id_eq, Function.comp_apply,
    ContinuousAlternatingMap.compContinuousLinearMapCLM_apply, Pullback.lift_proj,
    Pullback.lift_snd, Prod.mk.eta]
    using congrArg (fun a ↦ a v) h

end Bundle.Pullback

end MFDerivFamily

end
