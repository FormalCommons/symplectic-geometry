/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import SymplecticGeometry.Topology.VectorBundle.Pullback
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Tangent.Opens
import TauCeti.Analysis.Calculus.ContDiff.ContinuousAlternatingMap
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
import TauCeti.Geometry.Manifold.VectorBundle.TotalSpace.Basic
import TauCeti.Topology.VectorBundle.ContinuousAlternatingMap
import SymplecticGeometry.Topology.FiberBundle.Basic

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
(`Bundle.Pullback.contMDiff_continuousAlternatingMap_totalSpace`): by Tau Ceti's
`Bundle.contMDiff_totalSpace_of_eventuallyEq`, it is enough that near each point its fibre
coordinates are those of Tau Ceti's `C^n` map `Bundle.Pullback.lift`, which
`ContinuousAlternatingMap.eventually_inCoordinates_pullback_trivial`
(`SymplecticGeometry.Topology.VectorBundle.Pullback`) gives. The identity of each fibre is also
`C^n` in the other direction
(`Bundle.Pullback.contMDiff_continuousAlternatingMap_totalSpace_symm`): through Tau Ceti's
`Bundle.Pullback.contMDiff_iff`, the same lemmas compare the coordinates with those of the
identity, as in Tau Ceti's `Bundle.Pullback.contMDiff_homEquiv`. The two maps form a
diffeomorphism of total spaces
(`Bundle.Pullback.continuousAlternatingMapDiffeomorph`), as Tau Ceti's
`Bundle.Pullback.homDiffeomorph` does for the bundle of linear maps. Each direction of the iff
composes the section with one of these maps and then applies `Bundle.Pullback.contMDiff_iff`.

In the same way, a family `β x` of continuous bilinear forms on `V (f x)` is a `C^n` section of
the bundle of bilinear forms on `f *ᵖ V` exactly when `x ↦ ⟨f x, β x⟩` is `C^n` into the bundle
of bilinear forms on `V` (`Bundle.Pullback.contMDiff_bilinear_section_iff`). The proof is built
in the same way: the identity of each fibre is a `C^n` map from the total space of the pull-back
of the bundle of bilinear forms on `V` to that of the bundle of bilinear forms on `f *ᵖ V`
(`Bundle.Pullback.contMDiff_bilinear_totalSpace`), since the coordinate expressions agree near
each point by `ContinuousLinearMap.eventually_inCoordinates_pullback_bilinear`
(`SymplecticGeometry.Topology.VectorBundle.Pullback`). Its inverse is `C^n` too
(`Bundle.Pullback.contMDiff_bilinear_totalSpace_symm`), the two form the diffeomorphism
`Bundle.Pullback.bilinearDiffeomorph`, and both directions of the iff are compositions with them
followed by Tau Ceti's `Bundle.Pullback.contMDiff_iff`.

Finally, for a `C^∞` map `f : Q → M`, the derivative `(q, v) ↦ (q, df_q v)` is a `C^∞` map from
the tangent bundle of `Q` to the pull-back `f *ᵖ TM`
(`Bundle.Pullback.contMDiff_totalSpace_mfderiv`), so the maps `df_q` form a `C^∞` section of the
bundle of linear maps from `TQ` to `f *ᵖ TM` (`Bundle.Pullback.contMDiff_mfderiv_hom`).

For a map `f : N → M` and a map `g : M → G` into a normed space, the differentials of `g` along
`f` give the map `(x, v) ↦ dg_{f x} v` on the total space of `f *ᵖ TM`. It is the second
component of the tangent map of `g` composed with Tau Ceti's `Bundle.Pullback.lift`, so it is
`C^m` when `f` is `C^m` and `g` is `C^(m + 1)` (`Bundle.Pullback.contMDiff_mfderiv_apply`), and
continuous for any `f` when `g` is `C^1` (`Bundle.Pullback.continuous_mfderiv_apply`). Both hold
at a point, for `f` and `g` that are smooth enough there
(`Bundle.Pullback.contMDiffAt_mfderiv_apply`, `Bundle.Pullback.continuousAt_mfderiv_apply`).

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

Last, for a map `ι : X → M` and a normed space `G`, a family of maps `A x : G → T_(ι x) M` is a
`Cⁿ` section of the bundle of maps from the trivial bundle `ι *ᵖ G` to `ι *ᵖ TM` exactly when it
is `Cⁿ` in tangent coordinates
(`Bundle.Pullback.contMDiffAt_hom_trivial_section_iff_inTangentCoordinates`), by Tau Ceti's
`Bundle.Pullback.contMDiffAt_hom_section_iff` and Mathlib's `contMDiffAt_hom_bundle`. This is
the smoothness in which Tau Ceti's `exists_partialDiffeomorph_mfderiv_eq` asks for a prescribed
differential. In the same way, for two continuous maps `f : X → B` and `g : X → C` and vector
bundles `V` over `B` and `W` over `C`, a family of maps `A x : V (f x) → W (g x)` is a `Cⁿ`
section of the bundle of maps from `f *ᵖ V` to `g *ᵖ W` exactly when its coordinates between `V`
and `W` are `Cⁿ` (`Bundle.Pullback.contMDiffAt_hom_section_iff_inCoordinates`), by Mathlib's
`contMDiffAt_hom_bundle` and Tau Ceti's `ContinuousLinearMap.inCoordinates_pullback_of_mem`; it
is the converse of Tau Ceti's `Bundle.Pullback.contMDiffAt_inCoordinates_of_contMDiffAt`. For
tangent bundles these coordinates are tangent coordinates. So, for `g` into an open subset `U` of
`M'`, a section of the bundle of maps from `f *ᵖ TM` to `g *ᵖ TU` is `Cⁿ` exactly when it is one
along `g` followed by the inclusion of `U`
(`Bundle.Pullback.contMDiffAt_hom_section_subtypeVal_iff`).

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
  refine Bundle.contMDiff_totalSpace_of_eventuallyEq (h := Pullback.lift f)
    (contMDiff_proj _) (Pullback.contMDiff_lift f hf) fun p₀ ↦ ?_
  filter_upwards [(FiberBundle.continuous_proj _ _).continuousAt.eventually
    (ContinuousAlternatingMap.eventually_inCoordinates_pullback_trivial (𝕜 := 𝕜) (F := F)
      (G := G) (ι := ι) (V := V) f p₀.proj)] with p hp
  exact hp p.snd

/-- Along a `C^n` map `f`, the identity of each fibre is a `C^n` map from the total space of the
bundle of alternating maps from `f *ᵖ V` to `Bundle.Trivial X G`, to the total space of the
pull-back along `f` of the bundle of alternating maps from `V` to `Bundle.Trivial B G`: the
inverse of the map of `contMDiff_continuousAlternatingMap_totalSpace`. -/
theorem contMDiff_continuousAlternatingMap_totalSpace_symm [Fintype ι] (f : K)
    (hf : ContMDiff IX IB n f) :
    ContMDiff (IX.prod 𝓘(𝕜, F [⋀^ι]→L[𝕜] G)) (IX.prod 𝓘(𝕜, F [⋀^ι]→L[𝕜] G)) n
      (fun p : TotalSpace (F [⋀^ι]→L[𝕜] G)
          (fun x ↦ ((f : X → B) *ᵖ V) x [⋀^ι]→L[𝕜] Bundle.Trivial X G x) ↦
        TotalSpace.mk' (F [⋀^ι]→L[𝕜] G)
          (E := (f : X → B) *ᵖ (fun b ↦ V b [⋀^ι]→L[𝕜] Bundle.Trivial B G b))
          p.proj p.snd) := by
  refine (Pullback.contMDiff_iff f hf).2 ⟨contMDiff_proj _,
    Bundle.contMDiff_totalSpace_of_eventuallyEq (h := id) (hf.comp (contMDiff_proj _))
      contMDiff_id fun p₀ ↦ ?_⟩
  filter_upwards [(FiberBundle.continuous_proj _ _).continuousAt.eventually
    (ContinuousAlternatingMap.eventually_inCoordinates_pullback_trivial (𝕜 := 𝕜) (F := F)
      (G := G) (ι := ι) (V := V) f p₀.proj)] with p hp
  exact (hp p.snd).symm

/-- Along a `C^n` map `f`, the total space of the pull-back along `f` of the bundle of alternating
maps from `V` to `Bundle.Trivial B G` and that of the bundle of alternating maps from `f *ᵖ V` to
`Bundle.Trivial X G` are `C^n` diffeomorphic, by the identity of each fibre. -/
def continuousAlternatingMapDiffeomorph [Fintype ι] (f : K) (hf : ContMDiff IX IB n f) :
    TotalSpace (F [⋀^ι]→L[𝕜] G)
        ((f : X → B) *ᵖ (fun b ↦ V b [⋀^ι]→L[𝕜] Bundle.Trivial B G b))
      ≃ₘ^n⟮IX.prod 𝓘(𝕜, F [⋀^ι]→L[𝕜] G), IX.prod 𝓘(𝕜, F [⋀^ι]→L[𝕜] G)⟯
      TotalSpace (F [⋀^ι]→L[𝕜] G)
        (fun x ↦ ((f : X → B) *ᵖ V) x [⋀^ι]→L[𝕜] Bundle.Trivial X G x) where
  toFun p := ⟨p.proj, p.snd⟩
  invFun p := ⟨p.proj, p.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_continuousAlternatingMap_totalSpace f hf
  contMDiff_invFun := contMDiff_continuousAlternatingMap_totalSpace_symm f hf

/-- `continuousAlternatingMapDiffeomorph` keeps the base point and the alternating map. -/
@[simp]
theorem continuousAlternatingMapDiffeomorph_apply [Fintype ι] (f : K) (hf : ContMDiff IX IB n f)
    (p : TotalSpace (F [⋀^ι]→L[𝕜] G)
      ((f : X → B) *ᵖ (fun b ↦ V b [⋀^ι]→L[𝕜] Bundle.Trivial B G b))) :
    continuousAlternatingMapDiffeomorph f hf p = ⟨p.proj, p.snd⟩ :=
  (rfl)

/-- The inverse of `continuousAlternatingMapDiffeomorph` keeps the base point and the alternating
map. -/
@[simp]
theorem continuousAlternatingMapDiffeomorph_symm_apply [Fintype ι] (f : K)
    (hf : ContMDiff IX IB n f)
    (p : TotalSpace (F [⋀^ι]→L[𝕜] G)
      (fun x ↦ ((f : X → B) *ᵖ V) x [⋀^ι]→L[𝕜] Bundle.Trivial X G x)) :
    (continuousAlternatingMapDiffeomorph f hf).symm p = ⟨p.proj, p.snd⟩ :=
  (rfl)

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
  constructor
  · intro h
    have hA := ((Pullback.contMDiff_iff f hf).1
      ((contMDiff_continuousAlternatingMap_totalSpace_symm f hf).comp h)).2
    simpa only [Function.comp_def, Pullback.lift_mk] using hA
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

/-- Along a `C^n` map `f`, the identity of each fibre is a `C^n` map from the total space of the
pull-back along `f` of the bundle of continuous bilinear forms on `V`, to the total space of the
bundle of continuous bilinear forms on `f *ᵖ V`. No rank or smooth-bundle assumption is
needed. -/
theorem contMDiff_bilinear_totalSpace (f : K) (hf : ContMDiff IX IB n f) :
    ContMDiff (IX.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] 𝕜)) (IX.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] 𝕜)) n
      (fun p : TotalSpace (F →L[𝕜] F →L[𝕜] 𝕜)
          ((f : X → B) *ᵖ (fun b ↦ V b →L[𝕜] V b →L[𝕜] 𝕜)) ↦
        TotalSpace.mk' (F →L[𝕜] F →L[𝕜] 𝕜)
          (E := fun x ↦ ((f : X → B) *ᵖ V) x →L[𝕜] ((f : X → B) *ᵖ V) x →L[𝕜] 𝕜)
          p.proj p.snd) := by
  refine Bundle.contMDiff_totalSpace_of_eventuallyEq (h := Pullback.lift f)
    (contMDiff_proj _) (Pullback.contMDiff_lift f hf) fun p₀ ↦ ?_
  filter_upwards [(FiberBundle.continuous_proj _ _).continuousAt.eventually
    (ContinuousLinearMap.eventually_inCoordinates_pullback_bilinear (𝕜 := 𝕜) (F := F) (V := V)
      f p₀.proj)] with p hp
  exact hp p.snd

/-- Along a `C^n` map `f`, the identity of each fibre is a `C^n` map from the total space of the
bundle of continuous bilinear forms on `f *ᵖ V`, to the total space of the pull-back along `f` of
the bundle of continuous bilinear forms on `V`: the inverse of the map of
`contMDiff_bilinear_totalSpace`. -/
theorem contMDiff_bilinear_totalSpace_symm (f : K) (hf : ContMDiff IX IB n f) :
    ContMDiff (IX.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] 𝕜)) (IX.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] 𝕜)) n
      (fun p : TotalSpace (F →L[𝕜] F →L[𝕜] 𝕜)
          (fun x ↦ ((f : X → B) *ᵖ V) x →L[𝕜] ((f : X → B) *ᵖ V) x →L[𝕜] 𝕜) ↦
        TotalSpace.mk' (F →L[𝕜] F →L[𝕜] 𝕜)
          (E := (f : X → B) *ᵖ (fun b ↦ V b →L[𝕜] V b →L[𝕜] 𝕜)) p.proj p.snd) := by
  refine (Pullback.contMDiff_iff f hf).2 ⟨contMDiff_proj _,
    Bundle.contMDiff_totalSpace_of_eventuallyEq (h := id) (hf.comp (contMDiff_proj _))
      contMDiff_id fun p₀ ↦ ?_⟩
  filter_upwards [(FiberBundle.continuous_proj _ _).continuousAt.eventually
    (ContinuousLinearMap.eventually_inCoordinates_pullback_bilinear (𝕜 := 𝕜) (F := F) (V := V)
      f p₀.proj)] with p hp
  exact (hp p.snd).symm

/-- Along a `C^n` map `f`, the total space of the pull-back along `f` of the bundle of continuous
bilinear forms on `V` and that of the bundle of continuous bilinear forms on `f *ᵖ V` are `C^n`
diffeomorphic, by the identity of each fibre. -/
def bilinearDiffeomorph (f : K) (hf : ContMDiff IX IB n f) :
    TotalSpace (F →L[𝕜] F →L[𝕜] 𝕜) ((f : X → B) *ᵖ (fun b ↦ V b →L[𝕜] V b →L[𝕜] 𝕜))
      ≃ₘ^n⟮IX.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] 𝕜), IX.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] 𝕜)⟯
      TotalSpace (F →L[𝕜] F →L[𝕜] 𝕜)
        (fun x ↦ ((f : X → B) *ᵖ V) x →L[𝕜] ((f : X → B) *ᵖ V) x →L[𝕜] 𝕜) where
  toFun p := ⟨p.proj, p.snd⟩
  invFun p := ⟨p.proj, p.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_bilinear_totalSpace f hf
  contMDiff_invFun := contMDiff_bilinear_totalSpace_symm f hf

/-- `bilinearDiffeomorph` keeps the base point and the bilinear form. -/
@[simp]
theorem bilinearDiffeomorph_apply (f : K) (hf : ContMDiff IX IB n f)
    (p : TotalSpace (F →L[𝕜] F →L[𝕜] 𝕜) ((f : X → B) *ᵖ (fun b ↦ V b →L[𝕜] V b →L[𝕜] 𝕜))) :
    bilinearDiffeomorph f hf p = ⟨p.proj, p.snd⟩ :=
  (rfl)

/-- The inverse of `bilinearDiffeomorph` keeps the base point and the bilinear form. -/
@[simp]
theorem bilinearDiffeomorph_symm_apply (f : K) (hf : ContMDiff IX IB n f)
    (p : TotalSpace (F →L[𝕜] F →L[𝕜] 𝕜)
      (fun x ↦ ((f : X → B) *ᵖ V) x →L[𝕜] ((f : X → B) *ᵖ V) x →L[𝕜] 𝕜)) :
    (bilinearDiffeomorph f hf).symm p = ⟨p.proj, p.snd⟩ :=
  (rfl)

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
  constructor
  · intro h
    have hβ := ((Pullback.contMDiff_iff f hf).1
      ((contMDiff_bilinear_totalSpace_symm f hf).comp h)).2
    simpa only [Function.comp_def, Pullback.lift_mk] using hβ
  · intro h
    have hβ : ContMDiff IX (IX.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] 𝕜)) n
        (fun x ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] 𝕜)
          (E := (f : X → B) *ᵖ (fun b ↦ V b →L[𝕜] V b →L[𝕜] 𝕜)) x (β x)) :=
      (Pullback.contMDiff_iff f hf).2 ⟨contMDiff_id, by simpa only [Pullback.lift_mk] using h⟩
    exact (contMDiff_bilinear_totalSpace f hf).comp hβ

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

open TauCeti

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

end Bundle.Pullback

end MFDeriv

section MFDerivApply

variable {𝕜 E EM EG H HM N M K : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] {J : ModelWithCorners 𝕜 E H}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM]
  {I : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I 1 M]
  [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [TopologicalSpace N] {m n : WithTop ℕ∞}

namespace Bundle.Pullback

/-- For a map `f : N → M` that is `C^m` at the base point of `q` and a map `g` from `M` to a
normed space `G` that is `C^n` at its image, with `m + 1 ≤ n`, the map `(x, v) ↦ dg_{f x} v`,
from the total space of the pull-back `f *ᵖ TM` to `G`, is `C^m` at `q`. -/
theorem contMDiffAt_mfderiv_apply [ChartedSpace H N] [FunLike K N M] [ContinuousMapClass K N M]
    (f : K) {q : TotalSpace EM ((f : N → M) *ᵖ (TangentSpace I))}
    (hf : ContMDiffAt J I m f q.proj) {g : M → EG}
    (hg : ContMDiffAt I 𝓘(𝕜, EG) n g (f q.proj)) (hmn : m + 1 ≤ n) :
    ContMDiffAt (J.prod 𝓘(𝕜, EM)) 𝓘(𝕜, EG) m
      (fun p : TotalSpace EM ((f : N → M) *ᵖ (TangentSpace I)) ↦
        mfderiv I 𝓘(𝕜, EG) g (f p.proj) p.snd) q :=
  -- The composite is the stated map by definition: a vector of `f *ᵖ TM` at `x` is a tangent
  -- vector of `M` at `f x`, and a tangent vector of `G` is a vector of `G`.
  (contMDiff_snd_tangentBundle_modelSpace EG 𝓘(𝕜, EG)).contMDiffAt.comp q
    ((ContMDiffAt.contMDiffAt_tangentMap (X := Pullback.lift f q) hg hmn).comp q
      (contMDiffAt_lift f hf))

/-- For a `C^m` map `f : N → M` and a `C^n` map `g` from `M` to a normed space `G`, with
`m + 1 ≤ n`, the map `(x, v) ↦ dg_{f x} v`, from the total space of the pull-back `f *ᵖ TM` to
`G`, is `C^m`. -/
theorem contMDiff_mfderiv_apply [ChartedSpace H N] [FunLike K N M] [ContinuousMapClass K N M]
    (f : K) (hf : ContMDiff J I m f)
    {g : M → EG} (hg : ContMDiff I 𝓘(𝕜, EG) n g) (hmn : m + 1 ≤ n) :
    ContMDiff (J.prod 𝓘(𝕜, EM)) 𝓘(𝕜, EG) m
      (fun p : TotalSpace EM ((f : N → M) *ᵖ (TangentSpace I)) ↦
        mfderiv I 𝓘(𝕜, EG) g (f p.proj) p.snd) :=
  fun q ↦ contMDiffAt_mfderiv_apply f (hf q.proj) (hg (f q.proj)) hmn

/-- For any map `f : N → M` and a map `g` from `M` to a normed space `G` that is `C^n` at the
image of the base point of `q`, with `1 ≤ n`, the map `(x, v) ↦ dg_{f x} v`, from the total space
of the pull-back `f *ᵖ TM` to `G`, is continuous at `q`. -/
theorem continuousAt_mfderiv_apply (f : N → M) {q : TotalSpace EM (f *ᵖ (TangentSpace I))}
    {g : M → EG} (hg : ContMDiffAt I 𝓘(𝕜, EG) n g (f q.proj)) (hn : 1 ≤ n) :
    ContinuousAt (fun p : TotalSpace EM (f *ᵖ (TangentSpace I)) ↦
      mfderiv I 𝓘(𝕜, EG) g (f p.proj) p.snd) q :=
  -- As in `contMDiffAt_mfderiv_apply`, the composite is the stated map by definition.
  (contMDiff_snd_tangentBundle_modelSpace EG 𝓘(𝕜, EG) (n := 0)).continuous.continuousAt.comp
    ((ContMDiffAt.continuousAt_tangentMap (x₀ := Pullback.lift f q) hg hn).comp
      (Pullback.continuous_lift EM (TangentSpace I) f).continuousAt)

/-- For any map `f : N → M` and a `C^n` map `g` from `M` to a normed space `G`, with `1 ≤ n`,
the map `(x, v) ↦ dg_{f x} v`, from the total space of the pull-back `f *ᵖ TM` to `G`, is
continuous. -/
theorem continuous_mfderiv_apply (f : N → M) {g : M → EG} (hg : ContMDiff I 𝓘(𝕜, EG) n g)
    (hn : 1 ≤ n) :
    Continuous (fun p : TotalSpace EM (f *ᵖ (TangentSpace I)) ↦
      mfderiv I 𝓘(𝕜, EG) g (f p.proj) p.snd) :=
  continuous_iff_continuousAt.2 fun q ↦ continuousAt_mfderiv_apply f (hg (f q.proj)) hn

end Bundle.Pullback

end MFDerivApply

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
  filter_upwards [hp.1.continuousAt.eventually_mem_baseSet_trivializationAt E' (TangentSpace I')]
    with q hq
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

section HomTangentSpace

variable {𝕜 E H M G X EX HX K : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
  {IX : ModelWithCorners 𝕜 EX HX} [TopologicalSpace X] [ChartedSpace HX X]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FunLike K X M] [ContinuousMapClass K X M]
  {n : WithTop ℕ∞}

namespace Bundle.Pullback

/-- A family of maps `A x : G → T_(ι x) M`, from a normed space `G`, along a map `ι` that is `Cⁿ`
at `x₀`, is a `Cⁿ` section at `x₀` of the bundle of maps from the trivial bundle `ι *ᵖ G` to
`ι *ᵖ TM` exactly when it is `Cⁿ` at `x₀` in tangent coordinates. -/
theorem contMDiffAt_hom_trivial_section_iff_inTangentCoordinates (ι : K) {x₀ : X}
    (hι : ContMDiffAt IX I n ι x₀) (f : X → G) (A : ∀ x, G →L[𝕜] TangentSpace I (ι x)) :
    ContMDiffAt IX (IX.prod 𝓘(𝕜, G →L[𝕜] E)) n
        (fun x ↦ TotalSpace.mk' (G →L[𝕜] E)
          (E := fun x ↦ ((ι : X → M) *ᵖ (Trivial M G)) x →L[𝕜]
            ((ι : X → M) *ᵖ (TangentSpace I)) x) x (A x)) x₀ ↔
      ContMDiffAt IX 𝓘(𝕜, G →L[𝕜] E) n (inTangentCoordinates 𝓘(𝕜, G) I f ι A x₀) x₀ := by
  refine (Bundle.Pullback.contMDiffAt_hom_section_iff (V := Trivial M G)
    (W := TangentSpace I) ι hι A).trans ?_
  rw [contMDiffAt_hom_bundle]
  simp only [hι, true_and]
  congr! 2
  simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates]
  -- What remains is `φ = φ ∘L 1`, where `1` is the identity of `TangentSpace 𝓘(𝕜, G) (f x)`,
  -- which is `G` only up to unfolding.
  rfl

end Bundle.Pullback

end HomTangentSpace

section HomAlongMaps

variable {𝕜 B C X F G K L EX HX : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B] [TopologicalSpace C]
  [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
  {IX : ModelWithCorners 𝕜 EX HX} [TopologicalSpace X] [ChartedSpace HX X]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {V : B → Type*} {W : C → Type*}
  [∀ b, AddCommGroup (V b)] [∀ b, Module 𝕜 (V b)] [∀ b, TopologicalSpace (V b)]
  [∀ c, AddCommGroup (W c)] [∀ c, Module 𝕜 (W c)] [∀ c, TopologicalSpace (W c)]
  [∀ c, IsTopologicalAddGroup (W c)] [∀ c, ContinuousSMul 𝕜 (W c)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle 𝕜 G W]
  [FunLike K X B] [ContinuousMapClass K X B] [FunLike L X C] [ContinuousMapClass L X C]
  {n : WithTop ℕ∞}

namespace Bundle.Pullback

/-- For continuous maps `f : X → B` and `g : X → C`, a family of linear maps
`A x : V (f x) → W (g x)` is a `Cⁿ` section at `x₀` of the bundle of linear maps from `f *ᵖ V`
to `g *ᵖ W` exactly when its coordinates
`inCoordinates F V G W (f x₀) (f x) (g x₀) (g x) (A x)` are `Cⁿ` at `x₀`. -/
theorem contMDiffAt_hom_section_iff_inCoordinates (f : K) (g : L) {x₀ : X}
    (A : ∀ x, V (f x) →L[𝕜] W (g x)) :
    ContMDiffAt IX (IX.prod 𝓘(𝕜, F →L[𝕜] G)) n
        (fun x ↦ TotalSpace.mk' (F →L[𝕜] G)
          (E := fun x ↦ ((f : X → B) *ᵖ V) x →L[𝕜] ((g : X → C) *ᵖ W) x) x (A x)) x₀ ↔
      ContMDiffAt IX 𝓘(𝕜, F →L[𝕜] G) n
        (fun x ↦ ContinuousLinearMap.inCoordinates F V G W (f x₀) (f x) (g x₀) (g x) (A x))
        x₀ := by
  rw [contMDiffAt_hom_bundle]
  refine (and_iff_right contMDiffAt_id).trans (Filter.EventuallyEq.contMDiffAt_iff ?_)
  -- Near `x₀`, the coordinates between the pull-backs are those between `V` and `W`.
  filter_upwards [(map_continuous f).continuousAt.eventually_mem_baseSet_trivializationAt F V,
    (map_continuous g).continuousAt.eventually_mem_baseSet_trivializationAt G W] with y hyV hyW
  exact ContinuousLinearMap.inCoordinates_pullback_of_mem f g x₀ y (A y) hyV hyW

end Bundle.Pullback

end HomAlongMaps

section HomTangentSpaceAlongMaps

variable {𝕜 E E' H H' M M' X EX HX K L : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 1 M']
  [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
  {IX : ModelWithCorners 𝕜 EX HX} [TopologicalSpace X] [ChartedSpace HX X]
  [FunLike K X M] [ContinuousMapClass K X M] [FunLike L X M'] [ContinuousMapClass L X M']
  {n : WithTop ℕ∞}

namespace Bundle.Pullback

/-- Let `g : X → U` be a map into an open subset `U` of `M'` that is `g' : X → M'` followed by the
inclusion. A family of linear maps `A x : T_(f x) M → T_(g' x) M'` is a `Cⁿ` section at `x₀` of
the bundle of linear maps from `f *ᵖ TM` to `g *ᵖ TU` exactly when it is one of the bundle of
linear maps from `f *ᵖ TM` to `g' *ᵖ TM'`. -/
theorem contMDiffAt_hom_section_subtypeVal_iff {U : TopologicalSpace.Opens M'} {L' : Type*}
    [FunLike L' X U] [ContinuousMapClass L' X U] (f : K) (g : L') (g' : L)
    (hg : ∀ x, (g x : M') = g' x) {x₀ : X}
    (A : ∀ x, TangentSpace I (f x) →L[𝕜] TangentSpace I' (g' x)) :
    ContMDiffAt IX (IX.prod 𝓘(𝕜, E →L[𝕜] E')) n
        (fun x ↦ TotalSpace.mk' (E →L[𝕜] E')
          (E := fun x ↦ ((f : X → M) *ᵖ (TangentSpace I)) x →L[𝕜]
            ((g : X → U) *ᵖ (TangentSpace I')) x) x (A x)) x₀ ↔
      ContMDiffAt IX (IX.prod 𝓘(𝕜, E →L[𝕜] E')) n
        (fun x ↦ TotalSpace.mk' (E →L[𝕜] E')
          (E := fun x ↦ ((f : X → M) *ᵖ (TangentSpace I)) x →L[𝕜]
            ((g' : X → M') *ᵖ (TangentSpace I')) x) x (A x)) x₀ := by
  -- In tangent coordinates, `A` along `g` is `A` along `g'` near `x₀`.
  have h := TauCeti.Manifold.inTangentCoordinates_subtypeVal_comp_eventuallyEq (I := I')
    (I' := I) (f := f) (g := g) A (x₀ := x₀) (map_continuous g).continuousAt
  rw [show (fun x ↦ (g x : M')) = g' from funext hg] at h
  -- Tangent coordinates are the coordinates between the tangent bundles.
  unfold inTangentCoordinates at h
  exact (contMDiffAt_hom_section_iff_inCoordinates (V := TangentSpace I) (W := TangentSpace I')
    f g A).trans (h.contMDiffAt_iff.trans (contMDiffAt_hom_section_iff_inCoordinates
      (V := TangentSpace I) (W := TangentSpace I') f g' A).symm)

end Bundle.Pullback

end HomTangentSpaceAlongMaps

end
