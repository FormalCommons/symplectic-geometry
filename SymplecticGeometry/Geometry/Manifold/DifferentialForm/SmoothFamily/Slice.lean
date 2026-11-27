/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
import TauCeti.Geometry.Manifold.ContMDiff.ContinuousAlternatingMap

/-!
# The slice section of a family of forms, and smoothness at a point and in a frame

Let `F` be a manifold and let `β p` be a rough `k`-form on `F` for each point `p` of a parameter
manifold `P`. Its slice section `SymplecticGeometry.sliceSection β` sends `(p, y)` to `β p y`,
in the fibre over `y` of the bundle of `k`-forms of `F`; it is a section along the projection
`(p, y) ↦ y`. Smoothness of a family is stated through it, as in Tau Ceti's
`TauCeti.contMDiff_mpullback_prodMk_form` for the slices of a form on a product, where the
section is written out. Suppose that the slice section is `C^n`.

* `ContMDiffAt.roughForm_family_apply`: at a fixed `y₀`, the value `β p y₀` is `C^n` in `p`. The
  model space of `F` may have any dimension here; the trivialization at `y₀` of the bundle of
  `k`-forms is undone by its inverse `Trivialization.symmL` on the fibre.
* `ContMDiffAt.roughForm_family_apply_trivializationAt`: for a finite-dimensional model space,
  the values of `β p y` on the frame `e.symmL y ∘ v` of the tangent trivialization `e` of `F` at
  `y₀`, for a fixed tuple `v` of model vectors, are `C^n` in `(p, y)` at each point over `y₀`.
  This is the family version of one direction of Tau Ceti's
  `TauCeti.isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply`.

Both are statements about a `ContMDiffAt` hypothesis, so they sit in the namespace
`ContMDiffAt`, where dot notation finds them.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6 (integration
  along the fibre).
-/

public section

noncomputable section

open Bundle TauCeti
open scoped ContDiff Manifold

namespace SymplecticGeometry

variable {P E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace F] [ChartedSpace H F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {k : ℕ}

/-- The *slice section* of a family `β` of rough `k`-forms on `F` indexed by `P`: the map
sending `(p, y)` to `β p y` in the fibre over `y` of the bundle of `k`-forms of `F`. It is a
section along the projection `P × F → F`. -/
def sliceSection (β : P → RoughForm J F G k) (q : P × F) :
    TotalSpace (E [⋀^Fin k]→L[ℝ] G) fun y : F ↦ TangentSpace J y [⋀^Fin k]→L[ℝ] Trivial F G y :=
  TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] G) q.2 (β q.1 q.2)

/-- The defining equation of `SymplecticGeometry.sliceSection`. -/
theorem sliceSection_def (β : P → RoughForm J F G k) :
    sliceSection β = fun q ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] G)
      (E := fun y : F ↦ TangentSpace J y [⋀^Fin k]→L[ℝ] Trivial F G y) q.2 (β q.1 q.2) :=
  (rfl)

/-- The value of the slice section at `(p, y)` is `β p y` over `y`. -/
theorem sliceSection_apply (β : P → RoughForm J F G k) (q : P × F) :
    sliceSection β q = TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] G)
      (E := fun y : F ↦ TangentSpace J y [⋀^Fin k]→L[ℝ] Trivial F G y) q.2 (β q.1 q.2) :=
  (rfl)

/-- The slice section lies over the second coordinate. -/
@[simp]
theorem sliceSection_proj (β : P → RoughForm J F G k) (q : P × F) :
    (sliceSection β q).proj = q.2 :=
  (rfl)

/-- The fibre component of the slice section at `(p, y)` is `β p y`. -/
@[simp]
theorem sliceSection_snd (β : P → RoughForm J F G k) (q : P × F) :
    (sliceSection β q).snd = β q.1 q.2 :=
  (rfl)

variable {EP HP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {K : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]

/-- The slice section of `β` is `C^n` at `q₀` if and only if its fibre coordinate in the
trivialization at `q₀.2` of the bundle of `k`-forms of `F` is `C^n` at `q₀`. -/
theorem contMDiffAt_sliceSection_iff [IsManifold J 1 F] {n : WithTop ℕ∞}
    {β : P → RoughForm J F G k} {q₀ : P × F} :
    ContMDiffAt (K.prod J) (J.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] G)) n (sliceSection β) q₀ ↔
      ContMDiffAt (K.prod J) 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] G) n
        (fun q ↦ (trivializationAt (E [⋀^Fin k]→L[ℝ] G)
          (fun y : F ↦ TangentSpace J y [⋀^Fin k]→L[ℝ] Trivial F G y) q₀.2
          (sliceSection β q)).2) q₀ := by
  rw [contMDiffAt_totalSpace_iff]
  simp [contMDiffAt_snd]

/-- If the slice section of `β` is `C^n` and `χ : F → P` is `C^n`, then the rough form
`y ↦ β (χ y) y`, the slice of `β` along `χ`, is `C^n`. -/
theorem isSmoothForm_of_contMDiff_sliceSection [IsManifold J 1 F] {n : WithTop ℕ∞}
    {β : P → RoughForm J F G k}
    (hβ : ContMDiff (K.prod J) (J.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] G)) n (sliceSection β))
    {χ : F → P} (hχ : ContMDiff J K n χ) :
    IsSmoothForm J n (fun y ↦ β (χ y) y : RoughForm J F G k) := by
  rw [sliceSection_def] at hβ
  exact (isSmoothForm_def _ _).mpr (hβ.comp (hχ.prodMk contMDiff_id))

end SymplecticGeometry

open SymplecticGeometry

namespace ContMDiffAt

variable {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {K : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [TopologicalSpace F] [ChartedSpace H F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {k : ℕ}

/-- **A smooth family of forms at a fixed point.** Let `β p` be a `k`-form on `F` for each
`p : P`, such that `(p, y) ↦ β p y`, as a section of the bundle of `k`-forms along
`(p, y) ↦ y`, is `C^n` at `q₀`. Then `p ↦ β p q₀.2`, a map into the alternating maps on the
model space, is `C^n` at `q₀.1`. -/
theorem roughForm_family_apply [IsManifold J 1 F] {n : WithTop ℕ∞}
    {β : P → RoughForm J F G k} {q₀ : P × F}
    (hβ : ContMDiffAt (K.prod J) (J.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] G)) n (sliceSection β) q₀) :
    ContMDiffAt K 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] G) n
      (fun p ↦ show E [⋀^Fin k]→L[ℝ] G from β p q₀.2) q₀.1 := by
  have hc := (contMDiffAt_sliceSection_iff.1 hβ).comp q₀.1
    (contMDiffAt_id.prodMk contMDiffAt_const :
      ContMDiffAt K (K.prod J) n (fun p ↦ (p, q₀.2)) q₀.1)
  -- Undo the trivialization at `q₀.2` of the bundle of forms by its inverse on the fibre.
  have hb := mem_baseSet_trivializationAt (E [⋀^Fin k]→L[ℝ] G)
    (fun y : F ↦ TangentSpace J y [⋀^Fin k]→L[ℝ] Trivial F G y) q₀.2
  let L : (E [⋀^Fin k]→L[ℝ] G) →L[ℝ] E [⋀^Fin k]→L[ℝ] G :=
    (trivializationAt (E [⋀^Fin k]→L[ℝ] G)
      (fun y : F ↦ TangentSpace J y [⋀^Fin k]→L[ℝ] Trivial F G y) q₀.2).symmL ℝ q₀.2
  refine (L.contMDiff.contMDiffAt.comp q₀.1 hc).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun p ↦ ?_)
  exact ((Trivialization.symmL_apply _ hb _).trans
    (Trivialization.symm_apply_apply_mk _ hb _)).symm

variable [FiniteDimensional ℝ E]

/-- **A smooth family of forms read in a tangent trivialization.** Let `β p` be a `k`-form on
`F` for each `p : P`, such that `(p, y) ↦ β p y`, as a section of the bundle of `k`-forms along
`(p, y) ↦ y`, is `C^n` at `q₀`. For each tuple `v` of model vectors, the value of `β p y` on the
frame `e.symmL y ∘ v`, where `e` is the tangent trivialization of `F` at `q₀.2`, is `C^n` in
`(p, y)` at `q₀`. -/
theorem roughForm_family_apply_trivializationAt [IsManifold J 1 F] {n : WithTop ℕ∞}
    {β : P → RoughForm J F G k} {q₀ : P × F}
    (hβ : ContMDiffAt (K.prod J) (J.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] G)) n (sliceSection β) q₀)
    (v : Fin k → E) :
    ContMDiffAt (K.prod J) 𝓘(ℝ, G) n
      (fun q : P × F ↦ β q.1 q.2 ((trivializationAt E (TangentSpace J) q₀.2).symmL ℝ q.2 ∘ v))
      q₀ := by
  have h := contMDiffAt_sliceSection_iff.1 hβ
  simp only [sliceSection_apply, FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd,
    contMDiffAt_continuousAlternatingMap_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply] at h
  exact h v

end ContMDiffAt

end
