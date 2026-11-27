/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Vertical
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Slice
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Family

/-!
# Vertical forms of families of forms

Tau Ceti's `TauCeti.verticalForm J σ` is the form on `N × M` whose value at `(p, y)` evaluates
the member `σ p` of a family of forms on `M` on the components along `M` of tangent vectors. This
file is the library's counterpart of Tau Ceti's file
`TauCeti/Geometry/Manifold/DifferentialForm/Vertical.lean`: it relates vertical forms to pullbacks
along the projection `Prod.snd : N × M → M`, and characterizes their smoothness by that of the
slice section `(t, y) ↦ σ t y` (`SymplecticGeometry.sliceSection σ`).

## Main results

* `TauCeti.verticalForm_fun_smul_fst`: multiplying each member `σ p` by a scalar `c p` multiplies
  the vertical form by `c` of the first coordinate; the companion of Tau Ceti's
  `TauCeti.verticalForm_fun_smul`, which multiplies by a function on `M`.
* `TauCeti.verticalForm_apply_eq_mpullback_snd`: at `p`, the vertical form is the pullback of
  `σ p.1` along `Prod.snd`.
* `TauCeti.mpullback_verticalForm_apply`: the pullback of a vertical form along a map
  `f : X → N × M`.
* `TauCeti.mpullback_prodMap_verticalForm`: the pullback of a vertical form along a product map
  `Prod.map f g` is the vertical form of the pulled-back family.
* `TauCeti.contMDiffAt_verticalForm_iff`: a vertical form is `C^m` at a point exactly when the
  slice section of its family is.

## Implementation notes

The direct direction of `TauCeti.contMDiffAt_verticalForm_iff` is Tau Ceti's
`ContMDiffAt.mpullback_form_family`, applied to the family of inclusions `y ↦ (t, y)`; the converse
one is `ContMDiffAt.mpullback_form_family_of_family`, applied to the projection.
-/

public section

open Bundle Filter
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M EN HN N F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J 1 N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

omit [IsManifold I 1 M] [IsManifold J 1 N] in
/-- Multiplying every member `σ p` of a family by a scalar `c p` multiplies its vertical form by
`c` of the first coordinate. -/
theorem verticalForm_fun_smul_fst (c : N → ℝ) (σ : N → RoughForm I M F k) :
    verticalForm J (fun p ↦ c p • σ p) = fun z ↦ c z.1 • verticalForm J σ z := by
  funext z
  ext v
  simp only [verticalForm_apply, Pi.smul_apply, ContinuousAlternatingMap.smul_apply]
  -- The scalar action on the left comes from the pointwise one on `RoughForm`, which `simp`
  -- does not match with `ContinuousAlternatingMap.smul_apply`.
  exact ContinuousAlternatingMap.smul_apply (σ z.1 z.2) (c z.1) _

omit [IsManifold I 1 M] [IsManifold J 1 N] in
/-- The value of the vertical form `TauCeti.verticalForm J β` at `p` is the pullback of `β p.1`
along the projection `N × M → M`, at `p`. -/
theorem verticalForm_apply_eq_mpullback_snd (β : N → RoughForm I M F k) (p : N × M) :
    verticalForm J β p = mpullback (J.prod I) I Prod.snd (β p.1) p := by
  ext v
  rw [verticalForm_apply, mpullback_apply, mfderiv_snd]
  -- `ContinuousLinearMap.snd` is the second projection.
  rfl

omit [IsManifold I 1 M] [IsManifold J 1 N] in
/-- Pulling back the vertical form `TauCeti.verticalForm J β` of a family `β` along a map `f`
gives, at `x`, the pullback of `β (f x).1` along the second component of `f`. -/
theorem mpullback_verticalForm_apply {EX HX X : Type*} [NormedAddCommGroup EX]
    [NormedSpace ℝ EX] [TopologicalSpace HX] [TopologicalSpace X] [ChartedSpace HX X]
    {IX : ModelWithCorners ℝ EX HX} (β : N → RoughForm I M F k) {f : X → N × M} {x : X}
    (hf : MDifferentiableAt IX (J.prod I) f x) :
    mpullback IX (J.prod I) f (verticalForm J β) x =
      mpullback IX I (Prod.snd ∘ f) (β (f x).1) x := by
  rw [mpullback_comp_at hf mdifferentiableAt_snd]
  -- Both sides only read the value at `f x` of the form on `N × M`.
  exact mpullback_apply_congr (verticalForm_apply_eq_mpullback_snd β (f x))

omit [IsManifold I 1 M] [IsManifold J 1 N] in
/-- Pulling back the vertical form of a family `β` along a product map `Prod.map f g` of
differentiable maps gives the vertical form of the family `t ↦ g^* (β (f t))`. -/
theorem mpullback_prodMap_verticalForm {EX HX X EY HY Y : Type*} [NormedAddCommGroup EX]
    [NormedSpace ℝ EX] [TopologicalSpace HX] [TopologicalSpace X] [ChartedSpace HX X]
    {IX : ModelWithCorners ℝ EX HX} [NormedAddCommGroup EY] [NormedSpace ℝ EY]
    [TopologicalSpace HY] [TopologicalSpace Y] [ChartedSpace HY Y]
    {IY : ModelWithCorners ℝ EY HY} (β : N → RoughForm I M F k) {f : X → N} {g : Y → M}
    (hf : MDifferentiable IX J f) (hg : MDifferentiable IY I g) :
    mpullback (IX.prod IY) (J.prod I) (Prod.map f g) (verticalForm J β) =
      verticalForm IX fun t ↦ mpullback IY I g (β (f t)) := by
  funext p
  rw [mpullback_verticalForm_apply β ((hf p.1).prodMap (hg p.2)),
    verticalForm_apply_eq_mpullback_snd, ← mpullback_comp_at mdifferentiableAt_snd (hg p.2)]
  -- `Prod.snd ∘ Prod.map f g` is `g ∘ Prod.snd`.
  rfl

/-- **Smoothness of vertical forms.** The vertical form `TauCeti.verticalForm J β` of a family `β`
of rough forms on `M` over `N` is `C^m` at `p` exactly when its slice section
`SymplecticGeometry.sliceSection β`, the section `(t, y) ↦ β t y` along the projection, is. -/
theorem contMDiffAt_verticalForm_iff {m : WithTop ℕ∞} (β : N → RoughForm I M F k)
    (p : N × M) :
    ContMDiffAt (J.prod I) ((J.prod I).prod 𝓘(ℝ, (EN × E) [⋀^Fin k]→L[ℝ] F)) m
        (fun q ↦ TotalSpace.mk' ((EN × E) [⋀^Fin k]→L[ℝ] F) q (verticalForm J β q)) p ↔
      ContMDiffAt (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
        (SymplecticGeometry.sliceSection β) p := by
  rw [SymplecticGeometry.sliceSection_def]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := ContMDiffAt.mpullback_form_family (hφ := h) (f := fun q : N × M ↦ Prod.mk q.1)
      (g := Prod.snd) (n := ω) (p₀ := p)
      ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd).contMDiffAt contMDiffAt_snd le_top
    simpa only [mpullback_prodMk_verticalForm] using this
  · have := ContMDiffAt.mpullback_form_family_of_family (φ := fun q : N × M ↦ β q.1)
      (f := fun _ ↦ Prod.snd) (g := id) (n := ω) h
      (contMDiff_snd.comp contMDiff_snd).contMDiffAt contMDiffAt_id le_top
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun q ↦ ?_)
    simp only [id_eq, verticalForm_apply_eq_mpullback_snd]


end TauCeti

end
