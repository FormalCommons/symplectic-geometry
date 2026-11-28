/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Vertical
import SymplecticGeometry.Geometry.Symplectic.Manifold.TwoForm

/-!
# The slice of a smooth family along a smooth function of the point

For a smooth family `α : N → SmoothForm I M F k` (`SymplecticGeometry.IsSmoothFamily`) and a
smooth map `χ : M → N`, `SymplecticGeometry.IsSmoothFamily.sliceAlong` is the smooth form on `M`
whose value at `x` is the value of `α (χ x)` at `x`. It reads each member of the family only on
vectors tangent to `M`: it is not the pullback of a form on `N × M` with slices `α t` along the
graph map `x ↦ (χ x, x)`, which would also see the derivative of `χ`. It is the pullback along the
graph map of the vertical form `TauCeti.verticalForm J` of the family, which has no component
along `N`; its smoothness is that of the slice section of `α`
(`SymplecticGeometry.isSmoothFamily_iff_contMDiff`) composed with the graph map.

## Main definitions

* `SymplecticGeometry.IsSmoothFamily.sliceAlong hα χ hχ`: the smooth form
  `x ↦ (α (χ x)) x`.

## Main results

* `SymplecticGeometry.IsSmoothFamily.sliceAlong_val`: its value at `x` is that of `α (χ x)`.
* `SymplecticGeometry.IsSmoothFamily.coe_sliceAlong`: it is the pullback of the vertical form of
  the family along the graph map.
* `SymplecticGeometry.IsSmoothFamily.sliceAlong_const`: along a constant map `t`, it is `α t`.
* `SymplecticGeometry.IsSmoothFamily.mpullback_sliceAlong`: its pullback along a smooth map `f`
  is the slice of the pulled-back family along `χ ∘ f`.
* `SymplecticGeometry.IsSmoothFamily.sliceAlong_comp`: the slice of the reparametrized family
  `fun s ↦ α (φ s)` along `χ` is the slice of `α` along `φ ∘ χ`.
* `SymplecticGeometry.IsSmoothFamily.mpullback_subtypeVal_sliceAlong`: on an open set where `χ`
  is constantly `t`, its restriction is that of `α t`.
* `SymplecticGeometry.IsSmoothFamily.isNondegenerate_sliceAlong_iff`: a family of two-forms
  gives a nondegenerate form exactly when each `α (χ x)` is nondegenerate at `x`; and
  `SymplecticGeometry.IsSmoothFamily.isNondegenerate_sliceAlong`: it is nondegenerate when `χ`
  takes values in a set `s` on which every `α t` is nondegenerate.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.2
  (the symplectic connected sum: Exercise 7.2.1 and Lemma 7.2.2).
-/

public section

noncomputable section

open Bundle TopologicalSpace TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E H M EN HN N F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J 1 N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

namespace IsSmoothFamily

section

variable [IsManifold I 1 M] {α : N → SmoothForm I M F k}

/-- **The slice of a smooth family along a smooth map.** For a smooth family `α` of forms on `M`
over `N` and a smooth map `χ : M → N`, the smooth form on `M` whose value at `x` is the value
of `α (χ x)` at `x` (`SymplecticGeometry.IsSmoothFamily.sliceAlong_val`). -/
def sliceAlong (hα : IsSmoothFamily J α) (χ : M → N) (hχ : ContMDiff I J ∞ χ) :
    SmoothForm I M F k :=
  ⟨fun x ↦ (α (χ x)).val x, IsSmoothForm.mem_smoothBundleForms <|
    isSmoothForm_of_contMDiff_sliceSection (isSmoothFamily_iff_contMDiff.mp hα) hχ⟩

/-- The value of `SymplecticGeometry.IsSmoothFamily.sliceAlong hα χ hχ` at `x` is the value of
`α (χ x)` at `x`. -/
@[simp]
theorem sliceAlong_val (hα : IsSmoothFamily J α) (χ : M → N) (hχ : ContMDiff I J ∞ χ) (x : M) :
    (hα.sliceAlong χ hχ).val x = (α (χ x)).val x :=
  (rfl)

/-- The slice of `α` along `χ` is the pullback, along the graph map `x ↦ (χ x, x)`, of the
vertical form `TauCeti.verticalForm J` of the family, which has no component along `N`. -/
theorem coe_sliceAlong (hα : IsSmoothFamily J α) (χ : M → N) (hχ : ContMDiff I J ∞ χ) :
    (hα.sliceAlong χ hχ).val =
      mpullback I (J.prod I) (fun x ↦ (χ x, x)) (verticalForm J fun t ↦ (α t).val) := by
  funext x
  rw [mpullback_verticalForm_apply _
    ((hχ.mdifferentiableAt (by simp)).prodMk mdifferentiableAt_id :
      MDifferentiableAt I (J.prod I) (fun x ↦ (χ x, x)) x)]
  -- `Prod.snd ∘ (fun x ↦ (χ x, x))` is the identity of `M`.
  rw [sliceAlong_val]
  exact (congrFun (mpullback_id (I := I) (F := F) (k := k) (α (χ x)).val) x).symm

/-- Along a constant map `t`, the slice of `α` is `α t`. -/
@[simp]
theorem sliceAlong_const (hα : IsSmoothFamily J α) (t : N) :
    hα.sliceAlong (fun _ ↦ t) contMDiff_const = α t :=
  Subtype.ext (funext fun x ↦ sliceAlong_val hα _ _ x)

/-- The pullback of the slice of `α` along `χ` by a smooth map `f : M' → M` is the slice of the
pulled-back family `fun t ↦ f^* (α t)` along `χ ∘ f`. -/
theorem mpullback_sliceAlong {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] [TopologicalSpace M'] [ChartedSpace H' M']
    {I' : ModelWithCorners ℝ E' H'} [IsManifold I' 1 M'] (hα : IsSmoothFamily J α) {χ : M → N}
    (hχ : ContMDiff I J ∞ χ) (f : M' → M) (hf : ContMDiff I' I ∞ f) :
    SmoothForm.mpullback f hf (hα.sliceAlong χ hχ) =
      (hα.mpullback f hf).sliceAlong (χ ∘ f) (hχ.comp hf) :=
  Subtype.ext <| funext fun x ↦ by ext v; simp

/-- The slice of the reparametrized family `fun s ↦ α (φ s)` along `χ` is the slice of `α`
along `φ ∘ χ`. -/
theorem sliceAlong_comp {EN' HN' N' : Type*} [NormedAddCommGroup EN'] [NormedSpace ℝ EN']
    [TopologicalSpace HN'] [TopologicalSpace N'] [ChartedSpace HN' N']
    {J' : ModelWithCorners ℝ EN' HN'} [IsManifold J' 1 N'] (hα : IsSmoothFamily J α)
    (φ : N' → N) (hφ : ContMDiff J' J ∞ φ) {χ : M → N'} (hχ : ContMDiff I J' ∞ χ) :
    (hα.comp φ hφ).sliceAlong χ hχ = hα.sliceAlong (φ ∘ χ) (hφ.comp hχ) :=
  Subtype.ext (funext fun x ↦ by simp)

/-- **Locality.** On an open set `U` where `χ` is constantly `t`, the restriction of the slice of
`α` along `χ` is the restriction of `α t`. -/
theorem mpullback_subtypeVal_sliceAlong (hα : IsSmoothFamily J α) {χ : M → N}
    (hχ : ContMDiff I J ∞ χ) {U : Opens M} {t : N} (hU : ∀ x ∈ U, χ x = t) :
    SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal (hα.sliceAlong χ hχ) =
      SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal (α t) := by
  rw [hα.mpullback_sliceAlong]
  have : χ ∘ (Subtype.val : U → M) = fun _ ↦ t := funext fun x ↦ hU x x.property
  simp only [this, sliceAlong_const]

end

section TwoForm

variable [IsManifold I ∞ M] {α : N → SmoothTwoForm I M}

/-- The bilinear form of the slice of a smooth family of two-forms along `χ` at `x` is that of
`α (χ x)` at `x`. -/
@[simp]
theorem bilinFormAt_sliceAlong (hα : IsSmoothFamily J α) {χ : M → N} (hχ : ContMDiff I J ∞ χ)
    (x : M) : (hα.sliceAlong χ hχ).bilinFormAt x = (α (χ x)).bilinFormAt x :=
  LinearMap.ext₂ fun v w ↦ by
    rw [SmoothForm.bilinFormAt_apply, SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply,
      SmoothBundleForm.eval₂_apply, sliceAlong_val]

/-- The slice of a smooth family of two-forms along `χ` is nondegenerate exactly when, at each
point `x`, the form `α (χ x)` is nondegenerate at `x`. -/
theorem isNondegenerate_sliceAlong_iff (hα : IsSmoothFamily J α) {χ : M → N}
    (hχ : ContMDiff I J ∞ χ) :
    SmoothTwoForm.IsNondegenerate (hα.sliceAlong χ hχ) ↔
      ∀ x, ((α (χ x)).bilinFormAt x).Nondegenerate := by
  simp only [SmoothTwoForm.isNondegenerate_def, bilinFormAt_sliceAlong hα hχ]

/-- The slice of a smooth family of two-forms along a map `χ` with values in a set `s` is
nondegenerate when every `α t` with `t ∈ s` is. -/
theorem isNondegenerate_sliceAlong (hα : IsSmoothFamily J α) {χ : M → N}
    (hχ : ContMDiff I J ∞ χ) {s : Set N} (hχs : ∀ x, χ x ∈ s)
    (hs : ∀ t ∈ s, (α t).IsNondegenerate) :
    SmoothTwoForm.IsNondegenerate (hα.sliceAlong χ hχ) :=
  (hα.isNondegenerate_sliceAlong_iff hχ).mpr fun x ↦
    (hs (χ x) (hχs x)).nondegenerate_bilinFormAt x

end TwoForm

end IsSmoothFamily

end SymplecticGeometry

end
