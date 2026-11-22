/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Calculus.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Manifold.VectorField.Prod
import SymplecticGeometry.Geometry.Manifold.VectorField.Prod
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Lie derivatives of forms on a manifold: linearity in the field, horizontal fields

Tau Ceti's `TauCeti.mlieDerivFormWithin` and `TauCeti.mlieDerivForm` are additive in the vector
field (`TauCeti.mlieDerivFormWithin_add_left`, `TauCeti.mlieDerivForm_add_left`). This file adds
the rest of their linearity in the field: they vanish along the zero field and commute with
constant multiples of the field, `L_{c V} φ = c L_V φ`, with no differentiability asked of the
field or of the form. Both are read in charts from the flat statements
`TauCeti.lieDerivFormWithin_zero_left` and `TauCeti.lieDerivFormWithin_const_smul_left` of
`SymplecticGeometry.Analysis.Calculus.DifferentialForm.LieDeriv`. The proofs follow Tau Ceti's
`VectorField.mlieBracket_const_smul_left_field`.

On a product `N × P`, a form whose slices `ι_s^* β`, `ι_s : y ↦ (s, y)`, do not depend on `s` has
a Lie derivative with vanishing slices along the horizontal lift `(X, 0)` of any vector field `X`
on `N`. The proof extends tangent vectors of `P` to vector fields (`FiberBundle.extend`), lifts
them vertically, and evaluates the Lie derivative by the bracket formula
`TauCeti.mlieDerivForm_apply_vectorField`: the brackets vanish since horizontal and vertical
lifts commute (`Manifold.mlieBracket_prodVectorField_horizontal_vertical`), and the remaining
term differentiates a function of `P` alone along `(X, 0)`. No boundarylessness is needed.

## Main declarations

* `TauCeti.mlieDerivFormWithin_zero_left`, `TauCeti.mlieDerivForm_zero_left`: the Lie derivative
  along the zero field.
* `TauCeti.mlieDerivFormWithin_const_smul_left`, `TauCeti.mlieDerivForm_const_smul_left`:
  homogeneity in the field.
* `TauCeti.mpullback_prodMk_mlieDerivForm_prodVectorField_zero_eq_zero`: the slices of the Lie
  derivative of a form with constant slices along a horizontal field vanish.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14, and Corollary 12.33 (the bracket formula for Lie derivatives of
  forms).
-/

public section

noncomputable section

open Set Bundle VectorField
open scoped Manifold

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The Lie derivative within a set of a form along the zero vector field vanishes. -/
@[simp]
theorem mlieDerivFormWithin_zero_left (φ : RoughForm I M F k) (s : Set M) (x : M) :
    mlieDerivFormWithin (0 : (x : M) → TangentSpace I x) φ s x = 0 := by
  rw [mlieDerivFormWithin_def, VectorField.mpullbackWithin_zero]
  exact lieDerivFormWithin_zero_left _ _ _

/-- The Lie derivative of a form along the zero vector field vanishes. -/
@[simp]
theorem mlieDerivForm_zero_left (φ : RoughForm I M F k) :
    mlieDerivForm (0 : (x : M) → TangentSpace I x) φ = 0 := by
  rw [← mlieDerivFormWithin_univ]
  exact funext (mlieDerivFormWithin_zero_left φ univ)

/-- The Lie derivative within a set commutes with constant multiples of the vector field, where
derivatives within the set are unique. -/
@[simp]
theorem mlieDerivFormWithin_const_smul_left (c : ℝ) (V : (x : M) → TangentSpace I x)
    (φ : RoughForm I M F k) {s : Set M} {x : M} (hs : UniqueMDiffWithinAt I s x) :
    mlieDerivFormWithin (c • V) φ s x = c • mlieDerivFormWithin V φ s x := by
  simp only [mlieDerivFormWithin_def, VectorField.mpullbackWithin_const_smul]
  exact lieDerivFormWithin_const_smul_left c _ _ hs

/-- The Lie derivative commutes with constant multiples of the vector field:
`L_{c V} φ = c L_V φ`. -/
@[simp]
theorem mlieDerivForm_const_smul_left (c : ℝ) (V : (x : M) → TangentSpace I x)
    (φ : RoughForm I M F k) :
    mlieDerivForm (c • V) φ = c • mlieDerivForm V φ := by
  rw [← mlieDerivFormWithin_univ, ← mlieDerivFormWithin_univ]
  exact funext fun _ ↦ mlieDerivFormWithin_const_smul_left c V φ (uniqueMDiffWithinAt_univ I)

/-! ### Lie derivatives along horizontal fields of a product -/

section Horizontal

variable {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [CompleteSpace EN]
  [TopologicalSpace HN] {K : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N]
  [ChartedSpace HN N] [IsManifold K 2 N]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {P : Type*} [TopologicalSpace P]
  [ChartedSpace H' P] [IsManifold J 2 P]

/-- **Lie derivatives of a form with constant slices.** Let `β` be a form on `N × P` whose slices
`ι_s^* β`, `ι_s : y ↦ (s, y)`, do not depend on `s ∈ N`, and let `X` be a vector field on `N`,
lifted horizontally to `(X, 0)` on `N × P`. Then the slice at time `t` of the Lie derivative
`L_{(X, 0)} β` vanishes at every `x` such that `β` is differentiable at `(t, x)` and `X` at `t`. -/
theorem mpullback_prodMk_mlieDerivForm_prodVectorField_zero_eq_zero
    {β : RoughForm (K.prod J) (N × P) F k} {X : Π s : N, TangentSpace K s} {t : N} {x : P}
    (hβ : MDifferentiableAt (K.prod J) ((K.prod J).prod 𝓘(ℝ, (EN × E') [⋀^Fin k]→L[ℝ] F))
      (fun p ↦ TotalSpace.mk' ((EN × E') [⋀^Fin k]→L[ℝ] F) p (β p)) (t, x))
    (hX : MDifferentiableAt K K.tangent (fun s ↦ (⟨s, X s⟩ : TangentBundle K N)) t)
    (hslice : ∀ s, mpullback J (K.prod J) (Prod.mk s) β = mpullback J (K.prod J) (Prod.mk t) β) :
    mpullback J (K.prod J) (Prod.mk t)
      (mlieDerivForm (Manifold.prodVectorField X (0 : Π y : P, TangentSpace J y)) β) x = 0 := by
  have h2 : minSmoothness ℝ 2 = 2 := minSmoothness_of_isRCLikeNormedField
  have : IsManifold K (minSmoothness ℝ 2) N := by rw [h2]; infer_instance
  have : IsManifold J (minSmoothness ℝ 2) P := by rw [h2]; infer_instance
  have : IsManifold K 1 N := .of_le one_le_two
  have : IsManifold J 1 P := .of_le one_le_two
  ext v
  -- Extend each vector `v i` to a field `V i` on `P`, and lift it vertically to `(0, V i)`.
  set V : Fin k → Π y : P, TangentSpace J y := fun i ↦ FiberBundle.extend E' (v i)
  have hV (i : Fin k) :
      MDifferentiableAt J J.tangent (fun y ↦ (⟨y, V i y⟩ : TangentBundle J P)) x :=
    FiberBundle.mdifferentiableAt_extend J E' (v i)
  have h0 : MDifferentiableAt K K.tangent
      (fun s ↦ (⟨s, (0 : Π s : N, TangentSpace K s) s⟩ : TangentBundle K N)) t :=
    (contMDiff_zeroSection ℝ (TangentSpace K)).mdifferentiableAt one_ne_zero
  set Y : Fin k → Π q : N × P, TangentSpace (K.prod J) q :=
    fun i ↦ Manifold.prodVectorField 0 (V i)
  have hY (i : Fin k) : MDifferentiableAt (K.prod J) (K.prod J).tangent
      (fun q ↦ (⟨q, Y i q⟩ : TangentBundle (K.prod J) (N × P))) (t, x) :=
    Manifold.mdifferentiableAt_prodVectorField h0 (hV i)
  -- The vertical lift of a vector field is the image of the field under `dι_s`.
  have hι (q : N × P) (i : Fin k) :
      Y i q = mfderiv J (K.prod J) (Prod.mk q.1) q.2 (V i q.2) := by
    rw [mfderiv_prod_right]
    -- `inr w` is `(0, w)` by definition.
    exact (Manifold.prodVectorField_apply _ _ q).trans rfl
  have hYv : (Y · (t, x)) = fun i ↦ mfderiv J (K.prod J) (Prod.mk t) x (v i) := by
    funext i
    rw [hι (t, x) i]
    simp [V]
  rw [mpullback_apply, ← hYv, mlieDerivForm_apply_vectorField hβ hY]
  -- Horizontal and vertical lifts commute, so the bracket terms vanish.
  have hbr (i : Fin k) : mlieBracket (K.prod J) (Manifold.prodVectorField X 0) (Y i) (t, x) = 0 :=
    Manifold.mlieBracket_prodVectorField_horizontal_vertical hX (hV i)
  simp only [hbr, ContinuousAlternatingMap.map_update_zero, Finset.sum_const_zero, sub_zero]
  -- The evaluation of `β` on the vertical lifts is a function on `P` alone.
  have hg : (fun q : N × P ↦ β q (Y · q)) =
      (fun y ↦ mpullback J (K.prod J) (Prod.mk t) β y (V · y)) ∘ Prod.snd := by
    funext q
    rw [Function.comp_apply, ← hslice q.1, mpullback_apply]
    exact congrArg (β q) (funext fun i ↦ hι q i)
  rw [hg, mvfderiv_comp_snd_apply, Manifold.prodVectorField_snd, Pi.zero_apply, map_zero,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply]


end Horizontal

end TauCeti

end
