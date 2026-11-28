/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
import SymplecticGeometry.Data.Fin.Tuple.RemoveNth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Basic
import SymplecticGeometry.Geometry.Manifold.VectorField.Prod
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Prod

/-!
# The exterior derivative on a parameter product

Let `P` be a real Banach space of parameters and `M` a manifold modelled on a complete space `E`,
and let `φ` be a rough `n`-form on `P × M` with values in `F`, differentiable at `(p, x)`. This
file evaluates `dφ` at `(p, x)` on tangent vectors of the form `(c, w)`, with `c ∈ P` read as
a constant field in the parameter, splitting `dφ` into derivatives in the parameter and along
`M`, in every degree.

* `TauCeti.RoughForm.mextDeriv_prod_apply_of_mlieBracket_eq_zero`: for `c₀, …, cₙ ∈ P` and
  vector fields `W₀, …, Wₙ` on `M`, differentiable at `x` with pairwise brackets vanishing at `x`,
  `dφ((c₀, W₀ x), …, (cₙ, Wₙ x))` is the alternating sum over `i` of the parameter derivative
  along `cᵢ` of `q ↦ φ_(q, x)` on the other vectors, plus the derivative along `Wᵢ x` of
  `y ↦ φ_(p, y)` on the other fields `(cⱼ, Wⱼ y)`.
* `TauCeti.RoughForm.mextDeriv_prod_apply_inl`: all vectors along `P`. Then
  `dφ((a₀, 0), …, (aₙ, 0)) = ∑ᵢ (-1)ⁱ ∂_{aᵢ} (q ↦ φ_(q, x)((a₀, 0), …, (aₙ, 0) without i))`.
* `TauCeti.RoughForm.mextDeriv_prod_apply_snoc_inr`: one vector `(0, v)` along `M`, placed last.
  Then the parameter terms are as above, with `(0, v)` kept last, and the term of `(0, v)` is
  `(-1) ^ (n + 1)` times the derivative along `v` of `y ↦ φ_(p, y)((a₀, 0), …, (aₙ, 0))`.

The proof is that of Tau Ceti's
`TauCeti.SmoothForm.mextDeriv_apply_eq_fderiv_sub_fderiv_add_mvfderiv`, which is the second
formula for a smooth two-form, carried out on a frame of any length: the invariant formula
`TauCeti.mextDeriv_apply_vectorField_of_mlieBracket_eq_zero` on the product fields `(cᵢ, Wᵢ)`,
which commute at `(p, x)` by `TauCeti.Manifold.mlieBracket_prodVectorField`, and the splitting of
the derivative on a product into partial derivatives
(`MDifferentiableAt.mvfderiv_prod_eq_add_apply`). For the vector `(0, v)` the field along `M` is
the extension `FiberBundle.extend E v`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Proposition 14.32 (the invariant
  formula for the exterior derivative).
-/

public section

open Bundle VectorField
open scoped Manifold

namespace TauCeti.RoughForm

variable {E H M F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [CompleteSpace E] [CompleteSpace P] [IsManifold I 2 M]

/-- **The exterior derivative on product vectors with constant parameter parts.** Let `φ` be a
rough `n`-form on `P × M`, differentiable at `(p, x)`, let `c₀, …, cₙ ∈ P`, and let
`W₀, …, Wₙ` be vector fields on `M`, differentiable at `x`, whose pairwise Lie brackets vanish at
`x`. Then `dφ((c₀, W₀ x), …, (cₙ, Wₙ x))` is the sum over `i` of `(-1) ^ i` times the parameter
derivative along `cᵢ` of `q ↦ φ_(q, x)` on the vectors `(cⱼ, Wⱼ x)`, `j ≠ i`, plus the
derivative along `Wᵢ x` of `y ↦ φ_(p, y)` on the vectors `(cⱼ, Wⱼ y)`, `j ≠ i`. -/
theorem mextDeriv_prod_apply_of_mlieBracket_eq_zero {n : ℕ}
    {φ : RoughForm (𝓘(ℝ, P).prod I) (P × M) F n} {p : P} {x : M}
    (hφ : MDifferentiableAt (𝓘(ℝ, P).prod I)
      ((𝓘(ℝ, P).prod I).prod 𝓘(ℝ, (P × E) [⋀^Fin n]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' ((P × E) [⋀^Fin n]→L[ℝ] F) z (φ z)) (p, x))
    (c : Fin (n + 1) → P) (W : Fin (n + 1) → (y : M) → TangentSpace I y)
    (hW : ∀ i, MDifferentiableAt I I.tangent (fun y ↦ (W i y : TangentBundle I M)) x)
    (hWW : ∀ i j, mlieBracket I (W i) (W j) x = 0) :
    mextDeriv φ (p, x) (fun i ↦ (c i, W i x)) =
      ∑ i, (-1) ^ i.val •
        (fderiv ℝ (fun q ↦ φ (q, x) (i.removeNth fun j ↦ (c j, W j x))) p (c i) +
          mvfderiv I (fun y ↦ φ (p, y) (i.removeNth fun j ↦ (c j, W j y))) x (W i x)) := by
  have : IsManifold I 1 M := .of_le (n := 2) (by norm_num)
  -- The product fields `(cᵢ, Wᵢ)`, constant in the parameter.
  set V : Fin (n + 1) → (z : P × M) → TangentSpace (𝓘(ℝ, P).prod I) z := fun i ↦
    Manifold.prodVectorField (fun _ ↦ (c i : P)) (W i) with hVdef
  have hV (i : Fin (n + 1)) (z : P × M) : V i z = ((c i, W i z.2) : P × E) :=
    Manifold.prodVectorField_apply _ _ z
  have hVd (i : Fin (n + 1)) : MDifferentiableAt (𝓘(ℝ, P).prod I) (𝓘(ℝ, P).prod I).tangent
      (fun z ↦ (V i z : TangentBundle (𝓘(ℝ, P).prod I) (P × M))) (p, x) :=
    Manifold.mdifferentiableAt_prodVectorField (p := (p, x))
      ((contMDiff_tangentBundle_mk_const _).mdifferentiableAt one_ne_zero) (hW i)
  have hVV (i j : Fin (n + 1)) : mlieBracket (𝓘(ℝ, P).prod I) (V i) (V j) (p, x) = 0 := by
    have : IsManifold I (minSmoothness ℝ 2) M := by
      rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
    rw [hVdef, Manifold.mlieBracket_prodVectorField (p := (p, x))
      ((contMDiff_tangentBundle_mk_const _).mdifferentiableAt one_ne_zero)
      ((contMDiff_tangentBundle_mk_const _).mdifferentiableAt one_ne_zero) (hW i) (hW j),
      Manifold.prodVectorField_apply, mlieBracket_const_model_space, hWW]
    -- The zero of the tangent space of `P × M` is that of `P × E` only by unfolding.
    rfl
  have h := mextDeriv_apply_vectorField_of_mlieBracket_eq_zero hφ hVd hVV
  rw [show (V · (p, x)) = fun i ↦ ((c i, W i x) : P × E) from funext fun i ↦ hV i _] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg _ ?_
  have hd : MDifferentiableAt (𝓘(ℝ, P).prod I) 𝓘(ℝ, F)
      (fun z ↦ φ z (i.removeNth (V · z))) (p, x) :=
    mdifferentiableAt_apply_vectorField hφ (V := i.removeNth V) fun j ↦ hVd _
  rw [hd.mvfderiv_prod_eq_add_apply]
  simp only [hV]
  exact congrArg (· + _) (mvfderiv_eq_fderiv_apply _ _ _)

/-- **The exterior derivative on parameter vectors.** For a rough `n`-form `φ` on `P × M`,
differentiable at `(p, x)`, and `a₀, …, aₙ ∈ P`, `dφ((a₀, 0), …, (aₙ, 0))` is the sum over `i`
of `(-1) ^ i` times the derivative along `aᵢ` of `q ↦ φ_(q, x)` on the vectors `(aⱼ, 0)`,
`j ≠ i`. -/
theorem mextDeriv_prod_apply_inl {n : ℕ}
    {φ : RoughForm (𝓘(ℝ, P).prod I) (P × M) F n} {p : P} {x : M}
    (hφ : MDifferentiableAt (𝓘(ℝ, P).prod I)
      ((𝓘(ℝ, P).prod I).prod 𝓘(ℝ, (P × E) [⋀^Fin n]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' ((P × E) [⋀^Fin n]→L[ℝ] F) z (φ z)) (p, x))
    (a : Fin (n + 1) → P) :
    mextDeriv φ (p, x) (fun i ↦ (a i, 0)) =
      ∑ i, (-1) ^ i.val • fderiv ℝ (fun q ↦ φ (q, x) (i.removeNth fun j ↦ (a j, 0))) p (a i) := by
  have h := mextDeriv_prod_apply_of_mlieBracket_eq_zero hφ a 0
    (fun _ ↦ (contMDiff_zeroSection ℝ (TangentSpace I)).mdifferentiableAt one_ne_zero)
    (fun _ _ ↦ by simp)
  refine h.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  simp only [Pi.zero_apply, map_zero]
  -- `map_zero` leaves the zero of a tangent space of `F`, which is that of `F` by unfolding.
  exact congrArg _ (add_zero _)

/-- **The exterior derivative on parameter vectors and one vector along `M`.** For a rough
`(n + 1)`-form `φ` on `P × M`, differentiable at `(p, x)`, `a₀, …, aₙ ∈ P` and `v ∈ T_x M`,
`dφ((a₀, 0), …, (aₙ, 0), (0, v))` is the sum over `i` of `(-1) ^ i` times the derivative along
`aᵢ` of `q ↦ φ_(q, x)` on the vectors `(aⱼ, 0)`, `j ≠ i`, followed by `(0, v)`, plus
`(-1) ^ (n + 1)` times the derivative along `v` of `y ↦ φ_(p, y)((a₀, 0), …, (aₙ, 0))`. -/
theorem mextDeriv_prod_apply_snoc_inr {n : ℕ}
    {φ : RoughForm (𝓘(ℝ, P).prod I) (P × M) F (n + 1)} {p : P} {x : M}
    (hφ : MDifferentiableAt (𝓘(ℝ, P).prod I)
      ((𝓘(ℝ, P).prod I).prod 𝓘(ℝ, (P × E) [⋀^Fin (n + 1)]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' ((P × E) [⋀^Fin (n + 1)]→L[ℝ] F) z (φ z)) (p, x))
    (a : Fin (n + 1) → P) (v : TangentSpace I x) :
    mextDeriv φ (p, x) (Fin.snoc (fun i ↦ (a i, 0)) (0, v)) =
      ∑ i, (-1) ^ i.val • fderiv ℝ
          (fun q ↦ φ (q, x) (Fin.snoc (i.removeNth fun j ↦ (a j, 0)) (0, v))) p (a i) +
        (-1) ^ (n + 1) • mvfderiv I (fun y ↦ φ (p, y) fun j ↦ (a j, 0)) x v := by
  -- The frame: the parameter parts `a₀, …, aₙ, 0` and the fields `0, …, 0, Z` along `M`.
  set Z : (y : M) → TangentSpace I y := FiberBundle.extend E v
  have hZ0 : Z x = v := FiberBundle.extend_apply_self _ v
  set W : Fin (n + 2) → (y : M) → TangentSpace I y := Fin.snoc 0 Z
  have h := mextDeriv_prod_apply_of_mlieBracket_eq_zero hφ (Fin.snoc a 0) W
    (fun i ↦ by
      refine Fin.lastCases ?_ (fun i ↦ ?_) i
      · simpa [W] using FiberBundle.mdifferentiableAt_extend I E v
      · simp only [W, Fin.snoc_castSucc, Pi.zero_apply]
        exact (contMDiff_zeroSection ℝ (TangentSpace I)).mdifferentiableAt one_ne_zero)
    (fun i j ↦ by
      refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> refine Fin.lastCases ?_ (fun j ↦ ?_) j <;>
        simp [W])
  -- Along the slice through `x`, the frame takes the given vectors. The two sides are vectors
  -- of `P × E` and of the tangent space of `P × M`, which agree only by unfolding, so the
  -- entries are matched by `exact`.
  have hpt (q : P) : (fun i ↦ (Fin.snoc (α := fun _ ↦ P) a 0 i, W i x) :
      Fin (n + 2) → TangentSpace (𝓘(ℝ, P).prod I) (q, x)) =
      Fin.snoc (fun i ↦ (a i, 0)) (0, v) := by
    funext i
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · simp only [W, Fin.snoc_last, hZ0]
      exact (Fin.snoc_last (α := fun _ ↦ TangentSpace (𝓘(ℝ, P).prod I) (q, x)) _ _).symm
    · simp only [W, Fin.snoc_castSucc, Pi.zero_apply]
      exact (Fin.snoc_castSucc (α := fun _ ↦ TangentSpace (𝓘(ℝ, P).prod I) (q, x))
        (0, v) (fun i ↦ (a i, 0)) i).symm
  refine (congrArg (mextDeriv φ (p, x)) (hpt p)).symm.trans (h.trans ?_)
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    have e1 : Fin.snoc (α := fun _ ↦ P) a 0 i.castSucc = a i := Fin.snoc_castSucc _ _ _
    have e2 : W i.castSucc x = 0 := by simp [W]
    rw [e1, e2, map_zero, Fin.val_castSucc]
    -- As in `mextDeriv_prod_apply_inl`, the zero left by `map_zero` is that of `F` by unfolding.
    refine congrArg _ ((add_zero _).trans (congrArg (fderiv ℝ · p (a i)) (funext fun q ↦ ?_)))
    exact congrArg _ ((congrArg _ (hpt q)).trans (Fin.removeNth_castSucc_snoc _ _ _))
  · have e1 : Fin.snoc (α := fun _ ↦ P) a 0 (Fin.last (n + 1)) = 0 := Fin.snoc_last _ _
    have e2 : W (Fin.last (n + 1)) x = v := by simp [W, hZ0]
    rw [e1, e2, map_zero, Fin.val_last]
    refine congrArg _ ((zero_add _).trans (congrArg (mvfderiv I · x v) (funext fun y ↦ ?_)))
    refine congrArg _ (funext fun j ↦ ?_)
    simp only [Fin.removeNth_apply, Fin.succAbove_last, W, Fin.snoc_castSucc, Pi.zero_apply]
    -- The zero of `TangentSpace I y` is that of `E` only by unfolding `TangentSpace`.
    rfl

end TauCeti.RoughForm

end
