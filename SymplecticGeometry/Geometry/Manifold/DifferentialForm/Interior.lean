/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Interior
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Flat

/-!
# The interior product of smooth forms, bundled

For a smooth vector field `X`, given as a smooth section of the tangent bundle,
`TauCeti.SmoothForm.interiorProduct X` is the real-linear map
`SmoothForm I M F (k + 1) →ₗ[ℝ] SmoothForm I M F k`, `φ ↦ ι_X φ`, inserting `X` into the first
slot. Its rough form is Tau Ceti's `TauCeti.RoughForm.interior X` (`coe_interiorProduct`), and it
is smooth by Tau Ceti's `TauCeti.IsSmoothForm.interior`. The definition and
`coe_interiorProduct` are adapted from Tau Ceti's `TauCeti.SmoothForm.gradInteriorₗ` and
`TauCeti.SmoothForm.coe_gradInteriorₗ`, with any smooth vector field in place of a gradient.

## Main results

* `TauCeti.SmoothForm.interiorProduct_interiorProduct`: `ι_X ι_X = 0`.
* `TauCeti.SmoothForm.interiorProduct_wedge`: the graded Leibniz rule
  `ι_X (φ ∧ ψ) = ι_X φ ∧ ψ + (-1) ^ (k + 1) φ ∧ ι_X ψ` for `φ` of degree `k + 1`, from Tau Ceti's
  `TauCeti.RoughForm.interior_wedge_apply`.
* `TauCeti.SmoothForm.interiorProduct_apply_degree_one`: on a one-form `α`, `ι_X α` is the
  function `x ↦ α_x (X x)`.
* `TauCeti.SmoothTwoForm.interiorₗ_eq_interiorProduct`: on two-forms the map agrees with Tau
  Ceti's `TauCeti.SmoothTwoForm.interiorₗ`, which is linear in the field rather than in the form.

The map is not named `interiorₗ`, so that it does not clash with Tau Ceti's
`TauCeti.SmoothTwoForm.interiorₗ` under dot notation, `SmoothTwoForm` being an abbreviation of
`SmoothForm I M ℝ 2`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14 (Lemma 14.13).
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k l : ℕ}

/-- The interior product `φ ↦ ι_X φ` with a smooth vector field `X`, as a real-linear map from
smooth `(k + 1)`-forms to smooth `k`-forms: `(ι_X φ)_x (v₁, …, vₖ) = φ_x (X x, v₁, …, vₖ)`. -/
def interiorProduct (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯) :
    SmoothForm I M F (k + 1) →ₗ[ℝ] SmoothForm I M F k where
  toFun φ := ⟨RoughForm.interior (F := F) (k := k) X φ.val,
    (φ.isSmoothForm.interior X.contMDiff).mem_smoothBundleForms⟩
  map_add' φ ψ := Subtype.ext <| by
    simp only [Submodule.coe_add, RoughForm.interior_add]
  map_smul' c φ := Subtype.ext <| by
    simp only [Submodule.coe_smul, RoughForm.interior_smul, RingHom.id_apply]

/-- The rough form of `ι_X φ` is the interior product of the rough form of `φ`. -/
@[simp]
theorem coe_interiorProduct (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯)
    (φ : SmoothForm I M F (k + 1)) :
    (interiorProduct X φ : RoughForm I M F k) = RoughForm.interior (F := F) (k := k) X φ.val :=
  (rfl)

/-- The interior product with the zero vector field is zero. -/
@[simp]
theorem interiorProduct_zero_field (φ : SmoothForm I M F (k + 1)) :
    interiorProduct (0 : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯) φ = 0 :=
  Subtype.ext <| by simp

/-- The interior product is additive in the vector field. -/
@[simp]
theorem interiorProduct_add_field (X Y : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯)
    (φ : SmoothForm I M F (k + 1)) :
    interiorProduct (X + Y) φ = interiorProduct X φ + interiorProduct Y φ :=
  Subtype.ext <| by
    rw [Submodule.coe_add, coe_interiorProduct, coe_interiorProduct, coe_interiorProduct,
      ContMDiffSection.coe_add, RoughForm.interior_add_field]

/-- The interior product commutes with constant multiples of the vector field. -/
@[simp]
theorem interiorProduct_smul_field (c : ℝ) (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯)
    (φ : SmoothForm I M F (k + 1)) :
    interiorProduct (c • X) φ = c • interiorProduct X φ :=
  Subtype.ext <| by
    rw [Submodule.coe_smul, coe_interiorProduct, coe_interiorProduct, ContMDiffSection.coe_smul]
    simpa only [Pi.smul_def] using
      RoughForm.interior_smul_field (F := F) (k := k) (fun _ ↦ c) X φ.val

/-- Inserting the same vector field twice gives zero: `ι_X ι_X = 0`. -/
@[simp]
theorem interiorProduct_interiorProduct (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯)
    (φ : SmoothForm I M F (k + 2)) :
    interiorProduct X (interiorProduct X φ) = 0 :=
  Subtype.ext <| by
    rw [coe_interiorProduct, coe_interiorProduct, RoughForm.interior_self, Submodule.coe_zero]

/-- On a one-form `α`, the interior product with `X` is the function `x ↦ α_x (X x)`. -/
theorem interiorProduct_apply_degree_one (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯)
    (α : SmoothForm I M F 1) (x : M) (v : Fin 0 → TangentSpace I x) :
    (interiorProduct X α).val x v = α.val x ![X x] := by
  rw [coe_interiorProduct, RoughForm.interior_apply, Subsingleton.elim v ![]]

/-- The graded Leibniz rule for the interior product: for `φ` of degree `k + 1` and `ψ` of degree
`l + 1`, `ι_X (φ ∧ ψ) = ι_X φ ∧ ψ + (-1) ^ (k + 1) φ ∧ ι_X ψ`, the first term transported from
degree `k + (l + 1)` to degree `k + 1 + l`. -/
theorem interiorProduct_wedge (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯)
    (φ : SmoothForm I M ℝ (k + 1)) (ψ : SmoothForm I M ℝ (l + 1)) :
    interiorProduct (k := k + 1 + l) X (wedge φ ψ) =
      LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M ℝ q)
          (show k + (l + 1) = k + 1 + l by omega) (wedge (interiorProduct X φ) ψ) +
        (-1 : ℝ) ^ (k + 1) • wedge φ (interiorProduct X ψ) := by
  refine Subtype.ext (funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ ?_)
  rw [coe_interiorProduct, coe_wedge, RoughForm.interior_wedge_apply, Submodule.coe_add,
    Pi.add_apply, ContinuousAlternatingMap.add_apply, cast_apply, Submodule.coe_smul,
    Pi.smul_apply, ContinuousAlternatingMap.smul_apply, coe_wedge, coe_wedge, coe_interiorProduct,
    coe_interiorProduct]

end TauCeti.SmoothForm

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Tau Ceti's contraction `X ↦ ι_X σ` of vector fields into a two-form agrees with the interior
product of smooth forms. -/
theorem interiorₗ_eq_interiorProduct (σ : SmoothTwoForm I M)
    (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯) :
    σ.interiorₗ X = SmoothForm.interiorProduct X σ :=
  Subtype.ext <| by rw [coe_interiorₗ, SmoothForm.coe_interiorProduct]

end TauCeti.SmoothTwoForm

end
