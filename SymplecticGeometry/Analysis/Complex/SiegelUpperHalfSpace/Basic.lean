/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.CStarAlgebra.Classes
import TauCeti.Analysis.Matrix.PosDef
import SymplecticGeometry.LinearAlgebra.Matrix.OfReal
import SymplecticGeometry.LinearAlgebra.Matrix.PosDef.Basic

/-!
# The Siegel upper half space

For a type `ι`, the Siegel upper half space `SiegelUpperHalfSpace ι` is the space of complex
`ι × ι` matrices `Z = X + i Y` that are symmetric, `Zᵀ = Z`, and whose imaginary part `Y` is
positive definite. For `ι = Fin n` it is the space `𝒮ₙ` on which the real symplectic group
`Sp(2n)` acts by generalized Möbius transformations `Z ↦ (AZ + B)(CZ + D)⁻¹`.

## Main definitions

* `SymplecticGeometry.SiegelUpperHalfSpace ι`: the Siegel upper half space, a structure with the
  matrix `Z` and the two conditions on it, carrying the topology induced from the matrices.
* `SiegelUpperHalfSpace.re`, `SiegelUpperHalfSpace.im`: the real symmetric matrices `X` and `Y`.
* `SiegelUpperHalfSpace.I`: the base point `i𝟙`.
* `SiegelUpperHalfSpace.toSymm`: the inclusion into the complex symmetric matrices.
* `SiegelUpperHalfSpace.homeomorphUpperHalfPlane`: for a type with one element, the
  homeomorphism with Mathlib's `UpperHalfPlane`, sending `I` to `UpperHalfPlane.I`.

## Main results

* `SiegelUpperHalfSpace.coe_eq_re_add_I_smul_im`: `Z = X + i Y`.
* `SiegelUpperHalfSpace.isOpen_setOfPred_posDef_im`: the condition `Y > 0` cuts out an open subset
  of the complex symmetric matrices, and `SiegelUpperHalfSpace.isOpenEmbedding_toSymm`: the
  Siegel upper half space is homeomorphic to this open subset.

The structure and its basic and topological API follow Mathlib's `UpperHalfPlane`, in
`Mathlib/Analysis/Complex/UpperHalfPlane/Basic.lean` and
`Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.5
-/

public section

noncomputable section

open Complex Matrix Topology

namespace SymplecticGeometry

/-- The Siegel upper half space of index `ι`: the complex symmetric `ι × ι` matrices whose
imaginary part is positive definite. -/
@[ext]
structure SiegelUpperHalfSpace (ι : Type*) where
  /-- The underlying complex matrix of a point of the Siegel upper half space. -/
  protected coe : Matrix ι ι ℂ
  /-- A point of the Siegel upper half space is a symmetric matrix. -/
  isSymm : coe.IsSymm
  /-- The imaginary part of a point of the Siegel upper half space is positive definite. -/
  posDef_map_im : (coe.map Complex.im).PosDef

namespace SiegelUpperHalfSpace

variable {ι : Type*}

attribute [coe] SiegelUpperHalfSpace.coe

instance : CoeOut (SiegelUpperHalfSpace ι) (Matrix ι ι ℂ) := ⟨SiegelUpperHalfSpace.coe⟩

@[simp]
theorem coe_mk (Z : Matrix ι ι ℂ) (hZ : Z.IsSymm) (hY : (Z.map Complex.im).PosDef) :
    (mk Z hZ hY : Matrix ι ι ℂ) = Z :=
  (rfl)

@[simp]
theorem mk_coe (Z : SiegelUpperHalfSpace ι) : mk Z Z.isSymm Z.posDef_map_im = Z :=
  (rfl)

theorem coe_injective : Function.Injective (SiegelUpperHalfSpace.coe : _ → Matrix ι ι ℂ) :=
  fun _ _ ↦ SiegelUpperHalfSpace.ext

@[simp, norm_cast]
theorem coe_inj {Z W : SiegelUpperHalfSpace ι} : (Z : Matrix ι ι ℂ) = W ↔ Z = W :=
  coe_injective.eq_iff

/-- A complex matrix is a point of the Siegel upper half space exactly when it is symmetric
with positive definite imaginary part. -/
theorem mem_range_coe_iff {Z : Matrix ι ι ℂ} :
    Z ∈ Set.range (SiegelUpperHalfSpace.coe : _ → Matrix ι ι ℂ) ↔
      Z.IsSymm ∧ (Z.map Complex.im).PosDef :=
  ⟨fun ⟨W, hW⟩ ↦ hW ▸ ⟨W.isSymm, W.posDef_map_im⟩, fun h ↦ ⟨mk Z h.1 h.2, rfl⟩⟩

instance canLift : CanLift (Matrix ι ι ℂ) (SiegelUpperHalfSpace ι) (↑)
    fun Z ↦ Z.IsSymm ∧ (Z.map Complex.im).PosDef where
  prf _ h := mem_range_coe_iff.2 h

/-- The real part `X` of a point `Z = X + i Y` of the Siegel upper half space. -/
def re (Z : SiegelUpperHalfSpace ι) : Matrix ι ι ℝ :=
  (Z : Matrix ι ι ℂ).map Complex.re

/-- The imaginary part `Y` of a point `Z = X + i Y` of the Siegel upper half space. -/
def im (Z : SiegelUpperHalfSpace ι) : Matrix ι ι ℝ :=
  (Z : Matrix ι ι ℂ).map Complex.im

theorem re_def (Z : SiegelUpperHalfSpace ι) : Z.re = (Z : Matrix ι ι ℂ).map Complex.re :=
  (rfl)

theorem im_def (Z : SiegelUpperHalfSpace ι) : Z.im = (Z : Matrix ι ι ℂ).map Complex.im :=
  (rfl)

@[simp]
theorem re_apply (Z : SiegelUpperHalfSpace ι) (i j : ι) : Z.re i j = ((Z : Matrix ι ι ℂ) i j).re :=
  (rfl)

@[simp]
theorem im_apply (Z : SiegelUpperHalfSpace ι) (i j : ι) : Z.im i j = ((Z : Matrix ι ι ℂ) i j).im :=
  (rfl)

@[simp]
theorem re_mk (Z : Matrix ι ι ℂ) (hZ : Z.IsSymm) (hY : (Z.map Complex.im).PosDef) :
    (mk Z hZ hY).re = Z.map Complex.re :=
  (rfl)

@[simp]
theorem im_mk (Z : Matrix ι ι ℂ) (hZ : Z.IsSymm) (hY : (Z.map Complex.im).PosDef) :
    (mk Z hZ hY).im = Z.map Complex.im :=
  (rfl)

/-- The imaginary part of a point of the Siegel upper half space is positive definite. -/
theorem posDef_im (Z : SiegelUpperHalfSpace ι) : Z.im.PosDef :=
  Z.posDef_map_im

/-- The imaginary part of a point of the Siegel upper half space is invertible. -/
theorem isUnit_det_map_im [Fintype ι] [DecidableEq ι] (Z : SiegelUpperHalfSpace ι) :
    IsUnit ((Z : Matrix ι ι ℂ).map Complex.im).det :=
  (isUnit_iff_isUnit_det _).1 Z.posDef_map_im.isUnit

theorem isSymm_re (Z : SiegelUpperHalfSpace ι) : Z.re.IsSymm :=
  Z.isSymm.map _

theorem isSymm_im (Z : SiegelUpperHalfSpace ι) : Z.im.IsSymm :=
  Z.isSymm.map _

/-- A point of the Siegel upper half space is `X + i Y`, for its real part `X` and its
imaginary part `Y`. -/
theorem coe_eq_re_add_I_smul_im (Z : SiegelUpperHalfSpace ι) :
    (Z : Matrix ι ι ℂ) = Z.re.map ofReal + Complex.I • Z.im.map ofReal := by
  rw [re_def, im_def, map_re_add_I_smul_map_im]

/-- Two points of the Siegel upper half space with the same real and imaginary parts are
equal. -/
theorem ext_re_im {Z W : SiegelUpperHalfSpace ι} (hre : Z.re = W.re) (him : Z.im = W.im) :
    Z = W := by
  rw [← coe_inj, coe_eq_re_add_I_smul_im, coe_eq_re_add_I_smul_im, hre, him]

section I

variable [DecidableEq ι]

/-- The base point `i𝟙` of the Siegel upper half space. -/
protected def I : SiegelUpperHalfSpace ι where
  coe := Complex.I • (1 : Matrix ι ι ℂ)
  isSymm := isSymm_one.smul _
  posDef_map_im := by
    simpa using PosDef.one

@[simp]
theorem coe_I : (SiegelUpperHalfSpace.I : SiegelUpperHalfSpace ι) =
    Complex.I • (1 : Matrix ι ι ℂ) :=
  (rfl)

@[simp]
theorem re_I : (SiegelUpperHalfSpace.I : SiegelUpperHalfSpace ι).re = 0 := by
  simp [re_def]

@[simp]
theorem im_I : (SiegelUpperHalfSpace.I : SiegelUpperHalfSpace ι).im = 1 := by
  simp [im_def]

instance : Inhabited (SiegelUpperHalfSpace ι) := ⟨SiegelUpperHalfSpace.I⟩

end I

/-! ### Topology -/

instance : TopologicalSpace (SiegelUpperHalfSpace ι) :=
  .induced SiegelUpperHalfSpace.coe inferInstance

@[fun_prop]
theorem isEmbedding_coe : IsEmbedding ((↑) : SiegelUpperHalfSpace ι → Matrix ι ι ℂ) :=
  coe_injective.isEmbedding_induced

@[fun_prop]
theorem continuous_coe : Continuous ((↑) : SiegelUpperHalfSpace ι → Matrix ι ι ℂ) :=
  isEmbedding_coe.continuous

@[fun_prop]
theorem continuous_re : Continuous (re : SiegelUpperHalfSpace ι → Matrix ι ι ℝ) :=
  continuous_coe.matrix_map Complex.continuous_re

@[fun_prop]
theorem continuous_im : Continuous (im : SiegelUpperHalfSpace ι → Matrix ι ι ℝ) :=
  continuous_coe.matrix_map Complex.continuous_im

/-- A map into the Siegel upper half space is continuous when its matrix is. -/
@[fun_prop]
theorem _root_.Continuous.siegelUpperHalfSpaceMk {X : Type*} [TopologicalSpace X]
    {f : X → Matrix ι ι ℂ} (hf : Continuous f) (hS : ∀ x, (f x).IsSymm)
    (hY : ∀ x, ((f x).map Complex.im).PosDef) :
    Continuous fun x ↦ mk (f x) (hS x) (hY x) :=
  isEmbedding_coe.continuous_iff.mpr hf

instance : T3Space (SiegelUpperHalfSpace ι) := isEmbedding_coe.t3Space

/-! ### The Siegel upper half space in the symmetric matrices -/

/-- The inclusion of the Siegel upper half space into the complex symmetric matrices. -/
def toSymm (Z : SiegelUpperHalfSpace ι) : {Z : Matrix ι ι ℂ // Z.IsSymm} :=
  ⟨Z, Z.isSymm⟩

@[simp]
theorem coe_toSymm (Z : SiegelUpperHalfSpace ι) : (Z.toSymm : Matrix ι ι ℂ) = Z :=
  (rfl)

theorem toSymm_injective : Function.Injective (toSymm : SiegelUpperHalfSpace ι → _) :=
  fun _ _ h ↦ coe_injective (congrArg Subtype.val h)

/-- The image of the Siegel upper half space in the complex symmetric matrices consists of the
matrices with positive definite imaginary part. -/
theorem range_toSymm :
    Set.range (toSymm : SiegelUpperHalfSpace ι → _) =
      {Z : {Z : Matrix ι ι ℂ // Z.IsSymm} | ((Z : Matrix ι ι ℂ).map Complex.im).PosDef} := by
  ext ⟨Z, hZ⟩
  exact ⟨fun ⟨W, hW⟩ ↦ hW ▸ W.posDef_im, fun h ↦ ⟨mk Z hZ h, rfl⟩⟩

/-- Among the complex symmetric matrices, those with positive definite imaginary part form an
open set. -/
theorem isOpen_setOfPred_posDef_im [Finite ι] :
    IsOpen {Z : {Z : Matrix ι ι ℂ // Z.IsSymm} | ((Z : Matrix ι ι ℂ).map Complex.im).PosDef} := by
  let f : {Z : Matrix ι ι ℂ // Z.IsSymm} → selfAdjoint (Matrix ι ι ℝ) := fun Z ↦
    ⟨(Z : Matrix ι ι ℂ).map Complex.im,
      selfAdjoint.mem_iff.2 (isHermitian_iff_isSymm.2 (Z.property.map _))⟩
  have hf : Continuous f :=
    (continuous_subtypeVal.matrix_map Complex.continuous_im).subtype_mk _
  exact Matrix.isOpen_setOfPred_posDef_selfAdjoint.preimage hf

theorem isEmbedding_toSymm : IsEmbedding (toSymm : SiegelUpperHalfSpace ι → _) :=
  .of_comp (continuous_coe.subtype_mk _) continuous_subtypeVal isEmbedding_coe

/-- The Siegel upper half space is homeomorphic, by its inclusion, to an open subset of the
complex symmetric matrices. -/
theorem isOpenEmbedding_toSymm [Finite ι] :
    IsOpenEmbedding (toSymm : SiegelUpperHalfSpace ι → _) :=
  ⟨isEmbedding_toSymm, range_toSymm.symm ▸ isOpen_setOfPred_posDef_im⟩

/-! ### Index one: the upper half plane -/

section Unique

variable [Unique ι]

/-- For a type `ι` with one element, the Siegel upper half space of index `ι` is homeomorphic to
the upper half plane, by the only entry of its matrices. -/
def homeomorphUpperHalfPlane : SiegelUpperHalfSpace ι ≃ₜ UpperHalfPlane where
  toFun Z := ⟨(Z : Matrix ι ι ℂ) default default, posDef_iff_of_unique.1 Z.posDef_im⟩
  invFun z := ⟨Matrix.of fun _ _ ↦ (z : ℂ), IsSymm.ext fun _ _ ↦ rfl,
    posDef_iff_of_unique.2 z.im_pos⟩
  left_inv Z := by
    ext i j
    simp [Subsingleton.elim i default, Subsingleton.elim j default]
  right_inv _ := rfl
  continuous_toFun := (continuous_coe.matrix_elem _ _).upperHalfPlaneMk _
  continuous_invFun := Continuous.siegelUpperHalfSpaceMk
    (continuous_matrix fun _ _ ↦ UpperHalfPlane.continuous_coe) _ _

@[simp]
theorem coe_homeomorphUpperHalfPlane_apply (Z : SiegelUpperHalfSpace ι) :
    (homeomorphUpperHalfPlane Z : ℂ) = (Z : Matrix ι ι ℂ) default default :=
  (rfl)

@[simp]
theorem coe_homeomorphUpperHalfPlane_symm_apply (z : UpperHalfPlane) (i j : ι) :
    ((homeomorphUpperHalfPlane (ι := ι)).symm z : Matrix ι ι ℂ) i j = z :=
  (rfl)

@[simp]
theorem homeomorphUpperHalfPlane_I [DecidableEq ι] :
    homeomorphUpperHalfPlane (SiegelUpperHalfSpace.I : SiegelUpperHalfSpace ι) =
      UpperHalfPlane.I := by
  ext
  simp [UpperHalfPlane.coe_I]

end Unique

end SiegelUpperHalfSpace

end SymplecticGeometry

end
