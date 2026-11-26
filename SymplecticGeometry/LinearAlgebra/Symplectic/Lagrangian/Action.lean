/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Matrix.EuclideanLin
public import SymplecticGeometry.LinearAlgebra.Matrix.UnitaryGroup.Real
public import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Frame
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Matrix
public import TauCeti.Analysis.Complex.Circle.Basic
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Projective
public import TauCeti.LinearAlgebra.TotallyReal.Lagrangian
public import TauCeti.Topology.Algebra.Matrix.Realify
import SymplecticGeometry.LinearAlgebra.FiniteDimensional.Submodule

/-!
# The symplectic and unitary actions on the Lagrangian Grassmannian

Write `ℒ ι` for the Lagrangian Grassmannian of the standard model `(StdSpace ι, ω₀)`.

## Main definitions

* An action of the symplectic group `GLSymplectic ι ℝ` on `ℒ ι`, by images of subspaces, and the
  action of the unitary group `unitaryGroup ι ℂ` through realification
  `TauCeti.GLSymplectic.ofUnitary`.
* `SymplecticGeometry.LagrangianGrassmannian.horizontal ι` and `vertical ι`: the coordinate
  Lagrangians `{y = 0}` and `{x = 0}`.
* `SymplecticGeometry.LagrangianGrassmannian.unitaryFrame U`: the Lagrangian `U • {y = 0}` framed
  by the unitary matrix `U`. Its subspace is the span of the columns of
  `fromRows (Re U) (Im U)`, that is, Tau Ceti's real image `U ℝⁿ` read in real coordinates.
* `SymplecticGeometry.LagrangianGrassmannian.unitaryOfFrame h`: the unitary matrix of a frame
  `fromRows X Y` with Lagrangian range, the real orthonormalization of `X + i Y`; it frames that
  range (`unitaryFrame_unitaryOfFrame`).
* `SymplecticGeometry.LagrangianGrassmannian.rotate θ Λ`: the image of `Λ` under the scalar
  unitary matrix `e^{iθ} 1` (Tau Ceti's `Matrix.UnitaryGroup.scalarHom`), that is, under
  `e^{θ J₀}`, with `rotate_rotate` for composition and period `π` (`periodic_rotate`,
  `rotate_int_mul_pi`).

## Main results

* `SymplecticGeometry.isLagrangian_map_toEuclideanLin`: a matrix of
  `Matrix.symplecticGroup ι ℝ` maps Lagrangian subspaces to Lagrangian subspaces.
* `SymplecticGeometry.LagrangianGrassmannian.coe_smul_eq_map_toEuclideanCLE`: the subspace of
  `g • Λ` is the image of `Λ` under the linear equivalence of the matrix `g`.
* `SymplecticGeometry.LagrangianGrassmannian.coe_smul_of_coe_eq`: if `Λ` is spanned by the
  columns of a frame `Z`, then `g • Λ` is spanned by those of `g * Z`.
* `SymplecticGeometry.LagrangianGrassmannian.unitaryFrame_surjective`: every Lagrangian subspace
  has a unitary frame, so `U(n)` and `Sp(2n)` act transitively on `ℒ ι` (the two
  `MulAction.IsPretransitive` instances).
* `SymplecticGeometry.LagrangianGrassmannian.unitaryFrame_eq_unitaryFrame_iff`: two unitary
  frames span the same Lagrangian iff they differ by a real orthogonal matrix, so the stabilizer
  of `{y = 0}` in `U(n)` is `O(n)` (`stabilizer_horizontal`).
* `SymplecticGeometry.LagrangianGrassmannian.rotate_pi_div_two_horizontal`: a quarter turn
  takes `{y = 0}` to `{x = 0}`.

## Implementation notes

The scalar unitary matrix `e^{iθ} 1` of `rotate` is built as in Tau Ceti's
`TauCeti.GLSymplectic.scalarRotationLoop`, with the angle `θ` in place of `2 π t`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3.
-/

public section

namespace SymplecticGeometry

open Matrix Matrix.UnitaryGroup TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "ℒ" ι => LagrangianGrassmannian (stdForm ι)

open StdSpace

/-- A symplectic matrix maps Lagrangian subspaces of `StdSpace ι` to Lagrangian subspaces. -/
theorem isLagrangian_map_toEuclideanLin {A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ}
    (hA : A ∈ symplecticGroup ι ℝ) {L : Submodule ℝ (StdSpace ι)}
    (hL : (stdForm ι).IsLagrangian L) :
    (stdForm ι).IsLagrangian (L.map (toEuclideanLin A)) := by
  let e := (A.toEuclideanCLE (SymplecticGroup.symplectic_det hA).ne_zero).toLinearEquiv
  rw [← coe_toLinearEquiv_toEuclideanCLE A (SymplecticGroup.symplectic_det hA).ne_zero]
  exact (SymplecticForm.IsSymplectomorphism.isLagrangian_map_iff
    (SymplecticForm.isSymplectomorphism_iff.2 fun v w ↦ by
      simpa [e] using mem_symplecticGroup_iff_forall_stdForm.1 hA v w)).2 hL

namespace LagrangianGrassmannian

/-! ### The actions -/

/-- The symplectic group `Sp(2n) = GLSymplectic ι ℝ` acts on the Lagrangian subspaces of
`StdSpace ι` by images, `g • Λ = g Λ`. -/
noncomputable instance : MulAction (GLSymplectic ι ℝ) (ℒ ι) where
  smul g Λ := ⟨(Λ : Submodule ℝ (StdSpace ι)).map
      (toEuclideanLin ((g : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)),
    isLagrangian_map_toEuclideanLin (GLSymplectic.mem_iff_mem_symplecticGroup.1 g.property)
      Λ.isLagrangian⟩
  -- In both proofs, the subspace of `g • Λ` is by definition the `Submodule.map` given in
  -- `smul` above; `change` unfolds to it, as `coe_smul` can only be stated after the instance.
  one_smul Λ := toSubmodule_injective <| by
    change Submodule.map _ _ = _
    simp
  mul_smul g h Λ := toSubmodule_injective <| by
    change Submodule.map _ _ = Submodule.map _ (Submodule.map _ _)
    simp [Submodule.map_comp]

/-- The subspace of `g • Λ` is the image of `Λ` under the symplectic matrix `g`. -/
@[simp]
theorem coe_smul (g : GLSymplectic ι ℝ) (Λ : ℒ ι) :
    ((g • Λ : ℒ ι) : Submodule ℝ (StdSpace ι)) =
      (Λ : Submodule ℝ (StdSpace ι)).map
        (toEuclideanLin ((g : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)) :=
  (rfl)

/-- The subspace of `g • Λ` is the image of `Λ` under the linear automorphism of `StdSpace ι`
given by the symplectic matrix `g`. -/
theorem coe_smul_eq_map_toEuclideanCLE (g : GLSymplectic ι ℝ) (Λ : ℒ ι) :
    ((g • Λ : ℒ ι) : Submodule ℝ (StdSpace ι)) =
      (Λ : Submodule ℝ (StdSpace ι)).map
        ((((g : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).toEuclideanCLE
          (g : GL (ι ⊕ ι) ℝ).det_ne_zero).toLinearEquiv : StdSpace ι →ₗ[ℝ] StdSpace ι) := by
  rw [coe_smul, coe_toLinearEquiv_toEuclideanCLE]

/-- If a Lagrangian `Λ` is spanned by the columns of a frame `Z`, its image under a symplectic
matrix `g` is spanned by the columns of `g * Z`. -/
theorem coe_smul_of_coe_eq (g : GLSymplectic ι ℝ) {Λ : ℒ ι} {Z : Matrix (ι ⊕ ι) ι ℝ}
    (hΛ : (Λ : Submodule ℝ (StdSpace ι)) = LinearMap.range (toEuclideanLin Z)) :
    ((g • Λ : ℒ ι) : Submodule ℝ (StdSpace ι)) =
      LinearMap.range (toEuclideanLin (((g : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) * Z)) := by
  rw [coe_smul, hΛ, ← LinearMap.range_comp, toEuclideanLin, toLpLin_mul_same]

/-- The unitary group `U(n)` acts on the Lagrangian subspaces of `StdSpace ι` through its
realification `TauCeti.GLSymplectic.ofUnitary : U(n) → Sp(2n)`. -/
noncomputable instance : MulAction (unitaryGroup ι ℂ) (ℒ ι) :=
  MulAction.compHom _ GLSymplectic.ofUnitary

theorem unitary_smul_def (U : unitaryGroup ι ℂ) (Λ : ℒ ι) :
    U • Λ = GLSymplectic.ofUnitary U • Λ :=
  (rfl)

/-- Acting by the realification `ofUnitary U` of a unitary matrix is acting by `U`. As a simp
lemma it makes `U • Λ` the normal form of the unitary action. -/
@[simp]
theorem ofUnitary_smul (U : unitaryGroup ι ℂ) (Λ : ℒ ι) :
    GLSymplectic.ofUnitary U • Λ = U • Λ :=
  (unitary_smul_def U Λ).symm

/-- The subspace of `U • Λ` is the image of `Λ` under the realification of `U`. -/
@[simp]
theorem coe_unitary_smul (U : unitaryGroup ι ℂ) (Λ : ℒ ι) :
    ((U • Λ : ℒ ι) : Submodule ℝ (StdSpace ι)) =
      (Λ : Submodule ℝ (StdSpace ι)).map (toEuclideanLin (U : Matrix ι ι ℂ).realify) := by
  rw [unitary_smul_def, coe_smul, GLSymplectic.coe_ofUnitary]

/-! ### The coordinate Lagrangians -/

variable (ι) in
/-- The horizontal Lagrangian subspace `{y = 0}` of `StdSpace ι`. -/
noncomputable def horizontal : ℒ ι :=
  ⟨LinearMap.ker y, graph_zero (ι := ι) ▸ (isLagrangian_graph_iff 0).2 isSymm_zero⟩

variable (ι) in
/-- The vertical Lagrangian subspace `{x = 0}` of `StdSpace ι`. -/
noncomputable def vertical : ℒ ι :=
  ⟨LinearMap.ker x, graphY_zero (ι := ι) ▸ (isLagrangian_graphY_iff 0).2 isSymm_zero⟩

omit [DecidableEq ι] in
@[simp]
theorem coe_horizontal : (horizontal ι : Submodule ℝ (StdSpace ι)) = LinearMap.ker y :=
  (rfl)

omit [DecidableEq ι] in
@[simp]
theorem coe_vertical : (vertical ι : Submodule ℝ (StdSpace ι)) = LinearMap.ker x :=
  (rfl)

omit [DecidableEq ι] in
@[simp]
theorem mem_horizontal_iff {z : StdSpace ι} : z ∈ horizontal ι ↔ z.y = 0 :=
  LinearMap.mem_ker

omit [DecidableEq ι] in
@[simp]
theorem mem_vertical_iff {z : StdSpace ι} : z ∈ vertical ι ↔ z.x = 0 :=
  LinearMap.mem_ker

omit [DecidableEq ι] in
/-- The horizontal and vertical Lagrangians are complementary. -/
theorem isCompl_horizontal_vertical :
    IsCompl (horizontal ι : Submodule ℝ (StdSpace ι)) (vertical ι) := by
  simpa using isCompl_graph_ker_x (0 : Matrix ι ι ℝ)

/-- The matrix `J` of `TauCeti.GLSymplectic.symJ`, `(x, y) ↦ (-y, x)`, maps the horizontal
Lagrangian to the vertical one. -/
theorem symJ_smul_horizontal : GLSymplectic.symJ ι ℝ • horizontal ι = vertical ι :=
  toSubmodule_injective <| by
    simpa using map_symJ_graph (0 : Matrix ι ι ℝ)

/-! ### Unitary frames -/

/-- The Lagrangian subspace `U • {y = 0}` framed by a unitary matrix `U`: the span of the columns
of `fromRows (Re U) (Im U)`. -/
noncomputable def unitaryFrame (U : unitaryGroup ι ℂ) : ℒ ι :=
  U • horizontal ι

theorem unitaryFrame_def (U : unitaryGroup ι ℂ) : unitaryFrame U = U • horizontal ι :=
  (rfl)

/-- The Lagrangian framed by `U` is Tau Ceti's real image `U ℝⁿ`, read in `StdSpace ι`. -/
theorem coe_unitaryFrame_eq_map (U : unitaryGroup ι ℂ) :
    (unitaryFrame U : Submodule ℝ (StdSpace ι)) =
      (U : Matrix ι ι ℂ).realImage.map
        (complexEuclideanEquiv ι : EuclideanSpace ℂ ι →ₗ[ℝ] StdSpace ι) := by
  rw [unitaryFrame_def, coe_unitary_smul, coe_horizontal, map_realImage]

/-- The intersection of the Lagrangian framed by `U` with `{y = 0}` has the dimension of the
intersection of Tau Ceti's real image `U ℝⁿ` with `ℝⁿ`. -/
theorem finrank_unitaryFrame_inf_horizontal (U : unitaryGroup ι ℂ) :
    Module.finrank ℝ ↥((unitaryFrame U : Submodule ℝ (StdSpace ι)) ⊓ horizontal ι) =
      Module.finrank ℝ ↥((U : Matrix ι ι ℂ).realImage ⊓ TauCeti.realSubspace ι) := by
  rw [coe_unitaryFrame_eq_map, coe_horizontal, ← StdSpace.map_realSubspace,
    ← Submodule.map_inf _ (StdSpace.complexEuclideanEquiv ι).injective,
    LinearEquiv.finrank_map_eq]

/-- The Lagrangian framed by `U` is spanned by the columns of the real `2n × n` matrix
`fromRows (Re U) (Im U)`. -/
theorem coe_unitaryFrame (U : unitaryGroup ι ℂ) :
    (unitaryFrame U : Submodule ℝ (StdSpace ι)) =
      LinearMap.range (toEuclideanLin
        (fromRows ((U : Matrix ι ι ℂ).map Complex.re) ((U : Matrix ι ι ℂ).map Complex.im))) := by
  rw [coe_unitaryFrame_eq_map, range_toEuclideanLin_fromRows_eq_map_realImage,
    map_re_add_I_smul_map_im]

@[simp]
theorem unitaryFrame_one : unitaryFrame (1 : unitaryGroup ι ℂ) = horizontal ι :=
  one_smul _ _

@[simp]
theorem unitaryFrame_mul (U U' : unitaryGroup ι ℂ) :
    unitaryFrame (U * U') = U • unitaryFrame U' :=
  mul_smul _ _ _

/-! ### Rotations -/

/-- The rotation of a Lagrangian `Λ` by the scalar unitary matrix `e^{iθ} 1`, the image of
`e^{iθ}` under `Matrix.UnitaryGroup.scalarHom`, that is, by `e^{θ J₀}`. -/
noncomputable def rotate (θ : ℝ) (Λ : ℒ ι) : ℒ ι :=
  scalarHom ι ℂ (circleEquivUnitary (Circle.exp θ)) • Λ

theorem rotate_def (θ : ℝ) (Λ : ℒ ι) :
    rotate θ Λ = scalarHom ι ℂ (circleEquivUnitary (Circle.exp θ)) • Λ :=
  (rfl)

@[simp]
theorem rotate_zero (Λ : ℒ ι) : rotate 0 Λ = Λ := by
  rw [rotate_def, Circle.exp_zero, map_one, map_one, one_smul]

/-- Rotating by `φ` and then by `θ` is rotating by `θ + φ`. -/
theorem rotate_rotate (θ φ : ℝ) (Λ : ℒ ι) : rotate θ (rotate φ Λ) = rotate (θ + φ) Λ := by
  rw [rotate_def, rotate_def, rotate_def, smul_smul, Circle.exp_add, map_mul, map_mul]

/-- The scalar unitary matrix `-1` fixes every Lagrangian subspace. -/
@[simp]
theorem unitary_neg_one_smul (Λ : ℒ ι) : (-1 : unitaryGroup ι ℂ) • Λ = Λ :=
  toSubmodule_injective <| by simp [Unitary.coe_neg]

/-- Rotating by `π` fixes every Lagrangian subspace, since `e^{iπ} = -1`. -/
@[simp]
theorem rotate_pi (Λ : ℒ ι) : rotate Real.pi Λ = Λ := by
  have h : scalarHom ι ℂ (circleEquivUnitary (Circle.exp Real.pi)) = -1 :=
    Subtype.ext <| by
      rw [coe_scalarHom, coe_circleEquivUnitary, Circle.coe_exp, Complex.exp_pi_mul_I, map_neg,
        map_one, Unitary.coe_neg, OneMemClass.coe_one]
  rw [rotate_def, h, unitary_neg_one_smul]

/-- Rotating by `θ + π` is rotating by `θ`: rotations have period `π`. -/
@[simp]
theorem rotate_add_pi (θ : ℝ) (Λ : ℒ ι) : rotate (θ + Real.pi) Λ = rotate θ Λ := by
  rw [← rotate_rotate, rotate_pi]

/-- The rotations of a fixed Lagrangian subspace are periodic in the angle, with period `π`. -/
theorem periodic_rotate (Λ : ℒ ι) : Function.Periodic (rotate · Λ) Real.pi :=
  fun θ => rotate_add_pi θ Λ

/-- Rotating by an integer multiple of `π` fixes every Lagrangian subspace. -/
@[simp]
theorem rotate_int_mul_pi (k : ℤ) (Λ : ℒ ι) : rotate (k * Real.pi) Λ = Λ :=
  ((periodic_rotate Λ).int_mul_eq k).trans (rotate_zero Λ)

/-- A quarter turn takes the horizontal Lagrangian `{y = 0}` to the vertical one `{x = 0}`. -/
theorem rotate_pi_div_two_horizontal : rotate (Real.pi / 2) (horizontal ι) = vertical ι := by
  rw [← symJ_smul_horizontal, rotate_def, unitary_smul_def]
  congr 1
  refine Subtype.ext (Units.ext ?_)
  rw [GLSymplectic.coe_ofUnitary, GLSymplectic.coe_symJ, ← realify_I_smul_one, coe_scalarHom,
    coe_circleEquivUnitary, scalar_apply, ← smul_one_eq_diagonal]
  simp [Circle.coe_exp, Complex.exp_mul_I]

/-- The unitary matrix of a Lagrangian frame `fromRows X Y`: the real orthonormalization of its
complex frame `X + i Y`, which is invertible since the range of the frame is Lagrangian. Its
unitary frame is the range (`unitaryFrame_unitaryOfFrame`). -/
noncomputable def unitaryOfFrame {X Y : Matrix ι ι ℝ}
    (h : (stdForm ι).IsLagrangian (LinearMap.range (toEuclideanLin (fromRows X Y)))) :
    unitaryGroup ι ℂ :=
  ⟨GeneralLinearGroup.realOrthonormalize
      (GeneralLinearGroup.mkOfDetNeZero _ (det_ne_zero_of_isLagrangian_range_fromRows h)),
    GeneralLinearGroup.realOrthonormalize_mem_unitaryGroup
      (map_im_conjTranspose_mul_self_eq_zero_of_transpose_mul_eq
        ((isLagrangian_range_fromRows_iff _ _).1 h).2)⟩

theorem coe_unitaryOfFrame {X Y : Matrix ι ι ℝ}
    (h : (stdForm ι).IsLagrangian (LinearMap.range (toEuclideanLin (fromRows X Y)))) :
    (unitaryOfFrame h : Matrix ι ι ℂ) = GeneralLinearGroup.realOrthonormalize
      (GeneralLinearGroup.mkOfDetNeZero _ (det_ne_zero_of_isLagrangian_range_fromRows h)) :=
  (rfl)

/-- The Lagrangian framed by the unitary matrix of a Lagrangian frame is the Lagrangian that
the frame spans. -/
@[simp]
theorem unitaryFrame_unitaryOfFrame {X Y : Matrix ι ι ℝ}
    (h : (stdForm ι).IsLagrangian (LinearMap.range (toEuclideanLin (fromRows X Y)))) :
    unitaryFrame (unitaryOfFrame h) = ofFrame X Y h :=
  toSubmodule_injective <| by
    rw [coe_ofFrame, coe_unitaryFrame_eq_map, coe_unitaryOfFrame,
      GeneralLinearGroup.realImage_realOrthonormalize, GeneralLinearGroup.val_mkOfDetNeZero,
      ← range_toEuclideanLin_fromRows_eq_map_realImage]

/-- **Transitivity of `U(n)`.** Every Lagrangian subspace of `StdSpace ι` is framed by a unitary
matrix. -/
theorem unitaryFrame_surjective :
    Function.Surjective (unitaryFrame : unitaryGroup ι ℂ → ℒ ι) := by
  intro Λ
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ ι) =
      Module.finrank ℝ (Λ : Submodule ℝ (StdSpace ι)) := by
    rw [finrank_euclideanSpace, Λ.finrank_eq_card]
  obtain ⟨L, -, hLΛ⟩ := (Λ : Submodule ℝ (StdSpace ι)).exists_linearMap_injective_range_eq hdim
  set Z := toEuclideanLin.symm L
  have hZ : LinearMap.range (toEuclideanLin (fromRows Z.toRows₁ Z.toRows₂)) = Λ := by
    rw [fromRows_toRows, LinearEquiv.apply_symm_apply, hLΛ]
  have hL : (stdForm ι).IsLagrangian
      (LinearMap.range (toEuclideanLin (fromRows Z.toRows₁ Z.toRows₂))) :=
    hZ ▸ Λ.isLagrangian
  exact ⟨unitaryOfFrame hL, by
    rw [unitaryFrame_unitaryOfFrame]
    exact toSubmodule_injective ((coe_ofFrame _ _ _).trans hZ)⟩

instance : MulAction.IsPretransitive (unitaryGroup ι ℂ) (ℒ ι) :=
  MulAction.IsPretransitive.of_orbit (x₀ := horizontal ι) unitaryFrame_surjective

instance : MulAction.IsPretransitive (GLSymplectic ι ℝ) (ℒ ι) :=
  MulAction.IsPretransitive.of_smul_eq GLSymplectic.ofUnitary (unitary_smul_def _ _).symm

/-- A unitary matrix frames the horizontal Lagrangian iff it is real, that is, orthogonal. -/
theorem unitaryFrame_eq_horizontal_iff {U : unitaryGroup ι ℂ} :
    unitaryFrame U = horizontal ι ↔ U ∈ UnitaryGroup.realSubgroup ι := by
  rw [← toSubmodule_inj, coe_unitaryFrame_eq_map, coe_horizontal, ← map_realSubspace,
    (Submodule.map_injective_of_injective (complexEuclideanEquiv ι).injective).eq_iff,
    UnitaryGroup.mem_realSubgroup_iff_exists]
  constructor
  · intro h
    rw [← realImage_map_ofReal (isUnit_one (M := Matrix ι ι ℝ)), map_ofReal_one] at h
    obtain ⟨O, hO, hUO⟩ := exists_mem_orthogonalGroup_eq_mul_map_ofReal
      (M := 1) (M' := Unitary.toUnits U) h.symm (by simp)
      (UnitaryGroup.map_re_conjTranspose_mul_self U)
    exact ⟨O, hO, by simpa using hUO.symm⟩
  · rintro ⟨O, hO, hUO⟩
    rw [← hUO]
    exact realImage_map_ofReal ((isUnit_iff_isUnit_det _).2
      (isUnit_det_of_left_inverse ((mem_orthogonalGroup_iff' ι ℝ).1 hO)))

/-- Two unitary matrices frame the same Lagrangian iff they differ by a real orthogonal matrix
on the right. -/
theorem unitaryFrame_eq_unitaryFrame_iff {U U' : unitaryGroup ι ℂ} :
    unitaryFrame U = unitaryFrame U' ↔ U⁻¹ * U' ∈ UnitaryGroup.realSubgroup ι := by
  rw [← unitaryFrame_eq_horizontal_iff, unitaryFrame_mul, inv_smul_eq_iff, ← unitaryFrame_def,
    eq_comm]

/-- The stabilizer of the horizontal Lagrangian in `U(n)` is the orthogonal group `O(n)`. -/
theorem stabilizer_horizontal :
    MulAction.stabilizer (unitaryGroup ι ℂ) (horizontal ι) = UnitaryGroup.realSubgroup ι := by
  ext U
  rw [MulAction.mem_stabilizer_iff, ← unitaryFrame_def, unitaryFrame_eq_horizontal_iff]

end LagrangianGrassmannian

end SymplecticGeometry

end
