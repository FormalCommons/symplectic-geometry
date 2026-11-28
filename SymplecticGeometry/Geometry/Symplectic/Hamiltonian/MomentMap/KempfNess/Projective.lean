/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.Function
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Action
public import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Kahler
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.ComplexProjectiveSpace
import SymplecticGeometry.Geometry.Lie.Exponential.Units
import SymplecticGeometry.Geometry.Manifold.GroupAction.LogNorm
import SymplecticGeometry.Geometry.Manifold.Projectivization.Pseudoholomorphic
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Restrict
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.CompatibleMetric

/-!
# Complexified linear actions on complex projective space

Let `C : LieComplexification I G IC Gc` be a complexification, and let `G` and `Gc` act
`ℂ`-linearly on `V = ℂⁿ⁺¹`, so that both act on `ℙ ℂ V` by `g • [v] = [g • v]`
(`Projectivization.smul_mk`). This file shows that if the action of `Gc` on `V` is smooth and a
complexified action of that of `G` for multiplication by `i`, then so is the induced action on
`ℂPⁿ = ℙ ℂ V`, for its complex structure `J`. For an action through a representation
`ρ : Gc →* GL(n + 1, ℂ)` and `G` acting through `ρ ∘ C.toHom`, the first condition of a
complexified action on `V` holds by definition, and since the generator `X_Z v` is `dρ₁(Z) v`
(`TauCeti.fundamentalVectorField_eq_mfderiv_apply`), the second is the identity
`dρ₁ (C.cplx Z) = i • dρ₁ Z` on the directions `Z = C.lieMap ξ`. The library's Fubini–Study form
is invariant under the elements that act by unitary matrices, and `J` under every element
(`TauCeti.isPseudoholomorphic_const_smul`, which applies by Tau Ceti's
`Projectivization.instContMDiffConstSMul`).

## Main results

* `SymplecticGeometry.mpullback_smul_fubiniStudyForm`: the pull-back of the Fubini–Study form
  `SymplecticGeometry.fubiniStudyForm n` along `[v] ↦ [g • v]`, for `g` acting on `ℂⁿ⁺¹` by a
  unitary matrix, is the Fubini–Study form. This is
  `SymplecticGeometry.mpullback_unitary_fubiniStudyForm`, since `g • ·` is Tau Ceti's
  `Projectivization.mapDiffeomorph` of that matrix.
* `SymplecticGeometry.isComplexifiedAction_projectivization`: the complexified action. The
  fundamental vector field of `ζ` at `[y]` is the image of `X_ζ y` under the differential of the
  projection `Projectivization.mkNonzero` (`Projectivization.fundamentalVectorField_mk`), and
  that differential carries multiplication by `i` to `J`
  (`Projectivization.mfderiv_mkNonzero_I_smul`), as in the proof of
  `SymplecticGeometry.isComplexifiedAction_circle`.
* `SymplecticGeometry.projectivizationMoment I φ`: for `G` acting on `ℂⁿ⁺¹` through a
  homomorphism `φ` into the matrix unitary Lie group `unitarySubgroup (GL (Fin (n + 1)) ℂ)`, the
  map `x ↦ μ x ∘ dφ`, where `μ = SymplecticGeometry.unitaryProjectivizationMoment n` is half of
  Tau Ceti's `TauCeti.ComplexProjectiveSpace.unitaryMomentMap` read on `ℙ ℂ (Fin (n + 1) → ℂ)`,
  and `dφ` is the differential of `φ` at the identity. For a representation
  `ρ : Gc →* GL(n + 1, ℂ)` that is unitary on `G`, `φ` is `ρ ∘ C.toHom` with its values
  restricted to the unitary group. In homogeneous coordinates its component along `ξ` at `[v]` is
  `Im ⟪v, dφ ξ v⟫ / (2 ‖v‖²)` (`SymplecticGeometry.projectivizationMoment_mk_apply`).
* `SymplecticGeometry.isEquivariantMomentMap_neg_projectivizationMoment`: if `φ` is
  differentiable at the identity, `x ↦ -projectivizationMoment I φ x` is a coadjoint-equivariant
  moment map for `fubiniStudyForm n`, so `projectivizationMoment I φ` is a moment map with the
  sign convention of the stability theory. It is not derived again: it is the restriction of
  `SymplecticGeometry.isEquivariantMomentMap_neg_unitaryProjectivizationMoment` along `φ`, by
  Tau Ceti's `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.comp_monoidHom`.
* `SymplecticGeometry.coe_apply_expI_smul`: for a smooth representation `ρ : Gc → GL(n + 1, ℂ)`
  that restricts to `φ` on `G` and whose derivative `dρ` at `1` is complex, `ρ (C.expI (t • ξ))`
  is the matrix exponential of `t • (i • X)`, with `X` the skew-Hermitian matrix of `dφ ξ`, as in
  `projectivizationMoment_mk_apply`. The exponential `C.expI` goes to the exponential of
  `GL(n + 1, ℂ)` at `dρ` (`ContMDiffMonoidMorphism.coe_map_mulInvariantExp`), the identity
  `dρ (C.cplx Z) = i • dρ Z` takes out the factor `i`, and `dρ (C.lieMap ξ) = X` by the chain
  rule (`SymplecticGeometry.mfderiv_coe_apply_lieMap`), since `φ` is smooth into the unitary
  group (`TauCeti.Lie.contMDiff_unitarySubgroup_iff`), with derivative read as a matrix by
  `TauCeti.Lie.mfderiv_coe_eq_matrixUnitaryLieAlgebraEquiv`.
* `SymplecticGeometry.fundamentalVectorField_eq_mulVec_re_add_I_smul_mulVec_im`: for a
  complexified action of `Gc` on `ℂⁿ⁺¹` extending that of `G` through `φ`, the generator of
  `Z` at `w` is `A w + i B w`, with `A` and `B` the skew-Hermitian matrices of `dφ (C.re Z)`
  and `dφ (C.im Z)`
  (`SymplecticGeometry.IsComplexifiedAction.fundamentalVectorField_eq_re_add_im`).
* `SymplecticGeometry.kempfNessFunction_projectivization_mk`: for the complexified action of
  `Gc` on `ℂⁿ⁺¹` and `φ` differentiable at `1` with `g • v = φ g • v`, the Kempf–Ness function
  of `[v]` for `projectivizationMoment I φ` is `g ↦ (log ‖g⁻¹ • v‖² - log ‖v‖²) / 4`. By
  `SymplecticGeometry.eq_kempfNessFunction_of_mfderiv_eq`, for the metric `σ(·, J ·)` of the
  compatible pair (`SymplecticGeometry.compatible_fubiniStudyForm` and Tau Ceti's
  `TauCeti.SmoothTwoForm.Compatible.inner_eq_eval₂`), it is enough to compare differentials.
  That of the right side is `SymplecticGeometry.mfderiv_log_norm_sq_inv_smul_apply`. In the
  generator `A w + i B w` of `Z`, `re ⟪w, A w⟫ = 0` (Tau Ceti's
  `Matrix.re_inner_toEuclideanCLM_self_eq_zero_of_conjTranspose_eq_neg`), so only `Im ⟪w, B w⟫`
  is left, which `SymplecticGeometry.projectivizationMoment_mk_apply` reads as the moment of
  `[w]` along `C.im Z`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §5.7.
* [V. Georgoulas, J. W. Robbin, D. A. Salamon, *The moment-weight inequality and the
  Hilbert–Mumford criterion*][GeorgoulasRobbinSalamon2021], Theorem 12.4.
* [A. Cannas da Silva, *Lectures on Symplectic Geometry*][CannasdaSilva2001Lectures], Section 27.1
  (the unitary action on complex projective space and its moment map).
-/

public section

open Matrix TauCeti Projectivization SmoothAlmostComplexStructure
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace SymplecticGeometry

variable {n : ℕ}

/-- **Unitary symmetries of the Fubini–Study form.** If `g` acts on `ℂⁿ⁺¹` by the unitary matrix
`U`, the pull-back of the Fubini–Study form along `[v] ↦ [g • v]` is the Fubini–Study form. -/
theorem mpullback_smul_fubiniStudyForm {K : Type*} [Group K]
    [DistribMulAction K (Fin (n + 1) → ℂ)] [SMulCommClass K ℂ (Fin (n + 1) → ℂ)] (g : K)
    (U : unitaryGroup (Fin (n + 1)) ℂ)
    (hU : ∀ v : Fin (n + 1) → ℂ, g • v = (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ v) :
    SmoothForm.mpullback (fun x : ℙ ℂ (Fin (n + 1) → ℂ) ↦ g • x) (contMDiff_const_smul g)
      (fubiniStudyForm n) = fubiniStudyForm n := by
  have h : (fun x : ℙ ℂ (Fin (n + 1) → ℂ) ↦ g • x) =
      ⇑(mapDiffeomorph (UnitaryGroup.toLinearEquiv U) ∞) := by
    funext x
    induction x using ind with
    | h v hv => simp [smul_mk, map_mk, UnitaryGroup.toLinearEquiv, hU]
  simp only [h]
  exact mpullback_unitary_fubiniStudyForm U

section Moment

open TauCeti.Lie
open scoped Matrix.Norms.Operator TauCeti.Lie.MatrixUnitary InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- **The moment map of a unitary representation on `ℂPⁿ`.** For a homomorphism
`φ : G →* U(n + 1)` into the matrix unitary Lie group, the line `x` goes to the moment
`SymplecticGeometry.unitaryProjectivizationMoment n x` of the unitary group, read on the Lie
algebra of `G` through the differential `dφ` of `φ` at the identity. Its negative is a group-level
moment map for `fubiniStudyForm n` when `G` acts on `ℂⁿ⁺¹` through `φ`
(`SymplecticGeometry.isEquivariantMomentMap_neg_projectivizationMoment`). -/
noncomputable def projectivizationMoment (φ : G →* unitarySubgroup (GL (Fin (n + 1)) ℂ))
    (x : ℙ ℂ (Fin (n + 1) → ℂ)) : Module.Dual ℝ (GroupLieAlgebra I G) :=
  (unitaryProjectivizationMoment n x).comp
    (φ.groupLieAlgebraMap I 𝓘(ℝ, 𝔨[Fin (n + 1)])).toLinearMap

theorem projectivizationMoment_def (φ : G →* unitarySubgroup (GL (Fin (n + 1)) ℂ))
    (x : ℙ ℂ (Fin (n + 1) → ℂ)) :
    projectivizationMoment I φ x =
      (unitaryProjectivizationMoment n x).comp
        (φ.groupLieAlgebraMap I 𝓘(ℝ, 𝔨[Fin (n + 1)])).toLinearMap :=
  (rfl)

/-- The component of `projectivizationMoment I φ x` along `ξ` is that of the moment of the unitary
group along `dφ ξ`. -/
theorem projectivizationMoment_apply (φ : G →* unitarySubgroup (GL (Fin (n + 1)) ℂ))
    (x : ℙ ℂ (Fin (n + 1) → ℂ)) (ξ : GroupLieAlgebra I G) :
    projectivizationMoment I φ x ξ =
      unitaryProjectivizationMoment n x (φ.groupLieAlgebraMap I 𝓘(ℝ, 𝔨[Fin (n + 1)]) ξ) :=
  (rfl)

/-- **The moment map in homogeneous coordinates.** For a nonzero vector `v` of `ℂⁿ⁺¹`, the
component of `projectivizationMoment I φ [v]` along `ξ` is `Im ⟪v, X v⟫ / (2 ‖v‖²)`, for the
Hermitian inner product and norm of `EuclideanSpace ℂ (Fin (n + 1))`, where `X` is the
skew-Hermitian matrix of `dφ ξ` (through `matrixUnitaryLieAlgebraEquiv`). -/
theorem projectivizationMoment_mk_apply (φ : G →* unitarySubgroup (GL (Fin (n + 1)) ℂ))
    (ξ : GroupLieAlgebra I G) {v : Fin (n + 1) → ℂ} (hv : v ≠ 0) :
    projectivizationMoment I φ (mk ℂ v hv) ξ =
      (⟪WithLp.toLp 2 v, WithLp.toLp 2
        ((matrixUnitaryLieAlgebraEquiv (φ.groupLieAlgebraMap I 𝓘(ℝ, 𝔨[Fin (n + 1)]) ξ) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ v)⟫_ℂ).im / (2 * ‖WithLp.toLp 2 v‖ ^ 2) := by
  rw [projectivizationMoment_apply, unitaryProjectivizationMoment_mk_apply]

variable {I} [CompleteSpace E] [LieGroup I ∞ G]
  [DistribMulAction G (Fin (n + 1) → ℂ)] [SMulCommClass G ℂ (Fin (n + 1) → ℂ)]
  [ContMDiffSMul I 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ G (Fin (n + 1) → ℂ)]

/-- **The moment map of a unitary representation on `ℂPⁿ`.** Let `G` act on `ℂⁿ⁺¹` smoothly
through a homomorphism `φ : G →* U(n + 1)` that is differentiable at the identity. Then
`x ↦ -projectivizationMoment I φ x` is a coadjoint-equivariant moment map for the induced action on
`ℂPⁿ` and the Fubini–Study form `fubiniStudyForm n`. -/
theorem isEquivariantMomentMap_neg_projectivizationMoment
    (φ : G →* unitarySubgroup (GL (Fin (n + 1)) ℂ))
    (hφ : MDifferentiableAt I 𝓘(ℝ, 𝔨[Fin (n + 1)]) (⇑φ) 1)
    (hsmul : ∀ (g : G) (v : Fin (n + 1) → ℂ), g • v = φ g • v) :
    (fubiniStudyForm n).IsEquivariantMomentMap fun x ↦ -projectivizationMoment I φ x := by
  have h := (isEquivariantMomentMap_neg_unitaryProjectivizationMoment n).comp_monoidHom φ hφ
    fun g x ↦ by
      induction x using ind with
      | h v hv => simp only [Subgroup.smul_def, smul_mk, hsmul]
  simpa only [projectivizationMoment_def, LinearMap.neg_comp] using h

end Moment

section Exponential

open TauCeti.Lie
open scoped Matrix.Norms.Operator TauCeti.Lie.MatrixUnitary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC}
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc] [BoundarylessManifold IC Gc]

/-- **The derivative of a representation on the compact directions.** Let
`ρ : Gc → GL(n + 1, ℂ)` be a smooth homomorphism whose restriction to `G` along `C.toHom` is
`φ : G →* U(n + 1)`. For `ξ` in the Lie algebra of `G`, the derivative at `1` of
`g ↦ (ρ g : Matrix _ _ ℂ)` at `C.lieMap ξ` is the skew-Hermitian matrix of `dφ ξ`
(through `matrixUnitaryLieAlgebraEquiv`). -/
theorem mfderiv_coe_apply_lieMap (C : LieComplexification I G IC Gc)
    (ρ : ContMDiffMonoidMorphism IC 𝓘(ℝ, Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) ∞ Gc
      (GL (Fin (n + 1)) ℂ))
    (φ : G →* unitarySubgroup (GL (Fin (n + 1)) ℂ))
    (hφ : ∀ g, (φ g : GL (Fin (n + 1)) ℂ) = ρ (C.toHom g)) (ξ : GroupLieAlgebra I G) :
    mfderiv IC 𝓘(ℝ, Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (fun g ↦ (ρ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) 1 (C.lieMap ξ) =
      (matrixUnitaryLieAlgebraEquiv (φ.groupLieAlgebraMap I 𝓘(ℝ, 𝔨[Fin (n + 1)]) ξ) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  have hφd : MDifferentiableAt I 𝓘(ℝ, 𝔨[Fin (n + 1)]) φ 1 :=
    (contMDiff_unitarySubgroup_iff.2 <| (ρ.contMDiff_toFun.comp C.toHom.contMDiff_toFun).congr
      fun g ↦ by simp [hφ]).mdifferentiableAt (by simp)
  have htoHom : MDifferentiableAt I IC C.toHom 1 :=
    C.toHom.contMDiff_toFun.mdifferentiableAt (by simp)
  have hcomp : (fun g ↦ (ρ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) ∘ C.toHom =
      fun g ↦ ((φ g : GL (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :=
    funext fun g ↦ by simp [hφ]
  rw [C.lieMap_apply, ← mfderiv_comp_apply_of_eq 1 ρ.mdifferentiableAt_coe_one htoHom
    (map_one C.toHom) ξ, hcomp, mfderiv_coe_eq_matrixUnitaryLieAlgebraEquiv φ hφd]

variable [FiniteDimensional ℝ E]

/-- **A complexified representation along `C.expI` is a matrix exponential.** Let
`ρ : Gc → GL(n + 1, ℂ)` be a smooth homomorphism whose restriction to `G` along `C.toHom` is
`φ : G →* U(n + 1)`, and whose derivative `dρ` at `1`, the derivative of `g ↦ (ρ g : Matrix _ _ ℂ)`,
is complex: `dρ (C.cplx Z) = i • dρ Z`. Then for `ξ` in the Lie algebra of `G` and `t : ℝ`,
`ρ (C.expI (t • ξ))` is the exponential of `t • (i • X)`, where `X` is the skew-Hermitian matrix of
`dφ ξ` (through `matrixUnitaryLieAlgebraEquiv`); so it is the exponential of `-t` times the
Hermitian matrix `-i • X`. -/
theorem coe_apply_expI_smul (C : LieComplexification I G IC Gc)
    (ρ : ContMDiffMonoidMorphism IC 𝓘(ℝ, Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) ∞ Gc
      (GL (Fin (n + 1)) ℂ))
    (φ : G →* unitarySubgroup (GL (Fin (n + 1)) ℂ))
    (hφ : ∀ g, (φ g : GL (Fin (n + 1)) ℂ) = ρ (C.toHom g))
    (hρ : ∀ Z : GroupLieAlgebra IC Gc,
      mfderiv IC 𝓘(ℝ, Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
          (fun g ↦ (ρ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) 1 (C.cplx Z) =
        Complex.I • (show Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ from
          mfderiv IC 𝓘(ℝ, Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
            (fun g ↦ (ρ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) 1 Z))
    (ξ : GroupLieAlgebra I G) (t : ℝ) :
    ((ρ (C.expI (t • ξ)) : GL (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      NormedSpace.exp (t • (Complex.I •
        (matrixUnitaryLieAlgebraEquiv (φ.groupLieAlgebraMap I 𝓘(ℝ, 𝔨[Fin (n + 1)]) ξ) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))) := by
  have := C.finiteDimensional
  rw [C.expI_smul, ρ.coe_map_mulInvariantExp, map_smul, hρ, mfderiv_coe_apply_lieMap C ρ φ hφ]
  -- The two sides differ only by the `show` of `hρ`, which reads a tangent vector of
  -- `GL (Fin (n + 1)) ℂ` as a matrix.
  rfl

end Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC}
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc] [BoundarylessManifold IC Gc]
  [DistribMulAction G (Fin (n + 1) → ℂ)] [SMulCommClass G ℂ (Fin (n + 1) → ℂ)]
  [DistribMulAction Gc (Fin (n + 1) → ℂ)] [SMulCommClass Gc ℂ (Fin (n + 1) → ℂ)]
  [ContMDiffSMul IC 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ Gc (Fin (n + 1) → ℂ)]

/-- **Linear complexified actions on `ℂPⁿ`.** Let `G` and `Gc` act `ℂ`-linearly on `ℂⁿ⁺¹`, the
action of `Gc` smoothly. If the action of `Gc` on `ℂⁿ⁺¹` is a complexified action of that of `G`
for multiplication by `i`, then so is the induced action of `Gc` on `ℂPⁿ`, for the complex
structure of `ℂPⁿ`. -/
theorem isComplexifiedAction_projectivization {C : LieComplexification I G IC Gc}
    (h : IsComplexifiedAction C (ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ))) :
    IsComplexifiedAction C (ofComplexManifold (Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ))) where
  toHom_smul u x := by
    induction x using ind with
    | h v hv => simp only [smul_mk, h.toHom_smul]
  fundamentalVectorField_cplx ξ x := by
    induction x using ind with
    | h y hy =>
      have hX := fun Z ↦ fundamentalVectorField_mk (I := IC) Z hy
        ((ContMDiffSMul.contMDiff_smul_const (I := IC) (I' := 𝓘(ℝ, Fin (n + 1) → ℂ)) (n := 1)
          (G := Gc) y).mdifferentiableAt one_ne_zero)
      rw [hX, hX, h.fundamentalVectorField_cplx]
      exact (congrArg _ (ofComplexManifold_apply _ _)).trans
        ((mfderiv_mkNonzero_I_smul _ _).trans (by rw [mkNonzero_apply]))

section Generator

open TauCeti.Lie
open scoped Matrix.Norms.Operator TauCeti.Lie.MatrixUnitary

variable [FiniteDimensional ℝ E]

omit [SMulCommClass G ℂ (Fin (n + 1) → ℂ)] [SMulCommClass Gc ℂ (Fin (n + 1) → ℂ)] in
/-- **Generators of a complexified unitary representation.** In the setting of
`isComplexifiedAction_projectivization`, let `G` act on `ℂⁿ⁺¹` through a homomorphism
`φ : G →* U(n + 1)` that is differentiable at the identity. Then the fundamental vector field of
`Z` in the Lie algebra of `Gc` takes at `w` the value `A w + i B w`, where `A` and `B` are the
skew-Hermitian matrices of `dφ (C.re Z)` and `dφ (C.im Z)` (through
`matrixUnitaryLieAlgebraEquiv`). -/
theorem fundamentalVectorField_eq_mulVec_re_add_I_smul_mulVec_im
    {C : LieComplexification I G IC Gc}
    (h : IsComplexifiedAction C (ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)))
    (φ : G →* unitarySubgroup (GL (Fin (n + 1)) ℂ))
    (hφ : MDifferentiableAt I 𝓘(ℝ, 𝔨[Fin (n + 1)]) (⇑φ) 1)
    (hsmul : ∀ (g : G) (v : Fin (n + 1) → ℂ), g • v = φ g • v)
    (Z : GroupLieAlgebra IC Gc) (w : Fin (n + 1) → ℂ) :
    (fundamentalVectorField 𝓘(ℝ, Fin (n + 1) → ℂ) Z w : Fin (n + 1) → ℂ) =
      (matrixUnitaryLieAlgebraEquiv (φ.groupLieAlgebraMap I 𝓘(ℝ, 𝔨[Fin (n + 1)]) (C.re Z)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ w + Complex.I •
        (matrixUnitaryLieAlgebraEquiv (φ.groupLieAlgebraMap I 𝓘(ℝ, 𝔨[Fin (n + 1)]) (C.im Z)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ w := by
  have := h.contMDiffSMul
  have hX (ξ : GroupLieAlgebra I G) : fundamentalVectorField 𝓘(ℝ, Fin (n + 1) → ℂ) ξ w =
      (matrixUnitaryLieAlgebraEquiv (φ.groupLieAlgebraMap I 𝓘(ℝ, 𝔨[Fin (n + 1)]) ξ) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ w := by
    rw [← fundamentalVectorField_unitarySubgroup,
      φ.fundamentalVectorField_groupLieAlgebraMap hφ hsmul]
  rw [h.fundamentalVectorField_eq_re_add_im]
  exact congrArg₂ (· + ·) (hX _) ((ofComplexManifold_apply _ _).trans (congrArg _ (hX _)))

end Generator

section KempfNessFunction

open TauCeti.Lie
open scoped Matrix.Norms.Operator TauCeti.Lie.MatrixUnitary InnerProductSpace

variable [FiniteDimensional ℝ E] [ConnectedSpace G]

/-- **The Kempf–Ness function on `ℂPⁿ`.** In the setting of
`isComplexifiedAction_projectivization`, let `G` act on `ℂⁿ⁺¹` through a homomorphism
`φ : G →* U(n + 1)` that is differentiable at the identity. For `v ≠ 0`, the Kempf–Ness function
of `[v]` for the moment map `projectivizationMoment I φ` is
`g ↦ (log ‖g⁻¹ • v‖² - log ‖v‖²) / 4`, for the Hermitian norm of
`EuclideanSpace ℂ (Fin (n + 1))`. -/
theorem kempfNessFunction_projectivization_mk {C : LieComplexification I G IC Gc}
    (h : IsComplexifiedAction C (ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)))
    (φ : G →* unitarySubgroup (GL (Fin (n + 1)) ℂ))
    (hφ : MDifferentiableAt I 𝓘(ℝ, 𝔨[Fin (n + 1)]) (⇑φ) 1)
    (hsmul : ∀ (g : G) (v : Fin (n + 1) → ℂ), g • v = φ g • v)
    {v : Fin (n + 1) → ℂ} (hv : v ≠ 0) (g : Gc) :
    kempfNessFunction C (projectivizationMoment I φ) (mk ℂ v hv) g =
      1 / 4 * (Real.log (‖WithLp.toLp 2 (g⁻¹ • v)‖ ^ 2) - Real.log (‖WithLp.toLp 2 v‖ ^ 2)) := by
  have := h.contMDiffSMul
  let : Bundle.RiemannianBundle fun x : ℙ ℂ (Fin (n + 1) → ℂ) ↦ TangentSpace 𝓘(ℝ, Fin n → ℂ) x :=
    ⟨compatible_fubiniStudyForm.metric.toRiemannianMetric⟩
  let T : (Fin (n + 1) → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin (n + 1)) :=
    ((PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin (n + 1) ↦ ℂ).symm :
      (Fin (n + 1) → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin (n + 1)))
  have hT (w : Fin (n + 1) → ℂ) : T w = WithLp.toLp 2 w := rfl
  have hTi : Function.Injective T := (PiLp.continuousLinearEquiv 2 ℝ _).symm.injective
  have hf := eq_kempfNessFunction_of_mfderiv_eq C (projectivizationMoment I φ) (mk ℂ v hv)
    (isComplexifiedAction_projectivization h)
    (isEquivariantMomentMap_neg_projectivizationMoment φ hφ hsmul)
    compatible_fubiniStudyForm.inner_eq_eval₂
    (f := fun g ↦ 1 / 4 * (Real.log (‖T (g⁻¹ • v)‖ ^ 2) - Real.log (‖T v‖ ^ 2)))
    ?_ ?_ (by simp)
  · simpa [hT] using (congrFun hf g).symm
  · exact (contMDiff_const.mul ((contMDiff_log_norm_sq_inv_smul (n := ∞) ℂ hTi hv).sub
      contMDiff_const)).mdifferentiable (by simp)
  · intro x ĝ
    have hL := (contMDiff_log_norm_sq_inv_smul (I := IC) ℂ hTi hv (n := ∞)).mdifferentiableAt
      (x := x) (by simp)
    have hA : HasFDerivAt (fun t : ℝ ↦ 1 / 4 * (t - Real.log (‖T v‖ ^ 2)))
        ((1 / 4 : ℝ) • ContinuousLinearMap.id ℝ ℝ) (Real.log (‖T (x⁻¹ • v)‖ ^ 2)) :=
      ((hasFDerivAt_id _).sub_const _).const_mul _
    rw [show (fun g : Gc ↦ 1 / 4 * (Real.log (‖T (g⁻¹ • v)‖ ^ 2) - Real.log (‖T v‖ ^ 2))) =
        (fun t : ℝ ↦ 1 / 4 * (t - Real.log (‖T v‖ ^ 2))) ∘
          fun g : Gc ↦ Real.log (‖T (g⁻¹ • v)‖ ^ 2) from rfl,
      mfderiv_comp_apply x hA.differentiableAt.mdifferentiableAt hL, mfderiv_eq_fderiv,
      hA.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      NormedSpace.fromTangentSpace_symm_apply, NormedSpace.fromTangentSpace_apply,
      FunLike.coe_smul, ContinuousLinearMap.coe_id']
    rw [mfderiv_log_norm_sq_inv_smul_apply (𝕜 := ℂ) hTi hv x ĝ, smul_mk,
      projectivizationMoment_mk_apply]
    generalize x⁻¹ • v = w
    suffices key : ∀ Z : GroupLieAlgebra IC Gc,
        1 / 4 * (-2 * RCLike.re
          ⟪T w, T (fundamentalVectorField 𝓘(ℝ, Fin (n + 1) → ℂ) Z w)⟫_ℂ / ‖T w‖ ^ 2) =
        (⟪WithLp.toLp 2 w, WithLp.toLp 2
          ((matrixUnitaryLieAlgebraEquiv (φ.groupLieAlgebraMap I 𝓘(ℝ, 𝔨[Fin (n + 1)]) (C.im Z)) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ w)⟫_ℂ).im / (2 * ‖WithLp.toLp 2 w‖ ^ 2) from
      key _
    intro Z
    -- The skew-Hermitian matrix of `dφ (C.re Z)` contributes nothing to the real part.
    have hre : (⟪WithLp.toLp 2 w, WithLp.toLp 2
        ((matrixUnitaryLieAlgebraEquiv (φ.groupLieAlgebraMap I 𝓘(ℝ, 𝔨[Fin (n + 1)]) (C.re Z)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ w)⟫_ℂ).re = 0 := by
      simpa using re_inner_toEuclideanCLM_self_eq_zero_of_conjTranspose_eq_neg
        (conjTranspose_coe_unitaryLieAlgebra _) (WithLp.toLp 2 w)
    rw [fundamentalVectorField_eq_mulVec_re_add_I_smul_mulVec_im h φ hφ hsmul]
    simp only [hT, WithLp.toLp_add, WithLp.toLp_smul, inner_add_right, inner_smul_right,
      RCLike.re_to_complex, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      hre]
    field_simp
    ring

end KempfNessFunction

end SymplecticGeometry

end
