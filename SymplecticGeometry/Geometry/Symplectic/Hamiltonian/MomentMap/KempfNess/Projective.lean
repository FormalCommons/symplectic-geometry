/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.Basic
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Action
public import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Kahler
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.ComplexProjectiveSpace
import SymplecticGeometry.Geometry.Manifold.Projectivization.Pseudoholomorphic
import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Restrict
import SymplecticGeometry.Geometry.Lie.Exponential.Units
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.HilbertMumford
import SymplecticGeometry.Analysis.Matrix.HermitianExp
import SymplecticGeometry.Analysis.Matrix.Spectrum
import TauCeti.LinearAlgebra.Eigenspace.Anticommute
import SymplecticGeometry.Geometry.Lie.GroupLieAlgebraLieHom

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
* `SymplecticGeometry.projectivizationMoment_mk_apply_eq_rayleighQuotient`: the same component is
  `-1/2` times the Rayleigh quotient at `v` of the Hermitian matrix `i • X`.
* `SymplecticGeometry.momentWeight_projectivizationMoment_mk`: if `Gc` acts on `ℂⁿ⁺¹` through
  `ρ`, the moment weight of `[v]` along `ξ` is `-a / 2`, where `a` is the largest eigenvalue of
  `A = i • X` on which `v` has a nonzero coordinate. The curve `C.expI (t • ξ) • v` is
  `exp (t • A) v` by `coe_apply_expI_smul`, the Rayleigh quotient of `A` along it tends to `a`
  (`Matrix.IsHermitian.tendsto_rayleighQuotient_toEuclideanLin_exp_smul_sup'`), and the moment
  weight is a `limUnder`, so `Filter.Tendsto.limUnder_eq` gives it.
* `SymplecticGeometry.tendsto_smul_zero_of_momentWeight_pos`: if the moment weight of `[v]` along
  `ξ` is positive, then `v` lies in the sum of the eigenspaces of `-i • X` for positive
  eigenvalues, and `ρ (C.expI (t • ξ)) v` tends to `0` with antitone norm as `t → ∞`. By the
  previous item every eigenvalue of `A` on which `v` has a nonzero coordinate is negative, and
  `Matrix.IsHermitian.antitone_norm_toEuclideanLin_exp_smul`,
  `Matrix.IsHermitian.tendsto_toEuclideanLin_exp_smul_zero`,
  `Matrix.IsHermitian.mem_iSup_eigenspace`
  and Tau Ceti's `Module.End.genEigenspace_neg` conclude. The sign is always the same: the decay
  is along `ξ` itself.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §5.7.
* [V. Georgoulas, J. W. Robbin, D. A. Salamon, *The moment-weight inequality and the
  Hilbert–Mumford criterion*][GeorgoulasRobbinSalamon2021], Lemma 8.4 and Theorem 12.4.
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

/-- **The moment map as a Rayleigh quotient.** For a nonzero vector `v` of `ℂⁿ⁺¹`, the component
of `projectivizationMoment I φ [v]` along `ξ` is `-1/2` times the Rayleigh quotient at `v` of
`i • X`, for the Hermitian inner product of `EuclideanSpace ℂ (Fin (n + 1))`, where `X` is the
skew-Hermitian matrix of `dφ ξ` (through `matrixUnitaryLieAlgebraEquiv`). -/
theorem projectivizationMoment_mk_apply_eq_rayleighQuotient
    (φ : G →* unitarySubgroup (GL (Fin (n + 1)) ℂ)) (ξ : GroupLieAlgebra I G)
    {v : Fin (n + 1) → ℂ} (hv : v ≠ 0) :
    projectivizationMoment I φ (mk ℂ v hv) ξ =
      -(1 / 2) * (toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℂ) (Complex.I •
        (matrixUnitaryLieAlgebraEquiv (φ.groupLieAlgebraMap I 𝓘(ℝ, 𝔨[Fin (n + 1)]) ξ) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))).rayleighQuotient (WithLp.toLp 2 v) := by
  rw [projectivizationMoment_mk_apply, ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, toEuclideanCLM_apply, map_smul,
    LinearMap.smul_apply, toLpLin_toLp, toLin'_apply, inner_smul_left, ← inner_conj_symm]
  simp only [Complex.conj_I, RCLike.re_to_complex, Complex.mul_re, Complex.neg_re,
    Complex.I_re, Complex.neg_im, Complex.I_im, Complex.conj_im]
  ring

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

section Weight

open TauCeti.Lie Filter
open scoped Matrix.Norms.Operator TauCeti.Lie.MatrixUnitary InnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC}
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc] [BoundarylessManifold IC Gc]
  [DistribMulAction Gc (Fin (n + 1) → ℂ)] [SMulCommClass Gc ℂ (Fin (n + 1) → ℂ)]

/-- **The moment weight on `ℂPⁿ`.** In the setting of `coe_apply_expI_smul`, let `Gc` act on
`ℂⁿ⁺¹` through `ρ`, and let `X` be the skew-Hermitian matrix of `dφ ξ`. For a nonzero vector `v`,
the moment weight of `[v]` along `ξ` for `projectivizationMoment I φ` is `-1/2` times the largest
eigenvalue `hA.eigenvalues i` of the Hermitian matrix `i • X` with `v_i ≠ 0`, `v_i` the
coordinates of `v` in the eigenvector basis. -/
theorem momentWeight_projectivizationMoment_mk (C : LieComplexification I G IC Gc)
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
    (hsmul : ∀ (g : Gc) (v : Fin (n + 1) → ℂ),
      g • v = (ρ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ v)
    (ξ : GroupLieAlgebra I G) {v : Fin (n + 1) → ℂ} (hv : v ≠ 0)
    (hA : (Complex.I •
      (matrixUnitaryLieAlgebraEquiv (φ.groupLieAlgebraMap I 𝓘(ℝ, 𝔨[Fin (n + 1)]) ξ) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).IsHermitian)
    (hs : {i | hA.eigenvectorBasis.repr (WithLp.toLp 2 v) i ≠ 0}.toFinset.Nonempty) :
    momentWeight C (projectivizationMoment I φ) (mk ℂ v hv) ξ =
      -(1 / 2) * {i | hA.eigenvectorBasis.repr (WithLp.toLp 2 v) i ≠ 0}.toFinset.sup' hs
        hA.eigenvalues := by
  rw [momentWeight_def]
  refine Tendsto.limUnder_eq <|
    ((hA.tendsto_rayleighQuotient_toEuclideanLin_exp_smul_sup' hs).const_mul (-(1 / 2))).congr
      fun t ↦ ?_
  rw [smul_mk, projectivizationMoment_mk_apply_eq_rayleighQuotient, hsmul,
    coe_apply_expI_smul C ρ φ hφ hρ ξ t, toLpLin_toLp, toLin'_apply]
  -- The sides agree only up to unfolding: the limit of the Rayleigh quotient is stated over a
  -- general `RCLike` field.
  congr 1

/-- **A positive moment weight on `ℂPⁿ`.** In the setting of `coe_apply_expI_smul`, let `Gc`
act on `ℂⁿ⁺¹` through `ρ`, and let `X` be the skew-Hermitian matrix of `dφ ξ`, so that
`ρ (C.expI (t • ξ))` is the exponential of `-t` times the Hermitian matrix `-i • X`. If the
moment weight of `[v]` along `ξ` for `projectivizationMoment I φ` is positive, then `v` lies in
the sum of the eigenspaces of `-i • X` for positive eigenvalues, and `ρ (C.expI (t • ξ)) v`
is antitone in the Hermitian norm and tends to `0` as `t → ∞`. -/
theorem tendsto_smul_zero_of_momentWeight_pos (C : LieComplexification I G IC Gc)
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
    (hsmul : ∀ (g : Gc) (v : Fin (n + 1) → ℂ),
      g • v = (ρ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ v)
    (ξ : GroupLieAlgebra I G) {v : Fin (n + 1) → ℂ} (hv : v ≠ 0)
    (hpos : 0 < momentWeight C (projectivizationMoment I φ) (mk ℂ v hv) ξ) :
    WithLp.toLp 2 v ∈ ⨆ μ ∈ Set.Ioi (0 : ℝ), Module.End.eigenspace (toEuclideanLin (-Complex.I •
        (matrixUnitaryLieAlgebraEquiv (φ.groupLieAlgebraMap I 𝓘(ℝ, 𝔨[Fin (n + 1)]) ξ) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))) (μ : ℂ) ∧
      Antitone (fun t : ℝ ↦ ‖WithLp.toLp 2
        ((ρ (C.expI (t • ξ)) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ v)‖) ∧
      Tendsto (fun t : ℝ ↦ (ρ (C.expI (t • ξ)) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ v)
        atTop (𝓝 0) := by
  set Y := matrixUnitaryLieAlgebraEquiv (φ.groupLieAlgebraMap I 𝓘(ℝ, 𝔨[Fin (n + 1)]) ξ)
  set X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
  have hB : (-Complex.I • X).IsHermitian := by
    rw [← coe_unitaryLieAlgebraEquivSelfAdjoint_apply]
    exact (unitaryLieAlgebraEquivSelfAdjoint _ Y).property.isHermitian
  have hA : (Complex.I • X).IsHermitian := by simpa only [neg_smul, _root_.neg_neg] using hB.neg
  set x := WithLp.toLp 2 v
  have hs : {i | hA.eigenvectorBasis.repr x i ≠ 0}.toFinset.Nonempty := by
    by_contra h
    refine hv ?_
    have hx : x = 0 := by
      rw [← hA.eigenvectorBasis.repr.map_eq_zero_iff]
      ext i
      by_contra hi
      exact h ⟨i, by simpa using hi⟩
    simpa [x] using hx
  rw [momentWeight_projectivizationMoment_mk C ρ φ hφ hρ hsmul ξ hv hA hs] at hpos
  have hlt (i) (hi : hA.eigenvectorBasis.repr x i ≠ 0) : hA.eigenvalues i < 0 :=
    (Finset.le_sup' (s := {i | hA.eigenvectorBasis.repr x i ≠ 0}.toFinset) hA.eigenvalues
      (by simpa using hi)).trans_lt (by linarith)
  have hcurve (t : ℝ) : WithLp.toLp 2
      ((ρ (C.expI (t • ξ)) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ v) =
      toEuclideanLin (NormedSpace.exp (t • (Complex.I • X))) x := by
    rw [coe_apply_expI_smul C ρ φ hφ hρ ξ t, toLpLin_toLp, toLin'_apply]
  refine ⟨?_, fun s t hst ↦ ?_, ?_⟩
  · -- The eigenspaces of `-(i • X)` are those of `i • X` at the negated eigenvalues.
    refine IsConcreteLE.le_iff.mp (iSup₂_le fun μ (hμ : μ ∈ Set.Iio 0) ↦ ?_)
      (hA.mem_iSup_eigenspace (S := Set.Iio 0) hlt)
    rw [neg_smul, map_neg]
    refine le_iSup₂_of_le (-μ) (Set.mem_Ioi.mpr (neg_pos.mpr hμ)) ?_
    exact (Module.End.genEigenspace_neg _ _ 1).ge.trans_eq'
      (by simp)
  · dsimp only
    rw [hcurve, hcurve]
    exact hA.antitone_norm_toEuclideanLin_exp_smul (fun i hi ↦ (hlt i hi).le) hst
  · refine Tendsto.congr (fun t ↦ ?_) (((PiLp.continuous_ofLp 2 _).tendsto _).comp
      (hA.tendsto_toEuclideanLin_exp_smul_zero hlt))
    exact congrArg WithLp.ofLp (hcurve t).symm

end Weight

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

end SymplecticGeometry

end
