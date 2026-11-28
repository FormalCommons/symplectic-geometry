/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import SymplecticGeometry.Geometry.Diffeomorphism.Sphere.Mobius
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.StructureGroup
public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Topology.FiberBundle.Trivialization
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Geometry.Diffeomorphism.LieGroup
import TauCeti.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.Instances.AddCircle.Circle
import TauCeti.Geometry.Manifold.Instances.OnePoint.Moebius
import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# The product atlas and the rotations of the sphere

For topological spaces `B` and `F`, the first projection `Prod.fst : B × F → B` is trivialized
over all of `B` by the identity of `B × F`. The atlas `TauCeti.MapFiber.Atlas.productAtlas B F`
takes this trivialization as its chart at every point of `B`. It is the atlas of the trivial
bundle with fibre `F` over `B`, against which the other bundles over `B` are compared: a bundle
is trivial when it is isomorphic to `Prod.fst` with this atlas.

For manifolds `B` and `F` the atlas is `C^n` for every `n`, and since every coordinate change is
the identity of `F`, it has structure group `H` for every subgroup `H` of the `C^n`
diffeomorphisms of `F`.

The unit circle acts on the Riemann sphere `OnePoint ℂ` by the rotations `u • z = u⁻¹ * z` about
the axis through `0` and `∞`, which it fixes. The map `z ↦ u • z` is the Möbius transformation of
the diagonal matrix `diag(u⁻¹, 1)`. The action is jointly smooth, each rotation lies in the
Möbius group `SymplecticGeometry.mobiusSubgroup`, and so in `SymplecticGeometry.diffPlus`, and
for an integer `n` the rotations by `e^{2πinθ}`, for `θ` in `AddCircle 1`, form the loop
`SymplecticGeometry.rotationLoop n` of orientation preserving diffeomorphisms of the sphere.

## Main definitions

* `TauCeti.MapFiber.Atlas.productAtlas B F`: the atlas of `Prod.fst : B × F → B` whose every chart
  is the identity of `B × F`.
* `OnePoint.circleToGL`: the homomorphism `u ↦ diag(u⁻¹, 1)` from the circle to `GL(2, ℂ)`.
* `OnePoint.circleAction`: the action of `Circle` on `OnePoint ℂ` through `OnePoint.circleToGL`
  and the Möbius action of `GL(2, ℂ)`.
* `SymplecticGeometry.circleMobiusHom`: the rotations as a homomorphism from the circle to the
  Möbius group `mobiusSubgroup`.
* `SymplecticGeometry.rotationLoop n`: the loop `θ ↦ (z ↦ e^{2πinθ} • z)` in `diffPlus`, on
  `AddCircle 1`.

## Main results

* `TauCeti.MapFiber.Atlas.isContMDiff_productAtlas`: the product atlas is `C^n`.
* `TauCeti.MapFiber.Atlas.hasStructureGroup_productAtlas`: the product atlas has structure group
  `H` for every subgroup `H`.
* `OnePoint.circle_smul_coe`, `OnePoint.circle_smul_infty`, `OnePoint.circle_smul_zero`: the
  rotation by `u` multiplies a finite point by `u⁻¹`, and fixes `∞` and `0`.
* `OnePoint.instContMDiffSMulCircle`: the action of the circle on the sphere is jointly `C^n` over
  `ℝ`, for every `n`.
* `SymplecticGeometry.continuous_circleMobiusHom`: the rotations depend continuously on `u`, for
  the weak Whitney topology.
* `SymplecticGeometry.continuous_rotationLoop` and
  `SymplecticGeometry.contMDiff_uncurry_rotationLoop`: the rotation loop is continuous, and
  `(θ, z) ↦ rotationLoop n θ z` is smooth.

## Implementation notes

The chart of the product atlas is Tau Ceti's `Homeomorph.toTrivialization` of
`Homeomorph.refl (B × F)`.

The joint smoothness of the circle action is read off the jointly analytic Möbius action of
`GL(2, ℂ)` (Tau Ceti's `OnePoint.instContMDiffSMul`), with scalars restricted to `ℝ` as in the
library's `OnePoint.instContMDiffSMulPSLReal`, and composed with the smooth map
`OnePoint.circleToGL`. The circle does not map to `PSL(2, ℂ)` through a homomorphism to
`SL(2, ℂ)`, since `u⁻¹` has no continuous square root on the circle, so the general linear
group is used instead. That a rotation is a Möbius transformation of `PSL(2, ℂ)` is Tau Ceti's
`Matrix.GeneralLinearGroup.exists_psl_forall_smul_eq_smul`. Continuity of `circleMobiusHom`
comes from Tau Ceti's `Diffeomorph.smulContinuousMonoidHom`, as for the library's
`SymplecticGeometry.continuous_mobiusHom`.

The rotation loop is parametrized by `AddCircle 1`, the circle of the smoothing of homotopies
that the clutching argument uses, and `AddCircle.toCircle` sends `θ` to `e^{2πiθ}`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.2.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti.MapFiber.Atlas


variable (B F : Type*) [TopologicalSpace B] [TopologicalSpace F]

/-- The *product atlas* of the first projection `Prod.fst : B × F → B`: its chart at every point
of `B` is the identity of `B × F`, a trivialization over all of `B`. -/
def productAtlas : Atlas F (Prod.fst : B × F → B) where
  trivAt _ := (Homeomorph.refl (B × F)).toTrivialization (proj := Prod.fst) fun _ ↦ by simp
  mem_baseSet_trivAt _ := by simp

theorem trivAt_productAtlas (b : B) :
    (productAtlas B F).trivAt b =
      (Homeomorph.refl (B × F)).toTrivialization (proj := Prod.fst) fun _ ↦ by simp :=
  (rfl)

variable {B F}

/-- Every chart of the product atlas is the identity of `B × F`. -/
@[simp]
theorem coe_trivAt_productAtlas (b : B) : ⇑((productAtlas B F).trivAt b) = id := by
  simp [trivAt_productAtlas]

/-- The inverse of every chart of the product atlas is the identity of `B × F`. -/
@[simp]
theorem coe_trivAt_productAtlas_symm (b : B) :
    ⇑((productAtlas B F).trivAt b).toOpenPartialHomeomorph.symm = id := by
  simp [trivAt_productAtlas]

/-- Every chart of the product atlas trivializes `Prod.fst` over all of `B`. -/
@[simp]
theorem baseSet_trivAt_productAtlas (b : B) : ((productAtlas B F).trivAt b).baseSet = univ := by
  simp [trivAt_productAtlas]

/-- Every chart of the product atlas is defined on all of `B × F`. -/
@[simp]
theorem source_trivAt_productAtlas (b : B) : ((productAtlas B F).trivAt b).source = univ := by
  simp [Trivialization.source_eq]

/-- Every chart of the product atlas has all of `B × F` as its image. -/
@[simp]
theorem target_trivAt_productAtlas (b : B) : ((productAtlas B F).trivAt b).target = univ := by
  simp [Trivialization.target_eq]

/-- Every coordinate change of the product atlas is the identity of `F`. -/
@[simp]
theorem coordChange_trivAt_productAtlas (b b' x : B) :
    ((productAtlas B F).trivAt b).coordChange ((productAtlas B F).trivAt b') x = id := by
  rw [trivAt_productAtlas B F b', ← trivAt_productAtlas B F b]
  exact Trivialization.coordChange_same _ (by rw [baseSet_trivAt_productAtlas]; exact mem_univ x)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} [ChartedSpace HF F]

/-- The product atlas of `Prod.fst : B × F → B` is `C^n` for the product manifold structure on
`B × F`: its charts and their inverses are the identity. -/
theorem isContMDiff_productAtlas :
    (productAtlas B F).IsContMDiff n IB IF (IB.prod IF) where
  contMDiffOn_trivAt b := by
    rw [coe_trivAt_productAtlas]
    exact contMDiffOn_id
  contMDiffOn_trivAt_symm b := by
    rw [coe_trivAt_productAtlas_symm]
    exact contMDiffOn_id

/-- The product atlas has structure group `H` for every subgroup `H` of the `C^n` diffeomorphisms
of `F`, since each of its coordinate changes is the identity element. -/
theorem hasStructureGroup_productAtlas (H : Subgroup (F ≃ₘ^n⟮IF, IF⟯ F)) :
    (productAtlas B F).HasStructureGroup H := by
  rw [hasStructureGroup_iff]
  intro b b' x _ _
  exact ⟨1, one_mem H, by rw [coordChange_trivAt_productAtlas, Diffeomorph.coe_one]⟩

end TauCeti.MapFiber.Atlas

namespace OnePoint

open Matrix
open scoped MatrixGroups

/-- The diagonal matrix `diag(u⁻¹, 1)` of `GL(2, ℂ)`, as a homomorphism from the unit circle. Its
Möbius transformation is the rotation `z ↦ u⁻¹ * z` of the Riemann sphere. -/
noncomputable def circleToGL : Circle →* GL (Fin 2) ℂ where
  toFun u := ⟨!![(u : ℂ)⁻¹, 0; 0, 1], !![(u : ℂ), 0; 0, 1], by simp [one_fin_two],
    by simp [one_fin_two]⟩
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' u v := by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_comm]

/-- The matrix of `circleToGL u` is `diag(u⁻¹, 1)`. -/
theorem coe_circleToGL (u : Circle) :
    (circleToGL u : Matrix (Fin 2) (Fin 2) ℂ) = !![(u : ℂ)⁻¹, 0; 0, 1] :=
  (rfl)

/-- The circle acts on the Riemann sphere by the rotations `u • z = u⁻¹ * z`, the Möbius
transformations of the matrices `diag(u⁻¹, 1)`. -/
noncomputable instance circleAction : MulAction Circle (OnePoint ℂ) :=
  MulAction.compHom (OnePoint ℂ) circleToGL

/-- The rotation by `u` is the Möbius transformation of `circleToGL u`. -/
theorem circle_smul_def (u : Circle) (x : OnePoint ℂ) : u • x = circleToGL u • x :=
  (rfl)

/-- The rotation by `u` multiplies a finite point of the sphere by `u⁻¹`. -/
@[simp]
theorem circle_smul_coe (u : Circle) (z : ℂ) : u • (z : OnePoint ℂ) = ((u : ℂ)⁻¹ * z : ℂ) := by
  rw [circle_smul_def, smul_some_eq_ite]
  simp [coe_circleToGL]

/-- The rotations fix the point at infinity. -/
@[simp]
theorem circle_smul_infty (u : Circle) : u • (∞ : OnePoint ℂ) = (∞ : OnePoint ℂ) := by
  rw [circle_smul_def, smul_infty_eq_ite]
  simp [coe_circleToGL]

/-- The rotations fix `0`. -/
theorem circle_smul_zero (u : Circle) : u • ((0 : ℂ) : OnePoint ℂ) = (0 : ℂ) := by
  simp

section Smooth

open scoped Matrix.Norms.Operator

attribute [local instance] Matrix.linftyOpTopologicalSpace

attribute [local instance] finrank_real_complex_fact' in
/-- The map `u ↦ diag(u⁻¹, 1)` from the circle to `GL(2, ℂ)` is real analytic. -/
private theorem contMDiff_circleToGL :
    ContMDiff (𝓡 1) 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ) ω circleToGL := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  have hc : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ω (fun w : Circle ↦ (w : ℂ)) := contMDiff_coe_sphere
  -- On the circle `u⁻¹ = conj u`, so the matrix is a real affine function of `u`.
  have hA : ContDiff ℝ ω fun z : ℂ ↦
      (starRingEnd ℂ z) • !![(1 : ℂ), 0; 0, 0] + !![(0 : ℂ), 0; 0, 1] :=
    (Complex.conjCLE.contDiff.smul contDiff_const).add contDiff_const
  refine (hA.comp_contMDiff hc).congr fun u ↦ ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_circleToGL, ← Circle.coe_inv_eq_conj]

/-- The action of the circle on the Riemann sphere, regarded as a real surface, is jointly `Cⁿ`
for every `n`. -/
instance instContMDiffSMulCircle (n : ℕ∞ω) :
    ContMDiffSMul (𝓡 1) 𝓘(ℝ, ℂ) n Circle (OnePoint ℂ) where
  contMDiff_smul := by
    have h := (contMDiff_smul (I := 𝓘(ℂ, Matrix (Fin 2) (Fin 2) ℂ)) (I' := 𝓘(ℂ))
      (n := ω) (G := GL (Fin 2) ℂ) (M := OnePoint ℂ)).restrictScalars ℝ
    rw [ModelWithCorners.restrictScalars_prod, modelWithCornersSelf_restrictScalars,
      modelWithCornersSelf_restrictScalars] at h
    exact (h.comp (contMDiff_circleToGL.prodMap contMDiff_id)).of_le le_top

end Smooth

end OnePoint

namespace SymplecticGeometry

open scoped TauCeti.DiffeomorphWeakWhitney TauCeti.ComplexManifold

/-- Each rotation of the sphere by an element of the circle is a Möbius transformation. -/
theorem diffeomorphSmul_circle_mem_mobiusSubgroup (u : Circle) :
    Diffeomorph.smul (𝓡 1) 𝓘(ℝ, ℂ) ∞ u ∈ mobiusSubgroup := by
  obtain ⟨g, hg⟩ := (OnePoint.circleToGL u).exists_psl_forall_smul_eq_smul
  rw [mobiusSubgroup_eq_range]
  refine ⟨g, Diffeomorph.ext fun x ↦ ?_⟩
  rw [mobiusHom_apply, hg, Diffeomorph.smul_apply, OnePoint.circle_smul_def]

/-- The rotations of the sphere by the circle, as a homomorphism into the Möbius group: `u` goes
to the diffeomorphism `x ↦ u • x`. -/
noncomputable def circleMobiusHom : Circle →* mobiusSubgroup :=
  (Diffeomorph.smulContinuousMonoidHom (𝓡 1) 𝓘(ℝ, ℂ) ∞ Circle (OnePoint ℂ) :
    Circle →* TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞).codRestrict mobiusSubgroup fun u ↦ by
      convert diffeomorphSmul_circle_mem_mobiusSubgroup u using 1
      ext x
      rw [MonoidHom.coe_ofClass, Diffeomorph.smulContinuousMonoidHom_apply_apply,
        Diffeomorph.smul_apply]

/-- The diffeomorphism `circleMobiusHom u` sends `x` to `u • x`. -/
@[simp]
theorem coe_circleMobiusHom_apply (u : Circle) (x : OnePoint ℂ) :
    (circleMobiusHom u : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) x = u • x :=
  Diffeomorph.smulContinuousMonoidHom_apply_apply (I := 𝓡 1) u x

/-- The rotations depend continuously on the element of the circle, for the subspace topology of
the weak Whitney topology on the Möbius group. -/
theorem continuous_circleMobiusHom : Continuous circleMobiusHom := by
  refine continuous_induced_rng.2 <| (map_continuous <| Diffeomorph.smulContinuousMonoidHom
    (𝓡 1) 𝓘(ℝ, ℂ) ∞ Circle (OnePoint ℂ)).congr fun u ↦ ?_
  ext x
  rw [Function.comp_apply, coe_circleMobiusHom_apply,
    Diffeomorph.smulContinuousMonoidHom_apply_apply]

/-- The *rotation loop* of degree `n`: the loop `θ ↦ (z ↦ e^{2πinθ} • z)` of orientation
preserving diffeomorphisms of the sphere, parametrized by `AddCircle 1`. Since the circle acts
by `u • z = u⁻¹ * z`, it sends a finite point `z` to `e^{-2πinθ} * z`. -/
noncomputable def rotationLoop (n : ℤ) (θ : AddCircle (1 : ℝ)) : diffPlus :=
  Subgroup.inclusion mobiusSubgroup_le_diffPlus (circleMobiusHom (θ.toCircle ^ n))

/-- The rotation loop of degree `n` at `θ` is the rotation by `θ.toCircle ^ n`. -/
@[simp]
theorem rotationLoop_apply (n : ℤ) (θ : AddCircle (1 : ℝ)) (x : OnePoint ℂ) :
    (rotationLoop n θ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) x = θ.toCircle ^ n • x := by
  rw [rotationLoop, Subgroup.coe_inclusion, coe_circleMobiusHom_apply]

/-- The rotation loop is continuous for the subspace topology of the weak Whitney topology. -/
theorem continuous_rotationLoop (n : ℤ) : Continuous (rotationLoop n) :=
  (continuous_inclusion mobiusSubgroup_le_diffPlus).comp <| continuous_circleMobiusHom.comp <|
    (continuous_zpow n).comp AddCircle.continuous_toCircle

/-- The uncurried rotation loop `(θ, z) ↦ rotationLoop n θ z` is `Cᵏ` for every `k`. -/
theorem contMDiff_uncurry_rotationLoop (n : ℤ) {k : ℕ∞ω} :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) k fun p : AddCircle (1 : ℝ) × OnePoint ℂ ↦
      (rotationLoop n p.1 : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) p.2 := by
  simp only [rotationLoop_apply]
  exact contMDiff_smul.comp
    (((TauCeti.contMDiff_zpow n).comp (AddCircle.contMDiff_toCircle (p := 1) k)).prodMap
      contMDiff_id)

/-- The rotation loop of degree `0` is constant at the identity. -/
@[simp]
theorem rotationLoop_zero (θ : AddCircle (1 : ℝ)) : rotationLoop 0 θ = 1 := by
  ext x
  simp

/-- The rotation loops multiply pointwise as their degrees add. -/
theorem rotationLoop_add (n m : ℤ) (θ : AddCircle (1 : ℝ)) :
    rotationLoop (n + m) θ = rotationLoop n θ * rotationLoop m θ := by
  simp [rotationLoop, _root_.zpow_add]

end SymplecticGeometry

end
