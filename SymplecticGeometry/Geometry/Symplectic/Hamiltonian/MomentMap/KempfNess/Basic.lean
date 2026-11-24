/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.Complexification
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Manifold.Algebra.ComplexSmoothFunctions
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.RepresentationTheory.InvariantForm

/-!
# Complexified actions and the norm square of the moment map

Let `C : LieComplexification I G IC Gc` be a complexification of a real Lie group `G`, and suppose
that `G` and `Gc` both act on `M`, which carries the almost complex structure `J`. The action of
`Gc` is a *complexified action* of that of `G` if it extends it along the inclusion `C.toHom`, and
if, for every `ξ` in the Lie algebra of `G`, the fundamental vector field of the imaginary
direction `C.cplx (C.lieMap ξ)` is `J` applied to that of `ξ`: `X_{iξ} = J X_ξ`. This is the
infinitesimal form of the holomorphicity of the action of `Gc`, the only form in which the
Kempf–Ness theory uses it.

For a nondegenerate bilinear form `B` on the Lie algebra `𝔤` of `G`, a map `μ : M → 𝔤*` has a
dual `μ♯ : M → 𝔤`, with `B (μ♯ x) ξ = μ x ξ`, and a norm square `‖μ x‖² = B (μ♯ x) (μ♯ x)`. The
Kempf–Ness theory takes for `B` an `Ad`-invariant inner product, such as the one that
`TauCeti.Lie.exists_isSymm_posDef_continuousBilinearMap_adjoint_invariant` gives on a compact
group; the definitions take any nondegenerate `B`, and each result assumes only what it uses.

## Main definitions

* `SymplecticGeometry.IsComplexifiedAction C J`: the action of `Gc` on `M` is a complexified
  action of that of `G`, for `C` and `J`.
* `SymplecticGeometry.momentSharp B hB μ x`: the vector of `𝔤` dual to `μ x` under `B`.
* `SymplecticGeometry.momentNormSq B hB μ x`: the norm square `B (μ♯ x) (μ♯ x)` of `μ x`.

## Main results

* `SymplecticGeometry.IsComplexifiedAction.fundamentalVectorField_lieMap`: the fundamental vector
  field of `C.lieMap ξ` for the action of `Gc` is that of `ξ` for the action of `G`.
* `SymplecticGeometry.IsComplexifiedAction.isMIntegralCurve_expI_smul`: the curve
  `t ↦ C.expI (t • ξ) • p` is an integral curve of `x ↦ J x (X_ξ x)`.
* `SymplecticGeometry.isComplexifiedAction_circle`: the action of `ℂˣ` on `ℂ` by multiplication,
  with `J` multiplication by `i`, is a complexified action of the rotation action of `Circle`, for
  the complexification `LieComplexification.circle`.
* `SymplecticGeometry.momentNormSq_nonneg`, `SymplecticGeometry.momentNormSq_eq_zero_iff`: for a
  nonnegative, respectively anisotropic, `B`, the norm square is nonnegative, and it
  vanishes exactly where `μ` does.
* `SymplecticGeometry.momentSharp_neg`, `SymplecticGeometry.momentNormSq_neg`: replacing `μ`
  by `-μ`, as the sign convention of an equivariant moment map may require, negates `μ♯` and
  leaves the norm square unchanged.
* `SymplecticGeometry.momentSharp_smul`, `SymplecticGeometry.momentNormSq_smul`: for an
  `Ad`-invariant `B` and a coadjoint-equivariant `μ`, `μ♯` is equivariant and the norm square
  is `G`-invariant.
* `SymplecticGeometry.contMDiff_momentNormSq`: if each component `x ↦ μ x ξ` is `C^n`, so is the
  norm square.

The integral curve is Tau Ceti's `TauCeti.isMIntegralCurve_mulInvariantExp_smul_smul` for the
action of `Gc` and the direction `C.cplx (C.lieMap ξ)`. In the example, the orbit maps of `ℂˣ` are
holomorphic, so their real differentials commute with multiplication by `i`
(`MDifferentiableAt.mfderiv_ofComplexManifold_apply`). The smoothness of the action of `ℂˣ` on `ℂ`
for the real structures, which the results on complexified actions assume, is found by instance
search: Mathlib's `Units.contMDiffSMul` and `ContMDiffMul.contMDiffSMul` from Tau Ceti's
`TauCeti.realComplexContMDiffRing`.

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021], §2.
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.7.
-/

public section

noncomputable section

open Function Manifold TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

/-! ### The dual of the moment map and the norm square of the moment map -/

section MomentSharp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {M : Type*}
  {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)} {hB : B.Nondegenerate}
  {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)} {x : M}

variable (B hB μ) in
/-- The vector `μ♯ x` of the Lie algebra dual to `μ x` under the nondegenerate bilinear form `B`:
the unique vector with `B (μ♯ x) ξ = μ x ξ` for every `ξ`. -/
def momentSharp (x : M) : GroupLieAlgebra I G :=
  (B.toDual hB).symm (μ x)

theorem momentSharp_def : momentSharp B hB μ x = (B.toDual hB).symm (μ x) :=
  (rfl)

/-- The defining property of `μ♯ x`: pairing it with `ξ` under `B` gives `μ x ξ`. -/
@[simp]
theorem apply_momentSharp (ξ : GroupLieAlgebra I G) : B (momentSharp B hB μ x) ξ = μ x ξ := by
  rw [momentSharp_def, LinearMap.BilinForm.apply_toDual_symm_apply]

/-- `μ♯ x` is the only vector `v` with `B v ξ = μ x ξ` for every `ξ`. -/
theorem momentSharp_eq_iff {v : GroupLieAlgebra I G} :
    momentSharp B hB μ x = v ↔ ∀ ξ, B v ξ = μ x ξ := by
  rw [momentSharp_def, LinearEquiv.symm_apply_eq, eq_comm, LinearMap.ext_iff]
  simp only [LinearMap.BilinForm.toDual_def]

@[simp]
theorem momentSharp_eq_zero_iff : momentSharp B hB μ x = 0 ↔ μ x = 0 := by
  rw [momentSharp_def, LinearEquiv.map_eq_zero_iff]

/-- The dual vector of `-μ` is the negative of that of `μ`. -/
@[simp]
theorem momentSharp_neg : momentSharp B hB (fun x ↦ -μ x) x = -momentSharp B hB μ x := by
  simp [momentSharp_def]

variable (B hB μ) in
/-- The norm square `‖μ x‖² = B (μ♯ x) (μ♯ x)` of the moment map, for the form on the dual of
the Lie algebra that the nondegenerate form `B` induces. -/
def momentNormSq (x : M) : ℝ :=
  B (momentSharp B hB μ x) (momentSharp B hB μ x)

theorem momentNormSq_def :
    momentNormSq B hB μ x = B (momentSharp B hB μ x) (momentSharp B hB μ x) :=
  (rfl)

/-- The norm square of `μ x` is `μ x` evaluated at `μ♯ x`. -/
theorem momentNormSq_eq_apply_momentSharp :
    momentNormSq B hB μ x = μ x (momentSharp B hB μ x) := by
  rw [momentNormSq_def, apply_momentSharp]

/-- The norm square of `-μ` is that of `μ`. -/
@[simp]
theorem momentNormSq_neg : momentNormSq B hB (fun x ↦ -μ x) x = momentNormSq B hB μ x := by
  simp [momentNormSq_def, momentSharp_neg]

/-- For a nonnegative form `B`, the norm square of `μ x` is nonnegative. -/
theorem momentNormSq_nonneg (hpos : B.IsNonneg) : 0 ≤ momentNormSq B hB μ x :=
  hpos.nonneg _

/-- For an anisotropic form `B`, such as a positive definite one, the norm square of `μ x`
vanishes exactly when `μ x` does. -/
theorem momentNormSq_eq_zero_iff (hB' : B.toQuadraticMap.Anisotropic) :
    momentNormSq B hB μ x = 0 ↔ μ x = 0 := by
  rw [← momentSharp_eq_zero_iff (hB := hB)]
  exact ⟨hB' _, fun h ↦ by simp [momentNormSq_def, h]⟩

/-- For a coadjoint-equivariant `μ` and an `Ad`-invariant form `B`, the dual vector is
`Ad`-equivariant: `μ♯ (g • x) = Ad_g (μ♯ x)`. -/
theorem momentSharp_smul [LieGroup I 1 G] [MulAction G M]
    (hBG : Representation.IsInvariantForm (Lie.adjointRepresentation ℝ I G) B)
    (hμ : ∀ (g : G) (x : M), μ (g • x) = Lie.coadjointRepresentation ℝ I G g (μ x))
    (g : G) (x : M) :
    momentSharp B hB μ (g • x) = Lie.adjointContinuousLinearMap g (momentSharp B hB μ x) := by
  refine momentSharp_eq_iff.2 fun ξ ↦ ?_
  rw [← Lie.adjointRepresentation_apply (𝕜 := ℝ), hBG.apply_left, apply_momentSharp, hμ,
    Lie.coadjointRepresentation_apply, Lie.adjointRepresentation_apply]

/-- For a coadjoint-equivariant `μ` and an `Ad`-invariant form `B`, the norm square of the moment
map is invariant under `G`. -/
theorem momentNormSq_smul [LieGroup I 1 G] [MulAction G M]
    (hBG : Representation.IsInvariantForm (Lie.adjointRepresentation ℝ I G) B)
    (hμ : ∀ (g : G) (x : M), μ (g • x) = Lie.coadjointRepresentation ℝ I G g (μ x))
    (g : G) (x : M) : momentNormSq B hB μ (g • x) = momentNormSq B hB μ x := by
  rw [momentNormSq_def, momentSharp_smul hBG hμ, ← Lie.adjointRepresentation_apply (𝕜 := ℝ),
    Representation.isInvariantForm_iff.1 hBG, momentNormSq_def]

/-- In a basis `b` of the Lie algebra, the norm square of `μ x` is
`∑ i, μ x (b i) * μ x (B♯ (b.coord i))`, with `B♯` the inverse of `B.toDual hB`. -/
private theorem momentNormSq_eq_sum {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (GroupLieAlgebra I G)) :
    momentNormSq B hB μ x = ∑ i, μ x (b i) * μ x ((B.toDual hB).symm (b.coord i)) := by
  rw [momentNormSq_eq_apply_momentSharp, momentSharp_def]
  conv_lhs => arg 2; rw [← b.sum_dual_apply_smul_coord (μ x)]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- If every component `x ↦ μ x ξ` of the moment map is `C^n`, so is its norm square. -/
theorem contMDiff_momentNormSq [TopologicalSpace M] [ChartedSpace H' M] {n : WithTop ℕ∞}
    (hμ : ∀ ξ, ContMDiff I' 𝓘(ℝ) n fun x ↦ μ x ξ) : ContMDiff I' 𝓘(ℝ) n (momentNormSq B hB μ) := by
  let b := Module.finBasis ℝ (GroupLieAlgebra I G)
  simp_rw [funext fun x ↦ momentNormSq_eq_sum (hB := hB) (μ := μ) (x := x) b]
  exact ContMDiff.sum fun i _ ↦ (hμ _).mul (hμ _)

end MomentSharp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC}
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc] [BoundarylessManifold IC Gc]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [MulAction Gc M]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The action of the complexification `Gc` on `M` is a *complexified action* of that of `G`,
for the complexification `C` and the almost complex structure `J` of `M`: it extends the action of
`G` along `C.toHom`, and for every `ξ` in the Lie algebra of `G` the fundamental vector field of
`C.cplx (C.lieMap ξ)` is `J` applied to that of `C.lieMap ξ`, at every point. -/
structure IsComplexifiedAction (C : LieComplexification I G IC Gc)
    (J : SmoothAlmostComplexStructure I' M) : Prop where
  /-- The action of `Gc` extends that of `G` along `C.toHom`. -/
  toHom_smul (u : G) (x : M) : C.toHom u • x = u • x
  /-- The fundamental vector field of an imaginary direction is `J` applied to that of the real
  direction: `X_{iξ} = J X_ξ`. -/
  fundamentalVectorField_cplx (ξ : GroupLieAlgebra I G) (x : M) :
    fundamentalVectorField I' (C.cplx (C.lieMap ξ)) x =
      J x (fundamentalVectorField I' (C.lieMap ξ) x)

namespace IsComplexifiedAction

variable [ContMDiffSMul IC I' ∞ Gc M] {C : LieComplexification I G IC Gc}
  {J : SmoothAlmostComplexStructure I' M}

/-- For a complexified action, the fundamental vector field of `C.lieMap ξ` for the action of
`Gc` is that of `ξ` for the action of `G`. -/
theorem fundamentalVectorField_lieMap (h : IsComplexifiedAction C J) (ξ : GroupLieAlgebra I G) :
    fundamentalVectorField I' (C.lieMap ξ) =
      (fundamentalVectorField I' ξ : ∀ x : M, TangentSpace I' x) := by
  rw [LieComplexification.lieMap_def, ContMDiffMonoidMorphism.coe_groupLieAlgebraLieHom]
  exact C.toHom.toMonoidHom.fundamentalVectorField_groupLieAlgebraMap
    (C.toHom.contMDiff_toFun.mdifferentiableAt (by simp)) (fun u x ↦ (h.toHom_smul u x).symm) ξ

/-- **The imaginary one-parameter subgroups move points along `J X_ξ`.** For a complexified
action, the curve `t ↦ C.expI (t • ξ) • p` is an integral curve of the vector field
`x ↦ J x (X_ξ x)`, where `X_ξ` is the fundamental vector field of `ξ` for the action of `G`. -/
theorem isMIntegralCurve_expI_smul (h : IsComplexifiedAction C J) (ξ : GroupLieAlgebra I G)
    (p : M) :
    IsMIntegralCurve (fun t : ℝ ↦ C.expI (t • ξ) • p)
      (fun x ↦ J x (fundamentalVectorField I' ξ x)) := by
  have hγ : (fun t : ℝ ↦ C.expI (t • ξ) • p) =
      fun t : ℝ ↦ mulInvariantExp (t • C.cplx (C.lieMap ξ)) • p := by
    funext t
    rw [LieComplexification.expI_def, map_smul, AlmostComplexStructure.apply_smul]
  have hv : fundamentalVectorField I' (C.cplx (C.lieMap ξ)) =
      fun x ↦ J x (fundamentalVectorField I' ξ x) :=
    funext fun x ↦ by rw [h.fundamentalVectorField_cplx, h.fundamentalVectorField_lieMap]
  rw [hγ, ← hv]
  exact isMIntegralCurve_mulInvariantExp_smul_smul (I' := I') (C.cplx (C.lieMap ξ)) p

end IsComplexifiedAction

/-! ### The example: `ℂˣ` acting on `ℂ` -/

section Circle

open Complex

/-- **`ℂˣ` acting on `ℂ` is a complexified action.** The action of `ℂˣ` on `ℂ` by multiplication,
with the almost complex structure of `ℂ` given by multiplication by `i`
(`SmoothAlmostComplexStructure.ofComplexManifold`), is a complexified action of the rotation
action of `Circle`, for the complexification `LieComplexification.circle`. -/
theorem isComplexifiedAction_circle :
    IsComplexifiedAction LieComplexification.circle
      (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ) where
  toHom_smul u z := by
    rw [Units.smul_def, LieComplexification.circle_toHom, Circle.coe_contMDiffToUnits_apply,
      Circle.smul_def]
  fundamentalVectorField_cplx ξ z := by
    -- The orbit map of `z` is holomorphic, so its real differential commutes with `i`.
    have hf : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun g : ℂˣ ↦ g • z) 1 :=
      (ContMDiffSMul.contMDiff_smul_const (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ℂ)) (n := 1)
        z).mdifferentiableAt one_ne_zero
    rw [fundamentalVectorField_apply, fundamentalVectorField_apply,
      LieComplexification.circle_cplx, SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
    -- The two sides are `i` times the same vector, at the points `1 • z` and `z`.
    exact (hf.mfderiv_ofComplexManifold_apply _).trans
      ((SmoothAlmostComplexStructure.ofComplexManifold_apply _ _).trans
        (SmoothAlmostComplexStructure.ofComplexManifold_apply _ _).symm)

end Circle

end SymplecticGeometry
