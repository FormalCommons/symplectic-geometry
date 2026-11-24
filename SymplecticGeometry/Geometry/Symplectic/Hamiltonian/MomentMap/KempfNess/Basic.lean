/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.Complexification
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Metric
public import SymplecticGeometry.Topology.Algebra.GroupAction.Stabilizer
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Manifold.Algebra.ComplexSmoothFunctions
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Metric
public import TauCeti.RepresentationTheory.InvariantForm

/-!
# Complexified actions, the norm square of the moment map, stability and the gradient

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

For an action of `Gc` on `M`, a point `p` is *polystable* for `μ` if its `Gc`-orbit meets the
zero set of `μ`, *semistable* if the closure of that orbit does, and *stable* if it is
polystable with a discrete stabilizer in `Gc`, following [McDuffSalamon2017], §5.7, and
[GeorgoulasRobbinSalamon2021]. Later files characterize them through the Kempf–Ness function
and the moment weights.

## Main definitions

* `SymplecticGeometry.IsComplexifiedAction C J`: the action of `Gc` on `M` is a complexified
  action of that of `G`, for `C` and `J`.
* `SymplecticGeometry.momentSharp B hB μ x`: the vector of `𝔤` dual to `μ x` under `B`.
* `SymplecticGeometry.momentNormSq B hB μ x`: the norm square `B (μ♯ x) (μ♯ x)` of `μ x`.
* `SymplecticGeometry.IsSemistable C μ p`, `SymplecticGeometry.IsPolystable C μ p`,
  `SymplecticGeometry.IsStable C μ p`: the stability predicates.
* `SymplecticGeometry.polystableLocus C μ`: the polystable points, as a sub-action of `Gc`.

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
* `SymplecticGeometry.IsStable.isPolystable`, `SymplecticGeometry.IsPolystable.isSemistable`:
  stable points are polystable, and polystable points semistable.
* `SymplecticGeometry.isSemistable_smul_iff`, `SymplecticGeometry.isPolystable_smul_iff`,
  `SymplecticGeometry.isStable_smul_iff`: each predicate holds at `g • p` exactly when it holds
  at `p`.
* `SymplecticGeometry.isPolystable_of_moment_eq_zero`: a zero of `μ` is polystable.
* `SymplecticGeometry.isSemistable_of_moment_eq_zero`: a zero of `μ` is semistable.
* `SymplecticGeometry.isStable_of_moment_eq_zero`: a zero of `μ` whose stabilizer in `Gc` is
  discrete is stable.
* `SymplecticGeometry.mgradient_moment_apply`: if `-μ` is a moment map for `σ` and the metric is
  `g(u, w) = σ(u, J w)`, the gradient of `x ↦ μ x ξ` is `-J X_ξ`.
* `SymplecticGeometry.hasDerivAt_moment_expI`, `SymplecticGeometry.antitone_moment_expI`: for a
  complexified action, `t ↦ μ (C.expI (t • ξ) • p) ξ` has derivative `-‖X_ξ‖²` at the moving
  point, so it is antitone.

The integral curve is Tau Ceti's `TauCeti.isMIntegralCurve_mulInvariantExp_smul_smul` for the
action of `Gc` and the direction `C.cplx (C.lieMap ξ)`. In the example, the orbit maps of `ℂˣ` are
holomorphic, so their real differentials commute with multiplication by `i`
(`MDifferentiableAt.mfderiv_ofComplexManifold_apply`). The smoothness of the action of `ℂˣ` on `ℂ`
for the real structures, which the results on complexified actions assume, is found by instance
search: Mathlib's `Units.contMDiffSMul` and `ContMDiffMul.contMDiffSMul` from Tau Ceti's
`TauCeti.realComplexContMDiffRing`.

The gradient of `x ↦ μ x ξ` is computed as in Tau Ceti's
`TauCeti.SmoothTwoForm.IsNondegenerate.apply_hamiltonianVectorField_eq_mgradient`, read for the
component `-μ_ξ` with Hamiltonian vector field `X_ξ`; no nondegeneracy is needed, since the
gradient is tested directly against the moment map identity, through
`TauCeti.SmoothAlmostComplexStructure.apply_eq_mgradient_of_eval₂_eq`. The derivative along
`exp(itξ)` follows Tau Ceti's `TauCeti.hasDerivAt_comp_maximalIntegralCurve_neg_mgradient`: the
chain rule along the integral curve `isMIntegralCurve_expI_smul` of `J X_ξ`, and `J` is
orthogonal for `g` (`TauCeti.SmoothAlmostComplexStructure.inner_apply_apply_of_inner_eq`).
These results take any metric with `g(u, w) = σ(u, J w)`; for a compatible pair, Tau Ceti's
`TauCeti.SmoothTwoForm.Compatible.inner_eq_eval₂` says that `Compatible.metric` is one.

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

/-! ### The stability predicates -/

section Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC}
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc] [BoundarylessManifold IC Gc]
  {M : Type*} [MulAction Gc M]

/-- A point `p` is *polystable* for `μ` if its orbit under the complexification `Gc` meets the
zero level set of `μ`. -/
def IsPolystable (_C : LieComplexification I G IC Gc)
    (μ : M → Module.Dual ℝ (GroupLieAlgebra I G)) (p : M) : Prop :=
  ∃ x ∈ MulAction.orbit Gc p, μ x = 0

/-- A point `p` is *stable* for `μ` if it is polystable and its stabilizer in the
complexification `Gc` is discrete. -/
def IsStable (C : LieComplexification I G IC Gc)
    (μ : M → Module.Dual ℝ (GroupLieAlgebra I G)) (p : M) : Prop :=
  IsPolystable C μ p ∧ DiscreteTopology (MulAction.stabilizer Gc p)

/-- A point `p` is *semistable* for `μ` if the closure of its orbit under the complexification
`Gc` meets the zero level set of `μ`. -/
def IsSemistable [TopologicalSpace M] (_C : LieComplexification I G IC Gc)
    (μ : M → Module.Dual ℝ (GroupLieAlgebra I G)) (p : M) : Prop :=
  ∃ x ∈ closure (MulAction.orbit Gc p), μ x = 0

variable {C : LieComplexification I G IC Gc} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {p : M}

theorem isPolystable_iff : IsPolystable C μ p ↔ ∃ x ∈ MulAction.orbit Gc p, μ x = 0 :=
  Iff.rfl

/-- `p` is polystable exactly when `μ` vanishes at `g • p` for some `g` in `Gc`. -/
theorem isPolystable_iff_exists_smul : IsPolystable C μ p ↔ ∃ g : Gc, μ (g • p) = 0 := by
  simp [isPolystable_iff, MulAction.mem_orbit_iff]

theorem isStable_iff :
    IsStable C μ p ↔ IsPolystable C μ p ∧ DiscreteTopology (MulAction.stabilizer Gc p) :=
  Iff.rfl

/-- A stable point is polystable. -/
theorem IsStable.isPolystable (h : IsStable C μ p) : IsPolystable C μ p :=
  h.1

theorem IsStable.discreteTopology_stabilizer (h : IsStable C μ p) :
    DiscreteTopology (MulAction.stabilizer Gc p) :=
  h.2

/-- A zero of `μ` is polystable. -/
theorem isPolystable_of_moment_eq_zero (h : μ p = 0) : IsPolystable C μ p :=
  ⟨p, MulAction.mem_orbit_self p, h⟩

/-- A zero of `μ` with a discrete stabilizer in `Gc` is stable. -/
theorem isStable_of_moment_eq_zero (h : μ p = 0) [DiscreteTopology (MulAction.stabilizer Gc p)] :
    IsStable C μ p :=
  ⟨isPolystable_of_moment_eq_zero h, ‹_›⟩

/-- Polystability is invariant along the orbits of `Gc`. -/
@[simp]
theorem isPolystable_smul_iff (g : Gc) : IsPolystable C μ (g • p) ↔ IsPolystable C μ p := by
  simp only [isPolystable_iff, MulAction.orbit_smul]

/-- Stability is invariant along the orbits of `Gc`. -/
@[simp]
theorem isStable_smul_iff (g : Gc) : IsStable C μ (g • p) ↔ IsStable C μ p := by
  have := continuousMul_of_contMDiffMul IC ∞ (G := Gc)
  rw [isStable_iff, isStable_iff, isPolystable_smul_iff,
    MulAction.discreteTopology_stabilizer_smul_iff]

/-- The *polystable locus*: the set of polystable points, as a sub-action of `Gc`. -/
def polystableLocus (C : LieComplexification I G IC Gc)
    (μ : M → Module.Dual ℝ (GroupLieAlgebra I G)) : SubMulAction Gc M where
  carrier := {p | IsPolystable C μ p}
  smul_mem' g _ hp := (isPolystable_smul_iff (C := C) g).2 hp

@[simp]
theorem mem_polystableLocus : p ∈ polystableLocus C μ ↔ IsPolystable C μ p :=
  Iff.rfl

@[simp]
theorem coe_polystableLocus : (polystableLocus C μ : Set M) = {p | IsPolystable C μ p} :=
  (rfl)

/-- The zero level set of `μ` lies in the polystable locus. -/
theorem setOf_moment_eq_zero_subset_polystableLocus :
    {x | μ x = 0} ⊆ (polystableLocus C μ : Set M) :=
  fun _ hx ↦ isPolystable_of_moment_eq_zero (C := C) hx

variable [TopologicalSpace M]

theorem isSemistable_iff : IsSemistable C μ p ↔ ∃ x ∈ closure (MulAction.orbit Gc p), μ x = 0 :=
  Iff.rfl

/-- A polystable point is semistable. -/
theorem IsPolystable.isSemistable (h : IsPolystable C μ p) : IsSemistable C μ p :=
  let ⟨x, hx, hμ⟩ := h
  ⟨x, subset_closure hx, hμ⟩

theorem IsStable.isSemistable (h : IsStable C μ p) : IsSemistable C μ p :=
  h.isPolystable.isSemistable

/-- A zero of `μ` is semistable. -/
theorem isSemistable_of_moment_eq_zero (h : μ p = 0) : IsSemistable C μ p :=
  (isPolystable_of_moment_eq_zero h).isSemistable

/-- Semistability is invariant along the orbits of `Gc`. -/
@[simp]
theorem isSemistable_smul_iff (g : Gc) : IsSemistable C μ (g • p) ↔ IsSemistable C μ p := by
  simp only [isSemistable_iff, MulAction.orbit_smul]

end Stability

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

/-! ### The gradient of a component of the moment map -/

section Gradient

open _root_.Bundle
open scoped RealInnerProductSpace

variable [FiniteDimensional ℝ E'] [ContMDiffSMul I I' ∞ G M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I' x)]
  {σ : SmoothTwoForm I' M} {J : SmoothAlmostComplexStructure I' M}
  {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- **The gradient of a component of the moment map.** Let `-μ` be a moment map for `σ` of the
action of `G` by fundamental vector fields, and let the metric be `g(u, w) = σ(u, J w)`. Then the
gradient of `x ↦ μ x ξ` is `-J X_ξ`, where `X_ξ` is the fundamental vector field of `ξ`. -/
theorem mgradient_moment_apply
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (ξ : GroupLieAlgebra I G) (x : M) :
    Manifold.mgradient I' (fun y ↦ μ y ξ) x = -J x (fundamentalVectorField I' ξ x) := by
  -- `J X_ξ` is the gradient of the component `x ↦ (-μ x) ξ` of the moment map `-μ`.
  have h := J.apply_eq_mgradient_of_eval₂_eq hg (hμ.eval₂_apply ξ x)
  rw [InfinitesimalAction.fundamental_apply] at h
  rw [show (fun y ↦ μ y ξ) = -fun y ↦ (-μ y) ξ by ext; simp, Manifold.mgradient_neg, ← h]

/-- **The derivative of `⟨μ, ξ⟩` along `exp(itξ)`.** For a complexified action, with `-μ` a
moment map for `σ` and the metric `g(u, w) = σ(u, J w)`, the function
`t ↦ μ (C.expI (t • ξ) • p) ξ` has derivative `-‖X_ξ‖²` at the point `C.expI (t • ξ) • p`. -/
theorem hasDerivAt_moment_expI [ContMDiffSMul IC I' ∞ Gc M] {C : LieComplexification I G IC Gc}
    (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (ξ : GroupLieAlgebra I G) (p : M) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ μ (C.expI (s • ξ) • p) ξ)
      (-‖fundamentalVectorField I' ξ (C.expI (t • ξ) • p)‖ ^ 2) t := by
  have hd : MDifferentiableAt I' 𝓘(ℝ) (fun y ↦ μ y ξ) (C.expI (t • ξ) • p) := by
    convert (hμ.mdifferentiableAt ξ (C.expI (t • ξ) • p)).neg using 1
    funext y
    simp
  have hD := Manifold.hasDerivAt_comp_curve hd (h.isMIntegralCurve_expI_smul ξ p t)
  rwa [← Manifold.inner_mgradient, mgradient_moment_apply hμ hg, inner_neg_left,
    SmoothAlmostComplexStructure.inner_apply_apply_of_inner_eq hg,
    real_inner_self_eq_norm_sq] at hD

/-- **`⟨μ, ξ⟩` decreases along `exp(itξ)`.** For a complexified action, with `-μ` a moment map
for `σ` and the metric `g(u, w) = σ(u, J w)`, the function `t ↦ μ (C.expI (t • ξ) • p) ξ` is
antitone. -/
theorem antitone_moment_expI [ContMDiffSMul IC I' ∞ Gc M] {C : LieComplexification I G IC Gc}
    (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (ξ : GroupLieAlgebra I G) (p : M) :
    Antitone fun t : ℝ ↦ μ (C.expI (t • ξ) • p) ξ :=
  antitone_of_hasDerivAt_nonpos (hasDerivAt_moment_expI h hμ hg ξ p)
    fun _ ↦ neg_nonpos.2 (sq_nonneg _)

end Gradient

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
