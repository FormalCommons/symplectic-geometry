/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Orientation.Complex
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.OpenEmbedding
public import TauCeti.Geometry.Manifold.Complex.FundamentalClass
public import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Orientation.Euclidean
public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Topology.Circle.Loop
public import SymplecticGeometry.Geometry.Manifold.Complex.FundamentalClass
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.ChangeOfModel
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import SymplecticGeometry.LinearAlgebra.Complex.Orientation
import SymplecticGeometry.Geometry.Manifold.Instances.Sphere
import SymplecticGeometry.Geometry.Manifold.Orientation.CoordinateBall
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Geometry.Manifold.CoordinateBall
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Manifold.ModelTransport.Finrank
import TauCeti.LinearAlgebra.Orientation.Basic
import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# Coordinate discs of homologically oriented surfaces

Let `M` be a Hausdorff space charted on a finite-dimensional real normed space `E`, with a
homological orientation `o : TauCeti.HomologicalOrientation M E 2`. A *coordinate disc* of `M` is
an open embedding `φ` of the open ball of radius `2` of `ℂ` into `M` that carries the standard
orientation of `ℂ` to `o`. The ball and `M` have different models (`ℂ` and `E`), so pulling `o`
back along `φ` with `TauCeti.HomologicalOrientation.comap` is not available; instead the
orientation condition is stated point by point. At every `z` the excision isomorphism of `φ`
(`Topology.IsOpenEmbedding.localOrientationEquiv`) carries the local orientation at `z` of the
canonical orientation `TauCeti.complexHomologicalOrientation` of the ball to the local orientation
of `o` at `φ z`.

A coordinate disc has a closed disc `φ.disc = φ(B̄₁)`, which is compact, inside it an open disc
`φ.openDisc = φ(B₁)`, which is open, and a boundary circle `t ↦ φ(e^{2πit})`, which runs
counterclockwise in the chart, so that it is oriented as the boundary of the closed disc.

Complex conjugation maps the ball to itself and reverses its canonical orientation
(`TauCeti.comap_conj_complexHomologicalOrientation`). So a coordinate disc `φ` for `o` gives a
coordinate disc `φ.reverse = φ ∘ conj` for `-o`, with the same discs and with the boundary loop
run backwards.

Smaller coordinate discs come from precomposing with the affine maps `z ↦ a + r z`, `r > 0`, of
the ball into itself, which preserve its canonical orientation since they are holomorphic
(`TauCeti.comap_complexHomologicalOrientation`). More generally, an orientation-preserving open
embedding into `M` of an open set of `ℂ`, precomposed with an orientation-preserving open
embedding of the ball into that set, such as an affine map, is a coordinate disc. A coordinate
disc whose image lies in an open set `U` is one of `U`, for the restriction of `o`
(`TauCeti.HomologicalOrientation.comap`).

On a `C¹` surface `M` charted on `ℝ²` with an orientation
`o : TauCeti.Manifold.Orientation (𝓡 2) M (Fin 2)`, every chart `e` that preserves orientation
gives coordinate discs for `o.toHomologicalOrientation`: for a ball `B(c, r)` in the target of
`e`, the map `z ↦ e⁻¹(c + (r / 2) (re z, im z))` is one, centred at `e⁻¹(c)`. The identification
`z ↦ (re z, im z)` of `ℂ` with `ℝ²` carries the standard orientation of `ℂ` to that of `ℝ²`
(`Complex.orientation_map_orthonormalBasisOneI_repr`), and the local orientation of a smooth
orientation can be read in any chart whose derivative matches the orientations
(`TauCeti.Manifold.Orientation.toHomologicalOrientation_apply_eq_localOrientationOfOrientedChart`).

Coordinate discs exist on every homologically oriented surface. Chart `M` on `ℂ` through a linear
equivalence (`ChartedSpace.ofFinrankEq`) and read `o` with the model `ℂ`
(`TauCeti.HomologicalOrientation.changeModel`). An open embedding `f` of the ball into `M` (from a
coordinate ball of `M`, `IsOpen.exists_isOpenEmbedding_apply_zero_eq`) pulls it back to a
homological orientation of the ball, which is the canonical one or its opposite, since the ball is
connected (`TauCeti.HomologicalOrientation.eq_or_eq_neg`). So `f` is a coordinate disc for `o` or
for `-o` (`SymplecticGeometry.CoordinateDisc.ofComapEq`), and in the second case its reverse is one
for `o`. Finitely many distinct points have pairwise disjoint neighbourhoods
(`Pairwise.exists_mem_filter_of_disjoint`, applied to `pairwise_disjoint_nhds`), and coordinate
discs inside them have disjoint images.

On a smooth surface with a smooth orientation `o`, the coordinate discs can be taken of the form
`ofChart`, for charts of the maximal smooth atlas that preserve orientation on all of their
source: the inverse of Tau Ceti's oriented coordinate ball, restricted to a small ball
(`TauCeti.Manifold.Orientation.exists_mem_maximalAtlas_isOrientationPreservingAt`).

## Main definitions

* `SymplecticGeometry.CoordinateDisc o`: the coordinate discs of `M` for `o`.
* `SymplecticGeometry.CoordinateDisc.ball`: the open ball of radius `2` of `ℂ`, as an open set.
  Its centre is the point `0 : ball` (`SymplecticGeometry.CoordinateDisc.coe_zero`).
* `SymplecticGeometry.CoordinateDisc.disc`, `SymplecticGeometry.CoordinateDisc.openDisc`: the
  images of the closed and of the open unit ball.
* `SymplecticGeometry.CoordinateDisc.boundaryCircle`: the unit circle of the chart, as a map
  `C(Circle, M)`.
* `SymplecticGeometry.CoordinateDisc.boundaryLoop`: the loop `t ↦ φ(e^{2πit})`.
* `SymplecticGeometry.CoordinateDisc.discContraction`: the radial contraction
  `(s, t) ↦ φ((1 - s) e^{2πit})` of the boundary loop inside the closed disc.
* `SymplecticGeometry.CoordinateDisc.coord`: the inverse of a coordinate disc on its range, as a
  map to `ℂ`.
* `SymplecticGeometry.CoordinateDisc.phase`: the angular coordinate `w / ‖w‖` of a coordinate
  disc, as a map to `Circle`.
* `SymplecticGeometry.CoordinateDisc.reverse`: the coordinate disc `φ ∘ conj` for `-o`.
* `SymplecticGeometry.CoordinateDisc.affineBall`: the map `z ↦ a + r z` of the ball into an open
  set of `ℂ` that contains its image.
* `SymplecticGeometry.CoordinateDisc.ofComp`: the coordinate disc `g ∘ f`, for an
  orientation-preserving open embedding `g` of an open set `U` of `ℂ` into `M` and an
  orientation-preserving open embedding `f` of the ball into `U`.
* `SymplecticGeometry.CoordinateDisc.comp`: a coordinate disc precomposed with an
  orientation-preserving open embedding of the ball into itself, the case `U = ball` of `ofComp`.
* `SymplecticGeometry.CoordinateDisc.restrict`: a coordinate disc with image in an open set `U`,
  as a coordinate disc of `U`.
* `SymplecticGeometry.CoordinateDisc.subtypeVal`: the inclusion of the ball into `ℂ`, a coordinate
  disc of `ℂ` for its canonical orientation.
* `SymplecticGeometry.CoordinateDisc.ofChart`: the coordinate disc of an orientation-preserving
  chart of a smoothly oriented surface, on a ball in its target.

## Main results

* `SymplecticGeometry.CoordinateDisc.isCompact_disc`,
  `SymplecticGeometry.CoordinateDisc.isOpen_openDisc`,
  `SymplecticGeometry.CoordinateDisc.openDisc_subset_disc`.
* `SymplecticGeometry.CoordinateDisc.phase_boundaryCircle`,
  `SymplecticGeometry.CoordinateDisc.contMDiffOn_phase`,
  `SymplecticGeometry.CoordinateDisc.contMDiffOn_coe_phase`: the angular coordinate is `ζ` at the
  point `ζ` of the boundary circle, and it is `Cⁿ` off the centre where the coordinate is, as a
  map to `Circle` and as a map to `ℂ`.
* `SymplecticGeometry.CoordinateDisc.disc_diff_openDisc`: the closed disc minus the open disc is
  the boundary circle.
* `SymplecticGeometry.CoordinateDisc.exists_image_annulus_subset`: an open set around the boundary
  circle contains the image of a thin annulus `1 - ε < ‖z‖ < 1 + ε`.
* `SymplecticGeometry.CoordinateDisc.apply_boundaryCircle_eq_of_continuousOn`: a map continuous on
  the image of `ρ < ‖z‖ ≤ 1` and constant on the points of `ρ < ‖z‖ < 1` with angular coordinate
  `ζ` takes the same value at the point `ζ` of the boundary circle.
* `SymplecticGeometry.CoordinateDisc.disc_reverse`,
  `SymplecticGeometry.CoordinateDisc.openDisc_reverse`,
  `SymplecticGeometry.CoordinateDisc.boundaryLoop_reverse`: reversal keeps the discs and reverses
  the boundary loop (`Path.symm`).
* `SymplecticGeometry.CoordinateDisc.comap_affineBall_complexHomologicalOrientation`: the maps
  `z ↦ a + r z`, `r ≠ 0`, pull the canonical orientation of their codomain back to that of the
  ball.
* `SymplecticGeometry.CoordinateDisc.comap_eq_complexHomologicalOrientation`: when `M` is charted
  on `ℂ`, the orientation condition says that `o` pulls back to the canonical orientation of the
  ball.
* `SymplecticGeometry.CoordinateDisc.ofChart_apply`,
  `SymplecticGeometry.CoordinateDisc.ofChart_apply_zero`: the formula of `ofChart`, and its centre.
* `SymplecticGeometry.CoordinateDisc.contMDiffOn_coord_ofChart`: for a chart of the maximal atlas,
  the coordinate of `ofChart` is smooth on its range.
* `SymplecticGeometry.CoordinateDisc.disc_ofChart`,
  `SymplecticGeometry.CoordinateDisc.openDisc_ofChart`: the closed and the open disc of `ofChart`
  are the images under `e.symm` of the closed and the open ball of radius `r / 2` about `c`.
* `SymplecticGeometry.CoordinateDisc.range_ofChart`,
  `SymplecticGeometry.CoordinateDisc.range_ofChart_subset_source`: the image of `ofChart` is the
  image under `e.symm` of the ball of radius `r` about `c`, inside the source of `e`.
* `SymplecticGeometry.CoordinateDisc.add_smul_orthonormalBasisOneI_repr_mem_ball`,
  `SymplecticGeometry.CoordinateDisc.isOrientationPreservingAt_add_smul_orthonormalBasisOneI_repr`:
  the parametrization `w ↦ c + (r / 2) (re w, im w)` of `ofChart` maps the ball into `B(c, r)`
  and preserves the smooth orientations.
* `TauCeti.HomologicalOrientation.forall_localOrientationEquiv_eq_or_forall_eq_neg`: an open
  embedding of a connected open set of `ℂ` carries its canonical orientation to `o` at every point
  or to `-o` at every point.
* `SymplecticGeometry.CoordinateDisc.exists_coe_eq_or_exists_coe_eq`: an open embedding of the
  ball is a coordinate disc for `o` or for `-o`.
* `SymplecticGeometry.exists_coordinateDisc`: a coordinate disc centred at any point, inside any
  neighbourhood of it.
* `SymplecticGeometry.exists_coordinateDisc_pairwise_disjoint`: coordinate discs centred at
  finitely many distinct points, with pairwise disjoint images.
* `SymplecticGeometry.CoordinateDisc.exists_ofChart_pairwise_disjoint`: on a smoothly oriented
  surface, oriented charts of the maximal smooth atlas with pairwise disjoint sources about finitely
  many distinct points, whose coordinate discs `ofChart` are centred at these points.

## Implementation notes

The proof that `ofChart` preserves orientation adapts that of Tau Ceti's
`TauCeti.comap_complexHomologicalOrientation`: the chart `e`, read through the parametrization,
turns the disc into the inclusion of the ball, and
`OpenPartialHomeomorph.localHomologyMap_localOrientationOfOrientedChart` compares the local
orientations of the two charts.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7,
  where the first Chern number of a bundle over a surface is computed from trivializations over a
  disc and over its complement.
-/

public section

noncomputable section

open Module Topology TauCeti ComplexConjugate
open scoped Manifold

namespace SymplecticGeometry

namespace CoordinateDisc

/-- The open ball of radius `2` about `0` in `ℂ`, as an open set. Coordinate discs are defined on
it, and it carries the canonical orientation `TauCeti.complexHomologicalOrientation ball`. -/
def ball : TopologicalSpace.Opens ℂ :=
  ⟨Metric.ball 0 2, Metric.isOpen_ball⟩

@[simp]
theorem coe_ball : (ball : Set ℂ) = Metric.ball 0 2 :=
  (rfl)

/-- The ball of radius `2` of `ℂ` is connected. -/
instance : ConnectedSpace ball :=
  Subtype.connectedSpace (by simpa [coe_ball] using Metric.isConnected_ball (by norm_num))

@[simp]
theorem mem_ball_iff {z : ℂ} : z ∈ ball ↔ ‖z‖ < 2 := by
  rw [← SetLike.mem_coe, coe_ball, mem_ball_zero_iff]

theorem mem_ball_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) : z ∈ ball :=
  mem_ball_iff.2 (hz.trans_lt one_lt_two)

/-- The centre `0` of the ball of radius `2`, as a point of the ball. Coordinate discs are
centred at the image of this point. -/
instance : Zero ball :=
  ⟨⟨0, mem_ball_of_norm_le_one (by simp)⟩⟩

@[simp, norm_cast]
theorem coe_zero : ((0 : ball) : ℂ) = 0 :=
  (rfl)

theorem conj_mem_ball {z : ℂ} (hz : z ∈ ball) : conj z ∈ ball := by
  simpa using hz

/-- Complex conjugation, as a homeomorphism of the ball of radius `2`. -/
def conjBall : ball ≃ₜ ball :=
  Complex.conjCLE.toHomeomorph.subtype fun z ↦ by simp

@[simp]
theorem coe_conjBall_apply (z : ball) : (conjBall z : ℂ) = conj (z : ℂ) :=
  (rfl)

@[simp]
theorem conjBall_zero : conjBall 0 = 0 :=
  Subtype.ext (by simp)

@[simp]
theorem conjBall_conjBall (z : ball) : conjBall (conjBall z) = z :=
  Subtype.ext (by simp)

@[simp]
theorem symm_conjBall : conjBall.symm = conjBall :=
  Homeomorph.ext fun z ↦ conjBall.symm_apply_eq.2 (conjBall_conjBall z).symm

end CoordinateDisc

variable {M : Type} [TopologicalSpace M] [T2Space M] {E : Type} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]

open CoordinateDisc in
/-- A **coordinate disc** of a surface `M` with a homological orientation `o`: an open embedding
of the ball of radius `2` of `ℂ` into `M` that is orientation-preserving, in the sense that at
every point `z` of the ball it carries the canonical local orientation of the ball at `z`
(`TauCeti.complexHomologicalOrientation`) to the local orientation `o (toFun z)`. -/
structure CoordinateDisc (o : HomologicalOrientation M E 2) where
  /-- The map from the ball of radius `2` of `ℂ`. -/
  toFun : ball → M
  /-- The map is an open embedding. -/
  isOpenEmbedding' : IsOpenEmbedding toFun
  /-- The map carries the canonical local orientations of the ball to those of `o`. -/
  localOrientationEquiv_apply' (z : ball) :
    isOpenEmbedding'.localOrientationEquiv z 2 (complexHomologicalOrientation ball z) =
      o (toFun z)

namespace CoordinateDisc

variable {o : HomologicalOrientation M E 2}

instance : FunLike (CoordinateDisc o) ball M where
  coe := toFun
  coe_injective φ ψ h := by
    cases φ
    cases ψ
    congr

variable (φ : CoordinateDisc o)

@[simp]
theorem toFun_eq_coe : φ.toFun = φ :=
  (rfl)

@[simp]
theorem coe_mk (f : ball → M) (hf : IsOpenEmbedding f) (h) :
    ((⟨f, hf, h⟩ : CoordinateDisc o) : ball → M) = f :=
  (rfl)

/-- Two coordinate discs are equal when their maps are. -/
@[ext]
theorem ext {φ ψ : CoordinateDisc o} (h : ∀ z, φ z = ψ z) : φ = ψ :=
  DFunLike.ext _ _ h

theorem isOpenEmbedding : IsOpenEmbedding φ :=
  φ.isOpenEmbedding'

@[fun_prop]
theorem continuous : Continuous φ :=
  φ.isOpenEmbedding.continuous

theorem injective : Function.Injective φ :=
  φ.isOpenEmbedding.injective

/-- The orientation condition of a coordinate disc: the excision isomorphism of `φ` at `z` carries
the canonical local orientation of the ball at `z` to the local orientation of `o` at `φ z`. -/
@[simp]
theorem localOrientationEquiv_apply (z : ball) :
    φ.isOpenEmbedding.localOrientationEquiv z 2 (complexHomologicalOrientation ball z) = o (φ z) :=
  φ.localOrientationEquiv_apply' z

/-- The orientation condition of a coordinate disc, read on the ball: the canonical local
orientation of the ball at `z` is the one that corresponds to `o (φ z)`. -/
theorem complexHomologicalOrientation_apply (z : ball) :
    complexHomologicalOrientation ball z =
      (φ.isOpenEmbedding.localOrientationEquiv z 2).symm (o (φ z)) :=
  (Equiv.eq_symm_apply _).2 (φ.localOrientationEquiv_apply z)

/-! ### The closed and the open disc -/

/-- The closed disc of a coordinate disc: the image of the closed unit ball. -/
def disc : Set M :=
  φ '' {z | ‖(z : ℂ)‖ ≤ 1}

/-- The open disc of a coordinate disc: the image of the open unit ball. -/
def openDisc : Set M :=
  φ '' {z | ‖(z : ℂ)‖ < 1}

theorem disc_def : φ.disc = φ '' {z | ‖(z : ℂ)‖ ≤ 1} :=
  (rfl)

theorem openDisc_def : φ.openDisc = φ '' {z | ‖(z : ℂ)‖ < 1} :=
  (rfl)

theorem mem_disc_iff {x : M} : x ∈ φ.disc ↔ ∃ z : ball, ‖(z : ℂ)‖ ≤ 1 ∧ φ z = x :=
  Iff.rfl

theorem mem_openDisc_iff {x : M} : x ∈ φ.openDisc ↔ ∃ z : ball, ‖(z : ℂ)‖ < 1 ∧ φ z = x :=
  Iff.rfl

@[simp]
theorem apply_mem_disc_iff {z : ball} : φ z ∈ φ.disc ↔ ‖(z : ℂ)‖ ≤ 1 :=
  φ.injective.mem_set_image

@[simp]
theorem apply_mem_openDisc_iff {z : ball} : φ z ∈ φ.openDisc ↔ ‖(z : ℂ)‖ < 1 :=
  φ.injective.mem_set_image

/-- The centre of a coordinate disc lies in its open disc. -/
theorem apply_zero_mem_openDisc : φ 0 ∈ φ.openDisc :=
  φ.apply_mem_openDisc_iff.2 (by simp [coe_zero])

/-- The image of a closed ball of radius `ρ < 2` about the centre is compact. -/
theorem isCompact_image_closedBall {ρ : ℝ} (hρ : ρ < 2) :
    IsCompact (φ '' {z | ‖(z : ℂ)‖ ≤ ρ}) := by
  refine IsCompact.image ?_ φ.continuous
  rw [Subtype.isCompact_iff]
  convert isCompact_closedBall (0 : ℂ) ρ using 1
  ext w
  simp only [Set.mem_image, Set.mem_ofPred_eq, Subtype.exists, exists_and_right, exists_eq_right,
    mem_closedBall_zero_iff]
  exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨mem_ball_iff.2 (h.trans_lt hρ), h⟩⟩

theorem isCompact_disc : IsCompact φ.disc :=
  φ.isCompact_image_closedBall one_lt_two

theorem isOpen_openDisc : IsOpen φ.openDisc :=
  φ.isOpenEmbedding.isOpenMap _ <|
    (isOpen_lt continuous_subtypeVal.norm continuous_const : IsOpen {z : ball | ‖(z : ℂ)‖ < 1})

theorem openDisc_subset_disc : φ.openDisc ⊆ φ.disc :=
  Set.image_mono fun z (hz : ‖(z : ℂ)‖ < 1) ↦ hz.le

theorem disc_subset_range : φ.disc ⊆ Set.range φ :=
  Set.image_subset_range _ _

/-! ### The coordinate of a coordinate disc -/

/-- The coordinate of a coordinate disc: the inverse of `φ` on its range, as a map to `ℂ`, so
that `φ.coord (φ z) = z` (`coord_apply`). Its values off the range of `φ` are unspecified. -/
def coord : M → ℂ :=
  fun x ↦ ((φ.isOpenEmbedding.toOpenPartialHomeomorph φ).symm x : ℂ)

@[simp]
theorem coord_apply (z : ball) : φ.coord (φ z) = z :=
  congrArg Subtype.val (φ.isOpenEmbedding.toOpenPartialHomeomorph_left_inv φ)

/-- The coordinate of a coordinate disc is continuous on the range of `φ`. -/
theorem continuousOn_coord : ContinuousOn φ.coord (Set.range φ) :=
  continuous_subtypeVal.comp_continuousOn
    ((φ.isOpenEmbedding.toOpenPartialHomeomorph φ).continuousOn_symm.mono
      (by simp [IsOpenEmbedding.toOpenPartialHomeomorph_target]))

/-- The angular coordinate of a coordinate disc, as a point of the circle: `e^{iθ}` at
`φ (r e^{iθ})`, that is `w / ‖w‖` for `w = φ.coord x` when `w ≠ 0` (`coe_phase`). -/
def phase (x : M) : Circle :=
  Circle.exp (Complex.arg (φ.coord x))

theorem phase_def (x : M) : φ.phase x = Circle.exp (Complex.arg (φ.coord x)) :=
  (rfl)

theorem coe_phase {x : M} (hx : φ.coord x ≠ 0) : (φ.phase x : ℂ) = φ.coord x / ‖φ.coord x‖ := by
  rw [phase_def, Circle.coe_exp]
  exact Complex.exp_arg_mul_I hx

/-- At `φ z`, the angular coordinate is `exp (i arg z)`. -/
@[simp]
theorem phase_apply_self (z : ball) : φ.phase (φ z) = Circle.exp (Complex.arg z) := by
  rw [phase_def, coord_apply]

/-- At `φ z`, the angular coordinate is `z / ‖z‖`. -/
theorem coe_phase_apply {z : ball} (hz : (z : ℂ) ≠ 0) : (φ.phase (φ z) : ℂ) = z / ‖(z : ℂ)‖ := by
  rw [coe_phase φ (by rwa [coord_apply]), coord_apply]

/-- At a point `φ z` with `z = r ζ`, where `r > 0` and `|ζ| = 1`, the angular coordinate is
`ζ`. -/
theorem phase_apply_of_coe_eq_mul {z : ball} {r : ℝ} (hr : 0 < r) {ζ : Circle}
    (hz : (z : ℂ) = r * ζ) : φ.phase (φ z) = ζ := by
  rw [phase_apply_self, hz, Complex.arg_ofReal_mul hr, Circle.exp_arg]

/-- If the coordinate of a coordinate disc is `Cⁿ` on the range of `φ`, then its angular
coordinate, as a map to the circle, is `Cⁿ` on the points of that range where the coordinate does
not vanish. -/
theorem contMDiffOn_phase {n : WithTop ℕ∞}
    (hφ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) n φ.coord (Set.range φ)) :
    ContMDiffOn 𝓘(ℝ, E) (𝓡 1) n φ.phase {x ∈ Set.range φ | φ.coord x ≠ 0} :=
  (Circle.contMDiffOn_exp_arg.comp (hφ.mono (Set.sep_subset _ _)) fun _ hx ↦ hx.2).congr
    fun x _ ↦ φ.phase_def x

/-- If the coordinate of a coordinate disc is `Cⁿ` on the range of `φ`, then its angular
coordinate is `Cⁿ` on the points of that range where the coordinate does not vanish. -/
theorem contMDiffOn_coe_phase {n : WithTop ℕ∞}
    (hφ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) n φ.coord (Set.range φ)) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) n (fun x ↦ (φ.phase x : ℂ))
      {x ∈ Set.range φ | φ.coord x ≠ 0} := by
  have := finrank_real_complex_fact'
  exact (contMDiff_coe_sphere (E := ℂ) (n := 1)).comp_contMDiffOn (φ.contMDiffOn_phase hφ)

/-! ### The boundary circle -/

/-- The boundary circle of a coordinate disc: the unit circle of the chart, `z ↦ φ z`. -/
def boundaryCircle : C(Circle, M) where
  toFun z := φ ⟨z, mem_ball_of_norm_le_one (Circle.norm_coe z).le⟩
  continuous_toFun := by fun_prop

theorem boundaryCircle_apply (z : Circle) :
    φ.boundaryCircle z = φ ⟨z, mem_ball_of_norm_le_one (Circle.norm_coe z).le⟩ :=
  (rfl)

/-- The angular coordinate of the point `ζ` of the boundary circle is `ζ`. -/
@[simp]
theorem phase_boundaryCircle (ζ : Circle) : φ.phase (φ.boundaryCircle ζ) = ζ :=
  φ.phase_apply_of_coe_eq_mul one_pos (by simp)

@[simp]
theorem boundaryCircle_mem_disc (z : Circle) : φ.boundaryCircle z ∈ φ.disc := by
  simp [boundaryCircle_apply]

@[simp]
theorem boundaryCircle_notMem_openDisc (z : Circle) : φ.boundaryCircle z ∉ φ.openDisc := by
  simp [boundaryCircle_apply]

/-- The closed disc minus the open disc is the boundary circle. -/
theorem disc_diff_openDisc : φ.disc \ φ.openDisc = Set.range φ.boundaryCircle := by
  ext x
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hx⟩
    have h1 : ‖(z : ℂ)‖ = 1 := le_antisymm hz (not_lt.1 fun h ↦ hx ⟨z, h, rfl⟩)
    obtain ⟨c, hc⟩ : ∃ c : Circle, (c : ℂ) = z := ⟨⟨z, mem_sphere_zero_iff_norm.2 h1⟩, rfl⟩
    exact ⟨c, by rw [boundaryCircle_apply]; exact congrArg φ (Subtype.ext hc)⟩
  · rintro ⟨z, rfl⟩
    exact ⟨φ.boundaryCircle_mem_disc z, φ.boundaryCircle_notMem_openDisc z⟩

/-- An open set that contains the boundary circle of a coordinate disc contains the image of an
annulus `1 - ε < ‖z‖ < 1 + ε` of the ball, for some `0 < ε ≤ 1 / 2`. -/
theorem exists_image_annulus_subset {O : Set M} (hO : IsOpen O)
    (hφO : ∀ ζ, φ.boundaryCircle ζ ∈ O) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧
      ∀ z : ball, 1 - ε < ‖(z : ℂ)‖ → ‖(z : ℂ)‖ < 1 + ε → φ z ∈ O := by
  -- The points of the ball that `φ` sends into `O`, as an open set of `ℂ`, contain the circle.
  have hS : IsOpen (Subtype.val '' (φ ⁻¹' O) : Set ℂ) :=
    CoordinateDisc.ball.isOpen.isOpenMap_subtypeVal _ (hO.preimage φ.continuous)
  have hsph : Metric.sphere (0 : ℂ) 1 ⊆ Subtype.val '' (φ ⁻¹' O) := fun z hz ↦
    ⟨⟨z, mem_ball_of_norm_le_one (mem_sphere_zero_iff_norm.1 hz).le⟩,
      by have h := hφO (show Circle from ⟨z, hz⟩); rwa [boundaryCircle_apply] at h, rfl⟩
  obtain ⟨δ, hδ, hδS⟩ := (isCompact_sphere (0 : ℂ) 1).exists_thickening_subset_open hS hsph
  refine ⟨min δ (1 / 2), lt_min hδ one_half_pos, min_le_right _ _, fun z h₁ h₂ ↦ ?_⟩
  have hn : 0 < ‖(z : ℂ)‖ := by linarith [min_le_right δ (1 / 2)]
  -- `z` is within `δ` of the point `z / ‖z‖` of the circle.
  have hd : dist (z : ℂ) (z / ‖(z : ℂ)‖) < δ := by
    have he : (z : ℂ) - z / ‖(z : ℂ)‖ = (((‖(z : ℂ)‖ - 1) / ‖(z : ℂ)‖ : ℝ) : ℂ) * z := by
      have : (‖(z : ℂ)‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hn.ne'
      push_cast
      field_simp
    rw [dist_eq_norm, he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos hn, div_mul_cancel₀ _ hn.ne']
    have := min_le_left δ (1 / 2)
    exact abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  obtain ⟨w, hw, hwz⟩ := hδS (Metric.mem_thickening_iff.2
    ⟨(z : ℂ) / ‖(z : ℂ)‖, by simp [hn.ne'], hd⟩)
  rwa [Subtype.val_injective hwz] at hw

/-- A map that is continuous on the image of the half-open annulus `ρ < ‖z‖ ≤ 1`, for `ρ < 1`,
and constant on the points of the open annulus `ρ < ‖z‖ < 1` with angular coordinate `ζ`, takes
the same value at the point `φ.boundaryCircle ζ` of the boundary circle: it is the limit along the
ray through `ζ`. -/
theorem apply_boundaryCircle_eq_of_continuousOn {X : Type*} [TopologicalSpace X] [T1Space X]
    {ρ : ℝ} (hρ : ρ < 1) {f : M → X}
    (hf : ContinuousOn f (φ '' {z | ρ < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ ≤ 1})) {ζ : Circle} {c : X}
    (h : ∀ z : ball, ρ < ‖(z : ℂ)‖ → ‖(z : ℂ)‖ < 1 → φ.phase (φ z) = ζ → f (φ z) = c) :
    f (φ.boundaryCircle ζ) = c := by
  -- The ray through `ζ`, as a map from `[0, 1]` to the ball.
  let γ : unitInterval → ball := fun t ↦
    ⟨(t : ℝ) * ζ, mem_ball_of_norm_le_one (by simp [abs_le.2 ⟨by
      linarith [unitInterval.nonneg t], unitInterval.le_one t⟩])⟩
  have hnorm : ∀ t : unitInterval, ‖((γ t : ball) : ℂ)‖ = t := fun t ↦ by
    simp [γ, abs_of_nonneg (unitInterval.nonneg t)]
  have hγ1 : φ (γ 1) = φ.boundaryCircle ζ := by
    rw [boundaryCircle_apply]
    congr 1
    ext
    simp [γ]
  -- The open part of the ray beyond `ρ`, which has `1` in its closure.
  let T : Set unitInterval := {t | max ρ 0 < t ∧ (t : ℝ) < 1}
  have hT : Subtype.val '' T = Set.Ioo (max ρ 0) 1 := by
    ext x
    refine ⟨fun ⟨_, ht, hx⟩ ↦ hx ▸ ht, fun hx ↦
      ⟨⟨x, (le_max_right ρ 0).trans hx.1.le, hx.2.le⟩, hx, rfl⟩⟩
  have hmem : (1 : unitInterval) ∈ closure T := by
    rw [closure_subtype, hT, closure_Ioo (max_lt hρ one_pos).ne]
    exact ⟨(max_lt hρ one_pos).le, le_rfl⟩
  have hmaps : Set.MapsTo (φ ∘ γ) (insert 1 T) (φ '' {z | ρ < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ ≤ 1}) :=
    fun t ht ↦ ⟨γ t, ⟨by
      rw [hnorm]
      rcases ht with rfl | ht
      · exact hρ
      · exact (le_max_left ρ 0).trans_lt ht.1, by rw [hnorm]; exact unitInterval.le_one t⟩, rfl⟩
  have hcont : ContinuousWithinAt (f ∘ φ ∘ γ) T 1 :=
    ((hf.comp (φ.continuous.comp (by fun_prop : Continuous γ)).continuousOn hmaps) 1
      (Set.mem_insert _ _)).mono (Set.subset_insert _ _)
  rw [← hγ1]
  refine hcont.eq_const_of_mem_closure hmem fun t ht ↦ h (γ t)
    (by rw [hnorm]; exact (le_max_left ρ 0).trans_lt ht.1) (by rw [hnorm]; exact ht.2)
    (φ.phase_apply_of_coe_eq_mul ((le_max_right ρ 0).trans_lt ht.1) (by simp [γ]))

/-- The boundary loop of a coordinate disc, `t ↦ φ(e^{2πit})`, based at `φ.boundaryCircle 1`.
It runs counterclockwise in the chart, so it is oriented as the boundary of the closed disc. -/
def boundaryLoop : Path (φ.boundaryCircle 1) (φ.boundaryCircle 1) :=
  φ.boundaryCircle.toBasedLoop

theorem boundaryLoop_def : φ.boundaryLoop = φ.boundaryCircle.toBasedLoop :=
  (rfl)

@[simp]
theorem boundaryLoop_apply (t : unitInterval) :
    φ.boundaryLoop t = φ.boundaryCircle (Circle.exp (2 * Real.pi * t)) := by
  rw [boundaryLoop_def, ContinuousMap.toBasedLoop_apply, unitToCircle_apply]

theorem boundaryLoop_mem_disc (t : unitInterval) : φ.boundaryLoop t ∈ φ.disc := by
  rw [boundaryLoop_apply]
  exact φ.boundaryCircle_mem_disc _

theorem boundaryLoop_notMem_openDisc (t : unitInterval) : φ.boundaryLoop t ∉ φ.openDisc := by
  rw [boundaryLoop_apply]
  exact φ.boundaryCircle_notMem_openDisc _

/-! ### Contraction of the boundary loop -/

private theorem norm_radialLoop_le_one (p : unitInterval × unitInterval) :
    ‖((1 - (p.1 : ℝ) : ℝ) : ℂ) * Circle.exp (2 * Real.pi * p.2)‖ ≤ 1 := by
  rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.2 p.1.prop.2)]
  linarith [p.1.prop.1]

/-- The radial contraction of the boundary loop inside the closed disc: at time `s`, the loop
`t ↦ φ((1 - s) e^{2πit})`. It starts at the boundary loop (`discContraction_zero`), ends at the
constant loop at the centre (`discContraction_one`), and is a loop at every time
(`discContraction_apply_zero`). -/
def discContraction : C(unitInterval × unitInterval, φ.disc) where
  toFun p := ⟨φ ⟨_, mem_ball_of_norm_le_one (norm_radialLoop_le_one p)⟩,
    φ.apply_mem_disc_iff.2 (norm_radialLoop_le_one p)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (φ.continuous.comp (Continuous.subtype_mk ?_ _)) _
    fun_prop

/-- At time `0`, the radial contraction is the boundary loop. -/
theorem discContraction_zero (t : unitInterval) :
    φ.discContraction (0, t) = ⟨φ.boundaryLoop t, φ.boundaryLoop_mem_disc t⟩ := by
  refine Subtype.ext ?_
  simp only [discContraction, ContinuousMap.coe_mk, boundaryLoop_apply, boundaryCircle_apply]
  congr 2
  simp

/-- At time `1`, the radial contraction is the constant loop at the centre. -/
theorem discContraction_one (t : unitInterval) :
    φ.discContraction (1, t) = ⟨φ 0, φ.openDisc_subset_disc φ.apply_zero_mem_openDisc⟩ := by
  refine Subtype.ext ?_
  simp only [discContraction, ContinuousMap.coe_mk]
  congr 1
  ext
  simp [coe_zero]

/-- At every time, the radial contraction is a loop. -/
theorem discContraction_apply_zero (s : unitInterval) :
    φ.discContraction (s, 0) = φ.discContraction (s, 1) := by
  simp [discContraction]

/-! ### Reversal -/

/-- The **reverse** of a coordinate disc `φ` for `o`: the coordinate disc `φ ∘ conj` for the
opposite orientation `-o`. Conjugation maps the ball of radius `2` to itself and reverses its
canonical orientation (`TauCeti.comap_conj_complexHomologicalOrientation`). -/
def reverse : CoordinateDisc (-o) where
  toFun := φ ∘ conjBall
  isOpenEmbedding' := φ.isOpenEmbedding.comp conjBall.isOpenEmbedding
  localOrientationEquiv_apply' z := by
    have h := HomologicalOrientation.localOrientationEquiv_comap_apply
      (complexHomologicalOrientation ball) conjBall.isOpenEmbedding z
    rw [comap_conj_complexHomologicalOrientation _ coe_conjBall_apply,
      HomologicalOrientation.neg_apply, IsOpenEmbedding.localOrientationEquiv_neg,
      neg_eq_iff_eq_neg] at h
    rw [← IsOpenEmbedding.localOrientationEquiv_trans conjBall.isOpenEmbedding φ.isOpenEmbedding,
      Equiv.trans_apply, h, IsOpenEmbedding.localOrientationEquiv_neg,
      φ.localOrientationEquiv_apply, HomologicalOrientation.neg_apply]
    -- `(φ ∘ conjBall) z` is `φ (conjBall z)`; `rw [Function.comp_apply]` fails here, since the
    -- type of a local orientation depends on its point.
    rfl

theorem coe_reverse : ⇑φ.reverse = φ ∘ conjBall :=
  (rfl)

@[simp]
theorem reverse_apply (z : ball) : φ.reverse z = φ (conjBall z) :=
  (rfl)

/-- The reverse of a coordinate disc has the same centre. -/
theorem reverse_apply_zero : φ.reverse 0 = φ 0 := by
  simp

/-- Reversing a coordinate disc twice gives back its map. The discs themselves cannot be compared
by `=`, since they lie in `CoordinateDisc (-(-o))` and in `CoordinateDisc o`. -/
@[simp]
theorem coe_reverse_reverse : ⇑φ.reverse.reverse = φ := by
  ext z
  simp

/-- The reverse of a coordinate disc has the same image of every set of the ball that conjugation
maps to itself. -/
theorem image_reverse {s : Set ball} (hs : ∀ z, conjBall z ∈ s ↔ z ∈ s) :
    φ.reverse '' s = φ '' s := by
  rw [coe_reverse, Set.image_comp]
  congr 1
  ext z
  exact ⟨fun ⟨w, hw, hwz⟩ ↦ hwz ▸ (hs w).2 hw, fun hz ↦ ⟨conjBall z, (hs z).2 hz, by simp⟩⟩

@[simp]
theorem disc_reverse : φ.reverse.disc = φ.disc :=
  φ.image_reverse fun z ↦ by simp

@[simp]
theorem openDisc_reverse : φ.reverse.openDisc = φ.openDisc :=
  φ.image_reverse fun z ↦ by simp

/-- The boundary circle of the reverse of `φ` is that of `φ`, run through `z ↦ z⁻¹ = conj z`. -/
@[simp]
theorem boundaryCircle_reverse_apply (z : Circle) :
    φ.reverse.boundaryCircle z = φ.boundaryCircle z⁻¹ := by
  rw [boundaryCircle_apply, boundaryCircle_apply, reverse_apply]
  congr 1
  ext
  simp only [coe_conjBall_apply, Circle.coe_inv_eq_conj]

theorem boundaryCircle_reverse_one : φ.reverse.boundaryCircle 1 = φ.boundaryCircle 1 := by
  simp

/-- The boundary loop of the reverse of `φ` is `t ↦ φ(e^{-2πit})`, the boundary loop of `φ` run
backwards in time. -/
theorem boundaryLoop_reverse_apply (t : unitInterval) :
    φ.reverse.boundaryLoop t = φ.boundaryLoop (unitInterval.symm t) := by
  rw [boundaryLoop_apply, boundaryLoop_apply, boundaryCircle_reverse_apply,
    unitInterval.coe_symm_eq, mul_sub, mul_one, Circle.exp_sub, Circle.exp_two_pi, one_div]

/-- The boundary loop of the reverse of `φ` is the reversal `Path.symm` of the boundary loop of `φ`,
up to the equality of their base points. -/
theorem boundaryLoop_reverse :
    φ.reverse.boundaryLoop =
      φ.boundaryLoop.symm.cast φ.boundaryCircle_reverse_one φ.boundaryCircle_reverse_one := by
  ext t
  exact φ.boundaryLoop_reverse_apply t


/-! ### Smaller discs and restriction to an open set -/

/-- A point `a + r z`, for `z` in the ball of radius `2`, `r > 0` and `‖a‖ + 2 r ≤ 2`, lies in
the ball. -/
theorem add_mul_mem_ball {a : ℂ} {r : ℝ} (hr : 0 < r) (h : ‖a‖ + 2 * r ≤ 2) (z : ball) :
    a + r * (z : ℂ) ∈ ball :=
  mem_ball_iff.2 <| by
    calc ‖a + r * (z : ℂ)‖ ≤ ‖a‖ + r * ‖(z : ℂ)‖ := by
          simpa [norm_mul, abs_of_pos hr] using norm_add_le a (r * (z : ℂ))
      _ < ‖a‖ + r * 2 := by gcongr; exact mem_ball_iff.1 z.property
      _ ≤ 2 := by linarith

/-- The affine map `z ↦ a + r z` of the ball of radius `2` into an open set `V` of `ℂ` that
contains its image. For `V = ball`, `add_mul_mem_ball` gives the condition on the image. -/
def affineBall {V : TopologicalSpace.Opens ℂ} (a : ℂ) {r : ℝ}
    (h : ∀ z : ball, a + r * (z : ℂ) ∈ V) : ball → V :=
  fun z ↦ ⟨a + r * z, h z⟩

@[simp]
theorem coe_affineBall_apply {V : TopologicalSpace.Opens ℂ} (a : ℂ) {r : ℝ}
    (h : ∀ z : ball, a + r * (z : ℂ) ∈ V) (z : ball) :
    (affineBall a h z : ℂ) = a + r * z :=
  (rfl)

private theorem subtypeVal_comp_affineBall {V : TopologicalSpace.Opens ℂ} (a : ℂ) {r : ℝ}
    (h : ∀ z : ball, a + r * (z : ℂ) ∈ V) (hr : r ≠ 0) :
    Subtype.val ∘ affineBall a h =
      Diffeomorph.smulAdd 1 (r : ℂ) a (Complex.ofReal_ne_zero.2 hr) ∘ Subtype.val := by
  ext z
  simp [add_comm]

theorem isOpenEmbedding_affineBall {V : TopologicalSpace.Opens ℂ} (a : ℂ) {r : ℝ}
    (h : ∀ z : ball, a + r * (z : ℂ) ∈ V) (hr : r ≠ 0) :
    IsOpenEmbedding (affineBall a h) :=
  (IsOpenEmbedding.of_comp_iff _ V.isOpenEmbedding').1 <| by
    rw [subtypeVal_comp_affineBall a h hr]
    exact (Diffeomorph.smulAdd 1 (r : ℂ) a
      (Complex.ofReal_ne_zero.2 hr)).toHomeomorph.isOpenEmbedding.comp ball.isOpenEmbedding'

/-- The affine map `z ↦ a + r z`, `r ≠ 0`, of the ball into an open set `V` of `ℂ` pulls the
canonical orientation of `V` back to that of the ball. -/
theorem comap_affineBall_complexHomologicalOrientation {V : TopologicalSpace.Opens ℂ} (a : ℂ)
    {r : ℝ} (h : ∀ z : ball, a + r * (z : ℂ) ∈ V) (hr : r ≠ 0) :
    (complexHomologicalOrientation V).comap (isOpenEmbedding_affineBall a h hr) =
      complexHomologicalOrientation ball :=
  let T := Diffeomorph.smulAdd 1 (r : ℂ) a (Complex.ofReal_ne_zero.2 hr)
  comap_complexHomologicalOrientation_of_comp_eq _ T.toHomeomorph.isOpenEmbedding
    T.isLocalDiffeomorph (subtypeVal_comp_affineBall a h hr)

/-- Let `g` be an open embedding of an open set `U` of `ℂ` into `M` that carries the canonical
orientation of `U` to `o` at every point, and `f` an open embedding of the ball into `U` that
pulls the canonical orientation of `U` back to that of the ball. Then `z ↦ g (f z)` is a
coordinate disc. -/
def ofComp {U : TopologicalSpace.Opens ℂ} (g : U → M) (hg : IsOpenEmbedding g)
    (hgo : ∀ w, hg.localOrientationEquiv w 2 (complexHomologicalOrientation U w) = o (g w))
    (f : ball → U) (hf : IsOpenEmbedding f)
    (h : (complexHomologicalOrientation U).comap hf = complexHomologicalOrientation ball) :
    CoordinateDisc o where
  toFun z := g (f z)
  isOpenEmbedding' := hg.comp hf
  localOrientationEquiv_apply' z := by
    have h' := HomologicalOrientation.localOrientationEquiv_comap_apply
      (complexHomologicalOrientation U) hf z
    rw [h] at h'
    rw [← IsOpenEmbedding.localOrientationEquiv_trans hf hg, Equiv.trans_apply, h', hgo]

@[simp]
theorem ofComp_apply {U : TopologicalSpace.Opens ℂ} (g : U → M) (hg : IsOpenEmbedding g)
    (hgo : ∀ w, hg.localOrientationEquiv w 2 (complexHomologicalOrientation U w) = o (g w))
    (f : ball → U) (hf : IsOpenEmbedding f)
    (h : (complexHomologicalOrientation U).comap hf = complexHomologicalOrientation ball)
    (z : ball) : ofComp g hg hgo f hf h z = g (f z) :=
  (rfl)

/-- Precomposing a coordinate disc with an open embedding of the ball into itself that preserves
its canonical orientation gives a coordinate disc. -/
def comp (f : ball → ball) (hf : IsOpenEmbedding f)
    (h : (complexHomologicalOrientation ball).comap hf = complexHomologicalOrientation ball) :
    CoordinateDisc o :=
  ofComp φ φ.isOpenEmbedding φ.localOrientationEquiv_apply f hf h

@[simp]
theorem comp_apply (f : ball → ball) (hf : IsOpenEmbedding f)
    (h : (complexHomologicalOrientation ball).comap hf = complexHomologicalOrientation ball)
    (z : ball) : φ.comp f hf h z = φ (f z) :=
  (rfl)

/-- A coordinate disc whose image lies in an open set `U`, as a coordinate disc of `U` for the
restriction of the orientation. -/
def restrict (U : TopologicalSpace.Opens M) (hU : Set.range φ ⊆ U) :
    CoordinateDisc (o.comap U.isOpenEmbedding') where
  toFun z := ⟨φ z, hU (Set.mem_range_self z)⟩
  isOpenEmbedding' := (IsOpenEmbedding.of_comp_iff _ U.isOpenEmbedding').1
    φ.isOpenEmbedding
  localOrientationEquiv_apply' z := by
    apply (U.isOpenEmbedding'.localOrientationEquiv _ 2).injective
    rw [HomologicalOrientation.localOrientationEquiv_comap_apply, ← Equiv.trans_apply,
      IsOpenEmbedding.localOrientationEquiv_trans]
    exact φ.localOrientationEquiv_apply z

@[simp]
theorem coe_restrict_apply (U : TopologicalSpace.Opens M) (hU : Set.range φ ⊆ U) (z : ball) :
    (φ.restrict U hU z : M) = φ z :=
  (rfl)
end CoordinateDisc

/-! ### Surfaces charted on `ℂ` -/

namespace CoordinateDisc

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
  {o : HomologicalOrientation M ℂ 2}

/-- For a surface charted on `ℂ`, the orientation condition of a coordinate disc says that `o`
pulls back along it to the canonical orientation of the ball. -/
theorem comap_eq_complexHomologicalOrientation (φ : CoordinateDisc o) :
    o.comap φ.isOpenEmbedding = complexHomologicalOrientation ball := by
  ext z : 1
  rw [HomologicalOrientation.comap_apply, φ.complexHomologicalOrientation_apply]

/-- For a surface charted on `ℂ`, an open embedding of the ball along which `o` pulls back to the
canonical orientation of the ball is a coordinate disc. -/
def ofComapEq (f : ball → M) (hf : IsOpenEmbedding f)
    (h : o.comap hf = complexHomologicalOrientation ball) : CoordinateDisc o where
  toFun := f
  isOpenEmbedding' := hf
  localOrientationEquiv_apply' z := by
    rw [← h, HomologicalOrientation.localOrientationEquiv_comap_apply]

@[simp]
theorem coe_ofComapEq (f : ball → M) (hf : IsOpenEmbedding f)
    (h : o.comap hf = complexHomologicalOrientation ball) : ⇑(ofComapEq f hf h) = f :=
  (rfl)

/-- The inclusion of the ball of radius `2` into `ℂ`, a coordinate disc of `ℂ` for its canonical
orientation. -/
def subtypeVal : CoordinateDisc (complexHomologicalOrientation ℂ) :=
  ofComapEq Subtype.val ball.isOpen.isOpenEmbedding_subtypeVal
    (comap_subtypeVal_complexHomologicalOrientation _)

@[simp]
theorem coe_subtypeVal : ⇑subtypeVal = (Subtype.val : ball → ℂ) :=
  (rfl)

@[simp]
theorem disc_subtypeVal : subtypeVal.disc = Metric.closedBall 0 1 := by
  ext w
  simp only [mem_disc_iff, coe_subtypeVal, Subtype.exists, exists_and_left, exists_prop,
    exists_eq_right_right, mem_closedBall_zero_iff]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, mem_ball_of_norm_le_one h⟩⟩

@[simp]
theorem openDisc_subtypeVal : subtypeVal.openDisc = Metric.ball 0 1 := by
  ext w
  simp only [mem_openDisc_iff, coe_subtypeVal, Subtype.exists, exists_and_left, exists_prop,
    exists_eq_right_right, mem_ball_zero_iff]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, mem_ball_of_norm_le_one h.le⟩⟩

end CoordinateDisc

/-! ### Coordinate discs from oriented charts -/

namespace CoordinateDisc

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) 1 M] {o : Manifold.Orientation (𝓡 2) M (Fin 2)}

/-- The linear part `w ↦ (r / 2) (re w, im w)` of the parametrization of a coordinate disc from a
chart. -/
private def ofChartLinearEquiv {r : ℝ} (hr : 0 < r) : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.trans
    (ContinuousLinearEquiv.smulLeft (Units.mk0 (r / 2) (by positivity)))

/-- The affine homeomorphism `w ↦ c + (r / 2) (re w, im w)`, which sends the ball of radius `2`
into the ball of radius `r` about `c` (`ofChartHomeomorph_mem_ball`). -/
private def ofChartHomeomorph (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) :
    ℂ ≃ₜ EuclideanSpace ℝ (Fin 2) :=
  (ofChartLinearEquiv hr).toHomeomorph.trans (Homeomorph.addLeft c)

private theorem ofChartHomeomorph_apply (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r)
    (w : ℂ) : ofChartHomeomorph c hr w = c + (r / 2) • Complex.orthonormalBasisOneI.repr w :=
  (rfl)

private theorem coe_ofChartHomeomorph (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) :
    ⇑(ofChartHomeomorph c hr) =
      (c + ·) ∘ ((r / 2) • ·) ∘ ⇑Complex.orthonormalBasisOneI.repr :=
  funext (ofChartHomeomorph_apply c hr)

/-- The parametrization sends the ball of radius `s` about `0` to the ball of radius `r / 2 * s`
about `c`. -/
private theorem image_ofChartHomeomorph_ball (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r)
    (s : ℝ) : ofChartHomeomorph c hr '' Metric.ball 0 s = Metric.ball c (r / 2 * s) := by
  rw [coe_ofChartHomeomorph, Set.image_comp, Set.image_comp, LinearIsometryEquiv.image_ball,
    map_zero, Set.image_smul, smul_ball (by positivity), smul_zero, Set.image_add_left,
    preimage_add_ball, sub_neg_eq_add, zero_add, Real.norm_of_nonneg (by positivity)]

/-- The parametrization sends the closed ball of radius `s` about `0` to the closed ball of radius
`r / 2 * s` about `c`. -/
private theorem image_ofChartHomeomorph_closedBall (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ}
    (hr : 0 < r) (s : ℝ) :
    ofChartHomeomorph c hr '' Metric.closedBall 0 s = Metric.closedBall c (r / 2 * s) := by
  rw [coe_ofChartHomeomorph, Set.image_comp, Set.image_comp,
    LinearIsometryEquiv.image_closedBall, map_zero, Set.image_smul,
    smul_closedBall' (by positivity), smul_zero, Set.image_add_left, preimage_add_closedBall,
    sub_neg_eq_add, zero_add, Real.norm_of_nonneg (by positivity)]

/-- For `r > 0`, the map `w ↦ c + (r / 2) (re w, im w)` sends the ball of radius `2` of `ℂ` into
the ball of radius `r` about `c`. -/
theorem add_smul_orthonormalBasisOneI_repr_mem_ball (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ}
    (hr : 0 < r) (z : ball) :
    c + (r / 2) • Complex.orthonormalBasisOneI.repr (z : ℂ) ∈ Metric.ball c r := by
  rw [add_mem_ball_iff_norm, norm_smul, LinearIsometryEquiv.norm_map,
    Real.norm_of_nonneg (by positivity)]
  nlinarith [mem_ball_iff.1 z.property]

private theorem ofChartHomeomorph_mem_ball {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r)
    (z : ball) : ofChartHomeomorph c hr z ∈ Metric.ball c r := by
  rw [ofChartHomeomorph_apply]
  exact add_smul_orthonormalBasisOneI_repr_mem_ball c hr z

private theorem hasFDerivAt_ofChartHomeomorph_symm (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ}
    (hr : 0 < r) (y : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (ofChartHomeomorph c hr).symm
      ((ofChartLinearEquiv hr).symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ) y := by
  have h := ((ofChartLinearEquiv hr).symm.hasFDerivAt (x := -c + y)).comp y
    ((hasFDerivAt_id y).const_add (-c))
  rwa [ContinuousLinearMap.comp_id] at h

private theorem hasFDerivAt_ofChartHomeomorph (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ}
    (hr : 0 < r) (w : ℂ) :
    HasFDerivAt (ofChartHomeomorph c hr)
      ((ofChartLinearEquiv hr) : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 2)) w :=
  -- By definition, `ofChartHomeomorph c hr` is `ofChartLinearEquiv hr` followed by `c + ·`.
  ((ofChartLinearEquiv hr).hasFDerivAt (x := w)).const_add c

/-- The linear part of the parametrization carries the standard orientation of `ℂ` to that of
`ℝ²`: it is `Complex.orthonormalBasisOneI.repr` followed by a positive homothety. -/
private theorem orientation_map_ofChartLinearEquiv {r : ℝ} (hr : 0 < r) :
    Complex.orientation.map (Fin 2) (ofChartLinearEquiv hr).toLinearEquiv =
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation := by
  have hs : ((ContinuousLinearEquiv.smulLeft (Units.mk0 (r / 2) (by positivity))) :
      EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2)).toLinearEquiv =
        LinearEquiv.smulOfNeZero ℝ _ (r / 2) (by positivity) := by
    ext
    simp
  -- The underlying linear equivalence of `Complex.orthonormalBasisOneI.repr`, through either
  -- coercion.
  have hrepr : Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.toLinearEquiv =
      Complex.orthonormalBasisOneI.repr.toLinearEquiv :=
    (rfl)
  rw [ofChartLinearEquiv, ContinuousLinearEquiv.trans_toLinearEquiv, Orientation.map_trans,
    hrepr, Complex.orientation_map_orthonormalBasisOneI_repr, hs,
    Orientation.map_smulOfNeZero_of_pos _ (by positivity)]

/-- **The parametrization of a coordinate disc from a chart preserves orientation.** For `r > 0`,
the map `w ↦ c + (r / 2) (re w, im w)` from the ball of radius `2` of `ℂ` to `ℝ²` preserves
orientation at every point, from the standard orientation of `ℂ` restricted to the ball to the
standard orientation of `ℝ²`. -/
theorem isOrientationPreservingAt_add_smul_orthonormalBasisOneI_repr
    (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) (z : ball) :
    Manifold.Orientation.IsOrientationPreservingAt
      (Manifold.Orientation.complex.restrict ball)
      (Manifold.Orientation.euclideanSpace 2)
      (fun w : ball ↦ c + (r / 2) • Complex.orthonormalBasisOneI.repr (w : ℂ)) z := by
  have hf : (fun w : ball ↦ c + (r / 2) • Complex.orthonormalBasisOneI.repr (w : ℂ)) =
      ofChartHomeomorph c hr ∘ Subtype.val :=
    funext fun w ↦ (ofChartHomeomorph_apply c hr w).symm
  rw [hf]
  refine Manifold.Orientation.IsOrientationPreservingAt.comp ?_
    (Manifold.Orientation.isOrientationPreservingAt_restrict _ ball z)
  refine (Manifold.Orientation.isOrientationPreservingAt_iff_of_coe_eq _ _ _ _
    (ofChartLinearEquiv hr) (hasFDerivAt_ofChartHomeomorph c hr z).hasMFDerivAt.mfderiv.symm).2 ?_
  rw [Manifold.Orientation.orientationAt_complex, Manifold.Orientation.orientationAt_euclideanSpace]
  exact orientation_map_ofChartLinearEquiv hr

/-- At a point `x` where the chart `e` preserves orientation, the local orientation of `o` is the
one selected by the standard orientation of `ℂ` in `e` read through the parametrization. -/
private theorem toHomologicalOrientation_apply_ofChart
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (c : EuclideanSpace ℝ (Fin 2))
    {r : ℝ} (hr : 0 < r) {x : M}
    (he : o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x)
    (hx : x ∈ (e.transHomeomorph (ofChartHomeomorph c hr).symm).source) :
    o.toHomologicalOrientation finrank_euclideanSpace_fin x =
      (e.transHomeomorph (ofChartHomeomorph c hr).symm).localOrientationOfOrientedChart hx
        Complex.orientation Complex.finrank_real_complex := by
  obtain ⟨D, hD, hω⟩ := (Manifold.Orientation.isOrientationPreservingAt_iff _ _ _ _).1 he
  -- `D` is the derivative of `e` at `x`, between tangent spaces that are `ℝ²`.
  let D' : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) := D
  have hfd : HasFDerivAt (e ∘ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm)
      (D' : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
      (chartAt (EuclideanSpace ℝ (Fin 2)) x x) :=
    TauCeti.hasMFDerivAt_iff_hasFDerivAt_comp_chartAt_symm.1
      (hD ▸ (mdifferentiableAt_of_isInvertible_mfderiv ⟨D, hD⟩).hasMFDerivAt)
  have h := (hasFDerivAt_ofChartHomeomorph_symm c hr _).comp _ hfd
  rw [ContinuousLinearEquiv.comp_coe] at h
  refine Manifold.Orientation.toHomologicalOrientation_apply_eq_localOrientationOfOrientedChart
    finrank_euclideanSpace_fin o Complex.finrank_real_complex _ hx _ h ?_
  -- The orientation of `ℝ²` that `D` gives goes to that of `ℂ`.
  have key (ω : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2))
      (hω : ω.map (Fin 2) D'.toLinearEquiv =
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation) :
      ω.map (Fin 2) (D'.trans (ofChartLinearEquiv hr).symm).toLinearEquiv =
        Complex.orientation := by
    rw [ContinuousLinearEquiv.trans_toLinearEquiv, ContinuousLinearEquiv.toLinearEquiv_symm,
      Orientation.map_trans, hω, ← Orientation.map_symm, Equiv.symm_apply_eq,
      orientation_map_ofChartLinearEquiv]
  exact key _ (hω.trans (Manifold.Orientation.orientationAt_euclideanSpace 2 _))

/-- **The coordinate disc of an oriented chart.** Let `e` be a chart of a smoothly oriented surface
`M` that preserves orientation at every point of its source, from `o` to the standard orientation
of `ℝ²`, and let the ball of radius `r` about `c` lie in its target. Then
`z ↦ e.symm (c + (r / 2) (re z, im z))` is a coordinate disc for `o.toHomologicalOrientation`,
with centre `e.symm c` (`ofChart_apply_zero`). The identification `z ↦ (re z, im z)`
(`Complex.orthonormalBasisOneI.repr`) carries the standard
orientation of `ℂ` to that of `ℝ²`. -/
def ofChart (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r) (hc : Metric.ball c r ⊆ e.target)
    (he : ∀ x ∈ e.source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x) :
    CoordinateDisc (o.toHomologicalOrientation finrank_euclideanSpace_fin) where
  toFun z := e.symm (ofChartHomeomorph c hr z)
  isOpenEmbedding' := by
    refine e.symm.isOpenEmbedding_comp ((ofChartHomeomorph c hr).isOpenEmbedding.comp
      ball.isOpen.isOpenEmbedding_subtypeVal) ?_
    rintro _ ⟨z, rfl⟩
    exact hc (ofChartHomeomorph_mem_ball hr z)
  localOrientationEquiv_apply' z := by
    have hz : ofChartHomeomorph c hr z ∈ e.target := hc (ofChartHomeomorph_mem_ball hr z)
    have hx : e.symm (ofChartHomeomorph c hr z) ∈
        (e.transHomeomorph (ofChartHomeomorph c hr).symm).source := by
      simpa using e.map_target hz
    apply Subtype.ext
    rw [toHomologicalOrientation_apply_ofChart e c hr (he _ (e.map_target hz)) hx,
      TauCeti.complexHomologicalOrientation_apply, IsOpenEmbedding.coe_localOrientationEquiv,
      localHomologyIsoOfIsOpenEmbedding_hom]
    -- Read through the parametrization, `e` sends the disc to the inclusion of the ball.
    refine OpenPartialHomeomorph.localHomologyMap_localOrientationOfOrientedChart _ _ _ _ _
      (mem_chart_source ℂ z) hx (Filter.Eventually.of_forall fun w ↦ ?_) _
    simp [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_coe,
      e.right_inv (hc (ofChartHomeomorph_mem_ball hr w))]

private theorem ofChart_apply_eq (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r) (hc : Metric.ball c r ⊆ e.target)
    (he : ∀ x ∈ e.source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x) (z : ball) :
    ofChart e hr hc he z = e.symm (ofChartHomeomorph c hr z) :=
  (rfl)

private theorem coe_ofChart (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r) (hc : Metric.ball c r ⊆ e.target)
    (he : ∀ x ∈ e.source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x) :
    ⇑(ofChart e hr hc he) = e.symm ∘ ofChartHomeomorph c hr ∘ Subtype.val :=
  funext (ofChart_apply_eq e hr hc he)

/-- The coordinate disc of a chart is `z ↦ e.symm (c + (r / 2) (re z, im z))`. -/
@[simp]
theorem ofChart_apply (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r) (hc : Metric.ball c r ⊆ e.target)
    (he : ∀ x ∈ e.source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x) (z : ball) :
    ofChart e hr hc he z = e.symm (c + (r / 2) • Complex.orthonormalBasisOneI.repr z) :=
  (ofChart_apply_eq e hr hc he z).trans (congrArg e.symm (ofChartHomeomorph_apply c hr z))

/-- The coordinate of the coordinate disc of a chart `e` of the maximal `Cⁿ` atlas is `Cⁿ` on its
range: there it is `e` followed by an affine map. -/
theorem contMDiffOn_coord_ofChart {n : WithTop ℕ∞} [IsManifold (𝓡 2) n M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) {c : EuclideanSpace ℝ (Fin 2)}
    {r : ℝ} (hr : 0 < r) (hc : Metric.ball c r ⊆ e.target)
    (he : ∀ x ∈ e.source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x)
    (he' : e ∈ IsManifold.maximalAtlas (𝓡 2) n M) :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) n (ofChart e hr hc he).coord (Set.range (ofChart e hr hc he)) := by
  -- By definition of `ofChartHomeomorph`, its inverse is the affine map `y ↦ L⁻¹ (-c + y)`.
  have hL : ContDiff ℝ n (ofChartHomeomorph c hr).symm :=
    (ofChartLinearEquiv hr).symm.contDiff.comp (contDiff_const.add contDiff_id)
  refine ((hL.contMDiff.comp_contMDiffOn (contMDiffOn_of_mem_maximalAtlas he')).mono ?_).congr ?_
  · rintro _ ⟨z, rfl⟩
    rw [ofChart_apply_eq]
    exact e.map_target (hc (ofChartHomeomorph_mem_ball hr z))
  · rintro _ ⟨z, rfl⟩
    rw [coord_apply, Function.comp_apply, ofChart_apply_eq,
      e.right_inv (hc (ofChartHomeomorph_mem_ball hr z)), Homeomorph.symm_apply_apply]

/-- The centre of the coordinate disc of a chart is `e.symm c`. -/
theorem ofChart_apply_zero (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r) (hc : Metric.ball c r ⊆ e.target)
    (he : ∀ x ∈ e.source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x) :
    ofChart e hr hc he 0 = e.symm c := by
  simp

/-- The closed disc of the coordinate disc of a chart is the image under `e.symm` of the closed
ball of radius `r / 2` about `c`. -/
@[simp]
theorem disc_ofChart (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r) (hc : Metric.ball c r ⊆ e.target)
    (he : ∀ x ∈ e.source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x) :
    (ofChart e hr hc he).disc = e.symm '' Metric.closedBall c (r / 2) := by
  have h := (disc_def subtypeVal).symm.trans disc_subtypeVal
  rw [coe_subtypeVal] at h
  rw [disc_def, coe_ofChart, Set.image_comp, Set.image_comp, h,
    image_ofChartHomeomorph_closedBall, mul_one]

/-- The open disc of the coordinate disc of a chart is the image under `e.symm` of the open ball
of radius `r / 2` about `c`. -/
@[simp]
theorem openDisc_ofChart (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r) (hc : Metric.ball c r ⊆ e.target)
    (he : ∀ x ∈ e.source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x) :
    (ofChart e hr hc he).openDisc = e.symm '' Metric.ball c (r / 2) := by
  have h := (openDisc_def subtypeVal).symm.trans openDisc_subtypeVal
  rw [coe_subtypeVal] at h
  rw [openDisc_def, coe_ofChart, Set.image_comp, Set.image_comp, h,
    image_ofChartHomeomorph_ball, mul_one]

/-- The image of the coordinate disc of a chart is the image under `e.symm` of the ball of radius
`r` about `c`. -/
@[simp]
theorem range_ofChart (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r) (hc : Metric.ball c r ⊆ e.target)
    (he : ∀ x ∈ e.source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x) :
    Set.range (ofChart e hr hc he) = e.symm '' Metric.ball c r := by
  rw [coe_ofChart, Set.range_comp, Set.range_comp, Subtype.range_coe, coe_ball,
    image_ofChartHomeomorph_ball, div_mul_cancel₀ r two_ne_zero]

/-- The image of the coordinate disc of a chart lies in the source of the chart. -/
theorem range_ofChart_subset_source (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r) (hc : Metric.ball c r ⊆ e.target)
    (he : ∀ x ∈ e.source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x) :
    Set.range (ofChart e hr hc he) ⊆ e.source := by
  rw [range_ofChart]
  exact (e.mapsTo_symm.mono_left hc).image_subset

end CoordinateDisc

/-! ### Existence of coordinate discs -/

namespace CoordinateDisc

variable {M : Type} [TopologicalSpace M] [T2Space M] {E : Type} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {o : HomologicalOrientation M E 2}

/-- **Open embeddings of connected open sets of `ℂ` preserve or reverse orientation.** On a
surface `M` with a homological orientation `o`, an open embedding `f` of a connected open set `U`
of `ℂ` carries the canonical local orientation of `U` at `z`
(`TauCeti.complexHomologicalOrientation`) either to `o (f z)` at every `z`, or to `-o (f z)` at
every `z`: `o` read on `U` agrees with the canonical orientation of `U` or with the opposite
one. -/
theorem _root_.TauCeti.HomologicalOrientation.forall_localOrientationEquiv_eq_or_forall_eq_neg
    (hE : finrank ℝ E = 2) (o : HomologicalOrientation M E 2) {U : TopologicalSpace.Opens ℂ}
    [ConnectedSpace U] {f : U → M} (hf : IsOpenEmbedding f) :
    (∀ z, hf.localOrientationEquiv z 2 (complexHomologicalOrientation U z) = o (f z)) ∨
      ∀ z, hf.localOrientationEquiv z 2 (complexHomologicalOrientation U z) = -o (f z) := by
  have h : finrank ℝ E = finrank ℝ ℂ := hE.trans Complex.finrank_real_complex.symm
  -- Chart `M` on `ℂ` through a linear equivalence, to read `o` with the model `ℂ`.
  let : ChartedSpace ℂ M := ChartedSpace.ofFinrankEq (𝕜 := ℝ) M h
  -- If `o'`, read with the model `ℂ`, pulls back to the canonical orientation of `U`, then `f`
  -- carries the canonical orientation to `o'`: the two readings have the same local orientations.
  have key (o' : HomologicalOrientation M E 2)
      (ho : (o'.changeModel ℂ h).comap hf = complexHomologicalOrientation U) (z : U) :
      hf.localOrientationEquiv z 2 (complexHomologicalOrientation U z) = o' (f z) := by
    rw [← ho, HomologicalOrientation.localOrientationEquiv_comap_apply,
      HomologicalOrientation.changeModel_apply]
  rcases HomologicalOrientation.eq_or_eq_neg Complex.finrank_real_complex
    (complexHomologicalOrientation U) ((o.changeModel ℂ h).comap hf) with ho | ho
  · exact Or.inl (key o ho)
  · refine Or.inr (key (-o) ?_)
    rw [HomologicalOrientation.changeModel_neg, HomologicalOrientation.comap_neg, ho, neg_neg]

/-- **Open embeddings of the ball are coordinate discs up to orientation.** On a surface `M`
with a homological orientation `o`, an open embedding `f` of the ball of radius `2` of `ℂ` is a
coordinate disc either for `o` or for `-o`: the ball is connected, so `o` read on it agrees with
its canonical orientation or with the opposite one. -/
theorem exists_coe_eq_or_exists_coe_eq (hE : finrank ℝ E = 2) {f : ball → M}
    (hf : IsOpenEmbedding f) :
    (∃ φ : CoordinateDisc o, ⇑φ = f) ∨ ∃ φ : CoordinateDisc (-o), ⇑φ = f :=
  (o.forall_localOrientationEquiv_eq_or_forall_eq_neg hE hf).imp (fun h ↦ ⟨⟨f, hf, h⟩, rfl⟩)
    fun h ↦ ⟨⟨f, hf, h⟩, rfl⟩

omit [T2Space M] in
/-- An open embedding of the ball sending `0` to `x`, inside a neighbourhood `U` of `x`: Tau
Ceti's coordinate ball `E → interior U` about `x`, after a linear equivalence `ℂ ≃L[ℝ] E`. -/
private theorem exists_isOpenEmbedding_ball (hE : finrank ℝ E = 2) {x : M} {U : Set M}
    (hU : U ∈ 𝓝 x) :
    ∃ f : ball → M, IsOpenEmbedding f ∧ f 0 = x ∧ Set.range f ⊆ U := by
  obtain ⟨κ, hκ, hκx⟩ :=
    isOpen_interior.exists_isOpenEmbedding_apply_zero_eq (E := E) (mem_interior_iff_mem_nhds.2 hU)
  let L : ℂ ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofFinrankEq (Complex.finrank_real_complex.trans hE.symm)
  refine ⟨fun z ↦ κ (L z), isOpen_interior.isOpenEmbedding_subtypeVal.comp
    (hκ.comp (L.toHomeomorph.isOpenEmbedding.comp ball.isOpen.isOpenEmbedding_subtypeVal)),
    by simpa using hκx, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact interior_subset (κ (L z)).property

end CoordinateDisc

open CoordinateDisc

/-- **Existence of coordinate discs.** On a surface `M` with a homological orientation `o`, every
point `x` is the centre of a coordinate disc for `o` whose image lies in any given neighbourhood
`U` of `x`. -/
theorem exists_coordinateDisc (hE : finrank ℝ E = 2) (o : HomologicalOrientation M E 2) {x : M}
    {U : Set M} (hU : U ∈ 𝓝 x) :
    ∃ φ : CoordinateDisc o, φ 0 = x ∧ Set.range φ ⊆ U := by
  obtain ⟨f, hf, hfx, hfU⟩ := exists_isOpenEmbedding_ball hE hU
  rcases exists_coe_eq_or_exists_coe_eq (o := o) hE hf with ⟨φ, rfl⟩ | ⟨φ, rfl⟩
  · exact ⟨φ, hfx, hfU⟩
  · -- Reversing a coordinate disc for `-o` gives one for `-(-o) = o`, with the same centre and
    -- image.
    rw [← neg_neg o]
    refine ⟨φ.reverse, by simpa using hfx, ?_⟩
    rw [coe_reverse, Set.range_comp, conjBall.surjective.range_eq, Set.image_univ]
    exact hfU

/-- **Existence of disjoint coordinate discs.** On a surface `M` with a homological orientation
`o`, finitely many distinct points `x i` are the centres of coordinate discs `φ i` for `o`, each
inside a given neighbourhood `U i` of `x i`, whose images are pairwise disjoint. In particular
their closed discs are pairwise disjoint (`CoordinateDisc.disc_subset_range`). -/
theorem exists_coordinateDisc_pairwise_disjoint (hE : finrank ℝ E = 2)
    (o : HomologicalOrientation M E 2) {ι : Type*} [Finite ι] {x : ι → M}
    (hx : Function.Injective x) {U : ι → Set M} (hU : ∀ i, U i ∈ 𝓝 (x i)) :
    ∃ φ : ι → CoordinateDisc o, (∀ i, φ i 0 = x i) ∧
      (∀ i, Set.range (φ i) ⊆ U i) ∧
        Pairwise fun i j ↦ Disjoint (Set.range (φ i)) (Set.range (φ j)) := by
  obtain ⟨V, hV, hVd⟩ :=
    (pairwise_disjoint_nhds.comp_of_injective hx).exists_mem_filter_of_disjoint
  have hmem (i : ι) : U i ∩ V i ∈ 𝓝 (x i) := Filter.inter_mem (hU i) (hV i)
  choose φ hφx hφU using fun i ↦ exists_coordinateDisc hE o (hmem i)
  refine ⟨φ, hφx, fun i ↦ (hφU i).trans Set.inter_subset_left, fun i j hij ↦ ?_⟩
  exact (hVd hij).mono
    ((hφU i).trans Set.inter_subset_right) ((hφU j).trans Set.inter_subset_right)

/-! ### Disjoint coordinate discs from oriented smooth charts -/

namespace CoordinateDisc

open scoped ContDiff

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M]

/-- **Disjoint coordinate discs from oriented smooth charts.** On a smooth surface `M` modelled on
`ℝ²` with a smooth orientation `o`, finitely many distinct points `x i`, each with a neighbourhood
`U i`, have charts `e i` of the maximal smooth atlas, whose source contains `x i` and lies inside
`U i`, with pairwise disjoint sources, whose target is a ball `Metric.ball 0 (r i)`, which send
`x i` to `0`, and which preserve orientation, from `o` to the standard orientation of `ℝ²`, at
every point of their source. Their coordinate discs `ofChart (e i)`, on the whole target, are
coordinate discs for `o.toHomologicalOrientation` centred at `x i`,
`z ↦ (e i).symm ((r i / 2) (re z, im z))`, whose images lie in `U i` and are pairwise disjoint.
So their closed discs are pairwise disjoint too (`disc_subset_range`).

The charts are those of the maximal atlas, not the charts `chartAt` of the atlas of `M`. -/
theorem exists_ofChart_pairwise_disjoint (o : Manifold.Orientation (𝓡 2) M (Fin 2)) {ι : Type*}
    [Finite ι] {x : ι → M} (hx : Function.Injective x) {U : ι → Set M}
    (hU : ∀ i, U i ∈ 𝓝 (x i)) :
    ∃ (e : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (r : ι → ℝ)
      (hr : ∀ i, 0 < r i) (hc : ∀ i, Metric.ball 0 (r i) ⊆ (e i).target)
      (he : ∀ i, ∀ y ∈ (e i).source,
        o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) (e i) y),
      (∀ i, e i ∈ IsManifold.maximalAtlas (𝓡 2) ∞ M) ∧ (∀ i, x i ∈ (e i).source) ∧
      (∀ i, (e i).target = Metric.ball 0 (r i)) ∧ (∀ i, e i (x i) = 0) ∧
      (∀ i, ofChart (e i) (hr i) (hc i) (he i) 0 = x i) ∧ (∀ i, (e i).source ⊆ U i) ∧
      (Pairwise fun i j ↦ Disjoint (e i).source (e j).source) ∧
      (∀ i, Set.range (ofChart (e i) (hr i) (hc i) (he i)) ⊆ U i) ∧
      Pairwise fun i j ↦ Disjoint (Set.range (ofChart (e i) (hr i) (hc i) (he i)))
        (Set.range (ofChart (e j) (hr j) (hc j) (he j))) := by
  obtain ⟨V, hV, hVd⟩ :=
    (pairwise_disjoint_nhds.comp_of_injective hx).exists_mem_filter_of_disjoint
  have hmem (i : ι) : U i ∩ V i ∈ 𝓝 (x i) := Filter.inter_mem (hU i) (hV i)
  choose e r hr hatlas hxe hex hsU htgt hpres using fun i ↦
    Manifold.Orientation.exists_mem_maximalAtlas_isOrientationPreservingAt
      (Manifold.Orientation.euclideanSpace 2) o (hmem i)
  have hsU' (i : ι) : (e i).source ⊆ U i := (hsU i).trans Set.inter_subset_left
  have hdisj : Pairwise fun i j ↦ Disjoint (e i).source (e j).source := fun i j hij ↦
    (hVd hij).mono
      ((hsU i).trans Set.inter_subset_right) ((hsU j).trans Set.inter_subset_right)
  have hc (i : ι) : Metric.ball 0 (r i) ⊆ (e i).target := (htgt i).ge
  refine ⟨e, r, hr, hc, hpres, hatlas, hxe, htgt, hex, fun i ↦ ?_, hsU', hdisj,
    fun i ↦ (range_ofChart_subset_source _ _ _ _).trans (hsU' i), fun i j hij ↦
      (hdisj hij).mono (range_ofChart_subset_source _ _ _ _)
        (range_ofChart_subset_source _ _ _ _)⟩
  rw [ofChart_apply_zero, ← hex i, (e i).left_inv (hxe i)]

end CoordinateDisc

end SymplecticGeometry

end
