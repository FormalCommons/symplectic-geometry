/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.OpenEmbedding
public import TauCeti.Geometry.Manifold.Complex.FundamentalClass
public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.Geometry.Manifold.Orientation.Euclidean
public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Topology.Circle.Loop
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

On a smooth surface `M` charted on `ℝ²` with an orientation
`o : TauCeti.Manifold.Orientation (𝓡 2) M (Fin 2)`, every chart `e` that preserves orientation
gives coordinate discs for `o.toHomologicalOrientation`: for a ball `B(c, r)` in the target of
`e`, the map `z ↦ e⁻¹(c + (r / 2) (re z, im z))` is one, centred at `e⁻¹(c)`. The identification
`z ↦ (re z, im z)` of `ℂ` with `ℝ²` carries the standard orientation of `ℂ` to that of `ℝ²`
(`Complex.orientation_map_orthonormalBasisOneI_repr`), and the local orientation of a smooth
orientation can be read in any chart whose derivative matches the orientations
(`TauCeti.Manifold.Orientation.toHomologicalOrientation_apply_eq_localOrientationOfOrientedChart`).

## Main definitions

* `SymplecticGeometry.CoordinateDisc o`: the coordinate discs of `M` for `o`.
* `SymplecticGeometry.CoordinateDisc.ball`: the open ball of radius `2` of `ℂ`, as an open set.
* `SymplecticGeometry.CoordinateDisc.disc`, `SymplecticGeometry.CoordinateDisc.openDisc`: the
  images of the closed and of the open unit ball.
* `SymplecticGeometry.CoordinateDisc.boundaryCircle`: the unit circle of the chart, as a map
  `C(Circle, M)`.
* `SymplecticGeometry.CoordinateDisc.boundaryLoop`: the loop `t ↦ φ(e^{2πit})`.
* `SymplecticGeometry.CoordinateDisc.subtypeVal`: the inclusion of the ball into `ℂ`, a coordinate
  disc of `ℂ` for its canonical orientation.
* `SymplecticGeometry.CoordinateDisc.ofChart`: the coordinate disc of an orientation-preserving
  chart of a smoothly oriented surface, on a ball in its target.

## Main results

* `SymplecticGeometry.CoordinateDisc.isCompact_disc`,
  `SymplecticGeometry.CoordinateDisc.isOpen_openDisc`,
  `SymplecticGeometry.CoordinateDisc.openDisc_subset_disc`.
* `SymplecticGeometry.CoordinateDisc.disc_diff_openDisc`: the closed disc minus the open disc is
  the boundary circle.
* `SymplecticGeometry.CoordinateDisc.comap_eq_complexHomologicalOrientation`: when `M` is charted
  on `ℂ`, the orientation condition says that `o` pulls back to the canonical orientation of the
  ball.
* `TauCeti.Manifold.Orientation.toHomologicalOrientation_apply_eq_localOrientationOfOrientedChart`:
  the local orientation of a smooth orientation at `x`, read in any chart at `x`.
* `SymplecticGeometry.CoordinateDisc.ofChart_apply`,
  `SymplecticGeometry.CoordinateDisc.ofChart_apply_zero`: the formula of `ofChart`, and its centre.

## Implementation notes

The proof that `ofChart` preserves orientation adapts that of Tau Ceti's
`TauCeti.comap_complexHomologicalOrientation`: the chart `e`, read through the parametrization,
turns the disc into the inclusion of the ball, and
`OpenPartialHomeomorph.localHomologyMap_localOrientationOfOrientedChart` compares the local
orientations of the two charts. Reading the local orientation of a smooth orientation in another
chart is the change of chart of Tau Ceti's
`TauCeti.complexHomologicalOrientation_apply_of_mem_maximalAtlas`, for a transition map whose
derivative is the identity.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7,
  where the first Chern number of a bundle over a surface is computed from trivializations over a
  disc and over its complement.
-/

public section

noncomputable section

open Module Topology TauCeti
open scoped Manifold

/-! ### Oriented charts -/

/-- The real basis `(1, i)` of `ℂ` goes to the standard basis of `ℝ²` under
`Complex.orthonormalBasisOneI.repr`, so this identification carries the standard orientation of
`ℂ` to that of `ℝ²`. -/
theorem Complex.orientation_map_orthonormalBasisOneI_repr :
    Complex.orientation.map (Fin 2) Complex.orthonormalBasisOneI.repr.toLinearEquiv =
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation := by
  rw [Complex.orientation, ← Basis.orientation_map]
  congr 1
  ext i : 1
  rw [← Complex.toBasis_orthonormalBasisOneI, Basis.map_apply, OrthonormalBasis.coe_toBasis]
  fin_cases i <;> ext j <;> fin_cases j <;> simp [Complex.orthonormalBasisOneI_repr_apply]

namespace TauCeti.Manifold.Orientation

variable {M E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] {n : ℕ}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The local orientations of a smooth orientation, read in any chart.** Let `χ` be a chart of
`M` at `x` with values in an inner product space `F`, and `D` the derivative at `x` of `χ` read
in the preferred chart at `x`. Then the local orientation of `o` at `x` is the one selected in `χ`
by the image of the tangent orientation `o.orientationAt x` under `D`. -/
theorem toHomologicalOrientation_apply_eq_localOrientationOfOrientedChart
    (hE : finrank ℝ E = n + 1) (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1)))
    (hF : finrank ℝ F = n + 1) (χ : OpenPartialHomeomorph M F) {x : M} (hx : x ∈ χ.source)
    (D : E ≃L[ℝ] F)
    (hD : HasFDerivAt (χ ∘ (chartAt E x).symm) (D : E →L[ℝ] F) (chartAt E x x))
    {ω : _root_.Orientation ℝ F (Fin (n + 1))}
    (hω : (o.orientationAt x).map (Fin (n + 1)) D.toLinearEquiv = ω) :
    o.toHomologicalOrientation hE x = χ.localOrientationOfOrientedChart hx ω hF := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
  -- The preferred chart at `x` followed by `D`, in which `o` selects its local orientation.
  let φ := (chartAt E x).transHomeomorph (𝓘(ℝ, E).toHomeomorph.trans D.toHomeomorph)
  have hxφ : x ∈ φ.source := by simp [φ]
  -- The transition from `φ` to `χ` has derivative the identity at `φ x`.
  have hd : HasFDerivAt (χ ∘ φ.symm) (ContinuousLinearMap.id ℝ F) (φ x) := by
    have h1 : D.symm (φ x) = chartAt E x x := by simp [φ]
    convert HasFDerivAt.comp (φ x) (h1.symm ▸ hD) D.symm.hasFDerivAt using 1
    · ext y
      simp [φ]
    · ext y
      simp
  rw [toHomologicalOrientation_apply,
    localOrientationOfManifoldOrientation_eq_localOrientationOfOrientedChart_transHomeomorph
      o hE x rfl D hF hxφ, hω]
  have hdet : (ContinuousLinearMap.id ℝ F).det = 1 := LinearMap.det_id
  apply Subtype.ext
  rw [OpenPartialHomeomorph.coe_localOrientationOfOrientedChart_eq_sign_det_smul _ _ φ χ hxφ hx
    hd (hdet ▸ one_ne_zero), hdet, sign_one, SignType.coe_one, one_smul]

end TauCeti.Manifold.Orientation

namespace SymplecticGeometry

namespace CoordinateDisc

/-- The open ball of radius `2` about `0` in `ℂ`, as an open set. Coordinate discs are defined on
it, and it carries the canonical orientation `TauCeti.complexHomologicalOrientation ball`. -/
def ball : TopologicalSpace.Opens ℂ :=
  ⟨Metric.ball 0 2, Metric.isOpen_ball⟩

@[simp]
theorem coe_ball : (ball : Set ℂ) = Metric.ball 0 2 :=
  (rfl)

@[simp]
theorem mem_ball_iff {z : ℂ} : z ∈ ball ↔ ‖z‖ < 2 := by
  rw [← SetLike.mem_coe, coe_ball, mem_ball_zero_iff]

theorem mem_ball_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) : z ∈ ball :=
  mem_ball_iff.2 (hz.trans_lt one_lt_two)

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

theorem isCompact_disc : IsCompact φ.disc := by
  refine IsCompact.image ?_ φ.continuous
  rw [Subtype.isCompact_iff]
  convert isCompact_closedBall (0 : ℂ) 1 using 1
  ext w
  simp only [Set.mem_image, Set.mem_ofPred_eq, Subtype.exists, exists_and_right, exists_eq_right,
    mem_closedBall_zero_iff]
  exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨mem_ball_of_norm_le_one h, h⟩⟩

theorem isOpen_openDisc : IsOpen φ.openDisc :=
  φ.isOpenEmbedding.isOpenMap _ <|
    (isOpen_lt continuous_subtypeVal.norm continuous_const : IsOpen {z : ball | ‖(z : ℂ)‖ < 1})

theorem openDisc_subset_disc : φ.openDisc ⊆ φ.disc :=
  Set.image_mono fun z (hz : ‖(z : ℂ)‖ < 1) ↦ hz.le

/-! ### The boundary circle -/

/-- The boundary circle of a coordinate disc: the unit circle of the chart, `z ↦ φ z`. -/
def boundaryCircle : C(Circle, M) where
  toFun z := φ ⟨z, mem_ball_of_norm_le_one (Circle.norm_coe z).le⟩
  continuous_toFun := by fun_prop

theorem boundaryCircle_apply (z : Circle) :
    φ.boundaryCircle z = φ ⟨z, mem_ball_of_norm_le_one (Circle.norm_coe z).le⟩ :=
  (rfl)

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

private theorem ofChartHomeomorph_mem_ball {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r)
    (z : ball) : ofChartHomeomorph c hr z ∈ Metric.ball c r := by
  have hz := mem_ball_iff.1 z.property
  rw [ofChartHomeomorph_apply, Metric.mem_ball, dist_self_add_left, norm_smul,
    LinearIsometryEquiv.norm_map, Real.norm_of_nonneg (by positivity)]
  nlinarith

private theorem hasFDerivAt_ofChartHomeomorph_symm (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ}
    (hr : 0 < r) (y : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (ofChartHomeomorph c hr).symm
      ((ofChartLinearEquiv hr).symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ) y := by
  have h := ((ofChartLinearEquiv hr).symm.hasFDerivAt (x := -c + y)).comp y
    ((hasFDerivAt_id y).const_add (-c))
  rwa [ContinuousLinearMap.comp_id] at h

/-- The linear part of the parametrization carries the standard orientation of `ℂ` to that of
`ℝ²`: it is `Complex.orthonormalBasisOneI.repr` followed by a positive homothety. -/
private theorem orientation_map_ofChartLinearEquiv {r : ℝ} (hr : 0 < r) :
    Complex.orientation.map (Fin 2) (ofChartLinearEquiv hr).toLinearEquiv =
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation := by
  have hs : (((ContinuousLinearEquiv.smulLeft (Units.mk0 (r / 2) (by positivity))) :
      EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2)).toLinearEquiv :
        EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) = (r / 2) • LinearMap.id := by
    ext
    simp
  -- The underlying linear equivalence of `Complex.orthonormalBasisOneI.repr`, through either
  -- coercion.
  have hrepr : Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.toLinearEquiv =
      Complex.orthonormalBasisOneI.repr.toLinearEquiv :=
    (rfl)
  rw [ofChartLinearEquiv, ContinuousLinearEquiv.trans_toLinearEquiv, Orientation.map_trans,
    hrepr, Complex.orientation_map_orthonormalBasisOneI_repr,
    Orientation.map_eq_iff_det_pos _ _ (by simp), hs, LinearMap.det_smul, LinearMap.det_id,
    finrank_euclideanSpace_fin]
  positivity

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
      (chartAt (EuclideanSpace ℝ (Fin 2)) x x) := by
    have h := (mdifferentiableAt_of_isInvertible_mfderiv ⟨D, hD⟩).hasMFDerivAt.2
    have hext : writtenInExtChartAt (𝓡 2) (𝓡 2) x e =
        e ∘ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm := by
      ext y
      simp [writtenInExtChartAt]
    rwa [hext, ModelWithCorners.range_eq_univ, hasFDerivWithinAt_univ, ← hD] at h
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

/-- The coordinate disc of a chart is `z ↦ e.symm (c + (r / 2) (re z, im z))`. -/
@[simp]
theorem ofChart_apply (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r) (hc : Metric.ball c r ⊆ e.target)
    (he : ∀ x ∈ e.source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x) (z : ball) :
    ofChart e hr hc he z = e.symm (c + (r / 2) • Complex.orthonormalBasisOneI.repr z) :=
  congrArg e.symm (ofChartHomeomorph_apply c hr z)

/-- The centre of the coordinate disc of a chart is `e.symm c`. -/
theorem ofChart_apply_zero (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r) (hc : Metric.ball c r ⊆ e.target)
    (he : ∀ x ∈ e.source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x) :
    ofChart e hr hc he ⟨0, mem_ball_of_norm_le_one (by simp)⟩ = e.symm c := by
  simp

end CoordinateDisc

end SymplecticGeometry

end
