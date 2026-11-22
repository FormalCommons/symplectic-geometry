/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.OpenEmbedding
public import TauCeti.Geometry.Manifold.Complex.FundamentalClass
public import TauCeti.Topology.Circle.Loop

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

## Main results

* `SymplecticGeometry.CoordinateDisc.isCompact_disc`,
  `SymplecticGeometry.CoordinateDisc.isOpen_openDisc`,
  `SymplecticGeometry.CoordinateDisc.openDisc_subset_disc`.
* `SymplecticGeometry.CoordinateDisc.disc_diff_openDisc`: the closed disc minus the open disc is
  the boundary circle.
* `SymplecticGeometry.CoordinateDisc.comap_eq_complexHomologicalOrientation`: when `M` is charted
  on `ℂ`, the orientation condition says that `o` pulls back to the canonical orientation of the
  ball.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7,
  where the first Chern number of a bundle over a surface is computed from trivializations over a
  disc and over its complement.
-/

public section

noncomputable section

open Topology TauCeti

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

@[simp]
theorem boundaryCircle_apply (z : Circle) :
    φ.boundaryCircle z = φ ⟨z, mem_ball_of_norm_le_one (Circle.norm_coe z).le⟩ :=
  (rfl)

theorem boundaryCircle_mem_disc (z : Circle) : φ.boundaryCircle z ∈ φ.disc := by
  simp

theorem boundaryCircle_notMem_openDisc (z : Circle) : φ.boundaryCircle z ∉ φ.openDisc := by
  simp

/-- The closed disc minus the open disc is the boundary circle. -/
theorem disc_diff_openDisc : φ.disc \ φ.openDisc = Set.range φ.boundaryCircle := by
  ext x
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hx⟩
    have h1 : ‖(z : ℂ)‖ = 1 := le_antisymm hz (not_lt.1 fun h ↦ hx ⟨z, h, rfl⟩)
    obtain ⟨c, hc⟩ : ∃ c : Circle, (c : ℂ) = z := ⟨⟨z, by simp [Submonoid.unitSphere, h1]⟩, rfl⟩
    exact ⟨c, by rw [boundaryCircle_apply]; exact congrArg φ (Subtype.ext hc)⟩
  · rintro ⟨z, rfl⟩
    exact ⟨φ.boundaryCircle_mem_disc z, φ.boundaryCircle_notMem_openDisc z⟩

/-- The boundary loop of a coordinate disc, `t ↦ φ(e^{2πit})`, based at `φ 1`. It runs
counterclockwise in the chart, so it is oriented as the boundary of the closed disc. -/
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

theorem disc_subtypeVal : subtypeVal.disc = Metric.closedBall 0 1 := by
  ext w
  simp only [mem_disc_iff, coe_subtypeVal, Subtype.exists, exists_and_left, exists_prop,
    exists_eq_right_right, mem_closedBall_zero_iff]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, mem_ball_of_norm_le_one h⟩⟩

theorem openDisc_subtypeVal : subtypeVal.openDisc = Metric.ball 0 1 := by
  ext w
  simp only [mem_openDisc_iff, coe_subtypeVal, Subtype.exists, exists_and_left, exists_prop,
    exists_eq_right_right, mem_ball_zero_iff]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, mem_ball_of_norm_le_one h.le⟩⟩

end CoordinateDisc

end SymplecticGeometry

end
