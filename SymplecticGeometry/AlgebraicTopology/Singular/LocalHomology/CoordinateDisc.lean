/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Determinant
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

Complex conjugation reverses the canonical orientation of `ℂ`, and of every open set of `ℂ` that
it maps to itself, since its real derivative `Complex.conjCLE` has determinant `-1`. So a
coordinate disc `φ` for `o` gives a coordinate disc `φ.reverse = φ ∘ conj` for `-o`, with the same
discs and with the boundary loop run backwards. The proof that conjugation reverses the
orientation of `ℂ` reads it in the chart `OpenPartialHomeomorph.refl`, through Tau Ceti's
`OpenPartialHomeomorph.localHomologyMap_restrict_localOrientationOfOrientedChart`, and passes
from the restriction to `univ` back to the map itself as the proof of
`OpenPartialHomeomorph.localHomologyMap_localOrientationOfOrientedChart` does.

## Main definitions

* `SymplecticGeometry.CoordinateDisc o`: the coordinate discs of `M` for `o`.
* `SymplecticGeometry.CoordinateDisc.ball`: the open ball of radius `2` of `ℂ`, as an open set.
* `SymplecticGeometry.CoordinateDisc.disc`, `SymplecticGeometry.CoordinateDisc.openDisc`: the
  images of the closed and of the open unit ball.
* `SymplecticGeometry.CoordinateDisc.boundaryCircle`: the unit circle of the chart, as a map
  `C(Circle, M)`.
* `SymplecticGeometry.CoordinateDisc.boundaryLoop`: the loop `t ↦ φ(e^{2πit})`.
* `SymplecticGeometry.CoordinateDisc.reverse`: the coordinate disc `φ ∘ conj` for `-o`.
* `SymplecticGeometry.CoordinateDisc.subtypeVal`: the inclusion of the ball into `ℂ`, a coordinate
  disc of `ℂ` for its canonical orientation.

## Main results

* `SymplecticGeometry.CoordinateDisc.isCompact_disc`,
  `SymplecticGeometry.CoordinateDisc.isOpen_openDisc`,
  `SymplecticGeometry.CoordinateDisc.openDisc_subset_disc`.
* `SymplecticGeometry.CoordinateDisc.disc_diff_openDisc`: the closed disc minus the open disc is
  the boundary circle.
* `TauCeti.comap_conj_complexHomologicalOrientation`: conjugation reverses the canonical
  orientation of an open set of `ℂ` that it maps to itself.
* `SymplecticGeometry.CoordinateDisc.disc_reverse`,
  `SymplecticGeometry.CoordinateDisc.openDisc_reverse`,
  `SymplecticGeometry.CoordinateDisc.boundaryLoop_reverse`: reversal keeps the discs and reverses
  the boundary loop (`Path.symm`).
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

open Topology TauCeti ComplexConjugate

/-! ### Complex conjugation reverses the canonical orientation -/

namespace TauCeti

open CategoryTheory

/-- Complex conjugation reverses the canonical homological orientation of `ℂ`: pulling it back
along `conj` gives its negation. -/
theorem comap_conjCLE_complexHomologicalOrientation :
    (complexHomologicalOrientation ℂ).comap Complex.conjCLE.toHomeomorph.isOpenEmbedding =
      -complexHomologicalOrientation ℂ := by
  ext x : 1
  apply (Complex.conjCLE.toHomeomorph.isOpenEmbedding.localOrientationEquiv x 2).injective
  rw [HomologicalOrientation.localOrientationEquiv_comap_apply, HomologicalOrientation.neg_apply,
    IsOpenEmbedding.localOrientationEquiv_neg, ← neg_eq_iff_eq_neg, eq_comm]
  apply Subtype.ext
  rw [complexHomologicalOrientation_apply, complexHomologicalOrientation_apply,
    IsOpenEmbedding.coe_localOrientationEquiv, localHomologyIsoOfIsOpenEmbedding_hom,
    LocalOrientation.coe_neg]
  simp only [chartAt_self_eq]
  -- In the chart `refl`, conjugation has derivative `conjCLE`, of determinant `-1`.
  have hf : HasFDerivAt (OpenPartialHomeomorph.refl ℂ ∘ Complex.conjCLE.toHomeomorph ∘
      (OpenPartialHomeomorph.refl ℂ).symm) (Complex.conjCLE : ℂ →L[ℝ] ℂ) x := by
    simpa using Complex.conjCLE.hasFDerivAt
  have key :=
    (OpenPartialHomeomorph.refl ℂ).localHomologyMap_restrict_localOrientationOfOrientedChart
      Complex.orientation Complex.finrank_real_complex (OpenPartialHomeomorph.refl ℂ)
      ⟨_, Complex.conjCLE.toHomeomorph.continuous⟩ (Set.mem_univ x) (Set.mem_univ _) isOpen_univ
      (Set.mem_univ x) (fun _ _ h ↦ Complex.conjCLE.injective h) hf
      (by rw [Complex.det_conjCLE]; norm_num)
  rw [Complex.det_conjCLE, sign_neg (by norm_num : (-1 : ℝ) < 0), SignType.coe_neg_one,
    neg_one_zsmul] at key
  -- Conjugation restricted to `univ` is conjugation after the inclusion of `univ`.
  have h' := isOpen_univ.isOpenEmbedding_subtypeVal.localHomologyMap_localOrientationEquiv_symm
    ⟨x, Set.mem_univ x⟩ ((OpenPartialHomeomorph.refl ℂ).localOrientationOfOrientedChart
      (Set.mem_univ x) Complex.orientation Complex.finrank_real_complex) fun _ hz ↦ Subtype.ext hz
  rw [← h', ← ConcreteCategory.comp_apply]
  exact (ConcreteCategory.congr_hom (localHomologyMap_comp _ _ _ _ _ 2) _).trans key

/-- Complex conjugation reverses the canonical homological orientation of every open set `U` of
`ℂ` that it maps to itself: pulling it back along an open embedding `f : U → U` that acts as
`conj` gives its negation. -/
theorem comap_conj_complexHomologicalOrientation {U : TopologicalSpace.Opens ℂ} {f : U → U}
    (hf : IsOpenEmbedding f) (hfc : ∀ z, (f z : ℂ) = conj (z : ℂ)) :
    (complexHomologicalOrientation U).comap hf = -complexHomologicalOrientation U := by
  have hU : IsOpenEmbedding (Subtype.val : U → ℂ) := U.isOpen.isOpenEmbedding_subtypeVal
  conv_lhs => rw [← comap_subtypeVal_complexHomologicalOrientation hU]
  rw [HomologicalOrientation.comap_comap_of_comp_eq _ hU hf
      (Complex.conjCLE.toHomeomorph.isOpenEmbedding.comp hU) (funext hfc),
    ← HomologicalOrientation.comap_comap _ Complex.conjCLE.toHomeomorph.isOpenEmbedding hU,
    comap_conjCLE_complexHomologicalOrientation, HomologicalOrientation.comap_neg,
    comap_subtypeVal_complexHomologicalOrientation]

end TauCeti

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

theorem conj_mem_ball {z : ℂ} (hz : z ∈ ball) : conj z ∈ ball := by
  simpa using hz

/-- Complex conjugation, as a homeomorphism of the ball of radius `2`. -/
def conjBall : ball ≃ₜ ball :=
  Complex.conjCLE.toHomeomorph.subtype fun z ↦ by simp

@[simp]
theorem coe_conjBall_apply (z : ball) : (conjBall z : ℂ) = conj (z : ℂ) :=
  (rfl)

@[simp]
theorem conjBall_conjBall (z : ball) : conjBall (conjBall z) = z :=
  Subtype.ext (by simp)

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
theorem reverse_apply (z : ball) : φ.reverse z = φ ⟨conj (z : ℂ), conj_mem_ball z.property⟩ :=
  (rfl)

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
  simp only [boundaryCircle_apply, reverse_apply, Circle.coe_inv_eq_conj]

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

end SymplecticGeometry

end
