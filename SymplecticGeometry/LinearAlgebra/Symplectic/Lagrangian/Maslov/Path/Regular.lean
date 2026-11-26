/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Maslov.Path.Basic
public import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Maslov.Crossing.Form
public import SymplecticGeometry.LinearAlgebra.QuadraticForm.Signature
import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Maslov.Crossing.Path
import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Maslov.Path.RegularPieces
import SymplecticGeometry.Analysis.Calculus.ContDiff.Concat
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.Matrix.ContDiff
import TauCeti.Geometry.Manifold.Instances.Icc.CollaredSmoothTransition
import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Maslov.Path.Naturality
import SymplecticGeometry.LinearAlgebra.Matrix.Rank
import SymplecticGeometry.Analysis.Calculus.Deriv.Matrix
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Regular representatives of paths of Lagrangian subspaces

Let `V` be a Lagrangian subspace of `(StdSpace ι, ω₀)`. This file shows that every path `γ` in
the Lagrangian Grassmannian `ℒ ι` is homotopic with fixed ends to a path with a smooth frame all
of whose crossings with `V` are regular. Together with the crossing-form formula of
`Maslov/Crossing/Path.lean`, this computes the Robbin–Salamon index `pathMaslovIndex γ V` of every
path through crossing forms, and the file collects the description of that index in one theorem.

## Main results

* `SymplecticGeometry.LagrangianGrassmannian.exists_homotopic_regular`: every path is homotopic
  with fixed ends to one with a smooth frame `Z`, with derivative `Z'`, whose crossing forms
  `lagrangianCrossingForm (Z t) (Z' t) V` are nondegenerate at all crossings.
* `SymplecticGeometry.pathMaslovIndex_eq_crossing_sum_and_properties`: the conjunction of the
  isolation of regular crossings, the crossing-form formula, the existence of regular
  representatives, the frame independence of the crossing form, and the properties of the index
  proved in `Maslov/Path/Basic.lean` and `Maslov/Path/Naturality.lean`.

## Implementation notes

No transversality theory is used. Two paths with the same ends are homotopic with fixed ends
exactly when their indices agree (`pathMaslovIndex_eq_iff_homotopic`), so it suffices to build,
for the given ends, one regular path with the index of `γ`; and by naturality
(`pathMaslovIndex_smul`) and the transitivity of the symplectic group on transverse pairs
(`exists_smul_eq_horizontal_vertical`) we may take `V = {y = 0}`. The path is a catenation of the
pieces of `Maslov/Path/RegularPieces.lean`, joined at times that are not crossings:

* a rotation `rotationPath Λ ε` off the first end, for a small `ε > 0`, whose only crossing is its
  first point, with a definite crossing form;
* a chart segment (`exists_chartPath`) from the rotated end to `{x = 0}`, without crossings;
* at `{x = 0}`, `|k|` copies of the coordinate half-turn `coordinateHalfTurn i`, of index `1`, or
  of its reverse;
* a chart segment and the reverse of a rotation onto the last end.

The index of the result is that of the path with `k = 0`, plus `k`. By the values property
(`pathMaslovIndex_add_half_sub_mem`), that path and `γ` have indices that differ by an integer,
and `k` is chosen to be that integer.

At a junction the two frames span the same Lagrangian, so they differ by an invertible matrix
(`LagrangianGrassmannian.exists_mul_eq_of_range_eq`), and a constant change of frame on the later
piece makes them agree; such a change keeps the crossing forms up to isometry
(`lagrangianCrossingForm_mul_equivalent`). Each piece is first reparametrized so that its frame is
constant near the junctions: by Tau Ceti's `TauCeti.collaredSmoothTransition`, constant near both
ends, whose derivative is positive where it is neither `0` nor `1`
(`TauCeti.deriv_collaredSmoothTransition_pos`); and
for the rotations, whose first point is a crossing that must stay regular, by a map equal to the
identity near `0`. The glued frame is then smooth. Making the pieces stationary near the joining
time follows Tau Ceti's `TauCeti.SmoothIsotopy.trans`, which concatenates smooth isotopies with
`Real.smoothTransition` in the same way.

## References

* [J. Robbin and D. Salamon, *The Maslov index for paths*][RobbinSalamon1993], Theorem 1.1, §2
  (crossings, the crossing-form formula and the isolation of regular crossings) and Theorems
  2.3–2.4 (the properties of the index).
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3.
-/

public section

namespace SymplecticGeometry

open Matrix TauCeti Set Filter Topology
open scoped unitInterval ContDiff Matrix.Norms.Elementwise

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "ℒ" ι => LagrangianGrassmannian (stdForm ι)

namespace LagrangianGrassmannian

/-- `Z` is a smooth frame of the path `γ`, all of whose crossings with `V` are regular for the
derivative of `Z`. -/
private structure IsRegularFrame {Λ Λ' : ℒ ι} (γ : Path Λ Λ') (V : ℒ ι)
    (Z : ℝ → Matrix (ι ⊕ ι) ι ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ Z
  range_eq : ∀ t : I, LinearMap.range (toEuclideanLin (Z t)) = γ t
  nondegenerate : ∀ t : I, (γ t : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥ →
    (lagrangianCrossingForm (Z t) (deriv Z t) V).Nondegenerate

/-- A regular frame `Z` has the derivative `deriv Z s` at every time `s`. -/
private theorem IsRegularFrame.hasDerivAt {Λ Λ' : ℒ ι} {γ : Path Λ Λ'} {V : ℒ ι}
    {Z : ℝ → Matrix (ι ⊕ ι) ι ℝ} (h : IsRegularFrame γ V Z) (s : ℝ) :
    HasDerivAt Z (deriv Z s) s :=
  ((h.contDiff.differentiable (by simp)) s).hasDerivAt

/-- A reparametrization of a path by a smooth map `φ` of `[0, 1]`, whose derivative does not
vanish where the reparametrized path crosses `V`, keeps regular frames. -/
private theorem IsRegularFrame.reparam {Λ Λ' : ℒ ι} {γ : Path Λ Λ'} {V : ℒ ι}
    {Z : ℝ → Matrix (ι ⊕ ι) ι ℝ} (h : IsRegularFrame γ V Z) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφI : ∀ t : I, φ t ∈ I) (hφ0 : φ 0 = 0) (hφ1 : φ 1 = 1)
    (hcross : ∀ t : I, (γ ⟨φ t, hφI t⟩ : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥ → deriv φ t ≠ 0) :
    IsRegularFrame (γ.reparam (fun t ↦ ⟨φ t, hφI t⟩)
      ((hφ.continuous.comp continuous_subtypeVal).subtype_mk _) (Subtype.ext hφ0)
      (Subtype.ext hφ1)) V (Z ∘ φ) where
  contDiff := h.contDiff.comp hφ
  range_eq t := h.range_eq ⟨φ t, hφI t⟩
  nondegenerate t ht := by
    have hd : deriv (Z ∘ φ) t = deriv φ t • deriv Z (φ t) :=
      deriv.scomp (t : ℝ) ((h.contDiff.differentiable (by simp)) _)
        ((hφ.differentiable (by simp)) _)
    rw [hd, nondegenerate_lagrangianCrossingForm_smul_iff _ _ (hcross t ht)]
    exact h.nondegenerate ⟨φ t, hφI t⟩ ht

/-- Reversing a path keeps regular frames: the frame `s ↦ Z (1 - s)` has the derivative
`-Z' (1 - s)`, and negating a quadratic form keeps it nondegenerate. -/
private theorem IsRegularFrame.symm {Λ Λ' : ℒ ι} {γ : Path Λ Λ'} {V : ℒ ι}
    {Z : ℝ → Matrix (ι ⊕ ι) ι ℝ} (h : IsRegularFrame γ V Z) :
    IsRegularFrame γ.symm V (fun s ↦ Z (1 - s)) where
  contDiff := h.contDiff.comp (contDiff_const.sub contDiff_id)
  range_eq t := by simpa [unitInterval.coe_symm_eq] using h.range_eq (σ t)
  nondegenerate t ht := by
    have hd : deriv (fun s ↦ Z (1 - s)) t = (-1 : ℝ) • deriv Z (1 - t) :=
      ((h.hasDerivAt (1 - t)).scomp (t : ℝ) ((hasDerivAt_id' (t : ℝ)).const_sub 1)).deriv
    rw [hd, nondegenerate_lagrangianCrossingForm_smul_iff _ _ (by norm_num)]
    have := h.nondegenerate (σ t) (by simpa using ht)
    rwa [unitInterval.coe_symm_eq] at this

/-- A constant change of frame `Z ↦ Z * g`, for an invertible `g`, keeps regular frames. -/
private theorem IsRegularFrame.mul_const {Λ Λ' : ℒ ι} {γ : Path Λ Λ'} {V : ℒ ι}
    {Z : ℝ → Matrix (ι ⊕ ι) ι ℝ} (h : IsRegularFrame γ V Z) (g : GL ι ℝ) :
    IsRegularFrame γ V (fun s ↦ Z s * (g : Matrix ι ι ℝ)) where
  contDiff := h.contDiff.matrix_mul contDiff_const
  range_eq t := by rw [range_toLpLin_mul_of_isUnit 2 _ g.isUnit, h.range_eq t]
  nondegenerate t ht := by
    have hd : deriv (fun s ↦ Z s * (g : Matrix ι ι ℝ)) t = deriv Z t * (g : Matrix ι ι ℝ) :=
      ((h.hasDerivAt t).matrix_mul_const _).deriv
    have hiso : (stdForm ι).IsIsotropic (LinearMap.range (toEuclideanLin (Z t))) := by
      rw [h.range_eq t]; exact (γ t).isLagrangian.isIsotropic
    have e := lagrangianCrossingForm_mul_equivalent hiso (deriv Z t) V g 0
    rw [Matrix.mul_zero, add_zero] at e
    rw [hd]
    exact (Classical.choice e).nondegenerate_iff.1 (h.nondegenerate t ht)

/-- **Gluing frames.** If the frame of `γ₁` is constant near `1`, that of `γ₂` constant near `0`,
the two agree at the junction, and the junction is not a crossing, then the glued frame is a
regular frame of the catenation. -/
private theorem IsRegularFrame.trans {Λ₀ Λ₁ Λ₂ : ℒ ι} {γ₁ : Path Λ₀ Λ₁} {γ₂ : Path Λ₁ Λ₂}
    {V : ℒ ι} {Z₁ Z₂ : ℝ → Matrix (ι ⊕ ι) ι ℝ} (h₁ : IsRegularFrame γ₁ V Z₁)
    (h₂ : IsRegularFrame γ₂ V Z₂) (hZ₁ : Z₁ =ᶠ[𝓝 1] fun _ ↦ Z₁ 1)
    (hZ₂ : Z₂ =ᶠ[𝓝 0] fun _ ↦ Z₂ 0) (h₁₂ : Z₂ 0 = Z₁ 1)
    (hΛ₁ : (Λ₁ : Submodule ℝ (StdSpace ι)) ⊓ V = ⊥) :
    IsRegularFrame (γ₁.trans γ₂) V (curveTrans Z₁ Z₂) := by
  refine ⟨h₁.contDiff.curveTrans h₂.contDiff hZ₁ hZ₂ h₁₂.symm, fun t ↦ ?_, fun t ht ↦ ?_⟩
  · by_cases h : (t : ℝ) ≤ 1 / 2
    · rw [Path.trans_apply, dite_eq_left h, curveTrans_of_le_half h]
      exact h₁.range_eq
        ⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.property.1, h⟩⟩
    · rw [Path.trans_apply, dite_eq_right h, curveTrans_of_half_lt (not_le.1 h)]
      exact h₂.range_eq ⟨2 * (t : ℝ) - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.property.2⟩⟩
  · rw [Path.trans_apply] at ht
    rcases lt_trichotomy (t : ℝ) (1 / 2) with h | h | h
    · rw [dite_eq_left h.le] at ht
      have key := h₁.nondegenerate ⟨2 * (t : ℝ),
        unitInterval.mul_pos_mem_iff zero_lt_two |>.2 ⟨t.property.1, h.le⟩⟩ ht
      -- `deriv` in `IsRegularFrame` is for the default topology of matrices, and that of
      -- `HasDerivAt.curveTrans_of_lt_half` for the entrywise norm: equal, but not syntactically, so
      -- we state `hd` with the former before rewriting with it.
      have hd : deriv (curveTrans Z₁ Z₂) t = (2 : ℝ) • deriv Z₁ (2 * t) :=
        (HasDerivAt.curveTrans_of_lt_half (h₁.hasDerivAt (2 * t)) h).deriv
      rw [hd, curveTrans_of_le_half h.le,
        nondegenerate_lagrangianCrossingForm_smul_iff _ _ two_ne_zero]
      exact key
    · rw [dite_eq_left h.le] at ht
      refine absurd ?_ ht
      rw [show (⟨2 * (t : ℝ), _⟩ : I) = 1 from Subtype.ext (by simp [h]), γ₁.target]
      exact hΛ₁
    · rw [dite_eq_right (not_le.2 h)] at ht
      have key := h₂.nondegenerate ⟨2 * (t : ℝ) - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨h.le, t.property.2⟩⟩ ht
      have hd : deriv (curveTrans Z₁ Z₂) t = (2 : ℝ) • deriv Z₂ (2 * t - 1) :=
        (HasDerivAt.curveTrans_of_half_lt (h₂.hasDerivAt (2 * t - 1)) h).deriv
      rw [hd, curveTrans_of_half_lt h,
        nondegenerate_lagrangianCrossingForm_smul_iff _ _ two_ne_zero]
      exact key

/-! ### Flat reparametrizations -/

/-- A reparametrization of `[0, 1]` that is the identity near `0` and `1` from `3 / 4` on. -/
private noncomputable def startReparam (s : ℝ) : ℝ := s + (1 - s) * collaredSmoothTransition s

private theorem contDiff_startReparam : ContDiff ℝ ∞ startReparam :=
  contDiff_id.add ((contDiff_const.sub contDiff_id).mul (contDiff_collaredSmoothTransition le_rfl))

private theorem startReparam_mem {s : ℝ} (hs : s ∈ I) : startReparam s ∈ I := by
  have := collaredSmoothTransition_mem s
  constructor <;> simp only [startReparam] <;> nlinarith [hs.1, hs.2, this.1, this.2]

private theorem le_startReparam {s : ℝ} (hs : s ∈ I) : s ≤ startReparam s := by
  have := collaredSmoothTransition_mem s
  simp only [startReparam]
  nlinarith [hs.2, this.1]

private theorem startReparam_eventuallyEq_one : startReparam =ᶠ[𝓝 1] fun _ ↦ 1 := by
  filter_upwards [collaredSmoothTransition_eventuallyEq_one] with s hs
  simp [startReparam, hs]

private theorem deriv_startReparam_zero : deriv startReparam 0 = 1 := by
  have h : startReparam =ᶠ[𝓝 0] id := by
    filter_upwards [collaredSmoothTransition_eventuallyEq_zero] with s hs
    simp [startReparam, hs]
  rw [h.deriv_eq, deriv_id]

/-- **Flattening the ends.** A path with a regular frame whose ends are not crossings is homotopic
with fixed ends to one with a regular frame that is constant near both ends. -/
private theorem IsRegularFrame.exists_flat {Λ Λ' : ℒ ι} {γ : Path Λ Λ'} {V : ℒ ι}
    {Z : ℝ → Matrix (ι ⊕ ι) ι ℝ} (h : IsRegularFrame γ V Z)
    (hΛ : (Λ : Submodule ℝ (StdSpace ι)) ⊓ V = ⊥) (hΛ' : (Λ' : Submodule ℝ (StdSpace ι)) ⊓ V = ⊥) :
    ∃ (γ' : Path Λ Λ') (Z' : ℝ → Matrix (ι ⊕ ι) ι ℝ), γ.Homotopic γ' ∧ IsRegularFrame γ' V Z' ∧
      (Z' =ᶠ[𝓝 0] fun _ ↦ Z' 0) ∧ (Z' =ᶠ[𝓝 1] fun _ ↦ Z' 1) := by
  have hφ0 : collaredSmoothTransition 0 = 0 := collaredSmoothTransition_eq_zero_of_le (by norm_num)
  have hφ1 : collaredSmoothTransition 1 = 1 := collaredSmoothTransition_eq_one_of_ge (by norm_num)
  refine ⟨_, _, ⟨Path.Homotopy.reparam γ _ _ (Subtype.ext hφ0) (Subtype.ext hφ1)⟩,
    h.reparam (contDiff_collaredSmoothTransition le_rfl) (fun t ↦ collaredSmoothTransition_mem t)
      hφ0 hφ1 fun t ht ↦ ?_, ?_, ?_⟩
  · refine (deriv_collaredSmoothTransition_pos (fun h0 ↦ ht ?_) (fun h1 ↦ ht ?_)).ne'
    · rw [show (⟨collaredSmoothTransition t, _⟩ : I) = 0 from Subtype.ext h0, γ.source]; exact hΛ
    · rw [show (⟨collaredSmoothTransition t, _⟩ : I) = 1 from Subtype.ext h1, γ.target]; exact hΛ'
  · filter_upwards [collaredSmoothTransition_eventuallyEq_zero] with s hs
    simp [hs, hφ0]
  · filter_upwards [collaredSmoothTransition_eventuallyEq_one] with s hs
    simp [hs, hφ1]

/-- **Flattening the last end.** A path with a regular frame whose only crossing is at `0` is
homotopic with fixed ends to one with a regular frame that is constant near `1`. -/
private theorem IsRegularFrame.exists_flat_one {Λ Λ' : ℒ ι} {γ : Path Λ Λ'} {V : ℒ ι}
    {Z : ℝ → Matrix (ι ⊕ ι) ι ℝ} (h : IsRegularFrame γ V Z)
    (hγ : ∀ t : I, t ≠ 0 → (γ t : Submodule ℝ (StdSpace ι)) ⊓ V = ⊥) :
    ∃ (γ' : Path Λ Λ') (Z' : ℝ → Matrix (ι ⊕ ι) ι ℝ), γ.Homotopic γ' ∧ IsRegularFrame γ' V Z' ∧
      (Z' =ᶠ[𝓝 1] fun _ ↦ Z' 1) := by
  have hφ0 : startReparam 0 = 0 := by simp [startReparam, collaredSmoothTransition_eq_zero_of_le]
  have hφ1 : startReparam 1 = 1 := by simp [startReparam]
  refine ⟨_, _, ⟨Path.Homotopy.reparam γ _ _ (Subtype.ext hφ0) (Subtype.ext hφ1)⟩,
    h.reparam contDiff_startReparam (fun t ↦ startReparam_mem t.property) hφ0 hφ1
      fun t ht ↦ ?_, ?_⟩
  · have ht0 : t = 0 := by
      by_contra h0
      refine ht (hγ _ fun h' ↦ h0 (Subtype.ext (le_antisymm ?_ t.property.1)))
      have := le_startReparam t.property
      rw [show startReparam t = 0 from congrArg Subtype.val h'] at this
      exact this
    rw [ht0, Icc.coe_zero, deriv_startReparam_zero]
    exact one_ne_zero
  · filter_upwards [startReparam_eventuallyEq_one] with s hs
    simp [hs, hφ1]

/-- **Gluing frames**, with the change of frame at the junction. -/
private theorem IsRegularFrame.exists_trans {Λ₀ Λ₁ Λ₂ : ℒ ι} {γ₁ : Path Λ₀ Λ₁}
    {γ₂ : Path Λ₁ Λ₂} {V : ℒ ι} {Z₁ Z₂ : ℝ → Matrix (ι ⊕ ι) ι ℝ} (h₁ : IsRegularFrame γ₁ V Z₁)
    (h₂ : IsRegularFrame γ₂ V Z₂) (hZ₁ : Z₁ =ᶠ[𝓝 1] fun _ ↦ Z₁ 1)
    (hZ₂ : Z₂ =ᶠ[𝓝 0] fun _ ↦ Z₂ 0) (hΛ₁ : (Λ₁ : Submodule ℝ (StdSpace ι)) ⊓ V = ⊥) :
    ∃ Z : ℝ → Matrix (ι ⊕ ι) ι ℝ, IsRegularFrame (γ₁.trans γ₂) V Z ∧
      ((Z₁ =ᶠ[𝓝 0] fun _ ↦ Z₁ 0) → Z =ᶠ[𝓝 0] fun _ ↦ Z 0) ∧
      ((Z₂ =ᶠ[𝓝 1] fun _ ↦ Z₂ 1) → Z =ᶠ[𝓝 1] fun _ ↦ Z 1) := by
  obtain ⟨g, hg⟩ := exists_mul_eq_of_range_eq (by simpa using h₁.range_eq 1)
    (by simpa using h₂.range_eq 0)
  have hZ₂g : (fun s ↦ Z₂ s * (g : Matrix ι ι ℝ)) =ᶠ[𝓝 0] fun _ ↦ Z₂ 0 * (g : Matrix ι ι ℝ) := by
    filter_upwards [hZ₂] with s hs
    rw [hs]
  refine ⟨_, (h₁.trans (h₂.mul_const g) hZ₁ hZ₂g hg hΛ₁), curveTrans_eventuallyEq_zero,
    fun h ↦ curveTrans_eventuallyEq_one ?_⟩
  filter_upwards [h] with s hs
  rw [hs]

/-! ### Regular pieces -/

/-- The rotation `rotationPath Λ ε`, framed by `s ↦ rotationFrame Z (ε s)`, is regular when it
has no crossing but at `0`. -/
private theorem isRegularFrame_rotationPath {Λ : ℒ ι} {Z : Matrix (ι ⊕ ι) ι ℝ}
    (hZ : LinearMap.range (toEuclideanLin Z) = Λ) {ε : ℝ} (hε : ε ≠ 0) (V : ℒ ι)
    (hγ : ∀ t : I, t ≠ 0 → (rotationPath Λ ε t : Submodule ℝ (StdSpace ι)) ⊓ V = ⊥) :
    IsRegularFrame (rotationPath Λ ε) V fun s ↦ rotationFrame Z (ε * s) where
  contDiff := (contDiff_rotationFrame Z).comp (contDiff_const.mul contDiff_id)
  range_eq t := by rw [rotationPath_apply, range_rotationFrame hZ]
  nondegenerate t ht := by
    obtain rfl : t = 0 := by_contra fun h ↦ ht (hγ t h)
    have hd := hasDerivAt_rotationFrame_comp Z ((hasDerivAt_id' (0 : ℝ)).const_mul ε)
    rw [mul_one] at hd
    have hd' : deriv (fun s ↦ rotationFrame Z (ε * s)) 0 = ε • (J ι ℝ * rotationFrame Z (ε * 0)) :=
      hd.deriv
    rw [Icc.coe_zero, hd', mul_zero, rotationFrame_zero]
    exact (anisotropic_lagrangianCrossingForm_smul_J_mul
      (injective_toEuclideanLin_of_range_eq hZ) hε V).nondegenerate

/-- A rotation off `Λ` by a small positive angle has a regular frame constant near its last end,
up to homotopy with fixed ends, and its last end is transverse to `V`. -/
private theorem exists_rotation (Λ V : ℒ ι) :
    ∃ (ε : ℝ) (γ : Path Λ (rotate ε Λ)) (Z : ℝ → Matrix (ι ⊕ ι) ι ℝ),
      ((rotate ε Λ : ℒ ι) : Submodule ℝ (StdSpace ι)) ⊓ V = ⊥ ∧ IsRegularFrame γ V Z ∧
      (Z =ᶠ[𝓝 1] fun _ ↦ Z 1) := by
  obtain ⟨ε, hε, hε0⟩ := ((eventually_rotationPath_inf_eq_bot Λ V).filter_mono
    (nhdsWithin_mono _ fun _ h ↦ ne_of_gt h)).and self_mem_nhdsWithin |>.exists
      (f := 𝓝[>] (0 : ℝ))
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (ι ⊕ ι) ι ℝ, LinearMap.range (toEuclideanLin Z) = Λ := by
    obtain ⟨U, rfl⟩ := unitaryFrame_surjective Λ
    exact ⟨_, (coe_unitaryFrame U).symm⟩
  obtain ⟨γ, Z', -, hγ, hZ'⟩ :=
    (isRegularFrame_rotationPath hZ (ne_of_gt hε0) V hε).exists_flat_one hε
  refine ⟨ε, γ, Z', ?_, hγ, hZ'⟩
  simpa using hε 1 one_ne_zero

/-- The flattened chart segment between two Lagrangians transverse to `{y = 0}`. -/
private theorem exists_chart {Λ Λ' : ℒ ι}
    (hΛ : (Λ : Submodule ℝ (StdSpace ι)) ⊓ horizontal ι = ⊥)
    (hΛ' : (Λ' : Submodule ℝ (StdSpace ι)) ⊓ horizontal ι = ⊥) :
    ∃ (γ : Path Λ Λ') (Z : ℝ → Matrix (ι ⊕ ι) ι ℝ), IsRegularFrame γ (horizontal ι) Z ∧
      (Z =ᶠ[𝓝 0] fun _ ↦ Z 0) ∧ (Z =ᶠ[𝓝 1] fun _ ↦ Z 1) := by
  have hc {L : ℒ ι} (h : (L : Submodule ℝ (StdSpace ι)) ⊓ horizontal ι = ⊥) :
      IsCompl (L : Submodule ℝ (StdSpace ι)) (horizontal ι) :=
    (isCompl_iff_disjoint _ _).2 (disjoint_iff.2 h)
  obtain ⟨γ, Z, -, hZ, -, hγ, hγV⟩ := exists_chartPath (hc hΛ) (hc hΛ')
  obtain ⟨γ', Z', -, h, h₀, h₁⟩ :=
    (IsRegularFrame.mk hZ hγ fun t ht ↦ absurd (hγV t) ht).exists_flat hΛ hΛ'
  exact ⟨γ', Z', h, h₀, h₁⟩

/-- The coordinate half-turn, framed by `s ↦ coordinateRotationFrame i (π s)`, is regular. -/
private theorem isRegularFrame_coordinateHalfTurn (i : ι) :
    IsRegularFrame (coordinateHalfTurn i) (horizontal ι)
      fun s ↦ coordinateRotationFrame i (Real.pi * s) where
  contDiff := (contDiff_coordinateRotationFrame i).comp (contDiff_const.mul contDiff_id)
  range_eq t := by rw [coordinateHalfTurn_apply, range_coordinateRotationFrame]
  nondegenerate t ht := by
    have ht' := (coordinateHalfTurn_inf_horizontal_ne_bot_iff i t).1 ht
    have hd := hasDerivAt_coordinateRotationFrame_comp i
      ((hasDerivAt_id' (t : ℝ)).const_mul Real.pi)
    rw [mul_one] at hd
    have hπ : Real.pi * (t : ℝ) = Real.pi / 2 := by rw [ht']; ring
    rw [hπ] at hd
    have hd' : deriv (fun s ↦ coordinateRotationFrame i (Real.pi * s)) t =
        Real.pi • fromRows (-single i i (Real.cos (Real.pi / 2)))
          (-single i i (Real.sin (Real.pi / 2))) :=
      hd.deriv
    rw [hd', hπ]
    exact
      (posDef_lagrangianCrossingForm_coordinateRotationFrame_pi_div_two i).anisotropic.nondegenerate

/-- For every integer `k`, a loop at `{x = 0}` of index `k` relative to `{y = 0}` with a regular
frame constant near both ends: a catenation of copies of the flattened coordinate half-turn, or
of its reverse. -/
private theorem exists_loop_vertical (i : ι) (k : ℤ) :
    ∃ (γ : Path (vertical ι) (vertical ι)) (Z : ℝ → Matrix (ι ⊕ ι) ι ℝ),
      pathMaslovIndex γ (horizontal ι) = k ∧ IsRegularFrame γ (horizontal ι) Z ∧
      (Z =ᶠ[𝓝 0] fun _ ↦ Z 0) ∧ (Z =ᶠ[𝓝 1] fun _ ↦ Z 1) := by
  have hV₁ : ((vertical ι : ℒ ι) : Submodule ℝ (StdSpace ι)) ⊓ horizontal ι = ⊥ :=
    isCompl_horizontal_vertical.symm.inf_eq_bot
  obtain ⟨H, ZH, hH, hreg, hH₀, hH₁⟩ := (isRegularFrame_coordinateHalfTurn i).exists_flat
    hV₁ hV₁
  have hsub (a b : ℝ) (h : 1 - a = b) : Tendsto (fun s : ℝ ↦ 1 - s) (𝓝 a) (𝓝 b) :=
    (continuous_const.sub continuous_id).tendsto' a b h
  have hHi : pathMaslovIndex H (horizontal ι) = 1 := by
    rw [← pathMaslovIndex_eq_of_homotopic hH, pathMaslovIndex_coordinateHalfTurn]
  induction k using Int.induction_on with
  | zero =>
    refine ⟨Path.refl _, fun _ ↦ fromRows 0 1, by simp [pathMaslovIndex_refl],
      ⟨contDiff_const, fun t ↦ ?_, fun t ht ↦ absurd hV₁ (by simpa using ht)⟩,
      EventuallyEq.rfl, EventuallyEq.rfl⟩
    rw [Path.refl_apply, StdSpace.range_toEuclideanLin_fromRows_one_eq_graphY,
      StdSpace.graphY_zero, coe_vertical]
  | succ k ih =>
    obtain ⟨γ, Z, hγ, hZ, hZ₀, hZ₁⟩ := ih
    obtain ⟨Z', hZ', h₀, h₁⟩ := hreg.exists_trans hZ hH₁ hZ₀ hV₁
    refine ⟨H.trans γ, Z', ?_, hZ', h₀ hH₀, h₁ hZ₁⟩
    rw [pathMaslovIndex_trans, hHi, hγ]
    push_cast
    ring
  | pred k ih =>
    obtain ⟨γ, Z, hγ, hZ, hZ₀, hZ₁⟩ := ih
    obtain ⟨Z', hZ', h₀, h₁⟩ := hreg.symm.exists_trans hZ
      (by simpa [Function.comp_def] using hH₀.comp_tendsto (hsub 1 0 (by norm_num))) hZ₀ hV₁
    refine ⟨H.symm.trans γ, Z', ?_, hZ',
      h₀ (by simpa [Function.comp_def] using hH₁.comp_tendsto (hsub 0 1 (by norm_num))), h₁ hZ₁⟩
    rw [pathMaslovIndex_trans, pathMaslovIndex_symm, hHi, hγ]
    push_cast
    ring

/-- Relative to `{y = 0}`, every path has a regular frame up to a change that keeps the index:
a rotation off the first end, a chart segment to `{x = 0}`, a loop there of the right index, a
chart segment and the reverse of a rotation onto the last end. -/
private theorem exists_regular_horizontal [Nonempty ι] {Λ Λ' : ℒ ι} (γ : Path Λ Λ') :
    ∃ (γ' : Path Λ Λ') (Z : ℝ → Matrix (ι ⊕ ι) ι ℝ),
      pathMaslovIndex γ' (horizontal ι) = pathMaslovIndex γ (horizontal ι) ∧
      IsRegularFrame γ' (horizontal ι) Z := by
  have hV₁ : ((vertical ι : ℒ ι) : Submodule ℝ (StdSpace ι)) ⊓ horizontal ι = ⊥ :=
    isCompl_horizontal_vertical.symm.inf_eq_bot
  obtain ⟨ε, A, ZA, hε, hA, hA₁⟩ := exists_rotation Λ (horizontal ι)
  obtain ⟨ε', B, ZB, hε', hB, hB₁⟩ := exists_rotation Λ' (horizontal ι)
  obtain ⟨C, ZC, hC, hC₀, hC₁⟩ := exists_chart hε hV₁
  obtain ⟨D, ZD, hD, hD₀, hD₁⟩ := exists_chart hV₁ hε'
  choose M ZM hMi hM hM₀ hM₁ using exists_loop_vertical (ι := ι) (Classical.arbitrary ι)
  let P (k : ℤ) : Path Λ Λ' := A.trans (C.trans ((M k).trans (D.trans B.symm)))
  have hP (k : ℤ) : pathMaslovIndex (P k) (horizontal ι) =
      pathMaslovIndex A (horizontal ι) + pathMaslovIndex C (horizontal ι) +
        pathMaslovIndex D (horizontal ι) - pathMaslovIndex B (horizontal ι) + k := by
    simp only [P, pathMaslovIndex_trans, pathMaslovIndex_symm, hMi]
    ring
  obtain ⟨a, ha⟩ := pathMaslovIndex_add_half_sub_mem γ (horizontal ι)
  obtain ⟨b, hb⟩ := pathMaslovIndex_add_half_sub_mem (P 0) (horizontal ι)
  refine ⟨P (a - b), ?_⟩
  have hB₁' := hB₁.comp_tendsto
    ((by fun_prop : Continuous fun s : ℝ ↦ 1 - s).tendsto' 0 1 (by norm_num))
  obtain ⟨Z₁, h₁, h₁₀, -⟩ := hD.exists_trans hB.symm hD₁
    (by simpa [Function.comp_def] using hB₁') hε'
  obtain ⟨Z₂, h₂, h₂₀, -⟩ := (hM (a - b)).exists_trans h₁ (hM₁ _) (h₁₀ hD₀) hV₁
  obtain ⟨Z₃, h₃, h₃₀, -⟩ := hC.exists_trans h₂ hC₁ (h₂₀ (hM₀ _)) hV₁
  obtain ⟨Z₄, h₄, -, -⟩ := hA.exists_trans h₃ hA₁ (h₃₀ hC₀) hε
  refine ⟨Z₄, ?_, h₄⟩
  rw [hP, Int.cast_sub]
  rw [hP 0, Int.cast_zero, add_zero] at hb
  linarith

/-- A symplectic matrix `g` carries a regular frame `Z` of `γ` relative to `V` to the regular
frame `g Z` of the moved path relative to `g • V`. -/
private theorem IsRegularFrame.smul {Λ Λ' : ℒ ι} {γ : Path Λ Λ'} {V : ℒ ι}
    {Z : ℝ → Matrix (ι ⊕ ι) ι ℝ} (h : IsRegularFrame γ V Z) (g : GLSymplectic ι ℝ) :
    IsRegularFrame (γ.map (continuous_const_smul g)) (g • V)
      fun s ↦ ((g : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) * Z s where
  contDiff := contDiff_const.matrix_mul h.contDiff
  range_eq t := (coe_smul_of_coe_eq g (h.range_eq t).symm).symm
  nondegenerate t ht := by
    set M := ((g : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
    have hM : M ∈ symplecticGroup ι ℝ := GLSymplectic.mem_iff_mem_symplecticGroup.1 g.property
    have hcross : (γ t : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥ := by
      rwa [Path.map_coe, Function.comp_apply, Ne, ← Submodule.finrank_eq_zero,
        finrank_smul_inf_smul, Submodule.finrank_eq_zero] at ht
    have hd : deriv (fun s ↦ M * Z s) t = M * deriv Z t :=
      ((h.hasDerivAt t).matrix_const_mul M).deriv
    have e := lagrangianCrossingForm_symplectic_mul_equivalent hM (Z t) (deriv Z t) V
    rw [← coe_smul] at e
    rw [hd]
    exact (Classical.choice e).nondegenerate_iff.1 (h.nondegenerate t hcross)

/-- Every path has a regular frame relative to `V`, up to a change of path that keeps the
index relative to `V`. -/
private theorem exists_regular {Λ Λ' : ℒ ι} (γ : Path Λ Λ') (V : ℒ ι) :
    ∃ (γ' : Path Λ Λ') (Z : ℝ → Matrix (ι ⊕ ι) ι ℝ),
      pathMaslovIndex γ' V = pathMaslovIndex γ V ∧ IsRegularFrame γ' V Z := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- In dimension zero every subspace is `0`.
    have hbot (L : ℒ ι) : (L : Submodule ℝ (StdSpace ι)) = ⊥ :=
      Submodule.finrank_eq_zero.1 (by rw [finrank_eq_card, Fintype.card_eq_zero])
    refine ⟨γ, 0, rfl, contDiff_const, fun t ↦ ?_, fun t ht ↦ absurd ?_ ht⟩
    · rw [hbot, Pi.zero_apply, map_zero, LinearMap.range_zero]
    · rw [hbot, bot_inf_eq]
  · obtain ⟨W, hW, -⟩ := exists_isCompl_isCompl V V
    obtain ⟨g, hgV, -⟩ := exists_smul_eq_horizontal_vertical hW.symm
    obtain ⟨P, Z, hP, hZ⟩ := exists_regular_horizontal (γ.map (continuous_const_smul g⁻¹))
    have hreg := hZ.smul g
    rw [hgV] at hreg
    refine ⟨(P.map (continuous_const_smul g)).cast (by rw [smul_inv_smul])
      (by rw [smul_inv_smul]), _, ?_, hreg.contDiff, hreg.range_eq, hreg.nondegenerate⟩
    have hV : horizontal ι = g⁻¹ • V := by rw [← hgV, inv_smul_smul]
    calc pathMaslovIndex ((P.map (continuous_const_smul g)).cast _ _) V
        = pathMaslovIndex (P.map (continuous_const_smul g)) (g • horizontal ι) := by
          rw [hgV]
          exact pathMaslovIndex_congr _ _ (fun _ ↦ by rfl) V
      _ = pathMaslovIndex (γ.map (continuous_const_smul g⁻¹)) (g⁻¹ • V) := by
          rw [pathMaslovIndex_smul, hP, ← hV]
      _ = pathMaslovIndex γ V := pathMaslovIndex_smul _ _ _

/-- **Regular representatives.** Every path `γ` of Lagrangian subspaces is homotopic with fixed
ends to a path `γ'` with a smooth frame `Z`, with derivative `Z'`, all of whose crossings with
`V` are regular: at each `t` where `γ' t` meets `V` nontrivially, the crossing form
`lagrangianCrossingForm (Z t) (Z' t) V` is nondegenerate. Smoothness is stated for the entrywise
norm on matrices. -/
theorem exists_homotopic_regular {Λ Λ' : ℒ ι} (γ : Path Λ Λ') (V : ℒ ι) :
    ∃ γ' : Path Λ Λ', γ.Homotopic γ' ∧ ∃ Z Z' : ℝ → Matrix (ι ⊕ ι) ι ℝ, ContDiff ℝ ∞ Z ∧
      (∀ s, HasDerivAt Z (Z' s) s) ∧
      (∀ t : I, LinearMap.range (toEuclideanLin (Z t)) = γ' t) ∧
      ∀ t : I, (γ' t : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥ →
        (lagrangianCrossingForm (Z t) (Z' t) V).Nondegenerate := by
  obtain ⟨γ', Z, hγ', hZ⟩ := exists_regular γ V
  exact ⟨γ', (pathMaslovIndex_eq_iff_homotopic V).1 hγ'.symm, Z, deriv Z, hZ.contDiff,
    hZ.hasDerivAt, hZ.range_eq, hZ.nondegenerate⟩

end LagrangianGrassmannian

open LagrangianGrassmannian

universe v

/-- **The Maslov index for paths of Lagrangian subspaces.** For the Robbin–Salamon index
`pathMaslovIndex γ V` of paths `γ` in `ℒ ι` relative to a Lagrangian `V`:
* regular crossings are isolated;
* if a frame `Z` of `γ` has a derivative `Z'` at every crossing, where the crossing form
  `lagrangianCrossingForm (Z t) (Z' t) V` is nondegenerate, then the index is the sum of the
  signatures of the crossing forms, those at `0` and `1` counting one half;
* every path is homotopic with fixed ends to one with a smooth frame and only regular crossings;
* the crossing form does not depend on the frame: replacing the frame `Z` and its derivative
  `Z'` by `Z g` and `Z' g + Z h` keeps its value on each vector `Z g w = Z (g w)` that lies
  in `V`;
* naturality under `Sp(2n)`, catenation, the product property for direct sums, localization
  relative to `{y = 0}` when each `γ t` is the graph `{(x, A t x)}`, with `A` continuous,
  homotopy (two paths with the same ends have the same index if and only if they are homotopic
  with fixed ends), zero (for paths whose intersection with `V` has constant dimension), the
  values `μ(γ, V) + (dim(Λ ∩ V) - dim(Λ' ∩ V)) / 2 ∈ ℤ`, the difference of the indices relative
  to two Lagrangians depending only on the ends of the path, and on loops the angle formula
  `(α 1 - α 0) / π` for `det δ(t) = e^{iα(t)}` along a path `δ` of unitary frames;

each for every `V`.

Milestone: *Maslov index for paths of Lagrangian subspaces*. -/
theorem pathMaslovIndex_eq_crossing_sum_and_properties :
    (∀ (γ : I → ℒ ι) (V : ℒ ι) {Z : ℝ → Matrix (ι ⊕ ι) ι ℝ} {Z' : Matrix (ι ⊕ ι) ι ℝ} {t₀ : I},
      (∀ t : I, LinearMap.range (toEuclideanLin (Z t)) = γ t) →
      HasDerivWithinAt Z Z' (Icc 0 1) t₀ →
      (lagrangianCrossingForm (Z t₀) Z' V).Nondegenerate →
      ∀ᶠ t in 𝓝[≠] t₀, (γ t : Submodule ℝ (StdSpace ι)) ⊓ V = ⊥) ∧
    (∀ {Λ Λ' : ℒ ι} (γ : Path Λ Λ') (V : ℒ ι) {Z Z' : ℝ → Matrix (ι ⊕ ι) ι ℝ},
      (∀ t : I, LinearMap.range (toEuclideanLin (Z t)) = γ t) →
      (∀ t : I, (γ t : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥ →
        HasDerivWithinAt Z (Z' t) (Icc 0 1) t) →
      (∀ t : I, (γ t : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥ →
        (lagrangianCrossingForm (Z t) (Z' t) V).Nondegenerate) →
      pathMaslovIndex γ V =
        (((lagrangianCrossingForm (Z 0) (Z' 0) V).signature +
            (lagrangianCrossingForm (Z 1) (Z' 1) V).signature : ℤ) : ℝ) / 2 +
          ((∑ᶠ t ∈ Ioo (0 : ℝ) 1, (lagrangianCrossingForm (Z t) (Z' t) V).signature : ℤ) : ℝ)) ∧
    (∀ {Λ Λ' : ℒ ι} (γ : Path Λ Λ') (V : ℒ ι),
      ∃ γ' : Path Λ Λ', γ.Homotopic γ' ∧ ∃ Z Z' : ℝ → Matrix (ι ⊕ ι) ι ℝ, ContDiff ℝ ∞ Z ∧
        (∀ s, HasDerivAt Z (Z' s) s) ∧
        (∀ t : I, LinearMap.range (toEuclideanLin (Z t)) = γ' t) ∧
        ∀ t : I, (γ' t : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥ →
          (lagrangianCrossingForm (Z t) (Z' t) V).Nondegenerate) ∧
    (∀ {Z : Matrix (ι ⊕ ι) ι ℝ}, (stdForm ι).IsIsotropic (LinearMap.range (toEuclideanLin Z)) →
      ∀ (Z' : Matrix (ι ⊕ ι) ι ℝ) (V : Submodule ℝ (StdSpace ι)) (g h : Matrix ι ι ℝ)
        (w : V.comap (toEuclideanLin (Z * g))),
        lagrangianCrossingForm (Z * g) (Z' * g + Z * h) V w =
          lagrangianCrossingForm Z Z' V ⟨toEuclideanLin g w, by
            simpa [toLpLin_mul_same] using w.property⟩) ∧
    (∀ (Ψ : GLSymplectic ι ℝ) {Λ Λ' : ℒ ι} (γ : Path Λ Λ') (V : ℒ ι),
      pathMaslovIndex (γ.map (continuous_const_smul Ψ)) (Ψ • V) = pathMaslovIndex γ V) ∧
    (∀ {Λ Λ' : ℒ ι} (γ : Path Λ Λ') (c : I) (V : ℒ ι),
      pathMaslovIndex γ V =
        pathMaslovIndex (γ.subpath 0 c) V + pathMaslovIndex (γ.subpath c 1) V) ∧
    (∀ (κ : Type v) [Fintype κ] [DecidableEq κ] {Λ₀ Λ₁ : ℒ ι} {Λ₀' Λ₁' : ℒ κ}
      (γ : Path Λ₀ Λ₁) (γ' : Path Λ₀' Λ₁') (V : ℒ ι) (V' : ℒ κ),
      pathMaslovIndex ((γ.prod γ').map continuous_sum) (sum (V, V')) =
        pathMaslovIndex γ V + pathMaslovIndex γ' V') ∧
    (∀ {Λ Λ' : ℒ ι} (γ : Path Λ Λ') {A : I → Matrix ι ι ℝ},
      (∀ t, (γ t : Submodule ℝ (StdSpace ι)) = StdSpace.graph (A t)) →
      pathMaslovIndex γ (horizontal ι) = ((A 1).signature - (A 0).signature : ℝ) / 2) ∧
    (∀ {Λ Λ' : ℒ ι} {γ γ' : Path Λ Λ'} (V : ℒ ι),
      pathMaslovIndex γ V = pathMaslovIndex γ' V ↔ γ.Homotopic γ') ∧
    (∀ {Λ Λ' : ℒ ι} (γ : Path Λ Λ') (V : ℒ ι) {k : ℕ},
      (∀ t, Module.finrank ℝ
        ↥((γ t : Submodule ℝ (StdSpace ι)) ⊓ (V : Submodule ℝ (StdSpace ι))) = k) →
      pathMaslovIndex γ V = 0) ∧
    (∀ {Λ Λ' : ℒ ι} (γ : Path Λ Λ') (V : ℒ ι),
      pathMaslovIndex γ V +
          ((Module.finrank ℝ ↥((Λ : Submodule ℝ (StdSpace ι)) ⊓ V) : ℝ) -
            Module.finrank ℝ ↥((Λ' : Submodule ℝ (StdSpace ι)) ⊓ V)) / 2 ∈
        Set.range (Int.cast : ℤ → ℝ)) ∧
    (∀ {Λ Λ' : ℒ ι} (γ γ' : Path Λ Λ') (V V' : ℒ ι),
      pathMaslovIndex γ V' - pathMaslovIndex γ V =
        pathMaslovIndex γ' V' - pathMaslovIndex γ' V) ∧
    (∀ {Λ : ℒ ι} (γ : Path Λ Λ) (V : ℒ ι) {U U' : unitaryGroup ι ℂ} (δ : Path U U'),
      (∀ t, unitaryFrame (δ t) = γ t) → ∀ {α : I → ℝ}, Continuous α →
      (∀ t, (δ t : Matrix ι ι ℂ).det = Complex.exp (α t * Complex.I)) →
      pathMaslovIndex γ V = (α 1 - α 0) / Real.pi) :=
  ⟨eventually_not_crossing_of_regular, pathMaslovIndex_eq_crossing_sum,
    exists_homotopic_regular, lagrangianCrossingForm_mul_apply, pathMaslovIndex_smul,
    pathMaslovIndex_eq_subpath_add, fun _ _ _ _ _ _ _ ↦ pathMaslovIndex_sum,
    pathMaslovIndex_graph, pathMaslovIndex_eq_iff_homotopic,
    pathMaslovIndex_eq_zero_of_finrank_eq, pathMaslovIndex_add_half_sub_mem,
    pathMaslovIndex_sub_pathMaslovIndex, fun γ V _ _ δ hδ _ hα h ↦
      pathMaslovIndex_eq_sub_div_pi γ V δ hδ hα h⟩

end SymplecticGeometry

end
