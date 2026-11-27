/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Blowup.Normalized.Basic
public import SymplecticGeometry.Geometry.Symplectic.Blowup.Weight.Basic
public import SymplecticGeometry.Geometry.Symplectic.Complex.Radial
import SymplecticGeometry.Geometry.Symplectic.Manifold.SymplecticMap

/-!
# The blowup form and the blowup of weight `l`

Let `ψ` be a normalized ball embedding of radius `r`, weight `l` and width `ε` for a normalization
`hN` of `(σ, J)` at `p₀`, let `c = hN.blowupChart`, and let `h` be a profile of the blowup of
weight `l` with collar `ε`, with radial map `F_h z = √(h(|z|²) / |z|²) z`. For `0 < ε' ≤ ε`, this
file compares the blowup `Blowup c` of `M` at `p₀`, with the form `ω̃_{ψ,l,ε}` of
`Blowup/Normalized/Basic.lean`, with the blowup `WeightBlowup` of weight `l` with collar `ε'`
along `ψ`, with its form `ω̃_ψ` of `Blowup/Weight/Basic.lean`: they are symplectomorphic
(McDuff–Salamon, Theorem 7.1.21 (ii)).

The map is built in the direction from the blowup of weight `l`, which is glued from two pieces,
so that `GluedAlong.descDiffeomorph` applies. On the model piece `openNbhd n ε'` it is the lift
`ψ̃`. On the outer piece `M ∖ ψ(B(l))` it is `radialContraction`, the map `ψ ∘ F_h⁻¹ ∘ ψ⁻¹`
inside the image of the open ball and the identity outside, followed by the inclusion of
`M ∖ p₀` in `Blowup c`. The two agree on the overlap since `F_h` is the radial map `F_l` of the
model on `B(ε)`, which glues the blowup of weight `l`, and `ψ̃` is `ψ ∘ π` off the divisor.
Both are injective local diffeomorphisms whose images cover `Blowup c`, the inverse of
`radialContraction` being `radialExpansion`, the map `ψ ∘ F_h ∘ ψ⁻¹`.

The forms are compared on the two pieces, by `WeightBlowup.eq_form_iff`. On the model piece,
`ψ̃` pulls `ω̃_{ψ,l,ε}` back to `ω̃_{l,ε}`, which is `ω̃_l` on `L(ε)`. On the outer piece, off
`ψ(B(l + ε))` the form is the pull-back of `σ` by the blowdown, and on the image of the open ball
it is pulled back to `σ` along `ψ̃ ∘ π⁻¹ ∘ F_h⁻¹ ∘ ψ⁻¹`, since `π⁻¹` pulls `ω̃_{l,ε}` back to
`F_h^* ω₀` (`BlowupModel.mpullback_radialMap_profileForm`) and `ψ` pulls `σ` back to `ω₀`.

## Main definitions

* `SymplecticGeometry.IsSymplecticBallEmbedding.radialContraction hψ hh`: the map
  `ψ ∘ F_h⁻¹ ∘ ψ⁻¹` of `M`, extended by the identity, and
  `SymplecticGeometry.IsSymplecticBallEmbedding.radialExpansion hψ hh`, the map `ψ ∘ F_h ∘ ψ⁻¹`
  of `M`, extended by the identity.
* `SymplecticGeometry.IsNormalizedBallEmbedding.normalizedBlowupSymplectomorph hψ hh hε' hε'ε`:
  the diffeomorphism from `Blowup c` onto the blowup of weight `l` with collar `ε'` along `ψ`.

## Main results

* `SymplecticGeometry.IsSymplecticBallEmbedding.radialContraction_radialExpansion`,
  `radialExpansion_radialContraction`: for `l + ε < r`, the two maps are inverse to each other,
  between `M ∖ ψ 0` and `M ∖ ψ(B(l))`.
* `SymplecticGeometry.IsSymplecticBallEmbedding.isLocalDiffeomorphAt_radialContraction`: for
  `l + ε < r`, `radialContraction` is a local diffeomorphism off `ψ(B(l))`; near each point of
  `ψ(B°(r)) ∖ ψ(B(l))` it is `ψ ∘ F_h⁻¹` after a local lift of `ψ⁻¹` into the shell of `h`
  (`exists_radialContraction_eventuallyEq`).
* `SymplecticGeometry.IsNormalizedBallEmbedding.normalizedBlowupSymplectomorph_ballLift`,
  `normalizedBlowupSymplectomorph_inl`, `normalizedBlowupSymplectomorph_inl_radialContraction`:
  the diffeomorphism on the two pieces.
* `SymplecticGeometry.IsNormalizedBallEmbedding.isSymplectomorphism_normalizedBlowupSymplectomorph`:
  it is a symplectomorphism from `ω̃_{ψ,l,ε}` to `ω̃_ψ` (McDuff–Salamon, Theorem 7.1.21 (ii)).

## Implementation notes

The radius `√(l² + ε'²)` of the blowup of weight `l` is at most `l + ε' ≤ l + ε < r`, so `ψ` is a
ball embedding of that radius (`isSymplecticBallEmbedding_sqrt`) and no further hypothesis is
needed. The statements hold for every profile `h` of the blowup, the default of
`normalizedBlowupForm` being `blowupProfile l ε`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1,
  Theorem 7.1.21 (ii).
-/

public section

noncomputable section

open Set Metric Topology
open scoped ContDiff Manifold

namespace SymplecticGeometry

open TauCeti

namespace IsSymplecticBallEmbedding

open BlowupModel

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M] {σ : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) M}
  {ψ : StdSpace (Fin (n + 1)) → M} {r l ε : ℝ} {h : ℝ → ℝ}

variable (hψ : IsSymplecticBallEmbedding σ r ψ) (hh : IsBlowupProfile l ε h)

/-- A point of `ψ(B°(r)) ∖ ψ(B(l))`, read in `E` through `ψ`, lies in the shell `|w| > l` of the
radial map of `h`. -/
theorem complexPartialDiffeomorph_symm_mem_radialShell {p : M}
    (hp : p ∈ ψ '' ball 0 r ∧ p ∉ ψ '' closedBall 0 l) :
    hψ.complexPartialDiffeomorph.symm p ∈
      radialShell (Fin (n + 1)) h hh.contDiff.contDiffOn (fun s _ ↦ hh.deriv_pos s) := by
  rw [hh.mem_radialShell_iff]
  exact not_le.1 fun hle ↦ hp.2 ⟨_, mem_closedBall_zero_iff.2 hle,
    hψ.apply_complexToRealEuclidean_complexPartialDiffeomorph_symm hp.1⟩

open scoped Classical in
/-- The map `ψ ∘ F_h⁻¹ ∘ ψ⁻¹` of `M`, for the radial map `F_h` of a profile `h` of the blowup of
weight `l` with collar `ε`: on `ψ(B°(r)) ∖ ψ(B(l))` it is `ψ ∘ F_h⁻¹ ∘ ψ⁻¹`, and elsewhere the
identity. It is the identity off `ψ(B(l + ε))` (`radialContraction_of_notMem`), and for
`l + ε < r` it undoes `ψ ∘ F_h ∘ ψ⁻¹` (`radialContraction_radialMap`). -/
def radialContraction (p : M) : M :=
  if hp : p ∈ ψ '' ball 0 r ∧ p ∉ ψ '' closedBall 0 l then
    hψ.complexPartialDiffeomorph
      ((hh.radialDiffeomorph n).symm ⟨_, hψ.complexPartialDiffeomorph_symm_mem_radialShell hh hp⟩ :
        Fin (n + 1) → ℂ)
  else p

/-- On `ψ(B°(r)) ∖ ψ(B(l))`, `radialContraction` is `ψ ∘ F_h⁻¹ ∘ ψ⁻¹`. -/
theorem radialContraction_of_mem {p : M} (hp : p ∈ ψ '' ball 0 r ∧ p ∉ ψ '' closedBall 0 l) :
    hψ.radialContraction hh p = hψ.complexPartialDiffeomorph
      ((hh.radialDiffeomorph n).symm ⟨_, hψ.complexPartialDiffeomorph_symm_mem_radialShell hh hp⟩ :
        Fin (n + 1) → ℂ) :=
  dite_eq_left hp

/-- `radialContraction` is the identity off `ψ(B°(r)) ∖ ψ(B(l))`. -/
theorem radialContraction_of_not {p : M} (hp : ¬(p ∈ ψ '' ball 0 r ∧ p ∉ ψ '' closedBall 0 l)) :
    hψ.radialContraction hh p = p :=
  dite_eq_right hp

/-- `radialContraction` is the identity off `ψ(B(l + ε))`. -/
theorem radialContraction_of_notMem {p : M}
    (hp : p ∉ ψ '' closedBall 0 (l + ε)) : hψ.radialContraction hh p = p := by
  by_cases hp' : p ∈ ψ '' ball 0 r ∧ p ∉ ψ '' closedBall 0 l
  · set Ψ := hψ.complexPartialDiffeomorph
    have hpt : p ∈ Ψ.target := by rw [complexPartialDiffeomorph_target]; exact hp'.1
    have hΨp := hψ.apply_complexToRealEuclidean_complexPartialDiffeomorph_symm hp'.1
    have hle : l + ε ≤ ‖complexToRealEuclidean (Fin (n + 1)) (Ψ.symm p)‖ :=
      not_lt.1 fun hlt ↦ hp ⟨_, mem_closedBall_zero_iff.2 hlt.le, hΨp⟩
    have h0 : Ψ.symm p ∈ puncturedSpace (Fin (n + 1) → ℂ) := by
      rw [mem_puncturedSpace]
      rintro h0
      rw [h0, map_zero, norm_zero] at hle
      linarith [hh.weight_pos, hh.collar_pos]
    rw [hψ.radialContraction_of_mem hh hp']
    have hR : (hh.radialDiffeomorph n).symm
        ⟨_, hψ.complexPartialDiffeomorph_symm_mem_radialShell hh hp'⟩ =
        ⟨Ψ.symm p, h0⟩ := by
      rw [← (hh.radialDiffeomorph n).symm_apply_apply ⟨Ψ.symm p, h0⟩]
      congr 1
      refine Subtype.ext ?_
      rw [coe_radialMapDiffeomorph_apply]
      exact congrArg Subtype.val (hh.radialMap_of_le (z := ⟨Ψ.symm p, h0⟩) hle).symm
    rw [hR]
    exact Ψ.right_inv hpt
  · exact hψ.radialContraction_of_not hh hp'

/-- For `l + ε < r`, `radialContraction` undoes `ψ ∘ F_h ∘ ψ⁻¹`: it sends `ψ(F_h z)` to `ψ z`, for
`0 < |z| < r`. -/
theorem radialContraction_radialMap (hr : l + ε < r) (z : puncturedSpace (Fin (n + 1) → ℂ))
    (hz : ‖complexToRealEuclidean (Fin (n + 1)) z‖ < r) :
    hψ.radialContraction hh
        (ψ (complexToRealEuclidean (Fin (n + 1))
          (radialMap h (fun _ hs ↦ hh.pos (le_of_lt hs)) z))) =
      ψ (complexToRealEuclidean (Fin (n + 1)) z) := by
  set Ψ := hψ.complexPartialDiffeomorph
  set w := radialMap h (fun _ hs ↦ hh.pos (le_of_lt hs)) z
  have hw : ‖complexToRealEuclidean (Fin (n + 1)) w‖ < r := hh.norm_radialMap_lt hr hz
  have hlw : l < ‖complexToRealEuclidean (Fin (n + 1)) w‖ := by
    have := (hh.radialDiffeomorph n z).property
    rwa [coe_radialMapDiffeomorph_apply, hh.mem_radialShell_iff] at this
  have hp : ψ (complexToRealEuclidean (Fin (n + 1)) w) ∈ ψ '' ball 0 r ∧
      ψ (complexToRealEuclidean (Fin (n + 1)) w) ∉ ψ '' closedBall 0 l := by
    refine ⟨⟨_, mem_ball_zero_iff.2 hw, rfl⟩, ?_⟩
    rw [hψ.injOn.mem_image_iff (closedBall_subset_closedBall
        (by linarith [hh.weight_pos, hh.collar_pos])) (mem_closedBall_zero_iff.2 hw.le),
      mem_closedBall_zero_iff]
    exact hlw.not_ge
  rw [hψ.radialContraction_of_mem hh hp]
  have hsymm := hψ.complexPartialDiffeomorph_symm_apply_complexToRealEuclidean hw
  have hR : (hh.radialDiffeomorph n).symm
      ⟨_, hψ.complexPartialDiffeomorph_symm_mem_radialShell hh hp⟩ = z := by
    rw [← (hh.radialDiffeomorph n).symm_apply_apply z]
    congr 1
    refine Subtype.ext ?_
    rw [coe_radialMapDiffeomorph_apply]
    exact hsymm
  rw [hR, coe_complexPartialDiffeomorph, Function.comp_apply]

/-- A point of `ψ(B°(r))` other than `ψ 0`, read in `E` through `ψ`, is not `0`. -/
theorem complexPartialDiffeomorph_symm_mem_puncturedSpace {q : M}
    (hq : q ∈ ψ '' ball 0 r ∧ q ≠ ψ 0) :
    hψ.complexPartialDiffeomorph.symm q ∈ puncturedSpace (Fin (n + 1) → ℂ) := by
  rw [mem_puncturedSpace]
  intro h0
  refine hq.2 ?_
  rw [← hψ.apply_complexToRealEuclidean_complexPartialDiffeomorph_symm hq.1, h0, map_zero]

open scoped Classical in
/-- The map `ψ ∘ F_h ∘ ψ⁻¹` of `M`, for the radial map `F_h` of a profile `h` of the blowup of
weight `l`: on `ψ(B°(r))` minus `ψ 0` it is `ψ ∘ F_h ∘ ψ⁻¹`, and elsewhere the identity. For
`l + ε < r` it is inverse to `radialContraction` (`radialContraction_radialExpansion`,
`radialExpansion_radialContraction`). -/
def radialExpansion (q : M) : M :=
  if hq : q ∈ ψ '' ball 0 r ∧ q ≠ ψ 0 then
    hψ.complexPartialDiffeomorph (radialMap h (fun _ hs ↦ hh.pos (le_of_lt hs))
      ⟨_, hψ.complexPartialDiffeomorph_symm_mem_puncturedSpace hq⟩ : Fin (n + 1) → ℂ)
  else q

/-- On `ψ(B°(r))` minus `ψ 0`, `radialExpansion` is `ψ ∘ F_h ∘ ψ⁻¹`. -/
theorem radialExpansion_of_mem {q : M} (hq : q ∈ ψ '' ball 0 r ∧ q ≠ ψ 0) :
    hψ.radialExpansion hh q =
      hψ.complexPartialDiffeomorph (radialMap h (fun _ hs ↦ hh.pos (le_of_lt hs))
        ⟨_, hψ.complexPartialDiffeomorph_symm_mem_puncturedSpace hq⟩ : Fin (n + 1) → ℂ) :=
  dite_eq_left hq

/-- `radialExpansion` is the identity off `ψ(B°(r))` minus `ψ 0`. -/
theorem radialExpansion_of_not {q : M} (hq : ¬(q ∈ ψ '' ball 0 r ∧ q ≠ ψ 0)) :
    hψ.radialExpansion hh q = q :=
  dite_eq_right hq

/-- For `l + ε < r`, `radialContraction` undoes `radialExpansion` at every point other than
`ψ 0`. -/
theorem radialContraction_radialExpansion (hr : l + ε < r) {q : M} (hq : q ≠ ψ 0) :
    hψ.radialContraction hh (hψ.radialExpansion hh q) = q := by
  by_cases hqb : q ∈ ψ '' ball 0 r
  · have hs := hψ.norm_complexPartialDiffeomorph_symm_lt hqb
    rw [hψ.radialExpansion_of_mem hh ⟨hqb, hq⟩, coe_complexPartialDiffeomorph,
      Function.comp_apply, hψ.radialContraction_radialMap hh hr
        ⟨_, hψ.complexPartialDiffeomorph_symm_mem_puncturedSpace ⟨hqb, hq⟩⟩ hs]
    exact hψ.apply_complexToRealEuclidean_complexPartialDiffeomorph_symm hqb
  · rw [hψ.radialExpansion_of_not hh fun h ↦ hqb h.1]
    refine hψ.radialContraction_of_notMem hh fun ⟨z, hz, hzq⟩ ↦ hqb ⟨z, ?_, hzq⟩
    exact mem_ball_zero_iff.2 ((mem_closedBall_zero_iff.1 hz).trans_lt hr)

/-- For `l + ε < r`, `radialContraction` sends no point off `ψ(B(l))` to `ψ 0`. -/
theorem radialContraction_ne (hr : l + ε < r) {p : M} (hp : p ∉ ψ '' closedBall 0 l) :
    hψ.radialContraction hh p ≠ ψ 0 := by
  by_cases hp' : p ∈ ψ '' ball 0 r ∧ p ∉ ψ '' closedBall 0 l
  · set z := (hh.radialDiffeomorph n).symm
      ⟨_, hψ.complexPartialDiffeomorph_symm_mem_radialShell hh hp'⟩
    have hz : ‖complexToRealEuclidean (Fin (n + 1)) z‖ < r :=
      hh.norm_radialDiffeomorph_symm_lt hr (hψ.norm_complexPartialDiffeomorph_symm_lt hp'.1)
    rw [hψ.radialContraction_of_mem hh hp', coe_complexPartialDiffeomorph, Function.comp_apply]
    refine hψ.apply_ne_apply_zero (mem_closedBall_zero_iff.2 hz.le) ?_
    rw [Ne, map_eq_zero_iff _ (complexToRealEuclidean (Fin (n + 1))).injective]
    exact mem_puncturedSpace.1 z.property
  · rw [hψ.radialContraction_of_not hh hp']
    rintro rfl
    exact hp ⟨0, mem_closedBall_self hh.weight_pos.le, rfl⟩

/-- For `l + ε < r`, `radialExpansion` undoes `radialContraction` at every point off `ψ(B(l))`. -/
theorem radialExpansion_radialContraction (hr : l + ε < r) {p : M}
    (hp : p ∉ ψ '' closedBall 0 l) :
    hψ.radialExpansion hh (hψ.radialContraction hh p) = p := by
  by_cases hp' : p ∈ ψ '' ball 0 r ∧ p ∉ ψ '' closedBall 0 l
  · set Ψ := hψ.complexPartialDiffeomorph
    set z := (hh.radialDiffeomorph n).symm
      ⟨_, hψ.complexPartialDiffeomorph_symm_mem_radialShell hh hp'⟩
    have hpt : p ∈ Ψ.target := by rw [complexPartialDiffeomorph_target]; exact hp'.1
    have hz : ‖complexToRealEuclidean (Fin (n + 1)) z‖ < r :=
      hh.norm_radialDiffeomorph_symm_lt hr (hψ.norm_complexPartialDiffeomorph_symm_lt hp'.1)
    have hc := hψ.radialContraction_of_mem hh hp'
    have hzs : (z : Fin (n + 1) → ℂ) ∈ Ψ.source := by
      rw [mem_complexPartialDiffeomorph_source_iff]; exact hz
    have hq : hψ.radialContraction hh p ∈ ψ '' ball 0 r ∧ hψ.radialContraction hh p ≠ ψ 0 :=
      ⟨by rw [← hψ.complexPartialDiffeomorph_target, hc]; exact Ψ.map_source hzs,
        hψ.radialContraction_ne hh hr hp⟩
    rw [hψ.radialExpansion_of_mem hh hq]
    have hsymm : Ψ.symm (hψ.radialContraction hh p) = z := by rw [hc]; exact Ψ.left_inv hzs
    have hz' : (⟨_, hψ.complexPartialDiffeomorph_symm_mem_puncturedSpace hq⟩ :
        puncturedSpace (Fin (n + 1) → ℂ)) = z := Subtype.ext hsymm
    rw [hz', coe_radialMap_radialMapDiffeomorph_symm_apply]
    exact Ψ.right_inv hpt
  · have hpb : p ∉ ψ '' ball 0 r := fun hpb ↦ hp' ⟨hpb, hp⟩
    rw [hψ.radialContraction_of_not hh hp', hψ.radialExpansion_of_not hh fun h ↦ hpb h.1]

/-- `radialExpansion` sends `ψ z` to `ψ(F_h z)`, for `0 < |z| < r`. -/
theorem radialExpansion_apply (z : puncturedSpace (Fin (n + 1) → ℂ))
    (hz : ‖complexToRealEuclidean (Fin (n + 1)) z‖ < r) :
    hψ.radialExpansion hh (ψ (complexToRealEuclidean (Fin (n + 1)) z)) =
      ψ (complexToRealEuclidean (Fin (n + 1))
        (radialMap h (fun _ hs ↦ hh.pos (le_of_lt hs)) z)) := by
  have hq : ψ (complexToRealEuclidean (Fin (n + 1)) z) ∈ ψ '' ball 0 r ∧
      ψ (complexToRealEuclidean (Fin (n + 1)) z) ≠ ψ 0 := by
    refine ⟨⟨_, mem_ball_zero_iff.2 hz, rfl⟩,
      hψ.apply_ne_apply_zero (mem_closedBall_zero_iff.2 hz.le) ?_⟩
    rw [Ne, map_eq_zero_iff _ (complexToRealEuclidean (Fin (n + 1))).injective]
    exact mem_puncturedSpace.1 z.property
  have hz' : (⟨_, hψ.complexPartialDiffeomorph_symm_mem_puncturedSpace hq⟩ :
      puncturedSpace (Fin (n + 1) → ℂ)) = z :=
    Subtype.ext (hψ.complexPartialDiffeomorph_symm_apply_complexToRealEuclidean hz)
  rw [hψ.radialExpansion_of_mem hh hq, hz', coe_complexPartialDiffeomorph, Function.comp_apply]

/-- For `l + ε < r`, `radialExpansion` sends every point other than `ψ 0` off `ψ(B(l))`. -/
theorem radialExpansion_notMem (hr : l + ε < r) {q : M} (hq : q ≠ ψ 0) :
    hψ.radialExpansion hh q ∉ ψ '' closedBall 0 l := by
  by_cases hqb : q ∈ ψ '' ball 0 r
  · set z : puncturedSpace (Fin (n + 1) → ℂ) :=
      ⟨_, hψ.complexPartialDiffeomorph_symm_mem_puncturedSpace ⟨hqb, hq⟩⟩
    have hzr : ‖complexToRealEuclidean (Fin (n + 1)) z‖ < r :=
      hψ.norm_complexPartialDiffeomorph_symm_lt hqb
    set w := radialMap h (fun _ hs ↦ hh.pos (le_of_lt hs)) z
    have hw : ‖complexToRealEuclidean (Fin (n + 1)) w‖ < r := hh.norm_radialMap_lt hr hzr
    have hlw : l < ‖complexToRealEuclidean (Fin (n + 1)) w‖ := by
      have := (hh.radialDiffeomorph n z).property
      rwa [coe_radialMapDiffeomorph_apply, hh.mem_radialShell_iff] at this
    rw [hψ.radialExpansion_of_mem hh ⟨hqb, hq⟩, coe_complexPartialDiffeomorph,
      Function.comp_apply, hψ.injOn.mem_image_iff (closedBall_subset_closedBall
        (by linarith [hh.weight_pos, hh.collar_pos])) (mem_closedBall_zero_iff.2 hw.le),
      mem_closedBall_zero_iff]
    exact hlw.not_ge
  · rw [hψ.radialExpansion_of_not hh fun h ↦ hqb h.1]
    rintro ⟨v, hv, rfl⟩
    refine hqb ⟨v, mem_ball_zero_iff.2 ((mem_closedBall_zero_iff.1 hv).trans_lt ?_), rfl⟩
    linarith [hh.collar_pos]

variable [T2Space M]

/-- Near a point `p` of `ψ(B°(r)) ∖ ψ(B(l))`, for `l ≤ r`, `radialContraction` is
`ψ ∘ F_h⁻¹ ∘ g` for a map `g` into the shell of `h` that is a local diffeomorphism at `p` and
equals `ψ⁻¹`, read on `E`, near `p`. -/
theorem exists_radialContraction_eventuallyEq (hl : l ≤ r) {p : M}
    (hp : p ∈ ψ '' ball 0 r ∧ p ∉ ψ '' closedBall 0 l) :
    ∃ g : M → radialShell (Fin (n + 1)) h hh.contDiff.contDiffOn (fun s _ ↦ hh.deriv_pos s),
      IsLocalDiffeomorphAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ g p ∧
      (∀ᶠ q in 𝓝 p, (g q : Fin (n + 1) → ℂ) = hψ.complexPartialDiffeomorph.symm q) ∧
      hψ.radialContraction hh =ᶠ[𝓝 p] hψ.complexPartialDiffeomorph ∘ Subtype.val ∘
        (hh.radialDiffeomorph n).symm ∘ g := by
  let U : Set M := ψ '' ball 0 r ∩ (ψ '' closedBall 0 l)ᶜ
  have hpt : p ∈ hψ.complexPartialDiffeomorph.target := by
    rw [complexPartialDiffeomorph_target]; exact hp.1
  have hUo : IsOpen U := by
    refine IsOpen.inter ?_ (hψ.isCompact_image_closedBall hl).isClosed.isOpen_compl
    rw [← hψ.complexPartialDiffeomorph_target]
    exact hψ.complexPartialDiffeomorph.open_target
  have hev : ∀ᶠ q in 𝓝 p, q ∈ U := hUo.mem_nhds hp
  obtain ⟨g, hgd, hg⟩ := TauCeti.exists_isLocalDiffeomorphAt_subtypeVal_comp_eventuallyEq
    (W := radialShell (Fin (n + 1)) h hh.contDiff.contDiffOn (fun s _ ↦ hh.deriv_pos s))
    (hψ.complexPartialDiffeomorph.symm.isLocalDiffeomorphAt _ _ _ hpt)
    (hev.mono fun _ hq ↦ hψ.complexPartialDiffeomorph_symm_mem_radialShell hh hq)
  refine ⟨g, hgd, hg.mono fun _ hq ↦ by rwa [Function.comp_apply] at hq, ?_⟩
  filter_upwards [hev, hg] with q hq hgq
  rw [hψ.radialContraction_of_mem hh hq, Function.comp_apply, Function.comp_apply,
    Function.comp_apply]
  rw [Function.comp_apply] at hgq
  exact congrArg _ (congrArg _ (congrArg _ (Subtype.ext hgq.symm)))

/-- `radialContraction` is a local diffeomorphism at each point off `ψ(B(l))`, for `l + ε < r`. -/
theorem isLocalDiffeomorphAt_radialContraction (hr : l + ε < r) {p : M}
    (hp : p ∉ ψ '' closedBall 0 l) :
    IsLocalDiffeomorphAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞
      (hψ.radialContraction hh) p := by
  by_cases hpb : p ∈ ψ '' ball 0 r
  · set Ψ := hψ.complexPartialDiffeomorph
    set R := hh.radialDiffeomorph n
    obtain ⟨g, hg, hgΨ, hfun⟩ :=
      hψ.exists_radialContraction_eventuallyEq hh (by linarith [hh.collar_pos]) ⟨hpb, hp⟩
    have hz : ((R.symm (g p) : puncturedSpace (Fin (n + 1) → ℂ)) : Fin (n + 1) → ℂ) ∈
        Ψ.source := by
      rw [mem_complexPartialDiffeomorph_source_iff]
      refine hh.norm_radialDiffeomorph_symm_lt hr ?_
      rw [hgΨ.self_of_nhds]
      exact hψ.norm_complexPartialDiffeomorph_symm_lt hpb
    have hcomp := IsLocalDiffeomorphAt.comp (hf := hg) (hg := IsLocalDiffeomorphAt.comp
      (hf := R.symm.isLocalDiffeomorph (g p))
      (hg := isLocalDiffeomorph_subtype_val (R.symm (g p))))
    exact (IsLocalDiffeomorphAt.comp (hf := hcomp) (hg := Ψ.isLocalDiffeomorphAt _ _ _ hz)
      ).congr_of_eventuallyEq hfun
  · have hK : IsClosed (ψ '' closedBall 0 (l + ε)) :=
      (hψ.isCompact_image_closedBall hr.le).isClosed
    have hpK : p ∉ ψ '' closedBall 0 (l + ε) := fun ⟨z, hz, hzp⟩ ↦
      hpb ⟨z, mem_ball_zero_iff.2 ((mem_closedBall_zero_iff.1 hz).trans_lt hr), hzp⟩
    refine ((Diffeomorph.refl 𝓘(ℝ, Fin (n + 1) → ℂ) M ∞).isLocalDiffeomorph p
      ).congr_of_eventuallyEq ?_
    filter_upwards [hK.isOpen_compl.mem_nhds hpK] with q hq
    rw [hψ.radialContraction_of_notMem hh hq, Diffeomorph.coe_refl, id]

end IsSymplecticBallEmbedding

namespace IsNormalizedBallEmbedding

open BlowupModel
open GluedAlong (inl inr)
open Blowup (gluingHomeomorph)
open scoped TauCeti.ComplexManifold

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M]
  {σ : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) M}
  {J : SmoothAlmostComplexStructure 𝓘(ℝ, Fin (n + 1) → ℂ) M} {p₀ : M} {δ : ℝ}
  {ψ₀ ψ : StdSpace (Fin (n + 1)) → M} {hN : IsNormalizedAt σ J p₀ δ ψ₀} {r l ε ε' : ℝ}
  {h : ℝ → ℝ}

variable (hψ : IsNormalizedBallEmbedding hN ψ r l ε)
include hψ

/-- For `0 ≤ ε' ≤ ε`, the radius `√(l² + ε'²)` of the blowup of weight `l` with collar `ε'`
is at most the radius `r` of a normalized ball embedding of weight `l` and width `ε`. -/
theorem sqrt_le_radius (hε' : 0 ≤ ε') (hε'ε : ε' ≤ ε) : √(l ^ 2 + ε' ^ 2) ≤ r := by
  have hl := hψ.weight_pos
  have hlε := hψ.weight_add_width_lt
  refine (Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩).trans hlε.le

/-- For `0 < ε' ≤ ε`, a normalized ball embedding of weight `l` and width `ε` is a symplectic
embedding of the closed ball of radius `√(l² + ε'²)`, along which the blowup of weight `l` with
collar `ε'` is defined. -/
theorem isSymplecticBallEmbedding_sqrt (hε' : 0 < ε') (hε'ε : ε' ≤ ε) :
    IsSymplecticBallEmbedding σ √(l ^ 2 + ε' ^ 2) ψ :=
  hψ.isSymplecticBallEmbedding.mono (hψ.sqrt_le_radius hε'.le hε'ε)

variable [T2Space M]

variable (hh : IsBlowupProfile l ε h) (hε' : 0 < ε') (hε'ε : ε' ≤ ε)

/-- A point of `M ∖ ψ(B(l))` is sent by `radialContraction` to a point other than `p₀`. -/
theorem radialContraction_mem_puncturedOpens
    (x : WeightBlowup.outerPiece (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε)) :
    hψ.isSymplecticBallEmbedding.radialContraction hh x ∈
      Blowup.puncturedOpens hN.blowupChart := by
  rw [Blowup.mem_puncturedOpens]
  intro h0
  exact hψ.isSymplecticBallEmbedding.radialContraction_ne hh hψ.weight_add_width_lt
    ((WeightBlowup.mem_outerPiece_iff _).1 x.property)
    (h0.trans hψ.map_zero.symm)

omit [T2Space M] in
/-- A point of `M` other than `p₀` is not `ψ 0`. -/
theorem ne_map_zero_of_mem_puncturedOpens (q : Blowup.puncturedOpens hN.blowupChart) :
    (q : M) ≠ ψ 0 := fun h0 ↦
  (Blowup.mem_puncturedOpens _).1 q.property (h0.trans hψ.map_zero)

/-- `radialExpansion` sends a point of `M ∖ p₀` into the outer piece `M ∖ ψ(B(l))`. -/
theorem radialExpansion_mem_outerPiece (q : Blowup.puncturedOpens hN.blowupChart) :
    hψ.isSymplecticBallEmbedding.radialExpansion hh q ∈
      WeightBlowup.outerPiece (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε) :=
  (WeightBlowup.mem_outerPiece_iff _).2 (hψ.isSymplecticBallEmbedding.radialExpansion_notMem hh
    hψ.weight_add_width_lt (hψ.ne_map_zero_of_mem_puncturedOpens q))

/-- The map from the outer piece `M ∖ ψ(B(l))` of the blowup of weight `l` to `Blowup c`:
`radialContraction`, followed by the inclusion of `M ∖ p₀`. -/
private def outerMap (x : WeightBlowup.outerPiece (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε)) :
    Blowup hN.blowupChart :=
  inl (gluingHomeomorph hN.blowupChart)
    ⟨_, hψ.radialContraction_mem_puncturedOpens hh hε' hε'ε x⟩

/-- The map from the model piece `openNbhd n ε'` of the blowup of weight `l` to `Blowup c`: the
lift of `ψ`. -/
private def modelMap (y : openNbhdOpens n ε') : Blowup hN.blowupChart :=
  hψ.ballLift ⟨y, openNbhd_mono (hε'ε.trans hψ.width_lt_radius.le)
    (mem_openNbhdOpens_iff.1 y.property)⟩

private theorem isLocalDiffeomorph_outerMap :
    IsLocalDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞
      (hψ.outerMap hh hε' hε'ε) := fun x ↦ by
  let k : WeightBlowup.outerPiece (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε) →
      Blowup.puncturedOpens hN.blowupChart :=
    fun x ↦ ⟨_, hψ.radialContraction_mem_puncturedOpens hh hε' hε'ε x⟩
  have hk : IsLocalDiffeomorphAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ k x :=
    isLocalDiffeomorphAt_subtypeVal_comp_iff.1 <| IsLocalDiffeomorphAt.comp
      (hf := isLocalDiffeomorph_subtype_val x)
      (hg := hψ.isSymplecticBallEmbedding.isLocalDiffeomorphAt_radialContraction hh
        hψ.weight_add_width_lt ((WeightBlowup.mem_outerPiece_iff _).1 x.property))
  exact IsLocalDiffeomorphAt.comp (hf := hk)
    (hg := Blowup.isLocalDiffeomorph_inl_real hN.blowupChart (k x))

omit [T2Space M] in
private theorem isLocalDiffeomorph_modelMap :
    IsLocalDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞
      (hψ.modelMap hε'ε) := fun y ↦ by
  have hy : (y : BlowupModel n) ∈ hψ.ballLiftPartialDiffeomorph.source := by
    rw [ballLiftPartialDiffeomorph_source]
    exact openNbhd_mono (hε'ε.trans hψ.width_lt_radius.le) (mem_openNbhdOpens_iff.1 y.property)
  refine (IsLocalDiffeomorphAt.comp (hf := isLocalDiffeomorph_subtype_val y)
    (hg := hψ.ballLiftPartialDiffeomorph.isLocalDiffeomorphAt _ _ _ hy)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y' ↦ ?_)
  rw [Function.comp_apply, modelMap,
    ← hψ.ballLiftPartialDiffeomorph_apply ⟨y', openNbhd_mono (hε'ε.trans hψ.width_lt_radius.le)
      (mem_openNbhdOpens_iff.1 y'.property)⟩]

private theorem injective_outerMap : Function.Injective (hψ.outerMap hh hε' hε'ε) := by
  intro x x' hxx'
  have h₁ := congrArg Subtype.val (GluedAlong.inl_injective _ hxx')
  refine Subtype.ext ?_
  rw [← hψ.isSymplecticBallEmbedding.radialExpansion_radialContraction hh
      hψ.weight_add_width_lt ((WeightBlowup.mem_outerPiece_iff _).1 x.property),
    ← hψ.isSymplecticBallEmbedding.radialExpansion_radialContraction hh
      hψ.weight_add_width_lt ((WeightBlowup.mem_outerPiece_iff _).1 x'.property)]
  exact congrArg _ h₁

omit [T2Space M] in
private theorem injective_modelMap : Function.Injective (hψ.modelMap hε'ε) := fun y y' hyy' ↦
  Subtype.ext (by simpa using congrArg Subtype.val (hψ.injective_ballLift hyy'))

/-- The two maps agree on the overlap of the pieces: a point `y` of `openNbhd n ε' ∖ Z`, glued to
`ψ(F_l(π y))`, is sent by both to `ψ(π y)`, since `F_h = F_l` on `B(ε)`. -/
private theorem modelMap_gluingDiffeomorphSymm
    (x : WeightBlowup.outerOverlap (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε)) :
    hψ.modelMap hε'ε (WeightBlowup.gluingDiffeomorphSymm
        (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε) hψ.weight_pos.le hε' x) =
      hψ.outerMap hh hε' hε'ε x := by
  obtain ⟨y, rfl⟩ : ∃ y, WeightBlowup.gluingDiffeomorph
      (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε) hψ.weight_pos.le hε' y = x :=
    ⟨_, WeightBlowup.gluingDiffeomorph_gluingDiffeomorphSymm_apply _ _ _ x⟩
  rw [WeightBlowup.gluingDiffeomorphSymm_gluingDiffeomorph_apply]
  have hyZ : (y.val : BlowupModel n) ∉ exceptionalDivisor n :=
    WeightBlowup.mem_modelOverlap_iff.1 y.property
  have hy0 : (y.val : BlowupModel n).blowdown ≠ 0 := fun h0 ↦
    hyZ (mem_exceptionalDivisor_iff.2 h0)
  have hyε' := mem_openNbhd_iff.1 (mem_openNbhdOpens_iff.1 y.val.property)
  set w : puncturedSpace (Fin (n + 1) → ℂ) :=
    blowdownPuncturedDiffeomorph n ⟨y.val, mem_offDivisorOpens.2 hyZ⟩
  have hw : (w : Fin (n + 1) → ℂ) = (y.val : BlowupModel n).blowdown :=
    coe_blowdownPuncturedDiffeomorph_apply _
  have hwε : ‖complexToRealEuclidean (Fin (n + 1)) w‖ ≤ ε := by
    rw [hw]; exact hyε'.le.trans hε'ε
  have hwr : ‖complexToRealEuclidean (Fin (n + 1)) w‖ < r :=
    hwε.trans_lt hψ.width_lt_radius
  rw [modelMap, hψ.ballLift_of_blowdown_ne_zero _ hy0, outerMap]
  congr 1
  refine Subtype.ext ?_
  dsimp only
  rw [WeightBlowup.coe_gluingDiffeomorph_apply,
    coe_shellSymplectomorph_apply, ← hh.radialMap_of_le_collar hwε,
    hψ.isSymplecticBallEmbedding.radialContraction_radialMap hh hψ.weight_add_width_lt w hwr, hw]

/-- The images of the two maps cover the blowup `Blowup c`: the exceptional divisor lies in the
image of `openNbhd n ε'` under the lift, and every other point is `p ≠ p₀`, the image of
`radialExpansion p`. -/
private theorem range_outerMap_union_range_modelMap :
    range (hψ.outerMap hh hε' hε'ε) ∪ range (hψ.modelMap hε'ε) = univ := by
  refine eq_univ_of_forall fun z ↦ ?_
  by_cases hz : z ∈ Blowup.exceptionalDivisor hN.blowupChart
  · right
    obtain ⟨y, hy0, rfl⟩ := (Blowup.mem_exceptionalDivisor_iff _).1 hz
    have hy : (y : BlowupModel n) ∈ openNbhd n ε' :=
      exceptionalDivisor_subset_openNbhd hε' (mem_exceptionalDivisor_iff.2 hy0)
    refine ⟨⟨y, mem_openNbhdOpens_iff.2 hy⟩, ?_⟩
    rw [modelMap, hψ.ballLift_of_mem_openNbhd _ (openNbhd_mono hε'ε hy)]
  · left
    rw [← mem_compl_iff, ← Blowup.range_inl] at hz
    obtain ⟨q, rfl⟩ := hz
    refine ⟨⟨_, hψ.radialExpansion_mem_outerPiece hh hε' hε'ε q⟩, ?_⟩
    rw [outerMap]
    congr 1
    exact Subtype.ext (hψ.isSymplecticBallEmbedding.radialContraction_radialExpansion hh
      hψ.weight_add_width_lt (hψ.ne_map_zero_of_mem_puncturedOpens q))

/-- A point of the outer piece sent by the first map to a point of the image of the second lies in
the overlap: it is `ψ(F_h(π y))` for a point `y` of `openNbhd n ε'` off the divisor, so it lies in
the image of the open ball of radius `√(l² + ε'²)`. -/
private theorem mem_outerOverlap_of_outerMap_eq
    (x : WeightBlowup.outerPiece (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε))
    (y : openNbhdOpens n ε') (hxy : hψ.outerMap hh hε' hε'ε x = hψ.modelMap hε'ε y) :
    x ∈ WeightBlowup.outerOverlap (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε) := by
  rw [WeightBlowup.mem_outerOverlap_iff]
  have hyε' := mem_openNbhd_iff.1 (mem_openNbhdOpens_iff.1 y.property)
  by_cases hy0 : (y : BlowupModel n).blowdown = 0
  · exfalso
    have hy : (y : BlowupModel n) ∈ openNbhd n ε :=
      openNbhd_mono hε'ε (mem_openNbhdOpens_iff.1 y.property)
    rw [modelMap, hψ.ballLift_of_mem_openNbhd _ hy, outerMap] at hxy
    exact Blowup.inl_notMem_exceptionalDivisor _ _
      (hxy ▸ (Blowup.inr_mem_exceptionalDivisor_iff _).2 hy0)
  · rw [modelMap, hψ.ballLift_of_blowdown_ne_zero _ hy0, outerMap] at hxy
    have h₁ := congrArg Subtype.val (GluedAlong.inl_injective _ hxy)
    have hyZ : (y : BlowupModel n) ∉ exceptionalDivisor n := fun hZ ↦
      hy0 (mem_exceptionalDivisor_iff.1 hZ)
    set w : puncturedSpace (Fin (n + 1) → ℂ) :=
      blowdownPuncturedDiffeomorph n ⟨y, mem_offDivisorOpens.2 hyZ⟩
    have hw : (w : Fin (n + 1) → ℂ) = (y : BlowupModel n).blowdown :=
      coe_blowdownPuncturedDiffeomorph_apply _
    have hwε' : ‖complexToRealEuclidean (Fin (n + 1)) w‖ < ε' := by rw [hw]; exact hyε'
    have hwr : ‖complexToRealEuclidean (Fin (n + 1)) w‖ < r :=
      hwε'.trans (hε'ε.trans_lt hψ.width_lt_radius)
    have hx : (x : M) = ψ (complexToRealEuclidean (Fin (n + 1))
        (radialMap h (fun _ hs ↦ hh.pos (le_of_lt hs)) w)) := by
      rw [← hψ.isSymplecticBallEmbedding.radialExpansion_radialContraction hh
          hψ.weight_add_width_lt ((WeightBlowup.mem_outerPiece_iff _).1 x.property),
        ← hψ.isSymplecticBallEmbedding.radialExpansion_apply hh w hwr, hw]
      exact congrArg _ h₁
    rw [hx]
    refine ⟨_, mem_ball_zero_iff.2 ?_, rfl⟩
    rw [hh.radialMap_of_le_collar (hwε'.le.trans hε'ε), Real.lt_sqrt (norm_nonneg _),
      norm_radialMap]
    have := pow_lt_pow_left₀ hwε' (norm_nonneg _) two_ne_zero
    linarith

/-- The diffeomorphism from the blowup of weight `l` with collar `ε'` onto `Blowup c` that is
`radialContraction` on the outer piece and the lift `ψ̃` on the model piece. -/
private def weightBlowupDiffeomorph :
    WeightBlowup (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε) hψ.weight_pos.le hε'
      ≃ₘ⟮𝓘(ℝ, Fin (n + 1) → ℂ), 𝓘(ℝ, Fin (n + 1) → ℂ)⟯ Blowup hN.blowupChart :=
  GluedAlong.descDiffeomorph (hψ.isLocalDiffeomorph_outerMap hh hε' hε'ε)
    (hψ.isLocalDiffeomorph_modelMap hε'ε) (hψ.modelMap_gluingDiffeomorphSymm hh hε' hε'ε)
    (hψ.injective_outerMap hh hε' hε'ε) (hψ.injective_modelMap hε'ε)
    (hψ.range_outerMap_union_range_modelMap hh hε' hε'ε)
    (hψ.mem_outerOverlap_of_outerMap_eq hh hε' hε'ε)

/-- **The blowup form and the blowup of weight `l`** (McDuff–Salamon, Theorem 7.1.21 (ii)): the
diffeomorphism from the blowup `Blowup c` of `M` at `p₀` onto the blowup of weight `l` with
collar `ε'` along `ψ`, for `0 < ε' ≤ ε`. It is the identity of the model on the image under the
lift `ψ̃` of `openNbhd n ε'`, and elsewhere `radialExpansion ∘ π`, for the blowdown `π` of
`Blowup c`: that is `ψ ∘ F_h ∘ ψ⁻¹ ∘ π` over the image of the open ball, for the radial map `F_h`
of the profile `h`, and `π` outside it. -/
def normalizedBlowupSymplectomorph :
    Blowup hN.blowupChart ≃ₘ⟮𝓘(ℝ, Fin (n + 1) → ℂ), 𝓘(ℝ, Fin (n + 1) → ℂ)⟯
      WeightBlowup (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε) hψ.weight_pos.le hε' :=
  (hψ.weightBlowupDiffeomorph hh hε' hε'ε).symm

/-- `normalizedBlowupSymplectomorph` sends the lift `ψ̃ y` of a point `y` of `openNbhd n ε'` to
the point `y` of the model piece. -/
theorem normalizedBlowupSymplectomorph_ballLift (y : openNbhdOpens n ε') :
    hψ.normalizedBlowupSymplectomorph hh hε' hε'ε
        (hψ.ballLift ⟨y, openNbhd_mono (hε'ε.trans hψ.width_lt_radius.le)
          (mem_openNbhdOpens_iff.1 y.property)⟩) =
      inr (WeightBlowup.gluingDiffeomorphSymm (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε)
        hψ.weight_pos.le hε').toHomeomorph y :=
  GluedAlong.descDiffeomorph_symm_apply_right _ _ _ _ _ _ _ y

/-- `normalizedBlowupSymplectomorph` sends the point `radialContraction x` of `M ∖ p₀` to the point
`x` of the outer piece `M ∖ ψ(B(l))`. -/
theorem normalizedBlowupSymplectomorph_inl_radialContraction
    (x : WeightBlowup.outerPiece (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε)) :
    hψ.normalizedBlowupSymplectomorph hh hε' hε'ε
        (inl (gluingHomeomorph hN.blowupChart)
          ⟨_, hψ.radialContraction_mem_puncturedOpens hh hε' hε'ε x⟩) =
      inl (WeightBlowup.gluingDiffeomorphSymm (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε)
        hψ.weight_pos.le hε').toHomeomorph x :=
  GluedAlong.descDiffeomorph_symm_apply_left _ _ _ _ _ _ _ x

/-- `normalizedBlowupSymplectomorph` sends a point `q` of `M ∖ p₀` to the point
`radialExpansion q` of the outer piece `M ∖ ψ(B(l))`. -/
theorem normalizedBlowupSymplectomorph_inl (q : Blowup.puncturedOpens hN.blowupChart) :
    hψ.normalizedBlowupSymplectomorph hh hε' hε'ε (inl (gluingHomeomorph hN.blowupChart) q) =
      inl (WeightBlowup.gluingDiffeomorphSymm (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε)
        hψ.weight_pos.le hε').toHomeomorph
        ⟨_, hψ.radialExpansion_mem_outerPiece hh hε' hε'ε q⟩ := by
  rw [← hψ.normalizedBlowupSymplectomorph_inl_radialContraction hh hε' hε'ε]
  refine congrArg _ (congrArg _ (Subtype.ext ?_))
  exact (hψ.isSymplecticBallEmbedding.radialContraction_radialExpansion hh
    hψ.weight_add_width_lt (hψ.ne_map_zero_of_mem_puncturedOpens q)).symm

attribute [local instance high] IsManifold.instOfNatWithTopENat_1

/-- On the model piece `openNbhd n ε'`, the diffeomorphism onto `Blowup c` pulls the form
`ω̃_{ψ,l,ε}` of `Blowup c` back to `ω̃_l`: there it is the lift `ψ̃`, which pulls the form back
to `ω̃_{l,ε}`, equal to `ω̃_l` on `L(ε)`. -/
private theorem mpullback_inr_weightBlowupDiffeomorph :
    SmoothForm.mpullback (inr (WeightBlowup.gluingDiffeomorphSymm
        (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε) hψ.weight_pos.le hε').toHomeomorph)
        (GluedAlong.isLocalDiffeomorph_inr _).contMDiff
        (SmoothForm.mpullback (hψ.weightBlowupDiffeomorph hh hε' hε'ε)
          (hψ.weightBlowupDiffeomorph hh hε' hε'ε).contMDiff (hψ.normalizedBlowupForm h)) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (blowupForm n l) := by
  rw [SmoothForm.mpullback_mpullback]
  refine Subtype.ext (funext fun y ↦ ?_)
  have hyr : (y : BlowupModel n) ∈ openNbhd n r :=
    openNbhd_mono (hε'ε.trans hψ.width_lt_radius.le) (mem_openNbhdOpens_iff.1 y.property)
  have hfun : ⇑(hψ.weightBlowupDiffeomorph hh hε' hε'ε) ∘
      inr (WeightBlowup.gluingDiffeomorphSymm (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε)
        hψ.weight_pos.le hε').toHomeomorph =
      hψ.ballLiftPartialDiffeomorph ∘ (Subtype.val : openNbhdOpens n ε' → BlowupModel n) := by
    funext y'
    rw [Function.comp_apply, weightBlowupDiffeomorph, GluedAlong.descDiffeomorph_inr,
      Function.comp_apply, modelMap]
    exact (hψ.ballLiftPartialDiffeomorph_apply _).symm
  have hΦ : MDifferentiableAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ)
      hψ.ballLiftPartialDiffeomorph (y : BlowupModel n) :=
    hψ.ballLiftPartialDiffeomorph.mdifferentiableAt (by simp)
      (by rw [ballLiftPartialDiffeomorph_source]; exact hyr)
  rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback_subtype_val_apply, hfun,
    mpullback_comp_at ((contMDiff_subtypeVal (n := ∞)).mdifferentiableAt (by simp)) hΦ,
    mpullback_subtype_val_apply, hψ.normalizedBlowupForm_eq_on_ballLift hh _ hyr]
  exact profileForm_eq_blowupForm_on n _
    (openNbhd_subset_closedNbhd ε (openNbhd_mono hε'ε (mem_openNbhdOpens_iff.1 y.property)))

/-- The first map, followed by the blowdown of `Blowup c`, is `radialContraction`. -/
private theorem blowdown_outerMap
    (x : WeightBlowup.outerPiece (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε)) :
    Blowup.blowdown hN.blowupChart (hψ.outerMap hh hε' hε'ε x) =
      hψ.isSymplecticBallEmbedding.radialContraction hh x := by
  rw [outerMap, Blowup.blowdown_inl]

/-- Off `ψ(B(l + ε))`, the first map pulls `ω̃_{ψ,l,ε}` back to `σ`: there it is the inclusion
of `M ∖ p₀`, and the form is the pull-back of `σ` by the blowdown. -/
private theorem mpullback_outerMap_apply_of_notMem
    (x : WeightBlowup.outerPiece (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε))
    (hx : (x : M) ∉ ψ '' closedBall 0 (l + ε)) :
    TauCeti.mpullback 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (hψ.outerMap hh hε' hε'ε)
      (hψ.normalizedBlowupForm h).val x = σ.val x := by
  have hK : IsClosed (ψ '' closedBall 0 (l + ε)) :=
    (hψ.isSymplecticBallEmbedding.isCompact_image_closedBall
      hψ.weight_add_width_lt.le).isClosed
  have hnot : hψ.outerMap hh hε' hε'ε x ∉
      hψ.ballLiftPartialDiffeomorph '' closedNbhd n (l + ε) := by
    rintro ⟨y, hy, hyx⟩
    have hyr : y ∈ openNbhd n r := closedNbhd_subset_openNbhd hψ.weight_add_width_lt hy
    have hb := congrArg (Blowup.blowdown hN.blowupChart) hyx
    rw [hψ.blowdown_outerMap hh hε' hε'ε,
      hψ.isSymplecticBallEmbedding.radialContraction_of_notMem hh hx,
      hψ.ballLiftPartialDiffeomorph_apply ⟨y, hyr⟩, blowdown_ballLift] at hb
    exact hx ⟨_, mem_closedBall_zero_iff.2 (mem_closedNbhd_iff.1 hy), hb⟩
  have hev : (Blowup.blowdown hN.blowupChart ∘ hψ.outerMap hh hε' hε'ε) =ᶠ[𝓝 x]
      Subtype.val := by
    filter_upwards [continuous_subtypeVal.continuousAt.preimage_mem_nhds
      (hK.isOpen_compl.mem_nhds hx)] with x' hx'
    rw [Function.comp_apply, hψ.blowdown_outerMap hh hε' hε'ε,
      hψ.isSymplecticBallEmbedding.radialContraction_of_notMem hh hx']
  rw [mpullback_apply_congr (hψ.normalizedBlowupForm_eq_on_compl _ hnot),
    SmoothForm.coe_mpullback,
    ← mpullback_comp_at ((hψ.isLocalDiffeomorph_outerMap hh hε' hε'ε).contMDiff.mdifferentiableAt
      (by simp)) ((Blowup.contMDiff_blowdown_real _).mdifferentiableAt (by simp)),
    hev.mpullback_eq, mpullback_subtype_val_apply]

omit [T2Space M] in
/-- For `w` in the shell with `w = ψ⁻¹ q` at a point `q` of `ψ(B°(r))`, the point `π⁻¹(F_h⁻¹ w)`
of `L` lies over the open ball of radius `r`. -/
private theorem norm_blowdown_radialDiffeomorph_symm_lt
    {w : radialShell (Fin (n + 1)) h hh.contDiff.contDiffOn (fun s _ ↦ hh.deriv_pos s)} {q : M}
    (hq : q ∈ ψ '' ball 0 r)
    (hw : (w : Fin (n + 1) → ℂ) = hψ.isSymplecticBallEmbedding.complexPartialDiffeomorph.symm q) :
    ‖complexToRealEuclidean (Fin (n + 1))
      ((blowdownPuncturedDiffeomorph n).symm ((hh.radialDiffeomorph n).symm w) :
        BlowupModel n).blowdown‖ < r := by
  rw [← coe_blowdownPuncturedDiffeomorph_apply, Diffeomorph.apply_symm_apply]
  refine hh.norm_radialDiffeomorph_symm_lt hψ.weight_add_width_lt ?_
  rw [hw]
  exact hψ.isSymplecticBallEmbedding.norm_complexPartialDiffeomorph_symm_lt hq

/-- Near a point `x` of the outer piece in `ψ(B°(r))`, given a local lift `g` of `ψ⁻¹` into the
shell along which `radialContraction` is `ψ ∘ F_h⁻¹ ∘ g`, the first map is the lift `ψ̃` composed
with `π⁻¹ ∘ F_h⁻¹ ∘ g`. -/
private theorem outerMap_eventuallyEq_ballLift
    (x : WeightBlowup.outerPiece (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε))
    (hx : (x : M) ∈ ψ '' ball 0 r)
    {g : M → radialShell (Fin (n + 1)) h hh.contDiff.contDiffOn (fun s _ ↦ hh.deriv_pos s)}
    (hgΨ : ∀ᶠ q in 𝓝 (x : M),
      (g q : Fin (n + 1) → ℂ) = hψ.isSymplecticBallEmbedding.complexPartialDiffeomorph.symm q)
    (hc : hψ.isSymplecticBallEmbedding.radialContraction hh =ᶠ[𝓝 (x : M)]
      hψ.isSymplecticBallEmbedding.complexPartialDiffeomorph ∘ Subtype.val ∘
        (hh.radialDiffeomorph n).symm ∘ g) :
    hψ.outerMap hh hε' hε'ε =ᶠ[𝓝 x] hψ.ballLiftPartialDiffeomorph ∘ (Subtype.val ∘
      fun x' ↦ (blowdownPuncturedDiffeomorph n).symm ((hh.radialDiffeomorph n).symm (g x'))) := by
  have hball : ψ '' ball 0 r ∈ 𝓝 (x : M) := by
    rw [← hψ.isSymplecticBallEmbedding.complexPartialDiffeomorph_target] at hx ⊢
    exact hψ.isSymplecticBallEmbedding.complexPartialDiffeomorph.open_target.mem_nhds hx
  filter_upwards [continuous_subtypeVal.continuousAt.eventually ((hgΨ.and hball).and hc)]
    with x' hx'
  set w := (blowdownPuncturedDiffeomorph n).symm ((hh.radialDiffeomorph n).symm (g x'))
  have hr' : (w : BlowupModel n) ∈ openNbhd n r :=
    mem_openNbhd_iff.2 (hψ.norm_blowdown_radialDiffeomorph_symm_lt hh hx'.1.2 hx'.1.1)
  have h0 : (w : BlowupModel n).blowdown ≠ 0 := fun h0 ↦
    mem_offDivisorOpens.1 w.property (mem_exceptionalDivisor_iff.2 h0)
  rw [Function.comp_apply, Function.comp_apply, hψ.ballLiftPartialDiffeomorph_apply ⟨_, hr'⟩,
    hψ.ballLift_of_blowdown_ne_zero _ h0, outerMap]
  congr 1
  refine Subtype.ext ?_
  dsimp only
  rw [hx'.2, Function.comp_apply, Function.comp_apply, Function.comp_apply,
    IsSymplecticBallEmbedding.coe_complexPartialDiffeomorph, Function.comp_apply,
    ← coe_blowdownPuncturedDiffeomorph_apply, Diffeomorph.apply_symm_apply]

/-- Given a local lift `g` of `ψ⁻¹` into the shell, `F_h ∘ π ∘ π⁻¹ ∘ F_h⁻¹ ∘ g`, read in `E`, is
`ψ⁻¹` near `x`. -/
private theorem radialMap_blowdown_eventuallyEq
    (x : WeightBlowup.outerPiece (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε))
    {g : M → radialShell (Fin (n + 1)) h hh.contDiff.contDiffOn (fun s _ ↦ hh.deriv_pos s)}
    (hgΨ : ∀ᶠ q in 𝓝 (x : M),
      (g q : Fin (n + 1) → ℂ) = hψ.isSymplecticBallEmbedding.complexPartialDiffeomorph.symm q) :
    Subtype.val ∘ ((radialMap h (fun _ hs ↦ hh.pos (le_of_lt hs)) ∘
      blowdownPuncturedDiffeomorph n) ∘ fun x' : WeightBlowup.outerPiece
        (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε) ↦
          (blowdownPuncturedDiffeomorph n).symm ((hh.radialDiffeomorph n).symm (g x'))) =ᶠ[𝓝 x]
      hψ.isSymplecticBallEmbedding.complexPartialDiffeomorph.symm ∘ Subtype.val := by
  filter_upwards [continuous_subtypeVal.continuousAt.eventually hgΨ] with x' hx'
  simp only [Function.comp_apply, Diffeomorph.apply_symm_apply]
  rw [coe_radialMap_radialMapDiffeomorph_symm_apply, hx']

/-- On `ψ(B°(r)) ∖ ψ(B(l))`, the first map pulls `ω̃_{ψ,l,ε}` back to `σ`: there it is
`ψ̃ ∘ π⁻¹ ∘ F_h⁻¹ ∘ ψ⁻¹`, the lift pulls the form back to `ω̃_{l,ε}`, which `π⁻¹` pulls back to
`F_h^* ω₀` (`mpullback_radialMap_profileForm`), and `ψ⁻¹` pulls `ω₀` back to `σ`. -/
private theorem mpullback_outerMap_apply_of_mem
    (x : WeightBlowup.outerPiece (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε))
    (hx : (x : M) ∈ ψ '' ball 0 r) :
    TauCeti.mpullback 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (hψ.outerMap hh hε' hε'ε)
      (hψ.normalizedBlowupForm h).val x = σ.val x := by
  obtain ⟨g₀, hg₀, hg₀Ψ, hc⟩ :=
    hψ.isSymplecticBallEmbedding.exists_radialContraction_eventuallyEq hh
      (by linarith [hh.collar_pos, hψ.weight_add_width_lt])
      ⟨hx, (WeightBlowup.mem_outerPiece_iff _).1 x.property⟩
  set Ψ := hψ.isSymplecticBallEmbedding.complexPartialDiffeomorph
  set R := hh.radialDiffeomorph n
  set B := blowdownPuncturedDiffeomorph n
  have hxt : (x : M) ∈ Ψ.target := by
    rw [IsSymplecticBallEmbedding.complexPartialDiffeomorph_target]; exact hx
  have hval {X : Type} [TopologicalSpace X] [ChartedSpace (Fin (n + 1) → ℂ) X]
      {V : TopologicalSpace.Opens X} (v : V) :
      MDifferentiableAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) Subtype.val v :=
    (contMDiff_subtypeVal (n := ∞)).mdifferentiableAt (by simp)
  -- The local lift `g₀` of `ψ⁻¹` into the shell, carried to `L` and read on the outer piece.
  let G' := fun x' : WeightBlowup.outerPiece (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε) ↦
    B.symm (R.symm (g₀ x'))
  have hG' : MDifferentiableAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) G' x :=
    ((B.symm.contMDiff.comp R.symm.contMDiff).mdifferentiableAt (by simp)).comp x
      ((IsLocalDiffeomorphAt.comp (hf := isLocalDiffeomorph_subtype_val x)
        (hg := hg₀)).mdifferentiableAt (by simp))
  have hGr : (G' x : BlowupModel n) ∈ openNbhd n r :=
    mem_openNbhd_iff.2 (hψ.norm_blowdown_radialDiffeomorph_symm_lt hh hx hg₀Ψ.self_of_nhds)
  have hΦ : MDifferentiableAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ)
      hψ.ballLiftPartialDiffeomorph (G' x : BlowupModel n) :=
    hψ.ballLiftPartialDiffeomorph.mdifferentiableAt (by simp)
      (by rw [ballLiftPartialDiffeomorph_source]; exact hGr)
  have hFB := (contMDiff_radialMap (ι := Fin (n + 1)) hh.contDiff.contDiffOn
    (fun _ hs ↦ hh.pos (le_of_lt hs))).comp B.contMDiff
  have hFBG : MDifferentiableAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ)
      ((radialMap h (fun _ hs ↦ hh.pos (le_of_lt hs)) ∘ B) ∘ G') x :=
    (hFB.mdifferentiableAt (by simp)).comp x hG'
  have hprof := congrArg Subtype.val (mpullback_radialMap_profileForm n hh)
  simp only [SmoothForm.coe_mpullback] at hprof
  rw [(hψ.outerMap_eventuallyEq_ballLift hh hε' hε'ε x hx hg₀Ψ hc).mpullback_eq,
    mpullback_comp_at ((hval _).comp x hG') hΦ,
    mpullback_apply_congr (f := Subtype.val ∘ G')
      (hψ.normalizedBlowupForm_eq_on_ballLift hh _ hGr),
    mpullback_comp_at hG' (hval _), ← hprof,
    ← mpullback_comp_at hG' (hFB.mdifferentiableAt (by simp)),
    ← mpullback_comp_at hFBG (hval _),
    (hψ.radialMap_blowdown_eventuallyEq hh hε' hε'ε x hg₀Ψ).mpullback_eq,
    mpullback_comp_at (hval _) (Ψ.symm.mdifferentiableAt (by simp) hxt),
    mpullback_subtype_val_apply,
    ω₀E_def,
    (hψ.isSymplecticBallEmbedding.isSymplecticMapOn_complexPartialDiffeomorph_symm).mpullback_apply
      hxt]

/-- On the outer piece `M ∖ ψ(B(l))`, the diffeomorphism onto `Blowup c` pulls the form
`ω̃_{ψ,l,ε}` of `Blowup c` back to `σ`. -/
private theorem mpullback_inl_weightBlowupDiffeomorph :
    SmoothForm.mpullback (inl (WeightBlowup.gluingDiffeomorphSymm
        (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε) hψ.weight_pos.le hε').toHomeomorph)
        (GluedAlong.isLocalDiffeomorph_inl _).contMDiff
        (SmoothForm.mpullback (hψ.weightBlowupDiffeomorph hh hε' hε'ε)
          (hψ.weightBlowupDiffeomorph hh hε' hε'ε).contMDiff (hψ.normalizedBlowupForm h)) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ := by
  rw [SmoothForm.mpullback_mpullback]
  refine Subtype.ext (funext fun x ↦ ?_)
  have hfun : ⇑(hψ.weightBlowupDiffeomorph hh hε' hε'ε) ∘
      inl (WeightBlowup.gluingDiffeomorphSymm (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε)
        hψ.weight_pos.le hε').toHomeomorph = hψ.outerMap hh hε' hε'ε := by
    funext x'
    rw [Function.comp_apply, weightBlowupDiffeomorph, GluedAlong.descDiffeomorph_inl]
  rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback_subtype_val_apply, hfun]
  by_cases hx : (x : M) ∈ ψ '' ball 0 r
  · exact hψ.mpullback_outerMap_apply_of_mem hh hε' hε'ε x hx
  · refine hψ.mpullback_outerMap_apply_of_notMem hh hε' hε'ε x fun ⟨z, hz, hzx⟩ ↦ hx ⟨z, ?_, hzx⟩
    exact mem_ball_zero_iff.2 ((mem_closedBall_zero_iff.1 hz).trans_lt hψ.weight_add_width_lt)

/-- **The blowup form is the form of the blowup of weight `l`** (McDuff–Salamon,
Theorem 7.1.21 (ii)). For a normalized ball embedding `ψ` of weight `l` and width `ε`, a profile
`h` of the blowup of weight `l` with collar `ε`, and `0 < ε' ≤ ε`, the diffeomorphism
`normalizedBlowupSymplectomorph` is a symplectomorphism from `Blowup c` with the form
`ω̃_{ψ,l,ε}` onto the blowup of weight `l` with collar `ε'` along `ψ` with its form `ω̃_ψ`. -/
theorem isSymplectomorphism_normalizedBlowupSymplectomorph :
    (hψ.normalizedBlowupForm h).IsSymplectomorphism
      (WeightBlowup.form (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε) hψ.weight_pos.le hε')
      (hψ.normalizedBlowupSymplectomorph hh hε' hε'ε) := by
  have hΘ : (WeightBlowup.form (hψ.isSymplecticBallEmbedding_sqrt hε' hε'ε) hψ.weight_pos.le
      hε').IsSymplectomorphism (hψ.normalizedBlowupForm h)
        (hψ.weightBlowupDiffeomorph hh hε' hε'ε) := by
    rw [SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq]
    exact (WeightBlowup.eq_form_iff _ _ _).2 ⟨hψ.mpullback_inl_weightBlowupDiffeomorph hh hε' hε'ε,
      hψ.mpullback_inr_weightBlowupDiffeomorph hh hε' hε'ε⟩
  exact hΘ.symm (by simp)

end IsNormalizedBallEmbedding

end SymplecticGeometry

end
