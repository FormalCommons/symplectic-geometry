/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Blowup.Normalized.Basic
public import SymplecticGeometry.Geometry.Symplectic.Blowup.Weight.Basic
public import SymplecticGeometry.Geometry.Symplectic.Complex.Radial
import SymplecticGeometry.Analysis.Complex.QuadraticLeviForm

/-!
# The blowup forms and the blowup of weight `l`

Work in progress: see the pull request.

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

namespace BlowupModel.IsBlowupProfile

variable {l ε : ℝ} {h : ℝ → ℝ}

/-- A profile of the blowup of weight `l` maps `(0, ∞)` onto `(l², ∞)`: it is increasing, equal
to `l²` at `0` and to the identity far out. -/
theorem image_Ioi (hh : IsBlowupProfile l ε h) : h '' Ioi 0 = Ioi (l ^ 2) := by
  have h0 : h 0 = l ^ 2 := by rw [hh.eq_of_le (by positivity)]; ring
  ext t
  refine ⟨?_, fun ht ↦ ?_⟩
  · rintro ⟨s, hs, rfl⟩
    exact h0 ▸ hh.strictMono hs
  · rw [mem_Ioi] at ht
    have hs₁ : h (max t ((l + ε) ^ 2)) = max t ((l + ε) ^ 2) := hh.eq_of_ge (le_max_right _ _)
    have hpos : 0 < max t ((l + ε) ^ 2) :=
      lt_max_of_lt_left ((sq_nonneg l).trans_lt ht)
    obtain ⟨s, hs, hst⟩ := intermediate_value_Ioc hpos.le hh.contDiff.continuous.continuousOn
      ⟨by rw [h0]; exact ht, by rw [hs₁]; exact le_max_left _ _⟩
    exact ⟨s, hs.1, hst⟩

variable (n : ℕ) in
/-- The radial map `F_h z = √(h(|z|²) / |z|²) z` of a profile `h` of the blowup of weight `l`, as
a diffeomorphism of `E ∖ 0` onto the complement of the closed ball `|w| ≤ l`. -/
abbrev radialDiffeomorph (hh : IsBlowupProfile l ε h) :=
  radialMapDiffeomorph (Fin (n + 1)) h hh.contDiff.contDiffOn (fun _ hs ↦ hh.pos (le_of_lt hs))
    fun s _ ↦ hh.deriv_pos s

/-- The shell of a profile of the blowup of weight `l` is the complement of the closed ball of
radius `l`. -/
theorem mem_radialShell_iff (hh : IsBlowupProfile l ε h) {w : Fin (n + 1) → ℂ} :
    w ∈ radialShell (Fin (n + 1)) h hh.contDiff.contDiffOn (fun s _ ↦ hh.deriv_pos s) ↔
      l < ‖complexToRealEuclidean (Fin (n + 1)) w‖ := by
  rw [mem_radialShell, ← norm_sq_complexToRealEuclidean, hh.image_Ioi, mem_Ioi,
    pow_lt_pow_iff_left₀ hh.weight_pos.le (norm_nonneg _) two_ne_zero]

/-- The radial map of a profile of the blowup of weight `l` with collar `ε` is the identity on
`|z| ≥ l + ε`. -/
theorem radialMap_of_le (hh : IsBlowupProfile l ε h) {z : puncturedSpace (Fin (n + 1) → ℂ)}
    (hz : l + ε ≤ ‖complexToRealEuclidean (Fin (n + 1)) z‖) :
    radialMap h (fun _ hs ↦ hh.pos (le_of_lt hs)) z = z := by
  have hz0 := norm_sq_complexToRealEuclidean_pos z
  refine Subtype.ext ?_
  rw [radialMap_apply, ← norm_sq_complexToRealEuclidean,
    hh.eq_of_ge (pow_le_pow_left₀ (by linarith [hh.weight_pos, hh.collar_pos]) hz 2),
    div_self hz0.ne', Real.sqrt_one, one_smul]

/-- The radial map of a profile of the blowup of weight `l` with collar `ε` is the radial map
`F_l z = √(1 + l² / |z|²) z` of the model on `|z| ≤ ε`. -/
theorem radialMap_of_le_collar (hh : IsBlowupProfile l ε h)
    {z : puncturedSpace (Fin (n + 1) → ℂ)} (hz : ‖complexToRealEuclidean (Fin (n + 1)) z‖ ≤ ε) :
    radialMap h (fun _ hs ↦ hh.pos (le_of_lt hs)) z =
      radialMap (fun s ↦ s + l ^ 2) (fun _ hs ↦ add_pos_of_pos_of_nonneg hs (sq_nonneg l)) z := by
  refine Subtype.ext ?_
  rw [radialMap_apply, radialMap_apply, ← norm_sq_complexToRealEuclidean,
    hh.eq_of_le (pow_le_pow_left₀ (norm_nonneg _) hz 2), add_comm (l ^ 2)]

/-- The radial map of a profile of the blowup of weight `l` with collar `ε` maps the open ball of
radius `r > l + ε` into itself. -/
theorem norm_radialMap_lt (hh : IsBlowupProfile l ε h) {r : ℝ} (hr : l + ε < r)
    {z : puncturedSpace (Fin (n + 1) → ℂ)} (hz : ‖complexToRealEuclidean (Fin (n + 1)) z‖ < r) :
    ‖complexToRealEuclidean (Fin (n + 1)) (radialMap h (fun _ hs ↦ hh.pos (le_of_lt hs)) z)‖ <
      r := by
  have hle : 0 ≤ l + ε := by linarith [hh.weight_pos, hh.collar_pos]
  by_cases hzle : l + ε ≤ ‖complexToRealEuclidean (Fin (n + 1)) z‖
  · rwa [hh.radialMap_of_le hzle]
  · refine (pow_lt_pow_iff_left₀ (norm_nonneg _) (hle.trans hr.le) two_ne_zero).1 ?_
    rw [norm_radialMap]
    calc h (‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2) < h ((l + ε) ^ 2) :=
          hh.strictMono (pow_lt_pow_left₀ (not_le.1 hzle) (norm_nonneg _) two_ne_zero)
      _ = (l + ε) ^ 2 := hh.eq_of_ge le_rfl
      _ < r ^ 2 := pow_lt_pow_left₀ hr hle two_ne_zero

/-- For `l + ε < r`, a point `z ≠ 0` whose image under the radial map of `h` lies in the open ball
of radius `r` lies in it too: off `B(l + ε)` the radial map is the identity. -/
theorem norm_lt_of_norm_radialMap_lt (hh : IsBlowupProfile l ε h) {r : ℝ} (hr : l + ε < r) {z : puncturedSpace (Fin (n + 1) → ℂ)}
    (hz : ‖complexToRealEuclidean (Fin (n + 1))
      (radialMap h (fun _ hs ↦ hh.pos (le_of_lt hs)) z)‖ < r) :
    ‖complexToRealEuclidean (Fin (n + 1)) z‖ < r := by
  by_contra hle
  rw [hh.radialMap_of_le (hr.le.trans (not_lt.1 hle))] at hz
  exact hle hz

end BlowupModel.IsBlowupProfile
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
  refine not_le.1 fun hle ↦ hp.2 ⟨_, mem_closedBall_zero_iff.2 hle, ?_⟩
  have := hψ.complexPartialDiffeomorph.right_inv
    (by rw [complexPartialDiffeomorph_target]; exact hp.1)
  rwa [coe_complexPartialDiffeomorph, Function.comp_apply] at this

open scoped Classical in
/-- The map `ψ ∘ F_h⁻¹ ∘ ψ⁻¹` of `M`, for the radial map `F_h` of a profile `h` of the blowup of
weight `l`: on `ψ(B°(r)) ∖ ψ(B(l))` it is `ψ ∘ F_h⁻¹ ∘ ψ⁻¹`, and elsewhere the identity. For
`l + ε < r` it is the identity off `ψ(B(l + ε))` (`radialContraction_of_notMem`) and undoes
`ψ ∘ F_h ∘ ψ⁻¹` (`radialContraction_radialMap`). -/
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
    have hΨp : ψ (complexToRealEuclidean (Fin (n + 1)) (Ψ.symm p)) = p := by
      have := Ψ.right_inv hpt
      rwa [coe_complexPartialDiffeomorph, Function.comp_apply] at this
    have hle : l + ε ≤ ‖complexToRealEuclidean (Fin (n + 1)) (Ψ.symm p)‖ :=
      not_lt.1 fun hlt ↦ hp ⟨_, mem_closedBall_zero_iff.2 hlt.le, hΨp⟩
    have h0 : Ψ.symm p ∈ puncturedSpace (Fin (n + 1) → ℂ) := by
      rw [mem_puncturedSpace]
      rintro h0
      rw [h0, map_zero, norm_zero] at hle
      linarith [hh.weight_pos, hh.collar_pos]
    rw [hψ.radialContraction_of_mem hh hp']
    have hR : (hh.radialDiffeomorph n).symm ⟨_, hψ.complexPartialDiffeomorph_symm_mem_radialShell hh hp'⟩ =
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
  have hws : (w : Fin (n + 1) → ℂ) ∈ Ψ.source := by
    rw [mem_complexPartialDiffeomorph_source_iff]; exact hw
  have hlw : l < ‖complexToRealEuclidean (Fin (n + 1)) w‖ := by
    have := (hh.radialDiffeomorph n z).property
    rwa [coe_radialMapDiffeomorph_apply, hh.mem_radialShell_iff] at this
  have hp : ψ (complexToRealEuclidean (Fin (n + 1)) w) ∈ ψ '' ball 0 r ∧
      ψ (complexToRealEuclidean (Fin (n + 1)) w) ∉ ψ '' closedBall 0 l := by
    refine ⟨⟨_, mem_ball_zero_iff.2 hw, rfl⟩, ?_⟩
    rintro ⟨v, hv, hvw⟩
    have hvr : v ∈ closedBall 0 r := closedBall_subset_closedBall
      (by linarith [hh.weight_pos, hh.collar_pos]) hv
    rw [hψ.injOn hvr (mem_closedBall_zero_iff.2 hw.le) hvw, mem_closedBall_zero_iff] at hv
    exact hv.not_gt hlw
  rw [hψ.radialContraction_of_mem hh hp]
  have hsymm : Ψ.symm (ψ (complexToRealEuclidean (Fin (n + 1)) w)) = w := by
    have := Ψ.left_inv hws
    rwa [coe_complexPartialDiffeomorph, Function.comp_apply] at this
  have hR : (hh.radialDiffeomorph n).symm ⟨_, hψ.complexPartialDiffeomorph_symm_mem_radialShell hh hp⟩ = z := by
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
  refine hq.2 ((hψ.complexPartialDiffeomorph.right_inv ?_).symm.trans ?_)
  · rw [complexPartialDiffeomorph_target]; exact hq.1
  · rw [coe_complexPartialDiffeomorph, Function.comp_apply]
    exact (congrArg (fun w ↦ ψ (complexToRealEuclidean (Fin (n + 1)) w)) h0).trans
      (by rw [map_zero])

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
  · have hqt : q ∈ hψ.complexPartialDiffeomorph.target := by
      rw [complexPartialDiffeomorph_target]; exact hqb
    have hs : ‖complexToRealEuclidean (Fin (n + 1))
        (hψ.complexPartialDiffeomorph.symm q)‖ < r := by
      rw [← hψ.mem_complexPartialDiffeomorph_source_iff]
      exact hψ.complexPartialDiffeomorph.map_target hqt
    rw [hψ.radialExpansion_of_mem hh ⟨hqb, hq⟩, coe_complexPartialDiffeomorph,
      Function.comp_apply, hψ.radialContraction_radialMap hh hr
        ⟨_, hψ.complexPartialDiffeomorph_symm_mem_puncturedSpace ⟨hqb, hq⟩⟩ hs]
    have := hψ.complexPartialDiffeomorph.right_inv hqt
    rwa [coe_complexPartialDiffeomorph, Function.comp_apply] at this
  · rw [hψ.radialExpansion_of_not hh fun h ↦ hqb h.1]
    refine hψ.radialContraction_of_notMem hh fun ⟨z, hz, hzq⟩ ↦ hqb ⟨z, ?_, hzq⟩
    exact mem_ball_zero_iff.2 ((mem_closedBall_zero_iff.1 hz).trans_lt hr)

/-- For `l + ε < r`, `radialContraction` sends no point off `ψ(B(l))` to `ψ 0`. -/
theorem radialContraction_ne (hr : l + ε < r) {p : M} (hp : p ∉ ψ '' closedBall 0 l) :
    hψ.radialContraction hh p ≠ ψ 0 := by
  by_cases hp' : p ∈ ψ '' ball 0 r ∧ p ∉ ψ '' closedBall 0 l
  · set z := (hh.radialDiffeomorph n).symm
      ⟨_, hψ.complexPartialDiffeomorph_symm_mem_radialShell hh hp'⟩
    have hz : ‖complexToRealEuclidean (Fin (n + 1)) z‖ < r := by
      refine hh.norm_lt_of_norm_radialMap_lt hr ?_
      rw [← coe_radialMapDiffeomorph_apply hh.contDiff.contDiffOn _ (fun s _ ↦ hh.deriv_pos s),
        Diffeomorph.apply_symm_apply, ← hψ.mem_complexPartialDiffeomorph_source_iff]
      exact hψ.complexPartialDiffeomorph.map_target
        (by rw [complexPartialDiffeomorph_target]; exact hp'.1)
    rw [hψ.radialContraction_of_mem hh hp', coe_complexPartialDiffeomorph, Function.comp_apply]
    intro h0
    have hr0 : (0 : ℝ) ≤ r := (norm_nonneg _).trans hz.le
    have := hψ.injOn (mem_closedBall_zero_iff.2 hz.le) (mem_closedBall_self hr0) h0
    rw [map_eq_zero_iff _ (complexToRealEuclidean (Fin (n + 1))).injective] at this
    exact mem_puncturedSpace.1 z.property this
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
    have hz : ‖complexToRealEuclidean (Fin (n + 1)) z‖ < r := by
      refine hh.norm_lt_of_norm_radialMap_lt hr ?_
      rw [← coe_radialMapDiffeomorph_apply hh.contDiff.contDiffOn _ (fun s _ ↦ hh.deriv_pos s),
        Diffeomorph.apply_symm_apply, ← hψ.mem_complexPartialDiffeomorph_source_iff]
      exact Ψ.map_target hpt
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
    rw [hz', ← coe_radialMapDiffeomorph_apply hh.contDiff.contDiffOn _
      (fun s _ ↦ hh.deriv_pos s), Diffeomorph.apply_symm_apply]
    exact Ψ.right_inv hpt
  · have hpb : p ∉ ψ '' ball 0 r := fun hpb ↦ hp' ⟨hpb, hp⟩
    rw [hψ.radialContraction_of_not hh hp', hψ.radialExpansion_of_not hh fun h ↦ hpb h.1]

variable [T2Space M]

/-- `radialContraction` is a local diffeomorphism at each point off `ψ(B(l))`, for `l + ε < r`. -/
theorem isLocalDiffeomorphAt_radialContraction (hr : l + ε < r) {p : M}
    (hp : p ∉ ψ '' closedBall 0 l) :
    IsLocalDiffeomorphAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞
      (hψ.radialContraction hh) p := by
  classical
  have hl : l ≤ r := by linarith [hh.collar_pos]
  have hlε : l + ε ≤ r := hr.le
  have hcl : IsClosed (ψ '' closedBall 0 l) := (hψ.isCompact_image_closedBall hl).isClosed
  by_cases hpb : p ∈ ψ '' ball 0 r
  · set Ψ := hψ.complexPartialDiffeomorph
    set R := hh.radialDiffeomorph n
    let U : Set M := ψ '' ball 0 r ∩ (ψ '' closedBall 0 l)ᶜ
    have hUo : IsOpen U := by
      refine IsOpen.inter ?_ hcl.isOpen_compl
      have := Ψ.open_target
      rwa [complexPartialDiffeomorph_target] at this
    have hev : ∀ᶠ q in 𝓝 p, q ∈ U := hUo.mem_nhds ⟨hpb, hp⟩
    let g : M → radialShell (Fin (n + 1)) h hh.contDiff.contDiffOn (fun s _ ↦ hh.deriv_pos s) :=
      fun q ↦ if hq : q ∈ U then ⟨_, hψ.complexPartialDiffeomorph_symm_mem_radialShell hh hq⟩
        else ⟨_, hψ.complexPartialDiffeomorph_symm_mem_radialShell hh ⟨hpb, hp⟩⟩
    have hpt : p ∈ Ψ.symm.source := by
      change p ∈ Ψ.target
      rw [complexPartialDiffeomorph_target]; exact hpb
    have hg : IsLocalDiffeomorphAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ g p := by
      rw [← isLocalDiffeomorphAt_subtypeVal_comp_iff]
      refine (Ψ.symm.isLocalDiffeomorphAt _ _ _ hpt).congr_of_eventuallyEq ?_
      filter_upwards [hev] with q hq
      simp only [g, dite_eq_left hq, Function.comp_apply]
      rfl
    have hz : ((R.symm (g p) : puncturedSpace (Fin (n + 1) → ℂ)) : Fin (n + 1) → ℂ) ∈
        Ψ.source := by
      rw [mem_complexPartialDiffeomorph_source_iff]
      refine hh.norm_lt_of_norm_radialMap_lt hr ?_
      rw [← coe_radialMapDiffeomorph_apply hh.contDiff.contDiffOn _ (fun s _ ↦ hh.deriv_pos s),
        Diffeomorph.apply_symm_apply]
      simp only [g, dite_eq_left (show p ∈ U from ⟨hpb, hp⟩)]
      rw [← hψ.mem_complexPartialDiffeomorph_source_iff]
      exact Ψ.map_target (by rw [complexPartialDiffeomorph_target]; exact hpb)
    have hcomp := IsLocalDiffeomorphAt.comp (hf := hg) (hg := IsLocalDiffeomorphAt.comp
      (hf := R.symm.isLocalDiffeomorph (g p))
      (hg := isLocalDiffeomorph_subtype_val (R.symm (g p))))
    refine (IsLocalDiffeomorphAt.comp (hf := hcomp) (hg := Ψ.isLocalDiffeomorphAt _ _ _ hz)
      ).congr_of_eventuallyEq ?_
    filter_upwards [hev] with q hq
    rw [hψ.radialContraction_of_mem hh hq]
    simp only [g, dite_eq_left hq, Function.comp_apply]
    -- `Ψ` and `R` are local names for the two maps on the left.
    rfl
  · have hK : IsClosed (ψ '' closedBall 0 (l + ε)) :=
      (hψ.isCompact_image_closedBall hlε).isClosed
    have hpK : p ∉ ψ '' closedBall 0 (l + ε) := fun ⟨z, hz, hzp⟩ ↦
      hpb ⟨z, mem_ball_zero_iff.2 ((mem_closedBall_zero_iff.1 hz).trans_lt hr), hzp⟩
    refine ((Diffeomorph.refl 𝓘(ℝ, Fin (n + 1) → ℂ) M ∞).isLocalDiffeomorph p
      ).congr_of_eventuallyEq ?_
    filter_upwards [hK.isOpen_compl.mem_nhds hpK] with q hq
    rw [hψ.radialContraction_of_notMem hh hq, Diffeomorph.coe_refl, id]

end IsSymplecticBallEmbedding

end SymplecticGeometry

end
