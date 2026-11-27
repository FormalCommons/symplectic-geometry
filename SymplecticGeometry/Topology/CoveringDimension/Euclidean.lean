/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Dimension.Covering
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Covering dimension of compact sets in Euclidean space

Every compact subset `K` of a finite-dimensional real normed space `E` has covering dimension at
most `finrank ℝ E`, as a subspace, in the sense of Tau Ceti's `TauCeti.HasCoveringDimensionLE`.
Tau Ceti proves this for `ℝ` only (`Real.hasCoveringDimensionLE_one_of_isCompact`).

The proof colours `Fin n → ℝ` by `n + 1` shifted grids of open cubes. For a scale `r > 0` and
`u = r / (3 (n + 1))`, the cube `gridCube n r c k` of colour `c : Fin (n + 1)` and index
`k : Fin n → ℤ` is the product of the open intervals
`((3 (n + 1) kᵢ + 3 c + 1) u, (3 (n + 1) kᵢ + 3 c + 3 (n + 1) - 1) u)`. Cubes of one colour are
disjoint, any two points of one cube are at distance less than `r`, and every point lies in a
cube of some colour: each coordinate lies near the boundary of the grid of at most one colour,
and there are `n` coordinates and `n + 1` colours. Given an open cover of a compact `K`, the
traces on `K` of the cubes of a scale below a Lebesgue number refine it, and a point lies in at
most one cube of each colour.

The proof of `IsCompact.hasCoveringDimensionLE_pi` adapts Tau Ceti's
`Real.hasCoveringDimensionLE_one_of_isCompact` (`TauCeti/Topology/Dimension/Covering.lean`)
from intervals to coloured cubes: the same Lebesgue number on the compact subspace, refinement by
the nonempty traces, and bound on the order.

## Main declarations

* `SymplecticGeometry.gridCube`: the cube of a colour and an index, with `isOpen_gridCube`,
  `eq_of_mem_gridCube` (cubes of one colour are disjoint), `dist_lt_of_mem_gridCube` and
  `exists_mem_gridCube` (every point lies in a cube).
* `IsCompact.hasCoveringDimensionLE_pi`: compact subsets of `Fin n → ℝ` have covering dimension
  at most `n`.
* `IsCompact.hasCoveringDimensionLE_finrank`: compact subsets of a finite-dimensional real
  normed space `E` have covering dimension at most `finrank ℝ E`.

## References

* J. R. Munkres, *Topology*, 2nd ed., Prentice Hall, 2000, §50 (covering dimension); the
  colouring by shifted grids used here is a different, elementary argument.
-/

public section

open Set

namespace SymplecticGeometry

/-- The open cube of colour `c` and index `k` at scale `r` in `Fin n → ℝ`: the product over
`i` of the open intervals `((3 (n + 1) kᵢ + 3 c + 1) u, (3 (n + 1) kᵢ + 3 c + 3 (n + 1) - 1) u)`,
with `u = r / (3 (n + 1))`. -/
noncomputable def gridCube (n : ℕ) (r : ℝ) (c : Fin (n + 1)) (k : Fin n → ℤ) : Set (Fin n → ℝ) :=
  univ.pi fun i => Ioo ((3 * (n + 1) * k i + 3 * c + 1) * (r / (3 * (n + 1))))
    ((3 * (n + 1) * k i + 3 * c + 3 * (n + 1) - 1) * (r / (3 * (n + 1))))

theorem gridCube_def (n : ℕ) (r : ℝ) (c : Fin (n + 1)) (k : Fin n → ℤ) :
    gridCube n r c k = univ.pi fun i => Ioo ((3 * (n + 1) * k i + 3 * c + 1) * (r / (3 * (n + 1))))
      ((3 * (n + 1) * k i + 3 * c + 3 * (n + 1) - 1) * (r / (3 * (n + 1)))) :=
  (rfl)

theorem mem_gridCube_iff {n : ℕ} {r : ℝ} {c : Fin (n + 1)} {k : Fin n → ℤ} {x : Fin n → ℝ} :
    x ∈ gridCube n r c k ↔ ∀ i,
      (3 * (n + 1) * k i + 3 * c + 1) * (r / (3 * (n + 1))) < x i ∧
        x i < (3 * (n + 1) * k i + 3 * c + 3 * (n + 1) - 1) * (r / (3 * (n + 1))) := by
  simp [gridCube_def]

theorem isOpen_gridCube (n : ℕ) (r : ℝ) (c : Fin (n + 1)) (k : Fin n → ℤ) :
    IsOpen (gridCube n r c k) :=
  isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo

/-- Cubes of one colour are disjoint: a point in the cubes of colour `c` with indices `k` and
`k'` has `k = k'`. -/
theorem eq_of_mem_gridCube {n : ℕ} {r : ℝ} (hr : 0 < r) {c : Fin (n + 1)} {k k' : Fin n → ℤ}
    {x : Fin n → ℝ} (hk : x ∈ gridCube n r c k) (hk' : x ∈ gridCube n r c k') : k = k' := by
  have hu : 0 < r / (3 * (n + 1)) := by positivity
  have key : ∀ {a b : Fin n → ℤ}, x ∈ gridCube n r c a → x ∈ gridCube n r c b → ∀ i, a i ≤ b i :=
    fun {a b} ha hb i => by
      have h1 := (mem_gridCube_iff.1 ha i).1
      have h2 := (mem_gridCube_iff.1 hb i).2
      have h3 : (3 * (n + 1) * a i + 3 * c + 1 : ℝ) < 3 * (n + 1) * b i + 3 * c + 3 * (n + 1) - 1 :=
        lt_of_mul_lt_mul_right (h1.trans h2) hu.le
      have h4 : ((a i : ℤ) : ℝ) < b i + 1 := by
        by_contra h
        push Not at h
        nlinarith
      exact_mod_cast Int.lt_add_one_iff.1 (by exact_mod_cast h4)
  exact funext fun i => le_antisymm (key hk hk' i) (key hk' hk i)

/-- Two points of one cube at scale `r > 0` are at distance less than `r`. -/
theorem dist_lt_of_mem_gridCube {n : ℕ} {r : ℝ} (hr : 0 < r) {c : Fin (n + 1)}
    {k : Fin n → ℤ} {x y : Fin n → ℝ} (hx : x ∈ gridCube n r c k) (hy : y ∈ gridCube n r c k) :
    dist x y < r := by
  refine (dist_pi_lt_iff hr).2 fun i => ?_
  have hx := mem_gridCube_iff.1 hx i
  have hy := mem_gridCube_iff.1 hy i
  have hlen : (3 * (n + 1) * k i + 3 * c + 3 * (n + 1) - 1) * (r / (3 * (n + 1))) -
      (3 * (n + 1) * k i + 3 * c + 1) * (r / (3 * (n + 1))) < r := by
    have : (3 * (n + 1) : ℝ) ≠ 0 := by positivity
    field_simp
    nlinarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- At scale `r > 0`, every point of `Fin n → ℝ` lies in a cube of some colour. -/
theorem exists_mem_gridCube (n : ℕ) {r : ℝ} (hr : 0 < r) (x : Fin n → ℝ) :
    ∃ c k, x ∈ gridCube n r c k := by
  set u := r / (3 * (n + 1))
  have hu : 0 < u := by positivity
  -- `q i` locates `x i` in the grid of step `u`, and `3 * j i` is a multiple of `3`
  -- at most `1` away from `q i`.
  set q : Fin n → ℤ := fun i => ⌊x i / u⌋
  set j : Fin n → ℤ := fun i => (q i + 1) / 3
  have hm : (0 : ℤ) < n + 1 := by omega
  -- The colour `j i mod (n + 1)` is the only one for which `x i` may be near a boundary.
  let f : Fin n → Fin (n + 1) := fun i =>
    ⟨(j i % (n + 1)).toNat, by
      have := Int.emod_lt_of_pos (j i) hm
      have := Int.emod_nonneg (j i) hm.ne'
      omega⟩
  obtain ⟨c, hc⟩ : ∃ c, c ∉ range f := by
    by_contra! h
    have := Fintype.card_le_of_surjective f fun c => h c
    simp at this
  have hc0 : (0 : ℤ) ≤ c := by positivity
  have hc1 : (c : ℤ) < n + 1 := by exact_mod_cast c.isLt
  refine ⟨c, fun i => (j i - c) / (n + 1), mem_gridCube_iff.2 fun i => ?_⟩
  have hdiv : ¬ ((n + 1 : ℤ) ∣ j i - c) := fun h => hc ⟨i, by
    ext
    have : j i % (n + 1) = (c : ℤ) := by
      obtain ⟨t, ht⟩ := h
      rw [show j i = c + (n + 1) * t by linarith, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt hc0 hc1]
    simp [f, this]⟩
  set a := (j i - c) / (n + 1)
  set ρ := (j i - c) % (n + 1)
  have hρ0 : ρ ≠ 0 := fun h => hdiv (Int.dvd_of_emod_eq_zero h)
  have hρ1 := Int.emod_nonneg (j i - c) hm.ne'
  have hρ2 := Int.emod_lt_of_pos (j i - c) hm
  have hja : ρ + (n + 1) * a = j i - c := Int.emod_add_mul_ediv _ _
  have hj : j i = (q i + 1) / 3 := rfl
  have hq1 : 3 * j i - 1 ≤ q i := by omega
  have hq2 : q i ≤ 3 * j i + 1 := by omega
  have hρ3 : 1 ≤ ρ := by omega
  have hlo : 3 * (n + 1) * a + 3 * c + 2 ≤ q i := by nlinarith
  have hhi : q i + 1 ≤ 3 * (n + 1) * a + 3 * c + 3 * (n + 1) - 1 := by nlinarith
  have hfl1 : (q i : ℝ) ≤ x i / u := Int.floor_le _
  have hfl2 : x i / u < q i + 1 := Int.lt_floor_add_one _
  have hlo' : (3 * (n + 1) * a + 3 * c + 2 : ℝ) ≤ q i := by exact_mod_cast hlo
  have hhi' : (q i + 1 : ℝ) ≤ 3 * (n + 1) * a + 3 * c + 3 * (n + 1) - 1 := by exact_mod_cast hhi
  constructor
  · rw [← lt_div_iff₀ hu]; linarith
  · rw [← div_lt_iff₀ hu]; linarith

end SymplecticGeometry

namespace IsCompact

open SymplecticGeometry TauCeti

/-- Every compact subset `K` of `Fin n → ℝ`, with the sup distance, has covering dimension at
most `n`. -/
theorem hasCoveringDimensionLE_pi {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K) :
    HasCoveringDimensionLE K n := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  refine hasCoveringDimensionLE_iff.2 fun 𝒰 hUo hUc => ?_
  obtain ⟨δ, hδ, hδU⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (c := fun U : 𝒰 => (U : Set K)) (fun U => hUo U U.property)
    (by simpa [sUnion_eq_iUnion] using hUc.ge)
  -- The refinement: the traces on `K` of all cubes at scale `δ` that meet `K`.
  let cube : Fin (n + 1) × (Fin n → ℤ) → Set K := fun p => (↑) ⁻¹' gridCube n δ p.1 p.2
  refine ⟨{V | ∃ p, cube p = V ∧ V.Nonempty}, ?_, ?_, ?_, fun x => ?_⟩
  · rintro _ ⟨p, rfl, -⟩
    exact (isOpen_gridCube n δ _ _).preimage continuous_subtypeVal
  · refine eq_univ_of_forall fun x => ?_
    obtain ⟨c, k, h⟩ := exists_mem_gridCube n hδ x
    exact mem_sUnion.2 ⟨cube (c, k), ⟨(c, k), rfl, x, h⟩, h⟩
  · rintro _ ⟨p, rfl, y, hy⟩
    obtain ⟨U, hyU⟩ := hδU y (mem_univ y)
    refine ⟨U, U.property, fun z hz => hyU ?_⟩
    rw [Metric.mem_ball, Subtype.dist_eq]
    exact dist_lt_of_mem_gridCube hδ hz hy
  · -- A cube containing `x` is determined by its colour.
    have hsub : {V | V ∈ {V | ∃ p, cube p = V ∧ V.Nonempty} ∧ x ∈ V} ⊆
        cube '' {p | (x : Fin n → ℝ) ∈ gridCube n δ p.1 p.2} := by
      rintro _ ⟨⟨p, rfl, -⟩, hx⟩
      exact ⟨p, hx, rfl⟩
    refine (encard_le_encard hsub).trans ((encard_image_le _ _).trans ?_)
    refine (encard_le_encard_of_injOn (f := Prod.fst) (t := univ) (mapsTo_univ _ _)
      fun p hp p' hp' hpp' => ?_).trans (by simp)
    obtain ⟨c, k⟩ := p
    obtain ⟨c', k'⟩ := p'
    obtain rfl : c = c' := hpp'
    rw [eq_of_mem_gridCube hδ (k := k) hp hp']

/-- Every compact subset `K` of a finite-dimensional real normed space `E` has covering
dimension at most `finrank ℝ E`. -/
theorem hasCoveringDimensionLE_finrank {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsCompact K) :
    HasCoveringDimensionLE K (Module.finrank ℝ E) := by
  let e : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  exact (e.toHomeomorph.image K).isHomeomorph.hasCoveringDimensionLE_iff.2
    (hK.image e.continuous).hasCoveringDimensionLE_pi

end IsCompact

end
