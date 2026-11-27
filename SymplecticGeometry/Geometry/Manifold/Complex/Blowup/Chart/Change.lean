/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Chart.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# The change of chart between blowups

Let `c` and `c'` be two charts at the centre `p₀` of the complex maximal atlas of `M`. The blowups
`Blowup c` and `Blowup c'` are built from different charts, but they are canonically
biholomorphic. This file constructs that biholomorphism `Blowup.chartChange c c'`.

Over the source of `c'`, the change of chart is the chart `Blowup.liftChart c c'` of `Blowup c`
lifted from `c'`, read in the second piece of `Blowup c'`; over the rest of `M`, which misses
`p₀`, it is the identity of `M \ {p₀}`, read in the first piece. It commutes with the blowdowns,
so off the exceptional divisors it is the identity of `M \ {p₀}`, while on the divisor it acts
on lines by the derivative at `0` of the transition map `c' ∘ c⁻¹`. The change of chart from `c'`
back to `c` is its inverse, and both are holomorphic: near the divisor, by the holomorphy of the
lifted chart, and off it, by `Blowup.blowdownDiffeomorph`.

## Main definitions

* `SymplecticGeometry.Blowup.chartChange c c'`: the biholomorphism `Blowup c ≃ Blowup c'`.

## Main results

* `SymplecticGeometry.Blowup.chartChange_inl`, `SymplecticGeometry.Blowup.chartChange_inr`,
  `SymplecticGeometry.Blowup.chartChange_ofDirection`: its values on the two pieces of the blowup
  and on the exceptional divisor.
* `SymplecticGeometry.Blowup.blowdown_chartChange`: it commutes with the blowdowns.
* `SymplecticGeometry.Blowup.chartChange_symm`, `SymplecticGeometry.Blowup.chartChange_self`:
  its inverse is the change of chart the other way, and the change of chart from `c` to itself
  is the identity.
* `SymplecticGeometry.Blowup.liftChart_self`: lifted from `c` itself, the lifted chart is
  `Blowup.lift c` over the source of `c`.
* `SymplecticGeometry.Blowup.chartChange_trans`,
  `SymplecticGeometry.Blowup.chartChange_chartChange`: the cocycle condition.
* `SymplecticGeometry.Blowup.chartChange_ofDirection_directionEquiv`: on the lines of the tangent
  space at the centre, read through `directionEquiv`, the change of chart is independent of the
  charts.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1, Exercise 7.1.4.
* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 1,
  §4.
-/

public section

open Projectivization
open scoped LinearAlgebra.Projectivization Manifold ContDiff

noncomputable section

namespace SymplecticGeometry

namespace Blowup

open BlowupModel TopologicalSpace

open GluedAlong (inl inr)

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  {p₀ : M} (c c' c'' : BlowupChart (n := n) M p₀)
  [hc : Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]
  [hc' : Fact (c'.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]
  [Fact (c''.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]

/-! ### The map -/

omit hc hc' in
/-- Off the source of `c'`, the blowdown misses the centre. -/
private theorem blowdown_mem_puncturedOpens_of_notMem {z : Blowup c}
    (hz : blowdown c z ∉ c'.source) :
    blowdown c z ∈ puncturedOpens c' :=
  (mem_puncturedOpens c').2 fun h ↦ hz (h.symm ▸ c'.mem_source)

open scoped Classical in
/-- The change of chart from `Blowup c` to `Blowup c'`, as a map. Over the source of `c'` it is the
lifted chart `liftChart c c'`, read in the second piece of `Blowup c'`; over the rest of `M`, it
is the blowdown, read in the first piece. -/
private def chartChangeMap (z : Blowup c) : Blowup c' :=
  if hz : blowdown c z ∈ c'.source then
    inr (gluingHomeomorph c') ⟨liftChart c c' z, liftChart_mem_modelOpens c c' hz⟩
  else inl (gluingHomeomorph c') ⟨blowdown c z, blowdown_mem_puncturedOpens_of_notMem c c' hz⟩

variable {c c'} in
private theorem chartChangeMap_of_mem {z : Blowup c} (hz : blowdown c z ∈ c'.source) :
    chartChangeMap c c' z =
      inr (gluingHomeomorph c') ⟨liftChart c c' z, liftChart_mem_modelOpens c c' hz⟩ :=
  dite_eq_left hz

/-- The change of chart commutes with the blowdowns. -/
private theorem blowdown_chartChangeMap (z : Blowup c) :
    blowdown c' (chartChangeMap c c' z) = blowdown c z := by
  rw [chartChangeMap]
  split_ifs with hz
  · rw [blowdown_inr, blowdown_liftChart c c' hz, c'.left_inv hz]
  · rw [blowdown_inl]

/-- The change of chart sends the exceptional divisor of `Blowup c` to that of `Blowup c'`, and
its complement to the complement. -/
private theorem chartChangeMap_mem_exceptionalDivisor_iff {z : Blowup c} :
    chartChangeMap c c' z ∈ exceptionalDivisor c' ↔ z ∈ exceptionalDivisor c := by
  rw [← blowdown_eq_center_iff, blowdown_chartChangeMap, blowdown_eq_center_iff]

/-- Off the exceptional divisor, the change of chart is the identity of `M \ {p₀}`. -/
private theorem chartChangeMap_of_notMem {z : Blowup c} (hz : z ∉ exceptionalDivisor c) :
    chartChangeMap c c' z =
      inl (gluingHomeomorph c')
        ⟨blowdown c z, (mem_puncturedOpens c').2 ((blowdown_eq_center_iff c).not.2 hz)⟩ :=
  injOn_blowdown c' ((chartChangeMap_mem_exceptionalDivisor_iff c c').not.2 hz)
    (inl_notMem_exceptionalDivisor c' _) (by rw [blowdown_chartChangeMap, blowdown_inl])

/-- On the exceptional divisor, the change of chart acts on lines by the derivative at `0` of
`c' ∘ c⁻¹`. -/
private theorem chartChangeMap_ofDirection (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    chartChangeMap c c' (ofDirection c ℓ) =
      ofDirection c' ((c.fderivTransEquiv c').mapProjectivization ℓ) := by
  rw [chartChangeMap_of_mem (by simpa using c'.mem_source), ofDirection_def c']
  congr 2
  exact liftChart_ofDirection c c' ℓ

/-- The cocycle condition: the change of chart from `c` to `c'` followed by the change of chart
from `c'` to `c''` is the change of chart from `c` to `c''`. -/
private theorem chartChangeMap_chartChangeMap (z : Blowup c) :
    chartChangeMap c' c'' (chartChangeMap c c' z) = chartChangeMap c c'' z := by
  by_cases hz : z ∈ exceptionalDivisor c
  · rw [exceptionalDivisor_def] at hz
    obtain ⟨ℓ, rfl⟩ := hz
    rw [chartChangeMap_ofDirection, chartChangeMap_ofDirection, chartChangeMap_ofDirection,
      ← Homeomorph.trans_apply, ← ContinuousLinearEquiv.mapProjectivization_trans,
      BlowupChart.fderivTransEquiv_trans]
  · refine injOn_blowdown c'' ?_ ?_ (by
      rw [blowdown_chartChangeMap, blowdown_chartChangeMap, blowdown_chartChangeMap])
    · rwa [Set.mem_compl_iff, chartChangeMap_mem_exceptionalDivisor_iff,
        chartChangeMap_mem_exceptionalDivisor_iff]
    · rwa [Set.mem_compl_iff, chartChangeMap_mem_exceptionalDivisor_iff]

/-- The change of chart from `c` to itself is the identity. -/
private theorem chartChangeMap_self (z : Blowup c) : chartChangeMap c c z = z := by
  by_cases hz : z ∈ exceptionalDivisor c
  · rw [exceptionalDivisor_def] at hz
    obtain ⟨ℓ, rfl⟩ := hz
    rw [chartChangeMap_ofDirection, BlowupChart.fderivTransEquiv_self,
      ContinuousLinearEquiv.mapProjectivization_refl, Homeomorph.refl_apply, id_eq]
  · refine injOn_blowdown c ?_ hz (by rw [blowdown_chartChangeMap])
    rwa [Set.mem_compl_iff, chartChangeMap_mem_exceptionalDivisor_iff]

/-! ### Holomorphy -/

variable [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]

/-- The change of chart is holomorphic. -/
private theorem contMDiff_chartChangeMap :
    ContMDiff 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (chartChangeMap c c') := by
  intro z
  by_cases hz : z ∈ exceptionalDivisor c
  · -- Near the divisor, it is the lifted chart read in the second piece of `Blowup c'`.
    have hzU : blowdown c z ∈ c'.source := by
      rw [(blowdown_eq_center_iff c).2 hz]
      exact c'.mem_source
    let U : Opens (Blowup c) :=
      ⟨blowdown c ⁻¹' c'.source, c'.open_source.preimage (blowdown c).continuous⟩
    let F : U → modelOpens c' := fun w ↦
      ⟨liftChart c c' w, liftChart_mem_modelOpens c c' w.property⟩
    have hF : ContMDiffAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω F ⟨z, hzU⟩ := by
      refine (TauCeti.ContMDiffAt.subtypeVal_comp_iff _ F _).1 ?_
      exact contMDiffAt_subtype_iff.2
        (((isLocalDiffeomorphOn_liftChart c c') ⟨z, hzU⟩).contMDiffAt)
    have h : ContMDiffAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω
        (fun w : U ↦ chartChangeMap c c' w) ⟨z, hzU⟩ :=
      (((isLocalDiffeomorph_inr c') _).contMDiffAt.comp _ hF).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun w ↦ chartChangeMap_of_mem w.property)
    exact contMDiffAt_subtype_iff.1 h
  · -- Off the divisor, it is the blowdown read in the first piece of `Blowup c'`.
    have h : ContMDiffAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω
        (fun w : offDivisorOpens c ↦ chartChangeMap c c' w) ⟨z, (mem_offDivisorOpens c).2 hz⟩ :=
      (((isLocalDiffeomorph_inl c') _).contMDiffAt.comp _
        ((contMDiff_inclusion (puncturedOpens_eq c c').le).comp
          (blowdownDiffeomorph c).contMDiff _)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun w ↦ by
          simp only [Function.comp_apply]
          rw [chartChangeMap_of_notMem c c' ((mem_offDivisorOpens c).1 w.property)]
          simp [Opens.inclusion])
    exact contMDiffAt_subtype_iff.1 h

/-! ### The biholomorphism -/

/-- **The change of chart between blowups.** For two charts `c` and `c'` at the centre of the
complex maximal atlas of `M`, the biholomorphism `Blowup c ≃ Blowup c'`. It commutes with the
blowdowns, is the identity of `M \ {p₀}` off the exceptional divisors, and acts on the divisor
by the derivative at `0` of `c' ∘ c⁻¹`; its inverse is the change of chart from `c'` to `c`. -/
def chartChange : Blowup c ≃ₘ^ω⟮𝓘(ℂ, Fin (n + 1) → ℂ), 𝓘(ℂ, Fin (n + 1) → ℂ)⟯ Blowup c' where
  toFun := chartChangeMap c c'
  invFun := chartChangeMap c' c
  left_inv z := (chartChangeMap_chartChangeMap c c' c z).trans (chartChangeMap_self c z)
  right_inv z := (chartChangeMap_chartChangeMap c' c c' z).trans (chartChangeMap_self c' z)
  contMDiff_toFun := contMDiff_chartChangeMap c c'
  contMDiff_invFun := contMDiff_chartChangeMap c' c

private theorem coe_chartChange : ⇑(chartChange c c') = chartChangeMap c c' :=
  (rfl)

/-- The inverse of the change of chart from `c` to `c'` is the change of chart from `c'` to
`c`. -/
@[simp]
theorem chartChange_symm : (chartChange c c').symm = chartChange c' c :=
  (rfl)

/-- The change of chart from `c` to itself is the identity. -/
@[simp]
theorem chartChange_self : chartChange c c = Diffeomorph.refl _ (Blowup c) ω :=
  Diffeomorph.ext fun z ↦ by rw [coe_chartChange, chartChangeMap_self, Diffeomorph.coe_refl, id_eq]

/-- The change of chart commutes with the blowdowns. -/
@[simp]
theorem blowdown_chartChange (z : Blowup c) :
    blowdown c' (chartChange c c' z) = blowdown c z := by
  rw [coe_chartChange, blowdown_chartChangeMap]

/-- The change of chart sends the exceptional divisor of `Blowup c` onto that of `Blowup c'`. -/
@[simp]
theorem chartChange_mem_exceptionalDivisor_iff {z : Blowup c} :
    chartChange c c' z ∈ exceptionalDivisor c' ↔ z ∈ exceptionalDivisor c := by
  rw [coe_chartChange, chartChangeMap_mem_exceptionalDivisor_iff]

/-- Over the source of `c'`, the change of chart is the lifted chart `liftChart c c'`, read in the
second piece of `Blowup c'`. -/
theorem chartChange_of_mem {z : Blowup c} (hz : blowdown c z ∈ c'.source) :
    chartChange c c' z =
      inr (gluingHomeomorph c') ⟨liftChart c c' z, liftChart_mem_modelOpens c c' hz⟩ := by
  rw [coe_chartChange, chartChangeMap_of_mem hz]

/-- Lifted from `c` itself, the lifted chart is the map `Blowup.lift c` to the model, over the
source of `c`. -/
theorem liftChart_self {z : Blowup c} (hz : blowdown c z ∈ c.source) :
    liftChart c c z = lift c z := by
  have h := chartChange_of_mem c c hz
  rw [chartChange_self, Diffeomorph.coe_refl, id_eq] at h
  conv_rhs => rw [h]
  rw [lift_inr]

/-- Off the exceptional divisor, the change of chart is the identity of `M \ {p₀}`, read in the
first piece of `Blowup c'`. -/
theorem chartChange_of_notMem {z : Blowup c} (hz : z ∉ exceptionalDivisor c) :
    chartChange c c' z =
      inl (gluingHomeomorph c')
        ⟨blowdown c z, (mem_puncturedOpens c').2 ((blowdown_eq_center_iff c).not.2 hz)⟩ := by
  rw [coe_chartChange, chartChangeMap_of_notMem c c' hz]

/-- On the first piece, the change of chart is the identity of `M \ {p₀}`. -/
@[simp]
theorem chartChange_inl (x : puncturedOpens c) :
    chartChange c c' (inl (gluingHomeomorph c) x) =
      inl (gluingHomeomorph c') (Opens.inclusion (puncturedOpens_eq c c').le x) := by
  rw [coe_chartChange, chartChangeMap_of_notMem c c' (inl_notMem_exceptionalDivisor c x)]
  congr 2
  exact blowdown_inl c x

/-- On the part of the model over the target of `c` whose image in `M` lies in the source of `c'`,
the change of chart is the lift of `c' ∘ c⁻¹` by its derivative at `0`, read in the second piece
of `Blowup c'`. -/
theorem chartChange_inr {y : modelOpens c} (hy : c.symm (y : BlowupModel n).blowdown ∈ c'.source) :
    chartChange c c' (inr (gluingHomeomorph c) y) =
      inr (gluingHomeomorph c')
        ⟨liftMap (c.symm.trans c'.toOpenPartialHomeomorph) (c.fderivTransEquiv c') y, by
          rw [mem_modelOpens, blowdown_liftMap, OpenPartialHomeomorph.coe_trans,
            Function.comp_apply]
          exact c'.map_source hy⟩ := by
  rw [coe_chartChange, chartChangeMap_of_mem (by rwa [blowdown_inr])]
  congr 2
  exact liftChart_inr c c' hy

/-- On the exceptional divisor, the change of chart acts on lines by the derivative at `0` of
`c' ∘ c⁻¹`. -/
@[simp]
theorem chartChange_ofDirection (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    chartChange c c' (ofDirection c ℓ) =
      ofDirection c' ((c.fderivTransEquiv c').mapProjectivization ℓ) := by
  rw [coe_chartChange, chartChangeMap_ofDirection]

/-- On the exceptional divisor, read as the lines of the tangent space of `M` at the centre
through `directionEquiv`, the change of chart does not depend on the charts: it sends the point
over a line `ℓ` of `T_{p₀}M` in `Blowup c` to the point over `ℓ` in `Blowup c'`. -/
theorem chartChange_ofDirection_directionEquiv
    (ℓ : ℙ ℂ (TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) p₀)) :
    chartChange c c' (ofDirection c (directionEquiv c ℓ)) =
      ofDirection c' (directionEquiv c' ℓ) := by
  simp

/-- **The cocycle condition**, applied to a point: the change of chart from `c` to `c'` followed
by the change of chart from `c'` to `c''` is the change of chart from `c` to `c''`. -/
@[simp]
theorem chartChange_chartChange (z : Blowup c) :
    chartChange c' c'' (chartChange c c' z) = chartChange c c'' z := by
  rw [coe_chartChange, coe_chartChange, coe_chartChange, chartChangeMap_chartChangeMap]

/-- **The cocycle condition.** The change of chart from `c` to `c'` followed by the change of
chart from `c'` to `c''` is the change of chart from `c` to `c''`. -/
@[simp]
theorem chartChange_trans :
    (chartChange c c').trans (chartChange c' c'') = chartChange c c'' :=
  Diffeomorph.ext fun z ↦ by
    rw [Diffeomorph.coe_trans, Function.comp_apply, chartChange_chartChange]

end Blowup

end SymplecticGeometry

end
