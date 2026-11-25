/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Submersion.ParallelTransport.Basic
import Mathlib.Topology.Connected.Clopen

/-!
# Parallel transport as a flow and as a diffeomorphism

Let `D` be a `C^n` Ehresmann connection, `1 ≤ n`, on a proper `C^(n+1)` map `f : P → B` of
finite-dimensional boundaryless Hausdorff manifolds, and `γ` a `C^(n+1)` curve in `B`.

If a jointly `C^n` time-dependent vector field `V` on `B`, vanishing outside a compact set, has
the velocity of `γ` as its value along `γ` at the times between `s` and `t`, then parallel
transport along `γ` from `s` to `t` is, on the fibre over `γ s`, the time-dependent flow of the
horizontal lift of `V` from `s` to `t`
(`TauCeti.IsEhresmannConnection.parallelTransport_eq_timeDependentFlowOf`): the trajectories of
that flow are horizontal lifts of `γ`
(`TauCeti.IsEhresmannConnection.isHorizontalMap_timeDependentFlowOf_horizontalLiftField`), and
transport follows every such lift (`TauCeti.IsEhresmannConnection.parallelTransport_eq`).

Such a field exists for times in a closed interval that `γ` maps into the base set of one
trivialization of the tangent bundle of `B`
(`Bundle.Trivialization.exists_timeDependentField_eq_curveVelocity`), and its flow is then a
`C^n` diffeomorphism of `P` (Tau Ceti's `TauCeti.timeDependentFlowDiffeomorph`). Transport from
`s` to `t` is the composition of the transports over the pieces of a subdivision of the interval
between them (`TauCeti.IsEhresmannConnection.parallelTransport_parallelTransport`), so it is the
restriction to the fibre over `γ s` of a composition of such diffeomorphisms
(`TauCeti.IsEhresmannConnection.exists_diffeomorph_eqOn_parallelTransport`). Rather than choosing
the subdivision, the proof applies Mathlib's `PreconnectedSpace.induction₂'` to the relation
between two times that some diffeomorphism of `P` agrees with transport between them on the
fibre: it is transitive, and holds between nearby times.

## Main results

* `TauCeti.IsEhresmannConnection.parallelTransport_eq_timeDependentFlowOf`: transport along `γ`
  is the time-dependent flow of the horizontal lift of a field through the velocities of `γ`.
* `TauCeti.IsEhresmannConnection.exists_diffeomorph_eqOn_parallelTransport`: transport from the
  fibre over `γ s` onto the fibre over `γ t` is the restriction of a `C^n` diffeomorphism of `P`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.3.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §9.
-/

public section

noncomputable section

open Function Bundle Set Filter TauCeti.Manifold
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace IsEhresmannConnection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P] [I.Boundaryless]
  [T2Space P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {B : Type*} [TopologicalSpace B] [ChartedSpace G B] [IsManifold J ∞ B] [J.Boundaryless]
  [T2Space B]
  {n : ℕ∞} {f : P → B} {D : Π x : P, Submodule ℝ (TangentSpace I x)}
  (hD : IsEhresmannConnection I J n f D)

/-- **Parallel transport is the flow of a lifted field.** Let `D` be a `C^n` Ehresmann
connection, `1 ≤ n`, on a proper `C^(n+1)` map `f : P → B`, `γ` a `C^(n+1)` curve in `B`, and `V`
a jointly `C^n` time-dependent vector field on `B` that vanishes outside a compact set and whose
value at `γ u` at time `u` is the velocity of `γ` at `u`, for every `u ∈ Set.uIcc s t`. On the
fibre over `γ s`, parallel transport along `γ` from `s` to `t` is the time-dependent flow from `s`
to `t` of the horizontal lift of `V`. -/
theorem parallelTransport_eq_timeDependentFlowOf (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f)
    (hfp : IsProperMap f) {γ : ℝ → B} (hγ : ContMDiff 𝓘(ℝ, ℝ) J (n + 1) γ)
    {V : ℝ → Π y : B, TangentSpace J y}
    (hV : ContMDiff (𝓘(ℝ, ℝ).prod J) J.tangent n
      (fun p : ℝ × B ↦ (⟨p.2, V p.1 p.2⟩ : TangentBundle J B)))
    {K : Set B} (hK : IsCompact K) (hV0 : ∀ u, ∀ y ∉ K, V u y = 0) {s t : ℝ}
    (hVγ : ∀ u ∈ uIcc s t, V u (γ u) = curveVelocity J γ u) :
    EqOn (hD.parallelTransport γ s t)
      (timeDependentFlowOf (fun u ↦ hD.horizontalLiftField (V u)) s t) (f ⁻¹' {γ s}) := by
  intro x hx
  rw [mem_preimage, mem_singleton_iff] at hx
  have hn' : (1 : ℕ∞ω) ≤ n := mod_cast hn
  have h2 : (2 : ℕ∞ω) ≤ n + 1 := by
    simpa [one_add_one_eq_two] using add_le_add_left hn' 1
  obtain ⟨hc, hh, hγc⟩ := hD.isHorizontalMap_timeDependentFlowOf_horizontalLiftField hn hf hfp
    (hγ.mdifferentiable (by simp)) hV hK hV0 isPreconnected_uIcc hVγ left_mem_uIcc hx
  exact hD.parallelTransport_eq hn' (hf.of_le h2) (hγ.of_le h2)
    (hc.mdifferentiable (zero_lt_one.trans_le hn').ne') hh hγc (timeDependentFlowOf_self _ s x)

include hD in
/-- The local step of `TauCeti.IsEhresmannConnection.exists_diffeomorph_eqOn_parallelTransport`:
between two times of a closed interval that `γ` maps into the base set of one trivialization of
the tangent bundle of `B`, transport is the restriction of the flow of a cut-off lifted field. -/
private theorem exists_diffeomorph_eqOn_parallelTransport_of_mapsTo_baseSet (hn : 1 ≤ n)
    (hf : ContMDiff I J (n + 1) f) (hfp : IsProperMap f) {γ : ℝ → B}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) J (n + 1) γ) {a b : ℝ}
    (e : Trivialization F (π F (TangentSpace J))) [MemTrivializationAtlas e]
    (hγe : MapsTo γ (Icc a b) e.baseSet) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ∃ Ψ : P ≃ₘ^n⟮I, I⟯ P, EqOn Ψ (hD.parallelTransport γ s t) (f ⁻¹' {γ s}) := by
  have : IsManifold I n P := .of_le (n := ∞) (by exact_mod_cast le_top)
  obtain ⟨V, K, hK, hV, hV0, hVγ⟩ := e.exists_timeDependentField_eq_curveVelocity hγ hγe
  refine ⟨timeDependentFlowDiffeomorph
    (hD.isCompleteVectorField_timeDependentSuspensionField_horizontalLiftField hn hf hfp hV hK hV0)
    hn (hD.contMDiff_horizontalLiftField_timeDependent hf hV) s t, fun x hx ↦ ?_⟩
  rw [timeDependentFlowDiffeomorph_apply]
  exact (hD.parallelTransport_eq_timeDependentFlowOf hn hf hfp hγ hV hK hV0
    (fun u hu ↦ hVγ u (uIcc_subset_Icc hs ht hu)) hx).symm

include hD in
/-- **Parallel transport is the restriction of a diffeomorphism.** Let `D` be a `C^n` Ehresmann
connection, `1 ≤ n`, on a proper `C^(n+1)` map `f : P → B` of finite-dimensional boundaryless
Hausdorff manifolds, and `γ` a `C^(n+1)` curve in `B`. There is a `C^n` diffeomorphism `Ψ` of
`P` that agrees with parallel transport along `γ` from `s` to `t` on the fibre over `γ s` and maps
that fibre onto the fibre over `γ t`. For `n = ∞`, `Ψ` is smooth. -/
theorem exists_diffeomorph_eqOn_parallelTransport (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f)
    (hfp : IsProperMap f) {γ : ℝ → B} (hγ : ContMDiff 𝓘(ℝ, ℝ) J (n + 1) γ) (s t : ℝ) :
    ∃ Ψ : P ≃ₘ^n⟮I, I⟯ P, EqOn Ψ (hD.parallelTransport γ s t) (f ⁻¹' {γ s}) ∧
      Ψ '' (f ⁻¹' {γ s}) = f ⁻¹' {γ t} := by
  -- Times between which some diffeomorphism agrees with transport on the fibre.
  let R : ℝ → ℝ → Prop := fun a b ↦
    ∃ Ψ : P ≃ₘ^n⟮I, I⟯ P, EqOn Ψ (hD.parallelTransport γ a b) (f ⁻¹' {γ a})
  -- The relation is transitive: compose the diffeomorphisms, and transport.
  have htrans : IsTrans ℝ R := ⟨fun a b c ⟨Ψ₁, h₁⟩ ⟨Ψ₂, h₂⟩ ↦ ⟨Ψ₁.trans Ψ₂, fun x hx ↦ by
    rw [Diffeomorph.coe_trans, comp_apply, h₁ hx,
      h₂ (hD.parallelTransport_mem_preimage hn hf hfp hγ hx b),
      hD.parallelTransport_parallelTransport hn hf hfp hγ hx]⟩⟩
  -- It holds between nearby times: near `u`, `γ` stays in the base set of one trivialization.
  have hloc (u : ℝ) : ∀ᶠ v in 𝓝 u, R u v ∧ R v u := by
    let e := trivializationAt F (TangentSpace J) (γ u)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1
      (hγ.continuous.continuousAt.preimage_mem_nhds
        (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (γ u))))
    have hmaps : MapsTo γ (Icc (u - ε / 2) (u + ε / 2)) e.baseSet := fun v hv ↦ hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hv.1, hv.2])
    have hu : u ∈ Icc (u - ε / 2) (u + ε / 2) := ⟨by linarith, by linarith⟩
    filter_upwards [Icc_mem_nhds (by linarith : u - ε / 2 < u) (by linarith : u < u + ε / 2)]
      with v hv
    exact ⟨hD.exists_diffeomorph_eqOn_parallelTransport_of_mapsTo_baseSet hn hf hfp hγ e hmaps
      hu hv, hD.exists_diffeomorph_eqOn_parallelTransport_of_mapsTo_baseSet hn hf hfp hγ e hmaps
      hv hu⟩
  obtain ⟨Ψ, hΨ⟩ := PreconnectedSpace.induction₂' R hloc htrans s t
  exact ⟨Ψ, hΨ, hΨ.image_eq.trans (hD.bijOn_parallelTransport hn hf hfp hγ s t).image_eq⟩

end IsEhresmannConnection

end TauCeti

end
