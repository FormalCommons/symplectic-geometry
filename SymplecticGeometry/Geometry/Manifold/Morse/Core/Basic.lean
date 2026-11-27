/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Flow
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import SymplecticGeometry.Geometry.Manifold.VectorField.ModelChart
import SymplecticGeometry.Topology.Order.Sublevel

/-!
# Pushing a band without critical points down, relative to the sublevel below it

Let `f` be a smooth real function on a boundaryless finite-dimensional manifold `M`, and let the
band `f⁻¹[a, b]` be compact and free of critical points of `f`. For every open set `U` containing
the sublevel `{f ≤ a}`, there is a smooth diffeotopy of `M` that does not move a neighbourhood of
`{f ≤ a}` and whose final diffeomorphism carries `{f ≤ b}` into `U`
(`TauCeti.exists_diffeotopy_mapsTo_of_sublevel_subset`).

The flows of `TauCeti.exists_flow_apply_eq_sub` and `TauCeti.exists_diffeomorph_sublevel` move
points of `{f ≤ a}` too. Here the descending field is multiplied by a smooth function of `f` that
vanishes on `{f ≤ a + ε / 3}` and is `1` on `{f ≥ a + 2 ε / 3}`, where `{f ≤ a + ε} ⊆ U`
(`exists_pos_sublevel_subset_of_isCompact_preimage_Icc`), and the cut-off field is run for the
time `b - a` by `TauCeti.compactlySupportedFlowDiffeotopy`. A point of `{f ≤ b}` whose orbit
stayed above `a + 2 ε / 3` would descend at unit speed all that time, ending below `a`.
The descending field is `TauCeti.exists_vectorField_mvfderiv_eq_neg_one_of_boundaryless`.

## Main declarations

* `TauCeti.exists_diffeotopy_mapsTo_of_sublevel_subset`: the diffeotopy fixed near `{f ≤ a}`
  carrying `{f ≤ b}` into a given open neighbourhood of `{f ≤ a}`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.1.
-/

public section

open Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [I.Boundaryless]
  [IsManifold I ∞ M] {f : M → ℝ} {a b : ℝ}

/-- **Pushing a band without critical points down, fixing a neighbourhood of the sublevel below
it.** Let `f` be smooth, let the band `f⁻¹[a, b]` be compact and contain no critical point of `f`,
and let `U` be an open set containing the sublevel `{f ≤ a}`. Then there is a smooth diffeotopy
`Φ` of `M` that fixes every point of some neighbourhood of `{f ≤ a}` at all times, and whose
final diffeomorphism carries `{f ≤ b}` into `U`. -/
theorem exists_diffeotopy_mapsTo_of_sublevel_subset (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0)
    {U : Set M} (hU : IsOpen U) (hsub : {x | f x ≤ a} ⊆ U) :
    ∃ Φ : Diffeotopy I ∞ M, (∃ V ∈ 𝓝ˢ {x | f x ≤ a}, ∀ t, ∀ x ∈ V, Φ (t, x) = x) ∧
      MapsTo Φ.final {x | f x ≤ b} U := by
  rcases le_or_gt b a with hba | hab
  · -- Without a band, the identity diffeotopy does.
    refine ⟨Diffeotopy.refl I ∞ M, ⟨univ, Filter.univ_mem, fun t x _ ↦ Diffeotopy.refl_apply _⟩,
      fun x hx ↦ ?_⟩
    rw [Diffeotopy.final_apply, Diffeotopy.refl_apply]
    exact hsub ((show f x ≤ b from hx).trans hba)
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  obtain ⟨ε, hε, hεU⟩ :=
    exists_pos_sublevel_subset_of_isCompact_preimage_Icc hf.continuous hab hcompact
      (hU.mem_nhdsSet.2 hsub)
  -- The cutoff `ρ ∘ f` vanishes below `c = a + ε / 3` and is `1` above `d = a + 2 ε / 3`.
  set c := a + ε / 3 with hc
  set d := a + 2 * ε / 3 with hd
  have hcd : c < d := by linarith
  set ρ : ℝ → ℝ := fun s ↦ Real.smoothTransition ((s - c) / (d - c))
  have hρC : ContMDiff I 𝓘(ℝ) ∞ (ρ ∘ f) :=
    (Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const _)).contMDiff.comp hf
  have hρ0 : ∀ s, s ≤ c → ρ s = 0 := fun s hs ↦
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      (by linarith))
  have hρ1 : ∀ s, d ≤ s → ρ s = 1 := fun s hs ↦
    Real.smoothTransition.one_of_one_le ((one_le_div (by linarith)).2 (by linarith))
  obtain ⟨X, hX, hXle, ⟨W, -, hKW, hXW⟩, C, hC, hXC⟩ :=
    exists_vectorField_mvfderiv_eq_neg_one_of_boundaryless hf hcompact
      fun x hx ↦ hreg x hx.1 hx.2
  -- The cut-off field `Y = (ρ ∘ f) • X`.
  set Y : (x : M) → TangentSpace I x := fun x ↦ ρ (f x) • X x with hY
  have hYC : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)) :=
    hρC.smul_section hX
  have hYzero : ∀ x ∉ C, Y x = 0 := fun x hx ↦ by simp [hY, hXC x hx]
  have hdY : ∀ x, mvfderiv I f x (Y x) = ρ (f x) * mvfderiv I f x (X x) := fun x ↦
    (map_smul (mvfderiv I f x) (ρ (f x)) (X x)).trans (smul_eq_mul _ _)
  have hYle : ∀ x, mvfderiv I f x (Y x) ≤ 0 := fun x ↦ by
    rw [hdY]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.smoothTransition.nonneg _) (hXle x)
  have hYW : ∀ x ∈ W ∩ {x | d ≤ f x}, mvfderiv I f x (Y x) = -1 := fun x hx ↦ by
    rw [hdY, hρ1 _ hx.2, hXW x hx.1, one_mul]
  have hY1 : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)) :=
    hYC.of_le (by simp)
  have hcomplete := isCompleteVectorField_of_isCompact_of_eq_zero_off hY1 hC hYzero
  refine ⟨compactlySupportedFlowDiffeotopy (n := ⊤) (by simp) hYC hC hYzero (b - a),
    ⟨{x | f x < c}, (isOpen_lt hf.continuous continuous_const).mem_nhdsSet.2
      fun x hx ↦ (show f x ≤ a from hx).trans_lt (by linarith), fun t x hx ↦ ?_⟩,
    fun x hx ↦ ?_⟩
  · refine compactlySupportedFlowDiffeotopy_apply_of_eq_zero _ hYC hC hYzero _ ?_ t
    simp [hY, hρ0 _ (show f x < c from hx).le]
  -- A point of `{f ≤ b}` whose orbit stayed above `d` would descend at unit speed for the time
  -- `b - a`, ending below `a`.
  rw [Diffeotopy.final_apply, compactlySupportedFlowDiffeotopy_apply, Set.Icc.coe_one, mul_one,
    ← globalFlow_apply hY1 hcomplete]
  set γ : ℝ → M := fun s ↦ globalFlow Y hY1 hcomplete s x
  have hanti : Antitone (f ∘ γ) :=
    (isMIntegralCurve_globalFlow hY1 hcomplete x).antitone_comp
      (fun _ ↦ hf.mdifferentiableAt (by simp)) fun _ ↦ hYle _
  refine hεU (show f (γ (b - a)) ≤ a + ε from ?_)
  by_contra! h
  have hγ0 : γ 0 = x := Flow.map_zero_apply _ x
  have hseg : ∀ w ∈ uIcc 0 (b - a), γ w ∈ W ∩ {x | d ≤ f x} := by
    intro w hw
    rw [uIcc_of_le (by linarith)] at hw
    have h1 : f (γ (b - a)) ≤ f (γ w) := hanti hw.2
    have h2 : f (γ w) ≤ f (γ 0) := hanti hw.1
    rw [hγ0] at h2
    exact ⟨hKW ⟨by linarith, h2.trans hx⟩, show d ≤ f (γ w) by linarith⟩
  have := apply_globalFlow_eq_sub_of_forall_mem hY1 hcomplete hYW hseg
  have hxb : f x ≤ b := hx
  linarith

end TauCeti

end
