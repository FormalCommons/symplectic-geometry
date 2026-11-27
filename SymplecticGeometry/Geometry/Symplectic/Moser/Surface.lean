/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Orientation.PositiveForm
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import Mathlib.Geometry.Manifold.Instances.Icc
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import SymplecticGeometry.Geometry.Symplectic.Moser.Stability
import TauCeti.Geometry.Symplectic.Manifold.Surface
import SymplecticGeometry.Geometry.Manifold.DeRham.Integration.Bijective

/-!
# Moser's theorem for area forms on closed surfaces

Let `M` be a closed connected surface with an orientation `o`, and let `ω₀` and `σ` be smooth
two-forms on `M` that are positive for `o`: both take positive values on every positively oriented
tangent basis. If `∫_M σ = ∫_M ω₀`, then there is a diffeotopy `Ψ` of `M`, which starts at the
identity, with `Ψ_1^* σ = ω₀`
(`TauCeti.SmoothTwoForm.exists_diffeotopy_mpullback_eq_of_integralTopForm_eq`). In particular
its time-one map `ψ = Ψ_1` is a diffeomorphism of `M` with `ψ^* σ = ω₀`
(`TauCeti.SmoothTwoForm.exists_diffeomorph_mpullback_eq_of_integralTopForm_eq`).

The proof is Moser's argument along the segment `σ_t = ω₀ + t (σ - ω₀)`, `t ∈ [0, 1]`.

1. Every `σ_t` takes the value `(1 - t) ω₀(b) + t σ(b) > 0` on a positively oriented basis `b`,
   so it vanishes nowhere, and on a surface a nowhere-vanishing two-form is symplectic
   (`TauCeti.SmoothTwoForm.isSymplectic_iff_forall_ne_zero_of_finrank_eq_two`).
2. Since `σ` and `ω₀` have the same integral, `σ - ω₀` is exact on the connected closed surface
   (`TauCeti.sub_mem_exactForms_iff_integralTopForm_eq`); hence so is
   `σ_t - σ_0 = t (σ - ω₀)`.
3. The slices `σ_t` form a smooth family over `[0, 1]`, so Moser stability
   (`TauCeti.SmoothTwoForm.exists_diffeotopy_mpullback_eq`) gives a diffeotopy `Ψ` with
   `Ψ_t^* σ_t = ω₀`; its slice at `t = 1` is `ψ`.

## Main results

* `TauCeti.SmoothTwoForm.exists_diffeotopy_mpullback_eq_of_integralTopForm_eq`: two area forms of
  equal integral, positive for the same orientation of a closed connected surface, are related by
  the time-one map of a diffeotopy.
* `TauCeti.SmoothTwoForm.exists_diffeomorph_mpullback_eq_of_integralTopForm_eq`: the same, with
  only the diffeomorphism.

## References

* J. Moser, *On the volume elements on a manifold*, Transactions of the American Mathematical
  Society 120 (1965), 286–294.
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.2.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

open SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

/-- **Moser's theorem for area forms.** Let `M` be a closed surface, connected or empty, with an
orientation `o`, and let `ω₀` and `σ` be smooth two-forms on `M`, both positive on every
positively oriented tangent basis. If `σ` and `ω₀` have the same integral over `M`, then there is a
diffeotopy `Ψ` of `M`, which starts at the identity, whose time-one map `Ψ.final` pulls `σ` back
to `ω₀`. -/
theorem exists_diffeotopy_mpullback_eq_of_integralTopForm_eq [PreconnectedSpace M]
    (o : Manifold.Orientation I M (Fin 2)) {ω₀ σ : SmoothTwoForm I M}
    (hω : o.IsPositive ω₀.val) (hσ : o.IsPositive σ.val)
    (hint : integralTopForm o σ.val = integralTopForm o ω₀.val) :
    ∃ Ψ : Diffeotopy I ∞ M, SmoothForm.mpullback Ψ.final Ψ.final.contMDiff σ = ω₀ := by
  have hE : Module.finrank ℝ E = 2 := by simpa using o.card_eq.symm
  -- The segment from `ω₀` to `σ`.
  set α : unitInterval → SmoothTwoForm I M := fun t ↦ ω₀ + (t : ℝ) • (σ - ω₀) with hα
  -- Step 1: every form of the segment is symplectic.
  have hsymp (t : unitInterval) : IsSymplectic (α t) := by
    refine (isSymplectic_iff_forall_ne_zero_of_finrank_eq_two hE).2 fun x h0 ↦ ?_
    -- `TangentSpace I x` is the model space `E` by definition
    have hx : Module.finrank ℝ (TangentSpace I x) = 2 := hE
    let b := (Module.finBasisOfFinrankEq ℝ (TangentSpace I x) hx).adjustToOrientation
      (o.orientationAt x)
    have hb : b.orientation = o.orientationAt x := Module.Basis.orientation_adjustToOrientation _ _
    have hval : (α t).val x b = ω₀.val x b + (t : ℝ) * (σ.val x b - ω₀.val x b) := by
      simp [hα]
    rw [h0, ContinuousAlternatingMap.coe_zero, Pi.zero_apply] at hval
    have hωb := hω.apply_pos hb
    have hσb := hσ.apply_pos hb
    nlinarith [mul_nonneg (unitInterval.nonneg t) hσb.le,
      mul_nonneg (unitInterval.one_sub_nonneg t) hωb.le]
  -- Step 2: `σ` and `ω₀` have the same integral, so `σ - ω₀` is exact.
  have hexact : σ - ω₀ ∈ exactForms I M 2 := (sub_mem_exactForms_iff_integralTopForm_eq o).2 hint
  -- Step 3: Moser stability along the segment.
  obtain ⟨Ω, hΩ⟩ := isSmoothFamily_def.mp <| (isSmoothFamily_const (J := 𝓡∂ 1) ω₀).add
    ((isSmoothFamily_const (σ - ω₀)).fun_smul (contMDiff_subtypeVal_Icc (x := 0) (y := 1)))
  have hΩα (t : unitInterval) :
      SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) Ω = α t := hΩ t
  obtain ⟨Ψ, hΨ⟩ := exists_diffeotopy_mpullback_eq Ω (fun t ↦ by rw [hΩα]; exact hsymp t)
    fun t ↦ by
      rw [hΩα, hΩα, hα]
      simpa using Submodule.smul_mem _ (t : ℝ) hexact
  refine ⟨Ψ, ?_⟩
  rw [Diffeotopy.final_def]
  simpa [hΩα, hα] using hΨ 1

/-- **Moser's theorem for area forms**, as a diffeomorphism. Let `M` be a closed surface, connected
or empty, with an orientation `o`, and let `ω₀` and `σ` be smooth two-forms on `M`, both positive
on every positively oriented tangent basis. If `σ` and `ω₀` have the same integral over `M`, then
there is a diffeomorphism `ψ` of `M` with `ψ^* σ = ω₀`. -/
theorem exists_diffeomorph_mpullback_eq_of_integralTopForm_eq [PreconnectedSpace M]
    (o : Manifold.Orientation I M (Fin 2)) {ω₀ σ : SmoothTwoForm I M}
    (hω : o.IsPositive ω₀.val) (hσ : o.IsPositive σ.val)
    (hint : integralTopForm o σ.val = integralTopForm o ω₀.val) :
    ∃ ψ : M ≃ₘ⟮I, I⟯ M, SmoothForm.mpullback ψ ψ.contMDiff σ = ω₀ :=
  let ⟨Ψ, hΨ⟩ := exists_diffeotopy_mpullback_eq_of_integralTopForm_eq o hω hσ hint
  ⟨Ψ.final, hΨ⟩

end TauCeti.SmoothTwoForm

end
