/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.MFDeriv.Constancy
public import SymplecticGeometry.Geometry.Symplectic.JHolomorphic.Energy.Density
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.TopForm
public import SymplecticGeometry.Geometry.Symplectic.Manifold.Energy.Surface

/-!
# The energy of a map from a surface, read through an area form

Let `(C, j)` be an oriented almost complex surface, `M` a manifold with a two-form `ω` (`form` in
the code) and an almost complex structure `J`, and `u : C → M`. Tau Ceti's energy
`TauCeti.SmoothTwoForm.energy` of `u` is the integral of its energy form
`TauCeti.SmoothTwoForm.energyForm`, which involves no area form on `C`. This file compares it with
the classical energy `½ ∫_C |du|² dvol` taken with an area form `dvol` that tames `j`, where
`|du|²` is `TauCeti.SmoothTwoForm.normSq` for the metrics `dvol (·, j ·)` and `ω (·, J ·)`, and
derives the integrated energy identity.

## Main results

* `TauCeti.SmoothTwoForm.energyForm_apply_eq_energyDensity`: on a surface, Tau Ceti's energy form
  at `c` is the energy density `TauCeti.SmoothTwoForm.energyDensity` of `du_c`. Both are top
  forms on the tangent plane that agree on a frame `(e, j e)`.
* `TauCeti.SmoothTwoForm.energy_eq_half_integralTopForm_normSq`: for every area form `dvol`
  taming `j`, the energy is `½ ∫_C |du|² dvol`. The left side involves no area form, so the
  classical energy does not depend on `dvol`.
* `TauCeti.SmoothTwoForm.Invariant.energy_eq_integralTopForm_add`: for `J`-invariant `ω` and a
  `C¹` map from a compact surface, the energy is `∫_C |∂̄_J u|² dvol + ∫_C u^* ω`, where
  `∂̄_J u = ½ (du + J ∘ du ∘ j)` is Tau Ceti's `complexAntilinearPart`.
* `TauCeti.SmoothTwoForm.Tames.energy_eq_zero_iff_isLocallyConstant`: under tameness, a `C¹` map
  from a compact surface, oriented so that the frames `(e, j e)` are positive, has zero energy
  exactly when it is locally constant.
* `TauCeti.SmoothTwoForm.Compatible.energy_identity`: for a compatible pair, the integrated
  identity with its left side written as `½ ∫_C |du|² dvol`, the case of pseudoholomorphic maps,
  and the independence of the area form.

The energy is integrated against the orientation `o`, which the statements take freely. It is the
classical energy only when `o` makes the frames `(e, j e)` positive; under the opposite
orientation every integral here changes sign, and the identities still hold.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §4.5,
  equation (4.5.4) and the paragraph after it.
* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  §2.2.
* [C. Wendl, *Lectures on Holomorphic Curves in Symplectic and Contact Geometry*][Wendl2010],
  equation (2.6), Definition 2.18 and Proposition 2.19.
-/

public section

open Module
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' H' C : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace C]
  [ChartedSpace H' C] [IsManifold I' ∞ C]
  {form : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
  {j : SmoothAlmostComplexStructure I' C} {u : C → M}

omit [IsManifold I' ∞ C] in
/-- On a surface, a tangent plane has a nonzero vector. -/
private theorem exists_tangent_ne_zero (h2 : finrank ℝ E' = 2) (c : C) :
    ∃ e : TangentSpace I' c, e ≠ 0 :=
  (finrank_pos_iff_exists_ne_zero (R := ℝ) (M := TangentSpace I' c)).1
    (by rw [TauCeti.finrank_tangentSpace, h2]; norm_num)

/-- A two-form that tames an almost complex structure does not vanish at a point whose tangent
space is nonzero. -/
theorem Tames.val_ne_zero (h : form.Tames J) {x : M} {v : TangentSpace I x} (hv : v ≠ 0) :
    form.val x ≠ 0 := fun h0 ↦ by
  have hpos := tames_iff.mp h x v hv
  rw [SmoothBundleForm.eval₂_apply, h0] at hpos
  exact hpos.false

/-- On a surface, Tau Ceti's energy form of `u` at `c` is the energy density `ε_{du_c}` of the
differential of `u` at `c`. -/
theorem energyForm_apply_eq_energyDensity (h2 : finrank ℝ E' = 2) (c : C) :
    form.energyForm J j u c = form.energyDensity J j (mfderiv I' I u c).toLinearMap := by
  obtain ⟨e, he⟩ := exists_tangent_ne_zero (I' := I') h2 c
  refine j.topForm_ext h2 he ?_
  rw [energyForm_apply_frame_eq_stdComplexLineEnergyDensity,
    energyDensity_apply_complexFrame_eq_stdComplexLineEnergyDensity]

/-- On a surface, if `dvol` tames `j`, then `|du_c|² dvol_c` is twice the energy form of `u`
at `c`. -/
theorem normSq_smul_eq_two_smul_energyForm (h2 : finrank ℝ E' = 2) {dvol : SmoothTwoForm I' C}
    (hdvol : dvol.Tames j) (c : C) :
    form.normSq J j dvol (mfderiv I' I u c).toLinearMap • dvol.val c =
      (2 : ℝ) • form.energyForm J j u c := by
  obtain ⟨e, he⟩ := exists_tangent_ne_zero (I' := I') h2 c
  rw [normSq_smul_eq_two_smul_energyDensity form J j h2 (hdvol.val_ne_zero he),
    energyForm_apply_eq_energyDensity h2]

variable {o : Manifold.Orientation I' C (Fin 2)}

/-- **The energy does not depend on the area form.** For every area form `dvol` taming `j`, the
energy of `u` is `½ ∫_C |du|² dvol`, with `|du|²` the squared norm for the metrics `dvol (·, j ·)`
and `form (·, J ·)`. -/
theorem energy_eq_half_integralTopForm_normSq {dvol : SmoothTwoForm I' C} (hdvol : dvol.Tames j) :
    form.energy J j o u = 1 / 2 * integralTopForm o
      (fun c ↦ form.normSq J j dvol (mfderiv I' I u c).toLinearMap • dvol.val c) := by
  have h2 : finrank ℝ E' = 2 := by simpa using o.card_eq.symm
  rw [show (fun c ↦ form.normSq J j dvol (mfderiv I' I u c).toLinearMap • dvol.val c) =
      (2 : ℝ) • form.energyForm J j u from
      funext (normSq_smul_eq_two_smul_energyForm h2 hdvol),
    integralTopForm_smul, energy_def]
  ring

/-- For a `J`-invariant `form` and an area form `dvol` taming `j`, `|∂̄_J u|² dvol` is the
energy form of `u` minus `u^* form`, at each point of a surface. -/
private theorem Invariant.normSq_complexAntilinearPart_smul_eq (hinv : form.Invariant J)
    (h2 : finrank ℝ E' = 2) {dvol : SmoothTwoForm I' C} (hdvol : dvol.Tames j) (c : C) :
    form.normSq J j dvol (complexAntilinearPart
        (j.toEndomorphism c : TangentSpace I' c →ₗ[ℝ] TangentSpace I' c)
        (J.toEndomorphism (u c) : TangentSpace I (u c) →ₗ[ℝ] TangentSpace I (u c))
        (mfderiv I' I u c).toLinearMap) • dvol.val c =
      (form.energyForm J j u + -mpullback I' I u form.val) c := by
  obtain ⟨e, he⟩ := exists_tangent_ne_zero (I' := I') h2 c
  rw [normSq_smul_eq_two_smul_energyDensity form J j h2 (hdvol.val_ne_zero he), Pi.add_apply,
    Pi.neg_apply, energyForm_apply_eq_energyDensity h2,
    hinv.energyDensity_eq_two_smul_add j h2 (mfderiv I' I u c)]
  ext v
  simp [mpullback_apply, Function.comp_def]

/-- **The integrated energy identity.** For a `J`-invariant `form`, an area form `dvol` taming `j`
and a `C¹` map `u` from a compact surface, the energy of `u` is `∫_C |∂̄_J u|² dvol + ∫_C u^* form`,
with `∂̄_J u = ½ (du + J ∘ du ∘ j)` and `|·|²` the squared norm for the metrics `dvol (·, j ·)`
and `form (·, J ·)`. -/
theorem Invariant.energy_eq_integralTopForm_add [CompactSpace C] (hinv : form.Invariant J)
    {dvol : SmoothTwoForm I' C} (hdvol : dvol.Tames j) (hu : ContMDiff I' I 1 u) :
    form.energy J j o u = integralTopForm o (fun c ↦ form.normSq J j dvol (complexAntilinearPart
        (j.toEndomorphism c : TangentSpace I' c →ₗ[ℝ] TangentSpace I' c)
        (J.toEndomorphism (u c) : TangentSpace I (u c) →ₗ[ℝ] TangentSpace I (u c))
        (mfderiv I' I u c).toLinearMap) • dvol.val c) +
      integralTopForm o (mpullback I' I u form.val) := by
  have h2 : finrank ℝ E' = 2 := by simpa using o.card_eq.symm
  have hpb : IsSmoothForm I' 0 (mpullback I' I u form.val) :=
    ((SmoothForm.isSmoothForm form).of_le (by simp)).mpullback (by simpa using hu)
  rw [funext (hinv.normSq_complexAntilinearPart_smul_eq h2 hdvol),
    ← integralTopForm_add_of_compactSpace o ((isSmoothForm_energyForm hu).add hpb.neg) hpb,
    neg_add_cancel_right, energy_def]

/-- **Zero energy.** Under tameness, a `C¹` map from a compact surface, oriented so that the
frames `(e, j e)` are positive, has zero energy exactly when it is locally constant. -/
theorem Tames.energy_eq_zero_iff_isLocallyConstant [CompactSpace C] (htame : form.Tames J)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hu : ContMDiff I' I 1 u) :
    form.energy J j o u = 0 ↔ IsLocallyConstant u := by
  rw [htame.energy_eq_zero_iff ho hu]
  exact ⟨(hu.mdifferentiable one_ne_zero).isLocallyConstant_of_mfderiv_eq_zero,
    IsLocallyConstant.mfderiv_eq_zero⟩

/-- **The energy identity for maps from a closed surface.** Let `form` be compatible with `J`,
`dvol` an area form taming `j`, and `u` a `C¹` map from a compact surface. Write
`E(u) = ½ ∫_C |du|² dvol`, with `|·|²` the squared norm for the metrics `dvol (·, j ·)` and
`form (·, J ·)`. Then
* `E(u) = ∫_C |∂̄_J u|² dvol + ∫_C u^* form`, with `∂̄_J u = ½ (du + J ∘ du ∘ j)`;
* if `u` is pseudoholomorphic, `E(u) = ∫_C u^* form`;
* `E(u)` is the same for every area form taming `j`.

All integrals are taken against the orientation `o`. When `o` makes the frames `(e, j e)`
positive, `E(u)` is the energy of `u`; for the opposite
orientation every integral, and so each statement, changes sign. -/
theorem Compatible.energy_identity [CompactSpace C] (hc : form.Compatible J)
    {dvol : SmoothTwoForm I' C} (hdvol : dvol.Tames j) (hu : ContMDiff I' I 1 u) :
    (1 / 2 * integralTopForm o
        (fun c ↦ form.normSq J j dvol (mfderiv I' I u c).toLinearMap • dvol.val c) =
      integralTopForm o (fun c ↦ form.normSq J j dvol (complexAntilinearPart
          (j.toEndomorphism c : TangentSpace I' c →ₗ[ℝ] TangentSpace I' c)
          (J.toEndomorphism (u c) : TangentSpace I (u c) →ₗ[ℝ] TangentSpace I (u c))
          (mfderiv I' I u c).toLinearMap) • dvol.val c) +
        integralTopForm o (mpullback I' I u form.val)) ∧
    ((∀ c, IsPseudoholomorphicAt j J u c) →
      1 / 2 * integralTopForm o
          (fun c ↦ form.normSq J j dvol (mfderiv I' I u c).toLinearMap • dvol.val c) =
        integralTopForm o (mpullback I' I u form.val)) ∧
    ∀ dvol' : SmoothTwoForm I' C, dvol'.Tames j →
      1 / 2 * integralTopForm o
          (fun c ↦ form.normSq J j dvol' (mfderiv I' I u c).toLinearMap • dvol'.val c) =
        1 / 2 * integralTopForm o
          (fun c ↦ form.normSq J j dvol (mfderiv I' I u c).toLinearMap • dvol.val c) := by
  rw [← energy_eq_half_integralTopForm_normSq hdvol]
  exact ⟨hc.invariant.energy_eq_integralTopForm_add hdvol hu, energy_eq_integralTopForm_mpullback,
    fun dvol' hdvol' ↦ (energy_eq_half_integralTopForm_normSq hdvol').symm⟩

end SmoothTwoForm

end TauCeti
