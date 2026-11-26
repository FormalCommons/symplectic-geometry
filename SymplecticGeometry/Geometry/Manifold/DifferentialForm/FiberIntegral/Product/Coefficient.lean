/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.Basic
public import TauCeti.Geometry.Manifold.Riemannian.HodgeStar
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence

/-!
# Smooth families of top forms and their integrals

Let `F` be a manifold of dimension `m` with an orientation `o`, and let `β p` be a top form on
`F` for each point `p` of a parameter manifold `P`, depending `C^n` on `(p, y) ∈ P × F` as a
section of the bundle of `m`-forms of `F` along the projection `(p, y) ↦ y` (the form in which
Tau Ceti's `TauCeti.contMDiff_mpullback_prodMk_form` gives the slices of a form on a product).

* `TauCeti.RoughForm.exists_contMDiff_eq_smul_riemannianVolumeForm`: for a `C^n` Riemannian
  metric on `F`, the family is `β p y = c (p, y) • ν y` for a `C^n` function `c` on `P × F`,
  where `ν` is the Riemannian volume form of `o`. The coefficient is the Hodge star
  `c (p, ·) = ⋆(β p)`, and its smoothness comes from that of the fibrewise Hodge star
  (`TauCeti.contMDiff_formHodgeStar_totalSpace`); the identity `β p = ⋆⋆(β p)` and
  `⋆f = f ν` (`TauCeti.RoughForm.hodgeStar_ofFunction`) give the equation. This is the family
  version of `TauCeti.SmoothForm.exists_eq_funSMulₗ_hodgeStar_ofFunction_one`.
* `TauCeti.contMDiff_integralTopForm`: if `F` is compact and Hausdorff, the integrals
  `p ↦ ∫_F β p` are `C^n`. With a smooth metric from
  `TauCeti.nonempty_contMDiffRiemannianMetric`, the integral of `β p` is the integral of
  `c (p, ·)` against the Riemannian measure (`TauCeti.integralTopForm_smul_riemannianVolumeForm`),
  which is `C^n` in `p` by `ContMDiff.parametric_integral`.

These give the smoothness in the base of the fibre integral on a product `B × F`, as in Bott–Tu,
§6, where the integrand is written as a function times a fixed volume form on the fibre.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6 (integration
  along the fibre).
-/

public section

noncomputable section

open Bundle MeasureTheory
open scoped ContDiff Manifold

namespace TauCeti

variable {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {K : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [TopologicalSpace F] [ChartedSpace H F]
  {m : ℕ} {n : ℕ∞}

/-- **A smooth family of top forms is a smooth function times the volume form.** On an oriented
manifold `F` of dimension `m` with a `C^n` Riemannian metric, let `β p` be an `m`-form on `F`
for each `p : P`, such that `(p, y) ↦ β p y` is a `C^n` section of the bundle of `m`-forms along
`(p, y) ↦ y`. Then `β p y = c (p, y) • ν y` for a `C^n` function `c` on `P × F`, where `ν` is the
Riemannian volume form of the orientation. -/
theorem RoughForm.exists_contMDiff_eq_smul_riemannianVolumeForm {n : WithTop ℕ∞}
    [IsManifold J 1 F] [IsManifold J (n + 1) F] [RiemannianBundle (fun y : F ↦ TangentSpace J y)]
    [IsContMDiffRiemannianBundle J n E (fun y : F ↦ TangentSpace J y)]
    (o : Manifold.Orientation J F (Fin m)) {β : P → RoughForm J F ℝ m}
    (hβ : ContMDiff (K.prod J) (J.prod 𝓘(ℝ, E [⋀^Fin m]→L[ℝ] ℝ)) n
      (fun q : P × F ↦ TotalSpace.mk' (E [⋀^Fin m]→L[ℝ] ℝ)
        (E := fun y : F ↦ TangentSpace J y [⋀^Fin m]→L[ℝ] Trivial F ℝ y) q.2 (β q.1 q.2))) :
    ∃ c : P × F → ℝ, ContMDiff (K.prod J) 𝓘(ℝ) n c ∧
      ∀ p y, β p y = c (p, y) • riemannianVolumeForm o y := by
  refine ⟨fun q ↦ RoughForm.hodgeStar o (Nat.add_zero m) (β q.1) q.2 0, ?_, fun p y ↦ ?_⟩
  · have h := (contMDiff_formHodgeStar_totalSpace (n := n) o (Nat.add_zero m)).comp hβ
    intro q
    have h2 := ContMDiffAt.continuousAlternatingMap_bundle_apply (v := fun i : Fin 0 ↦ i.elim0)
      (F₁ := E) (E₁ := fun y : F ↦ TangentSpace J y) (F₂ := ℝ) (E₂ := Trivial F ℝ) (h q)
      (fun i ↦ i.elim0)
    have h3 := (contMDiffAt_totalSpace_iff.1 h2).2
    simp only [Trivial.eq_trivialization F ℝ, Trivial.trivialization_apply] at h3
    convert h3 using 2 with q'
    rw [RoughForm.hodgeStar_apply, formHodgeStarCLM_apply]
    exact congrArg _ (Subsingleton.elim _ _)
  · have h1 := RoughForm.hodgeStar_hodgeStar o (Nat.add_zero m) (Nat.zero_add m) (β p)
    rw [mul_zero, pow_zero, one_smul, RoughForm.eq_ofFunction (RoughForm.hodgeStar o _ (β p)),
      RoughForm.hodgeStar_ofFunction] at h1
    exact (congrFun h1 y).symm

/-- **Integrals of a smooth family of top forms depend smoothly on the parameter.** On a
compact Hausdorff manifold `F` of dimension `m` with an orientation `o`, let `β p` be an
`m`-form for each `p` in a boundaryless manifold `P`, such that `(p, y) ↦ β p y` is a `C^n`
section of the bundle of `m`-forms along `(p, y) ↦ y`. Then `p ↦ ∫_F β p` is `C^n`. -/
theorem contMDiff_integralTopForm [IsManifold J ∞ F] [T2Space F] [CompactSpace F]
    [K.Boundaryless] [IsManifold K n P]
    (o : Manifold.Orientation J F (Fin m)) {β : P → RoughForm J F ℝ m}
    (hβ : ContMDiff (K.prod J) (J.prod 𝓘(ℝ, E [⋀^Fin m]→L[ℝ] ℝ)) n
      (fun q : P × F ↦ TotalSpace.mk' (E [⋀^Fin m]→L[ℝ] ℝ)
        (E := fun y : F ↦ TangentSpace J y [⋀^Fin m]→L[ℝ] Trivial F ℝ y) q.2 (β q.1 q.2))) :
    ContMDiff K 𝓘(ℝ) n fun p ↦ integralTopForm o (β p) := by
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := J) (n := ⊤) (F := E)
    (E := fun y : F ↦ TangentSpace J y)
  let : RiemannianBundle (fun y : F ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E (fun y : F ↦ TangentSpace J y) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := J) (n := ∞)
  have : IsContMDiffRiemannianBundle J n E (fun y : F ↦ TangentSpace J y) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by exact_mod_cast le_top)
  obtain ⟨c, hc, hβc⟩ := RoughForm.exists_contMDiff_eq_smul_riemannianVolumeForm o hβ
  have heq (p : P) : integralTopForm o (β p) = ∫ y, c (p, y) ∂riemannianVolume J F := by
    rw [show β p = fun y ↦ c (p, y) • riemannianVolumeForm o y from funext (hβc p)]
    exact integralTopForm_smul_riemannianVolumeForm o
      (hc.continuous.comp (Continuous.prodMk_right p)) (HasCompactSupport.of_compactSpace _)
  simp only [heq]
  exact ContMDiff.parametric_integral (J := J) hc

end TauCeti

end
