/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.HodgeStar
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Opens
import SymplecticGeometry.Geometry.Manifold.ContMDiff.ParametricIntegral
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.Deriv

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
  which is `C^n` in `p` by `ContMDiff.parametric_integral_of_boundarylessManifold`.

When `P` is an open subset `U` of a normed space `EB`, with the model `𝓘(ℝ, EB)`, the derivative
in the parameter passes under the integral. Fix `b ∈ U` and a direction `a ∈ EB`, and write `D y`
for the derivative at `b`, in the direction `a`, of `b' ↦ β b' y`.

* `TauCeti.RoughForm.exists_contMDiffOn_opens_eq_smul_riemannianVolumeForm`: the coefficient
  above, extended by `0` to a function on `EB × F` that is `C^n` on `U × F`
  (`ContMDiff.contMDiffOn_opens_prod_of_eq`).
* `TauCeti.mfderiv_family_apply_eq_fderiv_smul`: if `β b' y = c b' • ν y` for `b' ∈ U` at a fixed
  `y`, with `c` differentiable at `b`, then `D y = (∂c/∂b)(b) a • ν y`. On `U` the derivative of
  a map is that of the same map on `EB` (`TauCeti.Manifold.mfderiv_comp_subtype_val_apply`).
* `TauCeti.isSmoothForm_mfderiv_family_apply`: for a smooth family over an oriented Hausdorff
  σ-compact `F`, `D` is a smooth `m`-form, since the partial derivative of the coefficient is
  smooth in `y` (`ContMDiffAt.fderiv_right`).
* `TauCeti.mdifferentiableAt_integralTopForm` and `TauCeti.mfderiv_integralTopForm_apply`: for
  `F` compact and Hausdorff, `b' ↦ ∫_F β b'` is differentiable at `b`, with derivative `∫_F D` in
  the direction `a`. As in the proof of `TauCeti.contMDiff_integralTopForm`, the integral is that
  of the coefficient against the Riemannian measure, and
  `TauCeti.hasFDerivAt_integral_of_contMDiffOn` differentiates it under the integral sign.

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
    [BoundarylessManifold K P] [IsManifold K n P]
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
  exact ContMDiff.parametric_integral_of_boundarylessManifold (J := J) hc

section Opens

open Set Function TopologicalSpace

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {U : Opens EB}

/-- **The coefficient of a smooth family over an open subset of a normed space.** On an oriented
manifold `F` with a `C^n` Riemannian metric, let `β b` be an `m`-form on `F` for each `b` in an
open subset `U` of a normed space `EB`, such that `(b, y) ↦ β b y` is a `C^n` section of the
bundle of `m`-forms along `(b, y) ↦ y`. Then there is a function `c` on `EB × F`, `C^n` on
`U × F`, with `β b y = c b y • ν y` for all `b ∈ U` and `y ∈ F`, where `ν` is the Riemannian
volume form of the orientation. -/
theorem RoughForm.exists_contMDiffOn_opens_eq_smul_riemannianVolumeForm {n : WithTop ℕ∞}
    [IsManifold J 1 F] [IsManifold J (n + 1) F] [RiemannianBundle (fun y : F ↦ TangentSpace J y)]
    [IsContMDiffRiemannianBundle J n E (fun y : F ↦ TangentSpace J y)]
    (o : Manifold.Orientation J F (Fin m)) {β : U → RoughForm J F ℝ m}
    (hβ : ContMDiff (𝓘(ℝ, EB).prod J) (J.prod 𝓘(ℝ, E [⋀^Fin m]→L[ℝ] ℝ)) n
      (fun q : U × F ↦ TotalSpace.mk' (E [⋀^Fin m]→L[ℝ] ℝ)
        (E := fun y : F ↦ TangentSpace J y [⋀^Fin m]→L[ℝ] Trivial F ℝ y) q.2 (β q.1 q.2))) :
    ∃ c : EB → F → ℝ, ContMDiffOn (𝓘(ℝ, EB).prod J) 𝓘(ℝ) n (uncurry c) (U ×ˢ univ) ∧
      ∀ (b : U) (y : F), β b y = c b y • riemannianVolumeForm o y := by
  obtain ⟨c, hc, hβc⟩ := RoughForm.exists_contMDiff_eq_smul_riemannianVolumeForm o hβ
  classical
  refine ⟨fun z y ↦ if h : z ∈ U then c (⟨z, h⟩, y) else 0,
    hc.contMDiffOn_opens_prod_of_eq fun z hz y ↦ dite_eq_left hz, fun b y ↦ ?_⟩
  exact (hβc b y).trans (congrArg (· • riemannianVolumeForm o y) (by simp))

omit [FiniteDimensional ℝ E] in
/-- **The derivative in the parameter of a family of forms, from its coefficient.** Let `β b` be
an `m`-form on `F` for each `b` in an open subset `U` of a normed space `EB`, and fix `y ∈ F`. If
`β b' y = c b' • ν y` for all `b' ∈ U`, for a form `ν` on `F` and a function `c` on `EB` that is
differentiable at `b ∈ U`, then the derivative at `b`, in the direction `a ∈ EB`, of
`b' ↦ β b' y` is `(∂c/∂b)(b) a • ν y`. -/
theorem mfderiv_family_apply_eq_fderiv_smul {β : U → RoughForm J F ℝ m} (ν : RoughForm J F ℝ m)
    {y : F} {c : EB → ℝ} {b : U} (hc : DifferentiableAt ℝ c b)
    (hβ : ∀ b' : U, β b' y = c b' • ν y) (a : EB) :
    (show E [⋀^Fin m]→L[ℝ] ℝ from mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, E [⋀^Fin m]→L[ℝ] ℝ)
        (fun b' : U ↦ show E [⋀^Fin m]→L[ℝ] ℝ from β b' y) b a) = fderiv ℝ c b a • ν y := by
  -- `ν y` read as an alternating map of vectors of `E`, so that it is a fixed vector of one
  -- normed space as `b'` varies; `dsimp only` below removes the `show` of the statement.
  let η : E [⋀^Fin m]→L[ℝ] ℝ := ν y
  have heq : (fun b' : U ↦ show E [⋀^Fin m]→L[ℝ] ℝ from β b' y) =
      (fun z ↦ c z • η) ∘ Subtype.val :=
    funext hβ
  dsimp only at heq ⊢
  have hF : HasFDerivAt (fun z : EB ↦ c z • η) ((fderiv ℝ c b).smulRight η) b :=
    hc.hasFDerivAt.smul_const η
  have hmf := Manifold.mfderiv_comp_subtype_val_apply (J := 𝓘(ℝ, EB)) (U := U)
    (I := 𝓘(ℝ, E [⋀^Fin m]→L[ℝ] ℝ)) (f := fun z : EB ↦ c z • η) (x := b) a
  rw [hF.hasMFDerivAt.mfderiv] at hmf
  rw [heq]
  exact hmf.trans (ContinuousLinearMap.smulRight_apply (M₁ := EB)
    (M₂ := E [⋀^Fin m]→L[ℝ] ℝ) (x := a))

variable [IsManifold J ∞ F]

/-- **The derivative in the parameter of a smooth family of forms is a smooth form.** On an
oriented, Hausdorff, σ-compact manifold `F`, let `β b` be an `m`-form on `F` for each `b` in an
open subset `U` of a normed space `EB`, such that `(b, y) ↦ β b y` is a smooth section of the
bundle of `m`-forms along `(b, y) ↦ y`. For `b ∈ U` and `a ∈ EB`, the `m`-form on `F` whose value
at `y` is the derivative at `b`, in the direction `a`, of `b' ↦ β b' y` is smooth. -/
theorem isSmoothForm_mfderiv_family_apply [T2Space F] [SigmaCompactSpace F]
    (o : Manifold.Orientation J F (Fin m)) {β : U → RoughForm J F ℝ m}
    (hβ : ContMDiff (𝓘(ℝ, EB).prod J) (J.prod 𝓘(ℝ, E [⋀^Fin m]→L[ℝ] ℝ)) ∞
      (fun q : U × F ↦ TotalSpace.mk' (E [⋀^Fin m]→L[ℝ] ℝ)
        (E := fun y : F ↦ TangentSpace J y [⋀^Fin m]→L[ℝ] Trivial F ℝ y) q.2 (β q.1 q.2)))
    (b : U) (a : EB) :
    IsSmoothForm J ∞ (fun y ↦ show E [⋀^Fin m]→L[ℝ] ℝ from
      mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, E [⋀^Fin m]→L[ℝ] ℝ)
        (fun b' : U ↦ show E [⋀^Fin m]→L[ℝ] ℝ from β b' y) b a) := by
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := J) (n := ⊤) (F := E)
    (E := fun y : F ↦ TangentSpace J y)
  let : RiemannianBundle (fun y : F ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩
  obtain ⟨c, hc, hβc⟩ := RoughForm.exists_contMDiffOn_opens_eq_smul_riemannianVolumeForm o hβ
  -- At each `y`, the coefficient is `C^∞` jointly, near `(b, y)`.
  have hcy (y : F) : ContMDiffAt (𝓘(ℝ, EB).prod J) 𝓘(ℝ) ∞ (uncurry c) ((b : EB), y) :=
    hc.contMDiffAt ((U.isOpen.prod isOpen_univ).mem_nhds ⟨b.property, mem_univ y⟩)
  rw [funext fun y ↦ mfderiv_family_apply_eq_fderiv_smul _
    (((hcy y).comp (b : EB) (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt
      (by simp)).differentiableAt (fun b' ↦ hβc b' y) a]
  refine (isSmoothForm_riemannianVolumeForm o).fun_smul ?_
  -- The derivative in the parameter of the coefficient is smooth in the fibre variable.
  have hd : ContMDiff J 𝓘(ℝ, EB →L[ℝ] ℝ) ∞ fun y ↦ fderiv ℝ (fun z ↦ c z y) b := fun y ↦ by
    have hg : ContMDiffAt (J.prod 𝓘(ℝ, EB)) 𝓘(ℝ) ∞ (uncurry fun (y : F) (z : EB) ↦ c z y)
        (y, b) :=
      (hcy y).comp (y, (b : EB)) (contMDiffAt_snd.prodMk contMDiffAt_fst)
    exact (hg.fderiv_right (n := ∞) (by simp)).comp y (contMDiffAt_id.prodMk contMDiffAt_const)
  exact hd.clm_apply contMDiff_const

variable [T2Space F] [CompactSpace F]

/-- **Differentiation of the integrals of a smooth family of forms under the integral sign.** On
a compact Hausdorff manifold `F` with an orientation `o`, let `β b` be an `m`-form on `F` for each
`b` in an open subset `U` of a normed space `EB`, such that `(b, y) ↦ β b y` is a smooth section
of the bundle of `m`-forms along `(b, y) ↦ y`. Then `b' ↦ ∫_F β b'` is differentiable at `b ∈ U`,
and its derivative at `b` in each direction `a ∈ EB` is the integral over `F` of the `m`-form
whose value at `y` is the derivative at `b`, in the direction `a`, of `b' ↦ β b' y`. -/
theorem mdifferentiableAt_integralTopForm_and_mfderiv_integralTopForm_apply
    (o : Manifold.Orientation J F (Fin m)) {β : U → RoughForm J F ℝ m}
    (hβ : ContMDiff (𝓘(ℝ, EB).prod J) (J.prod 𝓘(ℝ, E [⋀^Fin m]→L[ℝ] ℝ)) ∞
      (fun q : U × F ↦ TotalSpace.mk' (E [⋀^Fin m]→L[ℝ] ℝ)
        (E := fun y : F ↦ TangentSpace J y [⋀^Fin m]→L[ℝ] Trivial F ℝ y) q.2 (β q.1 q.2)))
    (b : U) :
    MDifferentiableAt 𝓘(ℝ, EB) 𝓘(ℝ) (fun b' ↦ integralTopForm o (β b')) b ∧
      ∀ a : EB, mfderiv 𝓘(ℝ, EB) 𝓘(ℝ) (fun b' ↦ integralTopForm o (β b')) b a =
        integralTopForm o (fun y ↦ show E [⋀^Fin m]→L[ℝ] ℝ from
          mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, E [⋀^Fin m]→L[ℝ] ℝ)
            (fun b' : U ↦ show E [⋀^Fin m]→L[ℝ] ℝ from β b' y) b a) := by
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := J) (n := ⊤) (F := E)
    (E := fun y : F ↦ TangentSpace J y)
  let : RiemannianBundle (fun y : F ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E (fun y : F ↦ TangentSpace J y) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := J) (n := ∞)
  obtain ⟨c, hc, hβc⟩ := RoughForm.exists_contMDiffOn_opens_eq_smul_riemannianVolumeForm o hβ
  have hc₁ : ContMDiffOn (𝓘(ℝ, EB).prod J) 𝓘(ℝ) 1 (uncurry c) (U ×ˢ univ) := hc.of_le (by simp)
  -- The integral of `β b'` for `b' ∈ U` is that of the coefficient against the volume.
  have hf : (fun b' : U ↦ integralTopForm o (β b')) =
      (fun z ↦ ∫ y, c z y ∂riemannianVolume J F) ∘ Subtype.val := funext fun b' ↦
    (congrArg (integralTopForm o) (funext fun y ↦ hβc b' y)).trans <|
      integralTopForm_smul_riemannianVolumeForm o (f := fun y ↦ c b' y)
        (hc.continuousOn.comp_continuous (Continuous.prodMk_right (b' : EB))
          fun y ↦ ⟨b'.property, mem_univ y⟩) (HasCompactSupport.of_compactSpace _)
  have hG := hasFDerivAt_integral_of_contMDiffOn (μ := riemannianVolume J F) U.isOpen
    b.property hc₁
  have hd : Continuous fun y ↦ fderiv ℝ (fun z ↦ c z y) b :=
    (continuousOn_fderiv_of_contMDiffOn U.isOpen isOpen_univ hc₁).comp_continuous
      (continuous_const.prodMk continuous_id) fun y ↦ ⟨b.property, mem_univ y⟩
  rw [hf]
  refine ⟨Manifold.mdifferentiableAt_comp_subtype_val_iff.2
    hG.differentiableAt.mdifferentiableAt, fun a ↦ ?_⟩
  refine (Manifold.mfderiv_comp_subtype_val_apply (J := 𝓘(ℝ, EB)) (I := 𝓘(ℝ)) (U := U)
    (f := fun z ↦ ∫ y, c z y ∂riemannianVolume J F) (x := b) a).trans ?_
  rw [hG.hasMFDerivAt.mfderiv]
  refine (ContinuousLinearMap.integral_apply
    (hd.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) a).trans ?_
  rw [funext fun y ↦ mfderiv_family_apply_eq_fderiv_smul _
    (((hc₁.contMDiffAt ((U.isOpen.prod isOpen_univ).mem_nhds ⟨b.property, mem_univ y⟩)).comp
      (b : EB) (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt
        one_ne_zero).differentiableAt (fun b' ↦ hβc b' y) a]
  exact (integralTopForm_smul_riemannianVolumeForm o (hd.clm_apply continuous_const)
    (HasCompactSupport.of_compactSpace _)).symm

/-- **The integrals of a smooth family of forms are differentiable in the parameter.** On a
compact Hausdorff manifold `F` with an orientation `o`, let `β b` be an `m`-form on `F` for each
`b` in an open subset `U` of a normed space `EB`, such that `(b, y) ↦ β b y` is a smooth section
of the bundle of `m`-forms along `(b, y) ↦ y`. Then `b' ↦ ∫_F β b'` is differentiable at every
`b ∈ U`. -/
theorem mdifferentiableAt_integralTopForm (o : Manifold.Orientation J F (Fin m))
    {β : U → RoughForm J F ℝ m}
    (hβ : ContMDiff (𝓘(ℝ, EB).prod J) (J.prod 𝓘(ℝ, E [⋀^Fin m]→L[ℝ] ℝ)) ∞
      (fun q : U × F ↦ TotalSpace.mk' (E [⋀^Fin m]→L[ℝ] ℝ)
        (E := fun y : F ↦ TangentSpace J y [⋀^Fin m]→L[ℝ] Trivial F ℝ y) q.2 (β q.1 q.2)))
    (b : U) :
    MDifferentiableAt 𝓘(ℝ, EB) 𝓘(ℝ) (fun b' ↦ integralTopForm o (β b')) b :=
  (mdifferentiableAt_integralTopForm_and_mfderiv_integralTopForm_apply o hβ b).1

/-- **The derivative in the parameter passes under the integral.** On a compact Hausdorff
manifold `F` with an orientation `o`, let `β b` be an `m`-form on `F` for each `b` in an open
subset `U` of a normed space `EB`, such that `(b, y) ↦ β b y` is a smooth section of the bundle
of `m`-forms along `(b, y) ↦ y`. For `b ∈ U` and `a ∈ EB`, the derivative at `b`, in the
direction `a`, of `b' ↦ ∫_F β b'` is the integral over `F` of the `m`-form whose value at `y` is
the derivative at `b`, in the direction `a`, of `b' ↦ β b' y`. -/
theorem mfderiv_integralTopForm_apply (o : Manifold.Orientation J F (Fin m))
    {β : U → RoughForm J F ℝ m}
    (hβ : ContMDiff (𝓘(ℝ, EB).prod J) (J.prod 𝓘(ℝ, E [⋀^Fin m]→L[ℝ] ℝ)) ∞
      (fun q : U × F ↦ TotalSpace.mk' (E [⋀^Fin m]→L[ℝ] ℝ)
        (E := fun y : F ↦ TangentSpace J y [⋀^Fin m]→L[ℝ] Trivial F ℝ y) q.2 (β q.1 q.2)))
    (b : U) (a : EB) :
    mfderiv 𝓘(ℝ, EB) 𝓘(ℝ) (fun b' ↦ integralTopForm o (β b')) b a =
      integralTopForm o (fun y ↦ show E [⋀^Fin m]→L[ℝ] ℝ from
        mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, E [⋀^Fin m]→L[ℝ] ℝ)
          (fun b' : U ↦ show E [⋀^Fin m]→L[ℝ] ℝ from β b' y) b a) :=
  (mdifferentiableAt_integralTopForm_and_mfderiv_integralTopForm_apply o hβ b).2 a

end Opens

end TauCeti

end
