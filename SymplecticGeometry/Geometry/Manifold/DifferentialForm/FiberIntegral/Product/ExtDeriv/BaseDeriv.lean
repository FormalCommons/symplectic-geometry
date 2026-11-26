/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Product.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Product.Coefficient
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Opens
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.Deriv
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.OpensModelSpace

/-!
# The base derivative of the fibre integral over an open subset of a normed space

Let `U` be an open subset of a normed space `E`, with the model `𝓘(ℝ, E)`, let `F` be a manifold
of dimension `m` over `J` with an orientation `o`, and let `α` be a smooth form of degree `r + m`
on `U × F`. Fix vectors `u₁, …, uᵣ ∈ E`, a point `b ∈ U` and a direction `a ∈ E`, and write
`D y` for the derivative at `b`, in the direction `a`, of `b' ↦ prodFiberIntegrand α b' u y`.
This file shows that `D` is a smooth `m`-form on `F`
(`SymplecticGeometry.isSmoothForm_mfderiv_prodFiberIntegrand`) and, for `F` compact, that
`b' ↦ ∫_F prodFiberIntegrand α b' u` is differentiable at `b`
(`SymplecticGeometry.mdifferentiableAt_integralTopForm_prodFiberIntegrand`) with derivative
`∫_F D` in the direction `a`
(`SymplecticGeometry.mfderiv_integralTopForm_prodFiberIntegrand_apply`): the derivative in the
base passes under the integral over the fibre. This holds for every `r` and `m`.

The proof writes the integrand against a volume form. With a smooth Riemannian metric on `F`
(`TauCeti.nonempty_contMDiffRiemannianMetric`) and its volume form `ν`, the constant vector fields
`u` on `U` (`TopologicalSpace.Opens.contMDiff_tangentBundle_mk_const`) make the integrands jointly
smooth (`SymplecticGeometry.contMDiff_prodFiberIntegrand`), so they are `c (b', y) • ν y` for a
coefficient `c` smooth on `U × F`
(`TauCeti.RoughForm.exists_contMDiff_eq_smul_riemannianVolumeForm`),
here extended by `0` to `E × F`
(`SymplecticGeometry.exists_contMDiffOn_prodFiberIntegrand_eq_smul_riemannianVolumeForm`). As in
the proof of `TauCeti.contMDiff_integralTopForm`, the integral of the integrand is then
`∫ c (b', y) ∂vol` (`TauCeti.integralTopForm_smul_riemannianVolumeForm`), and
`TauCeti.hasFDerivAt_integral_of_contMDiffAt` differentiates it under the integral sign. On `U`
the derivative of a function is that of the same function on `E`
(`TauCeti.Manifold.mfderiv_comp_subtype_val_apply`), so `D y` is `∂c/∂b (b, y) a • ν y`
(`SymplecticGeometry.mfderiv_prodFiberIntegrand_eq_fderiv_smul`). This gives both results: the
partial derivative of `c` is smooth in `y` (`ContMDiffAt.fderiv_right`), and its integral against
the volume is `∫_F D`.

This is the step of Bott–Tu, §6, that differentiates the fibre integral in the base, where the
integrand is a function times a fixed volume form on the fibre.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6.
-/

public section

noncomputable section

open Set Function Bundle TopologicalSpace MeasureTheory
open scoped Manifold ContDiff

namespace SymplecticGeometry

open TauCeti

variable {E E' H' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace F] [ChartedSpace H' F] {U : Opens E} {r m : ℕ}

/-- A constant vector field `b ↦ u` on an open subset `U` of a normed space is smooth, as a map
into the tangent bundle of `U`. -/
theorem _root_.TopologicalSpace.Opens.contMDiff_tangentBundle_mk_const {n : WithTop ℕ∞} (u : E) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent n fun b : U ↦ (⟨b, u⟩ : TangentBundle 𝓘(ℝ, E) U) := by
  intro b₀
  rw [contMDiffAt_totalSpace_iff]
  refine ⟨contMDiffAt_id, (contMDiffAt_const (c := u)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun b ↦ ?_)⟩
  have hb := Manifold.mem_trivializationAt_opens_model_space_baseSet (𝕜 := ℝ) b₀ b
  have h := (trivializationAt E (TangentSpace 𝓘(ℝ, E)) b₀).symm_apply_apply_mk hb u
  rw [← Trivialization.symmL_apply (R := ℝ) _ hb,
    Manifold.trivializationAt_opens_model_space_symmL] at h
  exact h

/-- **The base derivative of the integrand from its coefficient.** Let `c` be a function on
`E × F`, `C¹` on `U × F`, with `prodFiberIntegrand α b u y = c b y • ν y` for all `b ∈ U` and
`y ∈ F`, for a fixed form `ν` on `F`. Then the derivative at `b ∈ U`, in the direction `a ∈ E`,
of `b' ↦ prodFiberIntegrand α b' u y` is `(∂c/∂b)(b, y) a • ν y`. -/
theorem mfderiv_prodFiberIntegrand_eq_fderiv_smul
    (α : RoughForm (𝓘(ℝ, E).prod J) (U × F) ℝ (r + m)) (u : Fin r → E) (ν : RoughForm J F ℝ m)
    {c : E → F → ℝ} (hc : ContMDiffOn (𝓘(ℝ, E).prod J) 𝓘(ℝ) 1 (uncurry c) (U ×ˢ univ))
    (hβ : ∀ (b : U) (y : F), prodFiberIntegrand α b u y = c b y • ν y) (b : U) (a : E) (y : F) :
    (show E' [⋀^Fin m]→L[ℝ] ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E' [⋀^Fin m]→L[ℝ] ℝ)
        (fun b' : U ↦ show E' [⋀^Fin m]→L[ℝ] ℝ from prodFiberIntegrand α b' u y) b a) =
      fderiv ℝ (fun z ↦ c z y) b a • ν y := by
  have h : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 1 (fun z ↦ c z y) b :=
    (hc.contMDiffAt ((U.isOpen.prod isOpen_univ).mem_nhds ⟨b.property, mem_univ y⟩)).comp (b : E)
      (contMDiffAt_id.prodMk contMDiffAt_const)
  have hd : DifferentiableAt ℝ (fun z ↦ c z y) b :=
    (h.mdifferentiableAt one_ne_zero).differentiableAt
  -- `ν y` read as an alternating map of vectors of `E'`, so that it is a fixed vector of one
  -- normed space as `b'` varies; `dsimp only` below removes the `show` of the statement.
  let η : E' [⋀^Fin m]→L[ℝ] ℝ := ν y
  have heq : (fun b' : U ↦ show E' [⋀^Fin m]→L[ℝ] ℝ from prodFiberIntegrand α b' u y) =
      (fun z ↦ c z y • η) ∘ Subtype.val :=
    funext fun b' ↦ hβ b' y
  dsimp only at heq ⊢
  have hF : HasFDerivAt (fun z : E ↦ c z y • η)
      ((fderiv ℝ (fun z ↦ c z y) b).smulRight η) b :=
    hd.hasFDerivAt.smul_const η
  have hmf := Manifold.mfderiv_comp_subtype_val_apply (J := 𝓘(ℝ, E)) (U := U)
    (I := 𝓘(ℝ, E' [⋀^Fin m]→L[ℝ] ℝ))
    (f := fun z : E ↦ c z y • η) (x := b) a
  rw [hF.hasMFDerivAt.mfderiv] at hmf
  rw [heq]
  exact hmf.trans (ContinuousLinearMap.smulRight_apply (M₁ := E)
    (M₂ := E' [⋀^Fin m]→L[ℝ] ℝ) (x := a))

variable [FiniteDimensional ℝ E'] [IsManifold J ∞ F]

/-- **The integrand as a coefficient times a volume form.** Let `F` carry a smooth Riemannian
metric and an orientation `o`, with Riemannian volume form `ν`. For a smooth form `α` of degree
`r + m` on `U × F` and fixed vectors `u₁, …, uᵣ ∈ E`, there is a function `c` on `E × F`, smooth
on `U × F`, with `prodFiberIntegrand α b u y = c b y • ν y` for all `b ∈ U` and `y ∈ F`. -/
theorem exists_contMDiffOn_prodFiberIntegrand_eq_smul_riemannianVolumeForm
    [RiemannianBundle (fun y : F ↦ TangentSpace J y)]
    [IsContMDiffRiemannianBundle J ∞ E' (fun y : F ↦ TangentSpace J y)]
    (o : Manifold.Orientation J F (Fin m)) (α : SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ (r + m))
    (u : Fin r → E) :
    ∃ c : E → F → ℝ, ContMDiffOn (𝓘(ℝ, E).prod J) 𝓘(ℝ) ∞ (uncurry c) (U ×ˢ univ) ∧
      ∀ (b : U) (y : F), prodFiberIntegrand α.val b u y = c b y • riemannianVolumeForm o y := by
  obtain ⟨c, hc, hβ⟩ := RoughForm.exists_contMDiff_eq_smul_riemannianVolumeForm
    (K := 𝓘(ℝ, E)) (β := fun b ↦ prodFiberIntegrand α.val b u) o
    (contMDiff_prodFiberIntegrand (g := id) α.isSmoothForm contMDiff_id
      fun i ↦ Opens.contMDiff_tangentBundle_mk_const (u i))
  classical
  refine ⟨fun z y ↦ if h : z ∈ U then c (⟨z, h⟩, y) else 0,
    hc.contMDiffOn_opens_prod_of_eq fun z hz y ↦ dite_eq_left hz, fun b y ↦ ?_⟩
  exact (hβ b y).trans (congrArg (· • riemannianVolumeForm o y) (by simp))

/-- **The base derivative of the integrand is a smooth form.** Let `F` be Hausdorff and
σ-compact, with an orientation `o`, and let `α` be a smooth form of degree `r + m` on `U × F`.
For `b ∈ U` and `a, u₁, …, uᵣ ∈ E`, the `m`-form on `F` whose value at `y` is the derivative at
`b`, in the direction `a`, of `b' ↦ prodFiberIntegrand α b' u y` is smooth. -/
theorem isSmoothForm_mfderiv_prodFiberIntegrand [T2Space F] [SigmaCompactSpace F]
    (o : Manifold.Orientation J F (Fin m)) (α : SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ (r + m))
    (u : Fin r → E) (b : U) (a : E) :
    IsSmoothForm J ∞ (fun y ↦ show E' [⋀^Fin m]→L[ℝ] ℝ from
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E' [⋀^Fin m]→L[ℝ] ℝ)
        (fun b' : U ↦ show E' [⋀^Fin m]→L[ℝ] ℝ from prodFiberIntegrand α.val b' u y) b a) := by
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := J) (n := ⊤) (F := E')
    (E := fun y : F ↦ TangentSpace J y)
  let : RiemannianBundle (fun y : F ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩
  obtain ⟨c, hc, hβ⟩ := exists_contMDiffOn_prodFiberIntegrand_eq_smul_riemannianVolumeForm o α u
  rw [funext fun y ↦ mfderiv_prodFiberIntegrand_eq_fderiv_smul α.val u _ (hc.of_le (by simp))
    hβ b a y]
  refine (isSmoothForm_riemannianVolumeForm o).fun_smul ?_
  -- The derivative in the base of the coefficient is smooth in the fibre variable.
  have hd : ContMDiff J 𝓘(ℝ, E →L[ℝ] ℝ) ∞ fun y ↦ fderiv ℝ (fun z ↦ c z y) b := fun y ↦ by
    have hg : ContMDiffAt (J.prod 𝓘(ℝ, E)) 𝓘(ℝ) ∞ (uncurry fun (y : F) (z : E) ↦ c z y)
        (y, b) :=
      (hc.contMDiffAt ((U.isOpen.prod isOpen_univ).mem_nhds ⟨b.property, mem_univ y⟩)).comp
        (y, (b : E)) (contMDiffAt_snd.prodMk contMDiffAt_fst)
    exact (hg.fderiv_right (n := ∞) (by simp)).comp y (contMDiffAt_id.prodMk contMDiffAt_const)
  exact hd.clm_apply contMDiff_const

section Integral

variable [T2Space F] [CompactSpace F]

/-- Both conclusions of differentiation under the integral sign, read in the Riemannian volume of
a smooth metric on `F`: the integral of the integrand is differentiable at `b`, and its derivative
in the direction `a` is the integral of the base derivative of the integrand. -/
private theorem mdifferentiableAt_and_mfderiv_integralTopForm_prodFiberIntegrand
    (o : Manifold.Orientation J F (Fin m)) (α : SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ (r + m))
    (u : Fin r → E) (b : U) (a : E) :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ)
        (fun b' : U ↦ integralTopForm o (prodFiberIntegrand α.val b' u)) b ∧
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (fun b' : U ↦ integralTopForm o (prodFiberIntegrand α.val b' u)) b a =
        integralTopForm o (fun y ↦ show E' [⋀^Fin m]→L[ℝ] ℝ from
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E' [⋀^Fin m]→L[ℝ] ℝ)
            (fun b' : U ↦ show E' [⋀^Fin m]→L[ℝ] ℝ from prodFiberIntegrand α.val b' u y) b a) := by
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := J) (n := ⊤) (F := E')
    (E := fun y : F ↦ TangentSpace J y)
  let : RiemannianBundle (fun y : F ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E' (fun y : F ↦ TangentSpace J y) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := J) (n := ∞)
  obtain ⟨c, hc, hβ⟩ := exists_contMDiffOn_prodFiberIntegrand_eq_smul_riemannianVolumeForm o α u
  have hc₁ : ContMDiffOn (𝓘(ℝ, E).prod J) 𝓘(ℝ) 1 (uncurry c) (U ×ˢ univ) := hc.of_le (by simp)
  -- The integral of the integrand at `b' ∈ U` is that of the coefficient against the volume.
  have hf : (fun b' : U ↦ integralTopForm o (prodFiberIntegrand α.val b' u)) =
      (fun z ↦ ∫ y, c z y ∂riemannianVolume J F) ∘ Subtype.val := funext fun b' ↦
    (congrArg (integralTopForm o) (funext fun y ↦ hβ b' y)).trans <|
      integralTopForm_smul_riemannianVolumeForm o (f := fun y ↦ c b' y)
        (hc.continuousOn.comp_continuous (Continuous.prodMk_right (b' : E))
          fun y ↦ ⟨b'.property, mem_univ y⟩) (HasCompactSupport.of_compactSpace _)
  have hG := hasFDerivAt_integral_of_contMDiffAt (μ := riemannianVolume J F) (z₀ := (b : E))
    fun y ↦ hc₁.contMDiffAt ((U.isOpen.prod isOpen_univ).mem_nhds ⟨b.property, mem_univ y⟩)
  have hd : Continuous fun y ↦ fderiv ℝ (fun z ↦ c z y) b :=
    (continuousOn_fderiv_of_contMDiffOn U.isOpen isOpen_univ hc₁).comp_continuous
      (continuous_const.prodMk continuous_id) fun y ↦ ⟨b.property, mem_univ y⟩
  rw [hf]
  refine ⟨Manifold.mdifferentiableAt_comp_subtype_val_iff.2
    hG.differentiableAt.mdifferentiableAt, ?_⟩
  refine (Manifold.mfderiv_comp_subtype_val_apply (J := 𝓘(ℝ, E)) (I := 𝓘(ℝ)) (U := U)
    (f := fun z ↦ ∫ y, c z y ∂riemannianVolume J F) (x := b) a).trans ?_
  rw [hG.hasMFDerivAt.mfderiv]
  refine (ContinuousLinearMap.integral_apply
    (hd.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) a).trans ?_
  rw [funext fun y ↦ mfderiv_prodFiberIntegrand_eq_fderiv_smul α.val u _ hc₁ hβ b a y]
  exact (integralTopForm_smul_riemannianVolumeForm o (hd.clm_apply continuous_const)
    (HasCompactSupport.of_compactSpace _)).symm

/-- **The fibre integral of the integrand is differentiable in the base.** Let `F` be compact
and Hausdorff, with an orientation `o`, and let `α` be a smooth form of degree `r + m` on `U × F`.
For `u₁, …, uᵣ ∈ E`, the function `b' ↦ ∫_F prodFiberIntegrand α b' u` on `U` is differentiable
at every `b ∈ U`. -/
theorem mdifferentiableAt_integralTopForm_prodFiberIntegrand
    (o : Manifold.Orientation J F (Fin m)) (α : SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ (r + m))
    (u : Fin r → E) (b : U) :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ)
      (fun b' : U ↦ integralTopForm o (prodFiberIntegrand α.val b' u)) b :=
  (mdifferentiableAt_and_mfderiv_integralTopForm_prodFiberIntegrand o α u b 0).1

/-- **Differentiation of the fibre integral under the integral sign.** Let `F` be compact and
Hausdorff, with an orientation `o`, and let `α` be a smooth form of degree `r + m` on `U × F`.
For `b ∈ U` and `a, u₁, …, uᵣ ∈ E`, the derivative at `b`, in the direction `a`, of
`b' ↦ ∫_F prodFiberIntegrand α b' u` is the integral over `F` of the `m`-form whose value at `y`
is the derivative at `b`, in the direction `a`, of `b' ↦ prodFiberIntegrand α b' u y`. -/
theorem mfderiv_integralTopForm_prodFiberIntegrand_apply
    (o : Manifold.Orientation J F (Fin m)) (α : SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ (r + m))
    (u : Fin r → E) (b : U) (a : E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (fun b' : U ↦ integralTopForm o (prodFiberIntegrand α.val b' u)) b a =
      integralTopForm o (fun y ↦ show E' [⋀^Fin m]→L[ℝ] ℝ from
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E' [⋀^Fin m]→L[ℝ] ℝ)
          (fun b' : U ↦ show E' [⋀^Fin m]→L[ℝ] ℝ from prodFiberIntegrand α.val b' u y) b a) :=
  (mdifferentiableAt_and_mfderiv_integralTopForm_prodFiberIntegrand o α u b a).2

end Integral

end SymplecticGeometry

end
