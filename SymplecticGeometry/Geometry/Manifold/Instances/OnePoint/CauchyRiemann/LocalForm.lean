/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.Basic
public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Smooth
public import TauCeti.Geometry.Manifold.VectorField.ModelChart

/-!
# Local form of `D_J` on `𝒪(1)` in an isothermal chart

placeholder
-/

public section

open Bundle Set TauCeti TauCeti.Manifold
open OnePoint (twistCore twistTransition)
open scoped Manifold ContDiff Topology TauCeti.ComplexManifold VectorBundle.ComplexToReal

noncomputable section

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Let `ψ` be a partial diffeomorphism from `M` to `ℂ` whose derivative carries `J` to
multiplication by `i` on its source. At `w` in its target, `∂bar_J f` at `ψ.symm w`, evaluated on
the preimage `dψ⁻¹ 1` of `1`, is the conjugate Wirtinger derivative of `f ∘ ψ.symm` at `w` in the
direction `1`. -/
theorem dbarFunction_apply_mfderiv_symm_eq_conjWirtingerDeriv
    (J : SmoothAlmostComplexStructure I M) {ψ : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞}
    (hψ : ∀ y ∈ ψ.source, ∀ v : TangentSpace I y,
      mvfderiv I ψ y (J y v) = Complex.I * mvfderiv I ψ y v)
    {w : ℂ} (hw : w ∈ ψ.target) {f : M → F} (hf : MDifferentiableAt I 𝓘(ℝ, F) f (ψ.symm w)) :
    J.dbarFunction f (ψ.symm w) (mfderiv 𝓘(ℝ, ℂ) I ψ.symm w (1 : ℂ)) =
      conjWirtingerDeriv (f ∘ ψ.symm) w 1 := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hs : MDifferentiableAt 𝓘(ℝ, ℂ) I ψ.symm w := ψ.symm.mdifferentiableAt hn hw
  have hx : ψ.symm w ∈ ψ.source := ψ.map_target hw
  set u := mfderiv 𝓘(ℝ, ℂ) I ψ.symm w (1 : ℂ)
  have hu : mvfderiv I ψ (ψ.symm w) u = 1 := by
    rw [mvfderiv_apply_eq_mfderiv_apply]
    exact ψ.mfderiv_apply_mfderiv_symm_apply hn hw (1 : ℂ)
  have hJ : mfderiv 𝓘(ℝ, ℂ) I ψ.symm w (Complex.I • (1 : ℂ)) = J (ψ.symm w) u := by
    have h := hψ _ hx u
    rw [hu, mul_one, mvfderiv_apply_eq_mfderiv_apply] at h
    rw [smul_eq_mul, mul_one, ← h]
    have h2 := ψ.mfderiv_symm_apply_mfderiv_apply hn hx (J (ψ.symm w) u)
    erw [ψ.right_inv hw] at h2
    exact h2
  have hd (v : ℂ) : fderiv ℝ (f ∘ ψ.symm) w v =
      mvfderiv I f (ψ.symm w) (mfderiv 𝓘(ℝ, ℂ) I ψ.symm w v) := by
    rw [← mvfderiv_eq_fderiv_apply (𝕜 := ℝ) (f ∘ ψ.symm) w v, mvfderiv_comp w hf hs]
    rfl
  rw [conjWirtingerDeriv_apply, hd, hd, hJ, dbarFunction_apply, ← Complex.coe_smul]
  norm_num
  rfl

end TauCeti.SmoothAlmostComplexStructure

namespace SymplecticGeometry

variable {J : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)}

theorem twistOneDelBar_eq_symmL_comp_dbarFunction_add_smul {y x : OnePoint ℂ}
    (hx : x ∈ (chartAt ℂ y).source) {s : OnePoint ℂ → ℂ}
    (hs : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) 1).Fiber) p (s p)) x) :
    twistOneDelBar J s x =
      (((twistCore 1).localTriv y).symmL ℝ x).comp
          (J.dbarFunction (fun p ↦ ((twistCore (𝕜 := ℂ) 1).localTriv y ⟨p, s p⟩).2) x) +
        ((twistCore (𝕜 := ℂ) 1).localTriv y ⟨x, s x⟩).2 •
          twistOneDelBar J (((twistCore (𝕜 := ℂ) 1).localTriv y).localFrame Complex.basisOneI 0)
            x := by
  have hb : x ∈ ((twistCore (𝕜 := ℂ) 1).localTriv y).baseSet := by simpa using hx
  have hframe := ((((twistCore (𝕜 := ℂ) 1).localTriv y).contMDiffOn_localFrame_baseSet
    (I := 𝓘(ℝ, ℂ)) 1 Complex.basisOneI 0).mdifferentiableOn one_ne_zero).mdifferentiableAt
      (((twistCore (𝕜 := ℂ) 1).localTriv y).open_baseSet.mem_nhds hb)
  have h1 : ((twistCore (𝕜 := ℂ) 1).localTriv y).localFrame Complex.basisOneI 1 =
      Complex.I • ((twistCore (𝕜 := ℂ) 1).localTriv y).localFrame Complex.basisOneI 0 := by
    funext p
    by_cases hp : p ∈ ((twistCore (𝕜 := ℂ) 1).localTriv y).baseSet
    · rw [Pi.smul_apply, Trivialization.localFrame_apply_of_mem_baseSet _ _ hp,
        Trivialization.localFrame_apply_of_mem_baseSet _ _ hp, Trivialization.basisAt,
        Module.Basis.map_apply, Module.Basis.map_apply, Trivialization.linearEquivAt_symm_apply,
        Trivialization.linearEquivAt_symm_apply, ← Trivialization.symmL_apply (R := ℝ) _ hp,
        ← Trivialization.symmL_apply (R := ℝ) _ hp, ← OnePoint.twistCore_localTriv_symmL_smul]
      simp [Complex.coe_basisOneI]
    · rw [Pi.smul_apply, Trivialization.localFrame_apply_of_notMem _ _ hp,
        Trivialization.localFrame_apply_of_notMem _ _ hp, smul_zero]
  have hc (i : Fin 2) := ((twistCore (𝕜 := ℂ) 1).localTriv y).localFrameCoeff_eq_coeff
    (I := 𝓘(ℝ, ℂ)) (b := Complex.basisOneI) (s := (s : Π p, (twistCore (𝕜 := ℂ) 1).Fiber p))
    (i := i) hb
  rw [(isRealCauchyRiemannOperator_twistOneDelBar J).eq_frameCauchyRiemannOperator_add_sum
    Complex.basisOneI hb hs, OnePoint.frameCauchyRiemannOperator_twistCore_localTriv hx hs,
    Fin.sum_univ_two, h1, twistOneDelBar_const_smul J _ hframe,
    hc 0, hc 1]
  congr 1
  · simp only [OnePoint.twistCore_localTriv_apply]
  · simp only [Complex.coe_basisOneI_repr, OnePoint.twistCore_localTriv_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    conv_rhs => rw [← Complex.re_add_im (twistTransition 1 x y x * s x)]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

theorem contDiffOn_twistOneDelBar_localFrame_apply_mfderiv_symm (J) (y : OnePoint ℂ)
    (ψ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (OnePoint ℂ) ℂ ∞) :
    ContDiffOn ℝ ∞ (fun w ↦ ((twistCore (𝕜 := ℂ) 1).localTriv y
      ⟨ψ.symm w, twistOneDelBar J
        (((twistCore (𝕜 := ℂ) 1).localTriv y).localFrame Complex.basisOneI 0) (ψ.symm w)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ.symm w (1 : ℂ))⟩).2)
      (ψ.target ∩ ψ.symm ⁻¹' (chartAt ℂ y).source) := by
  set e := (twistCore (𝕜 := ℂ) 1).localTriv y
  set U := ψ.target ∩ ψ.symm ⁻¹' (chartAt ℂ y).source
  have hsource : (chartAt ℂ y).source = e.baseSet := (OnePoint.twistCore_localTriv_baseSet 1 y).symm
  have hDa : ContMDiffCovariantDerivativeOn ℂ ∞ (twistOneDelBar J) e.baseSet :=
    (isRealCauchyRiemannOperator_twistOneDelBar J).contMDiffCovariantDerivativeOn_mono_of_isOpen
      (contMDiffCovariantDerivativeOn_twistOneDelBar J ⊤) e.open_baseSet (subset_univ _)
  have hω := hDa.contMDiff ((e.contMDiffOn_localFrame_baseSet (I := 𝓘(ℝ, ℂ)) _
    Complex.basisOneI 0))
  have hψs : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ.symm U := ψ.symm.contMDiffOn.mono inter_subset_left
  have hΦ := hω.comp hψs fun w hw ↦ hsource ▸ hw.2
  have hv : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞
      (fun w ↦ TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℝ, ℂ)) (ψ.symm w)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ.symm w (1 : ℂ))) U := by
    intro w hw
    have h1 : ContMDiffAt 𝓘(ℝ, ℂ).tangent 𝓘(ℝ, ℂ).tangent ∞ (tangentMap 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ.symm)
        (⟨w, (1 : ℂ)⟩ : TangentBundle 𝓘(ℝ, ℂ) ℂ) :=
      (ψ.symm.contMDiffOn.contMDiffAt (ψ.symm.open_source.mem_nhds (by simpa using hw.1))
        ).contMDiffAt_tangentMap (by simp)
    have h2 := (TauCeti.contMDiff_tangentBundle_mk_const (n := ∞) (1 : ℂ)).contMDiffAt (x := w)
    exact (h1.comp w h2).contMDiffWithinAt
  have h := hΦ.clm_bundle_apply hv
  rw [← contMDiffOn_iff_contDiffOn]
  exact ((e.contMDiffOn_iff fun w hw ↦ e.mem_source.2 (hsource ▸ hw.2)).1 h).2

end SymplecticGeometry
