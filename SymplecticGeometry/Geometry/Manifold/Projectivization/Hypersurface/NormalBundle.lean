/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.Basic
public import SymplecticGeometry.Geometry.Manifold.Projectivization.TwistCore
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Topology
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic
import TauCeti.Topology.FiberBundle.Pullback

/-!
# The normal bundle of a smooth projective hypersurface

Let `X ⊆ ℂℙⁿ⁺¹` be a smooth projective hypersurface of degree `d`, cut out by the homogeneous
polynomial `f = X.poly`, with inclusion `ι = X.embedding`. Its normal bundle `ν` is isomorphic to
the pull-back `ι^* 𝒪(d)` of the line bundle `𝒪(d) = Projectivization.twistCore d`.

At a point `x` of `X` in the standard affine open `U_i`, the differential of the dehomogenized
polynomial `w ↦ f(affineChart i w)` vanishes on the tangent space of `X`, and identifies the
normal space at `x` with `ℂ` (Tau Ceti's `TauCeti.complexProjectiveZeroLocusNormalSpaceEquiv`).
In the frame of the chart `i`, this number is the coordinate of `𝒪(d)`: on `U_i ∩ U_j` the
dehomogenizations satisfy `f_j = (v_i / v_j) ^ d * f_i`, and since `f_i` vanishes at `x`, their
differentials at `x` differ by the factor `(v_i / v_j) ^ d`, which is the transition function
`Projectivization.twistTransition d i j` of `𝒪(d)`
(`HasMFDerivAt.eval_affineChart_dehomogenize`, in `Projectivization/TwistCore.lean`). So the
identifications in the different charts fit together into one isomorphism of bundles.

The continuity of that isomorphism is checked on ambient tangent representatives of normal
classes, as in Tau Ceti's `TauCeti.SmoothEmbedding.continuous_normalBundleMap`.

## Main declarations

* `SymplecticGeometry.SmoothProjectiveHypersurface.normalSpaceEquiv`: the fibrewise isomorphism
  of the normal space of `X` at `x` with the fibre of `𝒪(d)` at `x`, read in the preferred chart
  `(twistCore d).indexAt x`.
* `SymplecticGeometry.SmoothProjectiveHypersurface.normalSpaceEquiv_normalClass`: on the normal
  class of an ambient tangent vector, it is the differential of the dehomogenized polynomial.
* `SmoothProjectiveHypersurface.twistTransition_smul_normalSpaceEquiv_normalClass` (change of
  chart): its coordinate in the frame of any chart `i` containing `x` is the differential of the
  polynomial dehomogenized at `i`.
* `SymplecticGeometry.SmoothProjectiveHypersurface.continuous_normalSpaceEquiv` and
  `SymplecticGeometry.SmoothProjectiveHypersurface.continuous_normalSpaceEquiv_symm`: it is
  continuous on total spaces, from the normal bundle to `ι^* 𝒪(d)`, and so is its inverse.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  §4.4.
* [P. Griffiths and J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 1, §1.
-/

public section

open Bundle MvPolynomial Set Projectivization TauCeti
open scoped ContDiff Manifold LinearAlgebra.Projectivization Topology

namespace SymplecticGeometry

namespace SmoothProjectiveHypersurface

variable {n d : ℕ} (X : SmoothProjectiveHypersurface n d)

/-- **The normal bundle of a hypersurface is `ι^* 𝒪(d)`, fibrewise.** At a point `x` of the
hypersurface, the isomorphism of its normal space with the fibre `ℂ` of `𝒪(d)` at `x` induced by
the differential of the polynomial dehomogenized at the preferred chart `(twistCore d).indexAt x`
(`normalSpaceEquiv_normalClass`). -/
noncomputable def normalSpaceEquiv (x : X) :
    X.embedding.NormalSpace x WithTop.top_ne_zero ≃L[ℂ]
      (twistCore (𝕜 := ℂ) (n := n + 1) (d : ℤ)).Fiber (x : ℙ ℂ (Fin (n + 2) → ℂ)) :=
  (complexProjectiveZeroLocusNormalSpaceEquiv (fun _ ↦ X.isHomogeneous) isOpen_univ
      X.carrier_eq_inter_univ X.surjective_jacobiMatrixAt (r := ω) WithTop.top_ne_zero x
      (mem_affineOpen_twistCore_indexAt (d : ℤ) (x : ℙ ℂ (Fin (n + 2) → ℂ)))).trans
    (ContinuousLinearEquiv.funUnique Unit ℂ ℂ)

/-- `normalSpaceEquiv` is Tau Ceti's identification of the normal space with the space
`Unit → ℂ` of values of the equation, in the preferred chart of `𝒪(d)` at `x`. -/
theorem normalSpaceEquiv_apply (x : X) (a : X.embedding.NormalSpace x WithTop.top_ne_zero) :
    X.normalSpaceEquiv x a = ContinuousLinearEquiv.funUnique Unit ℂ ℂ
      (complexProjectiveZeroLocusNormalSpaceEquiv (fun _ ↦ X.isHomogeneous) isOpen_univ
        X.carrier_eq_inter_univ X.surjective_jacobiMatrixAt (r := ω) WithTop.top_ne_zero x
        (mem_affineOpen_twistCore_indexAt (d : ℤ) (x : ℙ ℂ (Fin (n + 2) → ℂ))) a) :=
  (rfl)

/-- On the normal class of an ambient tangent vector `v` at `x`, `normalSpaceEquiv` is the
differential at `x` of the polynomial dehomogenized at the preferred chart of `𝒪(d)` at `x`. -/
theorem normalSpaceEquiv_normalClass (x : X)
    (v : TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) (x : ℙ ℂ (Fin (n + 2) → ℂ))) :
    X.normalSpaceEquiv x (X.embedding.normalClass x WithTop.top_ne_zero v) =
      mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ)
        (fun y ↦ eval (affineChart ((twistCore (𝕜 := ℂ) (n := n + 1) (d : ℤ)).indexAt x) y)
          (dehomogenize ((twistCore (𝕜 := ℂ) (n := n + 1) (d : ℤ)).indexAt x) X.poly)) x v := by
  set i := (twistCore (𝕜 := ℂ) (n := n + 1) (d : ℤ)).indexAt (x : ℙ ℂ (Fin (n + 2) → ℂ))
  have hi : (x : ℙ ℂ (Fin (n + 2) → ℂ)) ∈ affineOpen i :=
    mem_affineOpen_twistCore_indexAt (d : ℤ) _
  -- The derivative of the equation, with values in `Unit → ℂ` as Tau Ceti states it.
  have h : HasMFDerivAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Unit → ℂ)
      (fun y (_ : Unit) ↦ eval (affineChart i y) (dehomogenize i X.poly))
      (x : ℙ ℂ (Fin (n + 2) → ℂ))
      ((ContinuousLinearEquiv.funUnique Unit ℂ ℂ).symm.toContinuousLinearMap.comp
        (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ)
          (fun y ↦ eval (affineChart i y) (dehomogenize i X.poly)) x :
            TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) (x : ℙ ℂ (Fin (n + 2) → ℂ)) →L[ℂ] ℂ)) :=
    (hasMFDerivAt_iff_hasFDerivAt.2
      (ContinuousLinearEquiv.funUnique Unit ℂ ℂ).symm.hasFDerivAt).comp _
        (((contMDiffOn_eval_affineChart _ i 1).contMDiffAt
          ((isOpen_affineOpen i).mem_nhds hi)).mdifferentiableAt one_ne_zero).hasMFDerivAt
  have hv := complexProjectiveZeroLocusNormalSpaceEquiv_normalClass (fun _ ↦ X.isHomogeneous)
    isOpen_univ X.carrier_eq_inter_univ X.surjective_jacobiMatrixAt (r := ω) WithTop.top_ne_zero x
    hi v
  rw [h.mfderiv] at hv
  rw [normalSpaceEquiv_apply]
  -- `X.embedding` is Tau Ceti's embedding by definition, so `hv` applies to its normal class.
  exact (congrArg (ContinuousLinearEquiv.funUnique Unit ℂ ℂ) hv).trans
    ((ContinuousLinearEquiv.funUnique Unit ℂ ℂ).apply_symm_apply _)

/-- **Change of chart.** For a point `x` of the hypersurface in the affine open `U_i`, the
coordinate of `normalSpaceEquiv x` in the frame of the chart `i` of `𝒪(d)` is, on the normal
class of an ambient tangent vector `v`, the differential at `x` of the polynomial dehomogenized
at `i`, applied to `v`. -/
theorem twistTransition_smul_normalSpaceEquiv_normalClass (x : X) {i : Fin (n + 2)}
    (hi : (x : ℙ ℂ (Fin (n + 2) → ℂ)) ∈ affineOpen i)
    (v : TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) (x : ℙ ℂ (Fin (n + 2) → ℂ))) :
    twistTransition (d : ℤ) ((twistCore (𝕜 := ℂ) (n := n + 1) (d : ℤ)).indexAt x) i
        (x : ℙ ℂ (Fin (n + 2) → ℂ)) •
        X.normalSpaceEquiv x (X.embedding.normalClass x WithTop.top_ne_zero v) =
      mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ)
        (fun y ↦ eval (affineChart i y) (dehomogenize i X.poly)) x v := by
  set k := (twistCore (𝕜 := ℂ) (n := n + 1) (d : ℤ)).indexAt (x : ℙ ℂ (Fin (n + 2) → ℂ))
  have hk : (x : ℙ ℂ (Fin (n + 2) → ℂ)) ∈ affineOpen k :=
    mem_affineOpen_twistCore_indexAt (d : ℤ) _
  have hx : eval (affineChart k (x : ℙ ℂ (Fin (n + 2) → ℂ))) (dehomogenize k X.poly) = 0 :=
    (mem_complexProjectiveZeroLocus_iff_eval_affineChart (fun _ ↦ X.isHomogeneous) hk).1
      (X.carrier_def ▸ x.property) ()
  have h := HasMFDerivAt.eval_affineChart_dehomogenize X.isHomogeneous hk hi hx
    (L := (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ)
      (fun y ↦ eval (affineChart k y) (dehomogenize k X.poly)) x :
        TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) (x : ℙ ℂ (Fin (n + 2) → ℂ)) →L[ℂ] ℂ))
    (((contMDiffOn_eval_affineChart _ k 1).contMDiffAt
      ((isOpen_affineOpen k).mem_nhds hk)).mdifferentiableAt one_ne_zero).hasMFDerivAt
  rw [normalSpaceEquiv_normalClass, h.mfderiv]
  -- `(c • L) v = c • L v`, with `L` valued in a tangent space of `ℂ`, which is `ℂ` by
  -- definition; the rewriting lemmas do not see through that identification.
  rfl

/-- **The normal bundle of a hypersurface is `ι^* 𝒪(d)`.** `normalSpaceEquiv` is continuous on
total spaces, from the normal bundle of `X` to the pull-back of `𝒪(d)` by the inclusion. -/
theorem continuous_normalSpaceEquiv :
    Continuous fun p : TotalSpace ℂ (fun x : X ↦ X.embedding.NormalSpace x WithTop.top_ne_zero) ↦
      TotalSpace.mk' ℂ (E := (X.embedding : X → ℙ ℂ (Fin (n + 2) → ℂ)) *ᵖ
        (twistCore (𝕜 := ℂ) (n := n + 1) (d : ℤ)).Fiber) p.proj
        (X.normalSpaceEquiv p.proj p.snd) := by
  rw [SmoothEmbedding.continuous_normalBundle_iff _ WithTop.top_ne_zero]
  -- On ambient tangent representatives, the map takes `normalSpaceEquiv` of the normal class.
  refine Continuous.congr (f := fun q : TotalSpace (Fin (n + 1) → ℂ)
      ((X.embedding : X → ℙ ℂ (Fin (n + 2) → ℂ)) *ᵖ (TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ))) ↦
      TotalSpace.mk' ℂ
      (E := (X.embedding : X → ℙ ℂ (Fin (n + 2) → ℂ)) *ᵖ
        (twistCore (𝕜 := ℂ) (n := n + 1) (d : ℤ)).Fiber) q.proj
        (X.normalSpaceEquiv q.proj (X.embedding.normalClass q.proj WithTop.top_ne_zero q.snd)))
    ?_ fun q ↦ ?_
  swap
  · rw [Function.comp_apply, SmoothEmbedding.normalQuotientMap_apply]
  refine Pullback.continuous_iff.2
    ⟨Pullback.continuous_proj _ _ _, continuous_iff_continuousAt.2 fun q₀ ↦ ?_⟩
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(X.embedding.contMDiff.continuous.comp (Pullback.continuous_proj _ _ _)).continuousAt, ?_⟩
  set i := (twistCore (𝕜 := ℂ) (n := n + 1) (d : ℤ)).indexAt (X.embedding q₀.proj)
  have hi : X.embedding q₀.proj ∈ affineOpen i :=
    mem_affineOpen_twistCore_indexAt (d : ℤ) _
  have hU : ∀ᶠ q in 𝓝 q₀, X.embedding q.proj ∈ affineOpen i :=
    (X.embedding.contMDiff.continuous.comp (Pullback.continuous_proj _ _ _)).continuousAt
      |>.preimage_mem_nhds
      ((isOpen_affineOpen i).mem_nhds hi)
  -- Near `q₀`, the coordinate in the chart `i` is the differential of the equation at `i`,
  -- which is continuous on the tangent bundle.
  have ht := ContMDiffAt.continuousAt_tangentMap (x₀ := Pullback.lift X.embedding q₀)
    ((contMDiffOn_eval_affineChart (dehomogenize i X.poly) i 1).contMDiffAt
      ((isOpen_affineOpen i).mem_nhds hi)) le_rfl
  have hc : ContinuousAt (fun q : TotalSpace (Fin (n + 1) → ℂ)
      ((X.embedding : X → ℙ ℂ (Fin (n + 2) → ℂ)) *ᵖ (TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ))) ↦
        (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ) (fun y ↦ eval (affineChart i y) (dehomogenize i X.poly))
          (X.embedding q.proj) q.snd : ℂ)) q₀ :=
    (continuous_snd.comp (tangentBundleModelSpaceHomeomorph 𝓘(ℂ)).continuous).continuousAt.comp
      (ht.comp (Pullback.continuous_lift _ _ _).continuousAt)
  have hr (b : ℙ ℂ (Fin (n + 2) → ℂ)) (a : ℂ) :
      (trivializationAt ℂ (twistCore (𝕜 := ℂ) (n := n + 1) (d : ℤ)).Fiber (X.embedding q₀.proj)
        ⟨b, a⟩).2 = twistTransition (d : ℤ) ((twistCore (d : ℤ)).indexAt b) i b * a := by
    rw [VectorBundleCore.trivializationAt, ← VectorBundleCore.localTrivAt_def,
      VectorBundleCore.localTriv_apply, twistCore_coordChange_apply]
  refine hc.congr ?_
  filter_upwards [hU] with q hq
  have he : X.embedding q.proj = q.proj := congrFun X.coe_embedding q.proj
  refine Eq.trans ?_ (hr _ _).symm
  rw [he]
  exact (X.twistTransition_smul_normalSpaceEquiv_normalClass q.proj (he ▸ hq) q.snd).symm

/-- The inverse of `normalSpaceEquiv` is continuous on total spaces, from the pull-back of `𝒪(d)`
by the inclusion to the normal bundle of `X`. -/
theorem continuous_normalSpaceEquiv_symm :
    Continuous fun q : TotalSpace ℂ ((X.embedding : X → ℙ ℂ (Fin (n + 2) → ℂ)) *ᵖ
        (twistCore (𝕜 := ℂ) (n := n + 1) (d : ℤ)).Fiber) ↦
      TotalSpace.mk' ℂ (E := fun x : X ↦ X.embedding.NormalSpace x WithTop.top_ne_zero) q.proj
        ((X.normalSpaceEquiv q.proj).symm q.snd) := by
  have hdim : Module.finrank ℂ ℂ = Module.finrank ℂ (Fin (n + 1) → ℂ) -
      Module.finrank ℂ (Fin (n + 1 - Fintype.card Unit) → ℂ) := by
    rw [finrank_model]
    simp
  let := X.embedding.normalSpaceFiberBundle WithTop.top_ne_zero hdim
  let := X.embedding.normalSpaceVectorBundle WithTop.top_ne_zero hdim
  -- The fibres of the pull-back are `ℂ`, so they are groups, as `continuous_bundle_symm` asks.
  let _ : ∀ x : X, AddCommGroup (((X.embedding : X → ℙ ℂ (Fin (n + 2) → ℂ)) *ᵖ
      (twistCore (𝕜 := ℂ) (n := n + 1) (d : ℤ)).Fiber) x) :=
    fun _ ↦ inferInstanceAs (AddCommGroup ℂ)
  exact TauCeti.continuous_bundle_symm (F₁ := ℂ) (F₂ := ℂ)
    (E₂ := (X.embedding : X → ℙ ℂ (Fin (n + 2) → ℂ)) *ᵖ
      (twistCore (𝕜 := ℂ) (n := n + 1) (d : ℤ)).Fiber)
    X.normalSpaceEquiv X.continuous_normalSpaceEquiv

end SmoothProjectiveHypersurface

end SymplecticGeometry

end
