/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.RescaledFamily
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville

import SymplecticGeometry.Geometry.Symplectic.Cotangent.Bundle.ZeroSection
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Rescaling symplectic maps of a cotangent bundle towards the zero section

Let `T*L = TauCeti.CotangentBundle J L` carry its canonical symplectic form `ω`, let `U` be an
open set of `T*L` and `ψ : U → T*L` a smooth map that fixes the points of the zero section lying
in `U` and pulls `ω` back to its restriction to `U`. The rescaled family
`SymplecticGeometry.vectorBundleRescaledFamily ψ` joins `ψ`, its slice at `t = 1`, to its slice
at `t = 0`. This file shows that the latter is the identity on the points `z` with `0_x ∈ U`, `x`
the base point of `z`
(`SymplecticGeometry.CotangentBundle.vectorBundleRescaledFamily_zero_eq_self`).

By `SymplecticGeometry.vectorBundleRescaledFamily_zero_eq_mfderiv`, the slice at `t = 0` sends a
covector `a` over `x` to the fibre component of `dψ (0, a)`, in Tau Ceti's splitting
`T_{0_x}(T*L) ≅ T_x L × T*_x L` (`TauCeti.Bundle.zeroSectionTangentEquiv`). Since `ψ` fixes the
zero section, `dψ (v, 0) = (v, 0)`. Write `dψ (0, a) = (u, a')`. Along the zero section
`ω((v, a), (w, b)) = b v - a w`
(`TauCeti.CotangentBundle.eval₂_symplecticForm_zeroSectionTangentEquiv_symm`), so the invariance
of `ω` at `0_x` evaluated on `(v, 0)` and `(0, a)` reads `a' v = a v` for every `v`. Hence
`a' = a`.

## Main results

* `SymplecticGeometry.CotangentBundle.vectorBundleRescaledFamily_zero_eq_self`: the slice at
  `t = 0` of the rescaled family of a symplectic map fixing the zero section is the identity.

## References

* [P. Seidel, *Floer homology and the symplectic isotopy problem*][Seidel1997Thesis], Lemma 2.2.
-/

public section

open Set Bundle Filter Topology TopologicalSpace TauCeti TauCeti.CotangentBundle
open scoped Manifold ContDiff

namespace SymplecticGeometry.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} {L : Type*} [TopologicalSpace L] [ChartedSpace H L]

/-- **The rescaled family of a symplectic map fixing the zero section starts at the identity.**
Let `L` be a Hausdorff manifold without boundary, `U` an open set of `T*L` and `ψ : U → T*L` a
smooth map that fixes every point of the zero section lying in `U` and pulls the canonical
symplectic form back to its restriction to `U`. Then the slice at `t = 0` of the rescaled family
of `ψ` fixes every point `z` of `T*L` such that `U` contains the zero covector over the base point
of `z`. -/
theorem vectorBundleRescaledFamily_zero_eq_self [IsManifold J ∞ L] [J.Boundaryless] [T2Space L]
    {U : Opens (CotangentBundle J L)} {ψ : U → CotangentBundle J L}
    (hψ : ContMDiff (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ ψ)
    (hψ0 : ∀ x (hx : zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) x ∈ U),
      ψ ⟨_, hx⟩ = zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) x)
    (hψω : SmoothForm.mpullback ψ hψ (symplecticForm J L) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (symplecticForm J L))
    {z : CotangentBundle J L}
    (hz : zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) z.proj ∈ U) :
    vectorBundleRescaledFamily ψ (z, 0) = z := by
  obtain ⟨x, a⟩ := z
  set Z := zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ)
  set σ := symplecticForm J L
  set T := Bundle.zeroSectionTangentEquiv (I := J) (F := E →L[ℝ] ℝ)
    (V := fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) x
  set p : U := ⟨Z x, hz⟩
  -- the differential of `ψ` at `p`, as an endomorphism of `T_{0_x}(T*L)`: the tangent spaces of
  -- `U` at `p` and of `T*L` at `ψ p = 0_x` are both the model space
  set D : TangentSpace (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (Z x) →L[ℝ]
      TangentSpace (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (Z x) :=
    mfderiv (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ψ p
  rw [vectorBundleRescaledFamily_zero_eq_mfderiv hz (hψ0 x hz)
    (hψ.mdifferentiableAt (by simp))]
  congr 1
  -- the goal, with `D` for the differential of `ψ` at `p`
  change (T (D (T.symm (0, a)))).2 = a
  -- `ψ` extended by the identity outside `U`
  set ψ' : CotangentBundle J L → CotangentBundle J L := Subtype.val.extend ψ id
  have hψψ' : ψ = ψ' ∘ Subtype.val :=
    funext fun z ↦ (Subtype.val_injective.extend_apply _ _ _).symm
  have hD : ∀ v, D v =
      mfderiv (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ψ' (Z x) v := by
    intro v
    simp only [D]
    rw [hψψ']
    exact Manifold.mfderiv_comp_subtype_val_apply (x := p) v
  have hψ' : MDifferentiableAt (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ψ' (Z x) := by
    have := hψ.mdifferentiableAt (x := p) (by simp)
    rw [hψψ'] at this
    exact Manifold.mdifferentiableAt_comp_subtype_val_iff.1 this
  -- `dψ` fixes the horizontal vectors `(v, 0)`, since `ψ` fixes the zero section near `0_x`
  have hZ : ψ' ∘ Z =ᶠ[𝓝 x] Z := by
    filter_upwards [(contMDiff_zeroSection ℝ (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) (IB := J)
      (n := ∞)).continuous.continuousAt.preimage_mem_nhds (U.isOpen.mem_nhds hz)] with y hy
    rw [Function.comp_apply,
      show ψ' (Z y) = ψ ⟨_, hy⟩ from Subtype.val_injective.extend_apply ψ id ⟨_, hy⟩, hψ0]
  have hhor : ∀ v, D (T.symm (v, 0)) = T.symm (v, 0) := by
    intro v
    have hT : T.symm (v, 0) = mfderiv J (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) Z x v := by
      rw [Bundle.zeroSectionTangentEquiv_symm_eq, Prod.mk_zero_zero, map_zero, add_zero]
    rw [hT, hD, ← mfderiv_comp_apply x hψ' (mdifferentiableAt_zeroSection ℝ _ (IB := J)),
      hZ.mfderiv_eq]
    -- `mfderiv_comp_apply` inserts the identity `tangentSpaceCast` between two equal points
    rfl
  -- `dψ` preserves `ω` at `0_x`
  have hpt : ∀ {y y' : CotangentBundle J L} (_ : y = y') (A B : E × (E →L[ℝ] ℝ)),
      SmoothBundleForm.eval₂ σ y A B = SmoothBundleForm.eval₂ σ y' A B := by
    rintro _ _ rfl _ _
    rfl
  have hσ : ∀ ξ η, SmoothBundleForm.eval₂ σ (Z x) (D ξ) (D η) =
      SmoothBundleForm.eval₂ σ (Z x) ξ η := by
    intro ξ η
    have := congrArg (fun φ ↦ SmoothBundleForm.eval₂ φ p ξ η) hψω
    rw [SmoothForm.eval₂_mpullback ψ hψ σ p ξ η, SmoothForm.eval₂_mpullback _ _ σ p ξ η,
      Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe] at this
    -- `tangentSpaceOpenEquiv` is the identity of the model space, but its body is not exposed
    erw [Manifold.tangentSpaceOpenEquiv_apply, Manifold.tangentSpaceOpenEquiv_apply] at this
    exact (hpt (hψ0 x hz) _ _).symm.trans this
  -- evaluate on `(v, 0)` and `(0, a)`
  obtain ⟨⟨u, a'⟩, hua⟩ : ∃ q, q = T (D (T.symm (0, a))) := ⟨_, rfl⟩
  rw [← hua]
  ext v
  have := hσ (T.symm (v, 0)) (T.symm (0, a))
  rw [hhor, ← T.symm_apply_eq.2 hua, eval₂_symplecticForm_zeroSectionTangentEquiv_symm,
    eval₂_symplecticForm_zeroSectionTangentEquiv_symm] at this
  simpa using this

end SymplecticGeometry.CotangentBundle

end
