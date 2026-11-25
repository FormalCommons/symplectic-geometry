/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.RescaledFamily
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.IsSymplectic
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Restriction
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
public import TauCeti.Geometry.Symplectic.Manifold.SymplecticMap
public import TauCeti.Topology.VectorBundle.Radial

import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ZeroSection
import SymplecticGeometry.Geometry.Symplectic.Cotangent.Bundle.ZeroSection
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
import SymplecticGeometry.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Fiberwise

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

On an open set `V` of covectors whose radial segments from the zero section stay in `U`
(contained in `TauCeti.VectorBundle.radialCore U`), the rescaled family is smooth on
`[0, 1] × V` (`CotangentBundle.contMDiff_vectorBundleRescaledFamily_of_subset_radialCore`).
When `ψ` is moreover an open embedding, each of its slices is a symplectic map from the
restriction of `ω` to `V` to `ω`, and an open embedding
(`CotangentBundle.isSymplecticMap_and_isOpenEmbedding_vectorBundleRescaledFamily`):
for `t > 0` the slice is `m_{1/t} ∘ ψ ∘ m_t`, and `m_c^* ω = c ω`
(`TauCeti.CotangentBundle.mpullback_vectorBundleScalarDiffeomorph_symplecticForm`). Hence each
slice has injective differential (`TauCeti.SmoothTwoForm.IsSymplecticMap.mfderiv_injective`), so
it is an immersion when `L` is finite-dimensional (`ContMDiff.isImmersion_of_injective_mfderiv`),
and a smooth embedding. On `TauCeti.VectorBundle.radialCore U` itself the rescaled family is
therefore a smooth isotopy from the inclusion to `ψ`
(`SymplecticGeometry.CotangentBundle.exists_smoothIsotopy_of_eqOn_zeroSection`).

## Main results

* `SymplecticGeometry.CotangentBundle.vectorBundleRescaledFamily_zero_eq_self`: the slice at
  `t = 0` of the rescaled family of a symplectic map fixing the zero section is the identity.
* `CotangentBundle.contMDiff_vectorBundleRescaledFamily_of_subset_radialCore`: the rescaled
  family is smooth on `[0, 1] × V` for `V` open in a radial core.
* `CotangentBundle.isSymplecticMap_and_isOpenEmbedding_vectorBundleRescaledFamily`:
  on a radial core, the slices of the rescaled family are symplectic open embeddings.
* `SymplecticGeometry.CotangentBundle.exists_smoothIsotopy_of_eqOn_zeroSection`: an open
  symplectic embedding `ψ : U → T*L`, `U ⊇ 0_L` open, that is the identity on `0_L` is joined
  to the inclusion of some open `U' ⊆ U` containing `0_L` by a symplectic smooth isotopy that
  is the identity on `0_L`.

## References

* [P. Seidel, *Floer homology and the symplectic isotopy problem*][Seidel1997Thesis], Lemma 2.2(b).
* M. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 4, §5.
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
  have hD : ∀ v, D v =
      mfderiv (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ψ' (Z x) v := by
    intro v
    simp only [D]
    rw [show ψ = ψ' ∘ Subtype.val from
      funext fun z ↦ (Subtype.val_injective.extend_apply _ _ _).symm]
    exact Manifold.mfderiv_comp_subtype_val_apply (x := p) v
  -- `dψ` fixes the horizontal vectors `(v, 0)`, since `ψ` fixes the zero section near `0_x`
  have hZ : ψ' ∘ Z =ᶠ[𝓝 x] Z := by
    filter_upwards [(contMDiff_zeroSection ℝ (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) (IB := J)
      (n := ∞)).continuous.continuousAt.preimage_mem_nhds (U.isOpen.mem_nhds hz)] with y hy
    rw [Function.comp_apply,
      show ψ' (Z y) = ψ ⟨_, hy⟩ from Subtype.val_injective.extend_apply ψ id ⟨_, hy⟩, hψ0]
  have hhor : ∀ v, D (T.symm (v, 0)) = T.symm (v, 0) := by
    intro v
    rw [hD, Bundle.mfderiv_zeroSectionTangentEquiv_symm_inl
      ((ContMDiffAt.extend_subtypeVal (hψ p) id).mdifferentiableAt (by simp)) hZ,
      Bundle.zeroSectionTangentEquiv_symm_eq, Prod.mk_zero_zero, map_zero, add_zero]
  -- `dψ` preserves `ω` at `0_x`
  have hσ : ∀ ξ η, SmoothBundleForm.eval₂ σ (Z x) (D ξ) (D η) =
      SmoothBundleForm.eval₂ σ (Z x) ξ η := fun ξ η ↦
    (congrArg (fun y ↦ SmoothBundleForm.eval₂ σ y (D ξ) (D η)) (hψ0 x hz)).symm.trans
      (SmoothForm.eval₂_mfderiv_eq_of_mpullback_eq_mpullback_subtype_val hψ hψω p ξ η)
  -- evaluate on `(v, 0)` and `(0, a)`
  obtain ⟨⟨u, a'⟩, hua⟩ : ∃ q, q = T (D (T.symm (0, a))) := ⟨_, rfl⟩
  rw [← hua]
  ext v
  have := hσ (T.symm (v, 0)) (T.symm (0, a))
  rw [hhor, ← T.symm_apply_eq.2 hua, eval₂_symplecticForm_zeroSectionTangentEquiv_symm,
    eval₂_symplecticForm_zeroSectionTangentEquiv_symm] at this
  simpa using this

section RadialCore

variable [IsManifold J ∞ L] [J.Boundaryless] [T2Space L] {U V : Opens (CotangentBundle J L)}

/-- **Smoothness of the rescaled family on a radial core.** Let `L` be a Hausdorff manifold
without boundary, `U` an open set of `T*L` and `ψ : U → T*L` a smooth map that fixes every point
of the zero section lying in `U`. On an open set `V` of covectors whose radial segments lie in
`U`, the rescaled family `(t, z) ↦ vectorBundleRescaledFamily ψ (z, t)` is smooth on
`[0, 1] × V`. -/
theorem contMDiff_vectorBundleRescaledFamily_of_subset_radialCore
    (hV : (V : Set (CotangentBundle J L)) ⊆ VectorBundle.radialCore U)
    {ψ : U → CotangentBundle J L}
    (hψ : ContMDiff (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ ψ)
    (hψ0 : ∀ x (hx : zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) x ∈ U),
      ψ ⟨_, hx⟩ = zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) x) :
    ContMDiff ((𝓡∂ 1).prod (J.prod 𝓘(ℝ, E →L[ℝ] ℝ))) (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      fun p : unitInterval × V ↦ vectorBundleRescaledFamily ψ ((p.2 : CotangentBundle J L), p.1) :=
  (contMDiffOn_vectorBundleRescaledFamily (U' := V) (fun z hz t ↦ by
      rw [vectorBundleFiberScaling_apply]
      exact VectorBundle.mem_radialCore.1 (hV hz) t t.prop) hψ hψ0).comp_contMDiff
    ((contMDiff_subtypeVal.comp contMDiff_snd).prodMk contMDiff_fst)
    fun p ↦ ⟨p.2.prop, mem_univ _⟩

/-- **The slices of the rescaled family are symplectic open embeddings.** Let `L` be a Hausdorff
manifold without boundary, `U` an open set of `T*L` containing every zero covector and
`ψ : U → T*L` a smooth open embedding that fixes every point of the zero section and pulls the
canonical symplectic form `ω` back to its restriction to `U`. On an open set `V` of covectors
whose radial segments lie in `U`, every slice `z ↦ vectorBundleRescaledFamily ψ (z, t)` of the
rescaled family is a symplectic map from the restriction of `ω` to `V` to `ω`, and an open
embedding of `V` into `T*L`. -/
theorem isSymplecticMap_and_isOpenEmbedding_vectorBundleRescaledFamily
    (hU : range (zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ)) ⊆ U)
    (hV : (V : Set (CotangentBundle J L)) ⊆ VectorBundle.radialCore U)
    (ψ : C^∞⟮J.prod 𝓘(ℝ, E →L[ℝ] ℝ), U; J.prod 𝓘(ℝ, E →L[ℝ] ℝ), CotangentBundle J L⟯)
    (hψ : IsOpenEmbedding ψ)
    (hψ0 : ∀ x, ψ ⟨_, hU (mem_range_self x)⟩ =
      zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) x)
    (hψω : SmoothForm.mpullback ψ ψ.contMDiff (symplecticForm J L) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (symplecticForm J L))
    (t : unitInterval) :
    SmoothTwoForm.IsSymplecticMap
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (symplecticForm J L))
        (symplecticForm J L)
        (fun z : V ↦ vectorBundleRescaledFamily ψ ((z : CotangentBundle J L), t)) ∧
      IsOpenEmbedding fun z : V ↦ vectorBundleRescaledFamily ψ ((z : CotangentBundle J L), t) := by
  set σ := symplecticForm J L
  have hψ0' : ∀ x (hx : _ ∈ U), ψ ⟨_, hx⟩ = _ := fun x _ ↦ hψ0 x
  have hf : ContMDiff (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      fun z : V ↦ vectorBundleRescaledFamily ψ ((z : CotangentBundle J L), t) :=
    (contMDiff_vectorBundleRescaledFamily_of_subset_radialCore hV ψ.contMDiff hψ0').comp
      (contMDiff_const.prodMk contMDiff_id)
  rw [SmoothTwoForm.isSymplecticMap_iff_mpullback_eq hf]
  rcases eq_or_lt_of_le t.prop.1 with ht | ht
  · -- at `t = 0` the slice is the inclusion of `V`
    obtain rfl : t = 0 := Subtype.ext ht.symm
    have h0 : (fun z : V ↦ vectorBundleRescaledFamily ψ ((z : CotangentBundle J L), 0)) =
        Subtype.val := funext fun z ↦
      vectorBundleRescaledFamily_zero_eq_self ψ.contMDiff hψ0' hψω (hU (mem_range_self _))
    refine ⟨SmoothForm.mpullback_congr _ _ h0 σ, ?_⟩
    rw [h0]
    exact V.isOpen.isOpenEmbedding_subtypeVal
  -- for `t > 0` the slice is `m_{1/t} ∘ ψ ∘ m_t`, with `m_t` seen as a map `V → U`
  set m := vectorBundleScalarDiffeomorph (I := J) (n := ∞) (F := E →L[ℝ] ℝ)
    (V := fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) (fun _ ↦ (t : ℝ)) contMDiff_const
    (fun _ ↦ ht.ne')
  set D := vectorBundleScalarDiffeomorph (I := J) (n := ∞) (F := E →L[ℝ] ℝ)
    (V := fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) (fun _ ↦ (t : ℝ)⁻¹) contMDiff_const
    (fun _ ↦ inv_ne_zero ht.ne')
  have hstar : ∀ z : V, vectorBundleFiberScaling (E →L[ℝ] ℝ)
      (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) ((z : CotangentBundle J L), t) ∈ U := fun z ↦ by
    rw [vectorBundleFiberScaling_apply]
    exact VectorBundle.mem_radialCore.1 (hV z.prop) t t.prop
  let g : V → U := fun z ↦ ⟨_, hstar z⟩
  have hgm : Subtype.val ∘ g = m ∘ Subtype.val := funext fun z ↦ by
    simp [g, m, vectorBundleFiberScaling_apply, vectorBundleScalarDiffeomorph_apply]
  have hg : ContMDiff (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ g :=
    (ContMDiff.subtypeVal_comp_iff U g).1 (hgm ▸ m.contMDiff.comp contMDiff_subtypeVal)
  have hfg : (fun z : V ↦ vectorBundleRescaledFamily ψ ((z : CotangentBundle J L), t)) =
      D ∘ ψ ∘ g := funext fun z ↦
    vectorBundleRescaledFamily_of_pos (IB := J) ψ ht z (hstar z)
  refine ⟨?_, ?_⟩
  · rw [SmoothForm.mpullback_congr _ (D.contMDiff.comp (ψ.contMDiff.comp hg)) hfg,
      ← SmoothForm.mpullback_mpullback _ _ (ψ.contMDiff.comp hg) D.contMDiff,
      ← SmoothForm.mpullback_mpullback _ _ hg ψ.contMDiff,
      mpullback_vectorBundleScalarDiffeomorph_symplecticForm, map_smul, hψω, map_smul,
      SmoothForm.mpullback_mpullback_of_comp_eq hg contMDiff_subtypeVal contMDiff_subtypeVal
        m.contMDiff hgm,
      mpullback_vectorBundleScalarDiffeomorph_symplecticForm, map_smul, smul_smul,
      inv_mul_cancel₀ ht.ne', one_smul]
  · rw [hfg]
    refine D.toHomeomorph.isOpenEmbedding.comp (hψ.comp ?_)
    refine (U.isOpen.isOpenEmbedding_subtypeVal.of_comp_iff g).1 ?_
    exact (congrArg IsOpenEmbedding hgm).mpr
      (m.toHomeomorph.isOpenEmbedding.comp V.isOpen.isOpenEmbedding_subtypeVal)

end RadialCore

/-- **A symplectic embedding fixing the zero section is isotopic to the inclusion.** Let `L` be a
finite-dimensional Hausdorff manifold without boundary, `U` an open set of `T*L` containing
every zero covector, and `ψ : U → T*L` a smooth open embedding that fixes every point of the zero
section and pulls the canonical symplectic form `ω` back to its restriction to `U`. Then there is
an open neighbourhood `U' ⊆ U` of the zero section and a smooth isotopy from the inclusion of `U'`
to the restriction of `ψ` to `U'` whose slices pull `ω` back to its restriction to `U'`, fix every
point of the zero section, and are open embeddings. -/
theorem exists_smoothIsotopy_of_eqOn_zeroSection [IsManifold J ∞ L] [J.Boundaryless] [T2Space L]
    [FiniteDimensional ℝ E] {U : Opens (CotangentBundle J L)}
    (hU : range (zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ)) ⊆ U)
    (ψ : C^∞⟮J.prod 𝓘(ℝ, E →L[ℝ] ℝ), U; J.prod 𝓘(ℝ, E →L[ℝ] ℝ), CotangentBundle J L⟯)
    (hψ : IsOpenEmbedding ψ)
    (hψ0 : ∀ x, ψ ⟨_, hU (mem_range_self x)⟩ =
      zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) x)
    (hψω : SmoothForm.mpullback ψ ψ.contMDiff (symplecticForm J L) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (symplecticForm J L)) :
    ∃ (U' : Opens (CotangentBundle J L)) (hU' : U' ≤ U)
      (hzero : range (zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ)) ⊆ U')
      (F : SmoothIsotopy (ContMDiffMap.id.restrict U')
        (ψ.comp ⟨Opens.inclusion hU', contMDiff_inclusion hU'⟩)),
      F.IsSymplectic (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (symplecticForm J L))
        (symplecticForm J L) ∧
      (∀ (t : unitInterval) x, F (t, ⟨_, hzero (mem_range_self x)⟩) =
        zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) x) ∧
      ∀ t : unitInterval, IsOpenEmbedding fun z : U' ↦ F (t, z) := by
  -- the neighbourhood: the vectors whose radial segment stays in `U`
  let U' : Opens (CotangentBundle J L) :=
    ⟨VectorBundle.radialCore (U : Set (CotangentBundle J L)),
      VectorBundle.isOpen_radialCore U.isOpen⟩
  have hV : (U' : Set (CotangentBundle J L)) ⊆ VectorBundle.radialCore U := subset_rfl
  have hzero : range (zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ)) ⊆ U' := by
    rintro _ ⟨x, rfl⟩
    exact (VectorBundle.zeroSection_mem_radialCore x).2 (hU (mem_range_self x))
  have hψ0' : ∀ x (hx : _ ∈ U), ψ ⟨_, hx⟩ = _ := fun x _ ↦ hψ0 x
  have hR := contMDiff_vectorBundleRescaledFamily_of_subset_radialCore hV ψ.contMDiff hψ0'
  have hf : ∀ t : unitInterval, ContMDiff (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      fun z : U' ↦ vectorBundleRescaledFamily ψ ((z : CotangentBundle J L), t) := fun t ↦
    hR.comp (contMDiff_const.prodMk contMDiff_id)
  have hslice :=
    isSymplecticMap_and_isOpenEmbedding_vectorBundleRescaledFamily hU hV ψ hψ hψ0 hψω
  refine ⟨U', VectorBundle.radialCore_subset _, hzero,
    { toContMDiffMap := ⟨_, hR⟩
      map_zero_left := fun z ↦ by
        rw [ContMDiffMap.restrict_apply, ContMDiffMap.id_apply]
        exact vectorBundleRescaledFamily_zero_eq_self ψ.contMDiff hψ0' hψω
          (hU (mem_range_self _))
      map_one_left := fun z ↦
        vectorBundleRescaledFamily_one ψ ⟨z, VectorBundle.radialCore_subset _ z.prop⟩
      -- every slice has injective differential, since it pulls back a nondegenerate form
      isSmoothEmbedding := fun t ↦ ⟨(hf t).isImmersion_of_injective_mfderiv (by simp)
        ((hslice t).1.mfderiv_injective
          (isSymplectic_symplecticForm.isNondegenerate.mpullback_subtype_val U')),
        (hslice t).2.isEmbedding⟩ },
    SmoothIsotopy.isSymplectic_def.2 fun t ↦ ?_, fun t x ↦ ?_, fun t ↦ (hslice t).2⟩
  · -- the slices of the isotopy are those of the rescaled family, by construction
    have h := congrArg Subtype.val ((SmoothTwoForm.isSymplecticMap_iff_mpullback_eq (hf t)).1
      (hslice t).1)
    rwa [SmoothForm.coe_mpullback] at h
  · exact vectorBundleRescaledFamily_zeroSection _ (hψ0 x) t

end SymplecticGeometry.CotangentBundle

end
