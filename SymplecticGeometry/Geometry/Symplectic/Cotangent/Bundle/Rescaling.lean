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

import SymplecticGeometry.Geometry.Manifold.Diffeomorph.NestedOpens
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ZeroSection
import SymplecticGeometry.Geometry.Symplectic.Cotangent.Bundle.ZeroSection
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
import TauCeti.Geometry.Symplectic.Manifold.Opens
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Fiberwise
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Diffeomorph
import TauCeti.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph
import TauCeti.Topology.Compactness.Compact
import SymplecticGeometry.Topology.VectorBundle.Basic
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Opens
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth

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
`[0, 1] × V` (`SymplecticGeometry.contMDiff_vectorBundleRescaledFamily_of_subset_radialCore`),
and its slice at `t = 0` is the inclusion of `V`
(`SymplecticGeometry.CotangentBundle.vectorBundleRescaledFamily_zero_comp_subtypeVal`).
For `t > 0` its slice is `m_{1/t} ∘ ψ ∘ m_t`
(`SymplecticGeometry.vectorBundleRescaledFamily_comp_subtypeVal_of_subset_radialCore`), and
`m_c^* ω = c ω` (`TauCeti.CotangentBundle.mpullback_vectorBundleScalarDiffeomorph_symplecticForm`).
So every slice is a symplectic map from the restriction of `ω` to `V` to `ω`
(`SymplecticGeometry.CotangentBundle.isSymplecticMap_vectorBundleRescaledFamily`), and, when `ψ`
is an open embedding, an open embedding
(`SymplecticGeometry.CotangentBundle.isOpenEmbedding_vectorBundleRescaledFamily`). Hence each
slice has injective differential (`TauCeti.SmoothTwoForm.IsSymplecticMap.mfderiv_injective`), so
it is an immersion when `L` is finite-dimensional (`ContMDiff.isImmersion_of_injective_mfderiv`),
and a smooth embedding. On `TauCeti.VectorBundle.radialCore U` itself the rescaled family is
therefore a smooth isotopy from the inclusion to `ψ`
(`SymplecticGeometry.CotangentBundle.exists_smoothIsotopy_of_eqOn_zeroSection`).

Two diffeomorphisms `ι₀ : U₀ ≃ V₀`, `ι₁ : U₁ ≃ V₁` from neighbourhoods of the zero section onto
open sets of a manifold `M` with a two-form `Ω`, each pulling `Ω` back to `c • ω` for one
`c ≠ 0`, and agreeing on the zero section, differ near the zero section by
`ψ = ι₁⁻¹ ∘ ι₀`. This map is defined on the open set of points of `U₀` that `ι₀` sends into
`V₁`, fixes the zero section and pulls `c • ω`, hence `ω`, back to its restriction. Its isotopy
`ψ_t` to the inclusion, from the previous theorem, fixes every `0_x`, for every `t`; since
`[0, 1]` is compact, the points `z` with `ψ_t z ∈ U₁` for all `t` form an open neighbourhood of
the zero section (`TauCeti.isOpen_forall_prodMk_mem`). There `t ↦ ι₁ ∘ ψ_{1-t}` is a symplectic
isotopy from `ι₀` to `ι₁`
(`SymplecticGeometry.CotangentBundle.exists_smoothIsotopy_of_apply_zeroSection_eq_smul`), built
from the reversed isotopy by `TauCeti.SmoothIsotopy.restrict`, `TauCeti.SmoothIsotopy.codRestrict`
and `TauCeti.SmoothIsotopy.postcompSmoothEmbedding`. The
cases `c = 1` and `c = -1` are the uniqueness of Lagrangian neighbourhoods up to isotopy for `ω`
and for `-ω`; neither needs `L` to be compact.

## Main results

* `SymplecticGeometry.CotangentBundle.vectorBundleRescaledFamily_zero_eq_self`: the slice at
  `t = 0` of the rescaled family of a symplectic map fixing the zero section is the identity.
* `SymplecticGeometry.CotangentBundle.isSymplecticMap_vectorBundleRescaledFamily`: on a radial
  core, the slices of the rescaled family are symplectic.
* `SymplecticGeometry.CotangentBundle.isOpenEmbedding_vectorBundleRescaledFamily`: on a radial
  core, the slices of the rescaled family of an open embedding are open embeddings.
* `SymplecticGeometry.CotangentBundle.exists_smoothIsotopy_of_eqOn_zeroSection`: an open
  symplectic embedding `ψ : U → T*L`, `U ⊇ 0_L` open, that is the identity on `0_L` is joined
  to the inclusion of some open `U' ⊆ U` containing `0_L` by a symplectic smooth isotopy that
  is the identity on `0_L`.
* `SymplecticGeometry.CotangentBundle.exists_smoothIsotopy_of_apply_zeroSection_eq`,
  `SymplecticGeometry.CotangentBundle.exists_smoothIsotopy_of_apply_zeroSection_eq_neg`: two
  diffeomorphisms of neighbourhoods of `0_L` onto open sets of `M` that pull `Ω` back to `ω`, or
  both to `-ω`, and agree on `0_L` are joined near `0_L` by a symplectic isotopy of open
  embeddings that is constant on `0_L`; `exists_smoothIsotopy_of_apply_zeroSection_eq_smul`
  is the same for `c • ω`, `c ≠ 0`.

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
      (Function.extend_comp Subtype.val_injective ψ id).symm]
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
      Bundle.zeroSectionTangentEquiv_symm_inl]
  -- `dψ` preserves `ω` at `0_x`
  have hσ : ∀ ξ η, SmoothBundleForm.eval₂ σ (Z x) (D ξ) (D η) =
      SmoothBundleForm.eval₂ σ (Z x) ξ η := fun ξ η ↦
    (congrArg (fun y ↦ SmoothBundleForm.eval₂ σ y (D ξ) (D η)) (hψ0 x hz)).symm.trans
      (SmoothForm.eval₂_mfderiv_eq_of_mpullback_eq_mpullback_subtypeVal hψ hψω p ξ η)
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
  {ψ : U → CotangentBundle J L}

/-- **The slice at `t = 0` on a radial core is the inclusion.** Let `L` be a Hausdorff manifold
without boundary, `U` an open set of `T*L` and `ψ : U → T*L` a smooth map that fixes every point
of the zero section lying in `U` and pulls the canonical symplectic form back to its restriction
to `U`. On a set `V` of covectors whose radial segments lie in `U`, the slice at `t = 0` of the
rescaled family of `ψ` is the inclusion of `V`. -/
theorem vectorBundleRescaledFamily_zero_comp_subtypeVal
    (hV : (V : Set (CotangentBundle J L)) ⊆ VectorBundle.radialCore U)
    (hψ : ContMDiff (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ ψ)
    (hψ0 : ∀ x (hx : zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) x ∈ U),
      ψ ⟨_, hx⟩ = zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) x)
    (hψω : SmoothForm.mpullback ψ hψ (symplecticForm J L) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (symplecticForm J L)) :
    (fun z : V ↦ vectorBundleRescaledFamily ψ ((z : CotangentBundle J L), 0)) = Subtype.val :=
  funext fun z ↦ vectorBundleRescaledFamily_zero_eq_self hψ hψ0 hψω (by
    simpa [zeroSection_def] using VectorBundle.mem_radialCore.1 (hV z.prop) 0 ⟨le_rfl, zero_le_one⟩)

/-- **The slices of the rescaled family are symplectic.** Let `L` be a Hausdorff manifold without
boundary, `U` an open set of `T*L` and `ψ : U → T*L` a smooth map that fixes every point of the
zero section lying in `U` and pulls the canonical symplectic form `ω` back to its restriction to
`U`. On an open set `V` of covectors whose radial segments lie in `U`, every slice
`z ↦ vectorBundleRescaledFamily ψ (z, t)` of the rescaled family is a symplectic map from the
restriction of `ω` to `V` to `ω`. -/
theorem isSymplecticMap_vectorBundleRescaledFamily
    (hV : (V : Set (CotangentBundle J L)) ⊆ VectorBundle.radialCore U)
    (hψ : ContMDiff (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ ψ)
    (hψ0 : ∀ x (hx : zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) x ∈ U),
      ψ ⟨_, hx⟩ = zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) x)
    (hψω : SmoothForm.mpullback ψ hψ (symplecticForm J L) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (symplecticForm J L))
    (t : unitInterval) :
    SmoothTwoForm.IsSymplecticMap
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (symplecticForm J L))
      (symplecticForm J L)
      (fun z : V ↦ vectorBundleRescaledFamily ψ ((z : CotangentBundle J L), t)) := by
  set σ := symplecticForm J L
  have hf : ContMDiff (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      fun z : V ↦ vectorBundleRescaledFamily ψ ((z : CotangentBundle J L), t) :=
    (contMDiff_vectorBundleRescaledFamily_of_subset_radialCore hV hψ hψ0).comp
      (contMDiff_const.prodMk contMDiff_id)
  rw [SmoothTwoForm.isSymplecticMap_iff_mpullback_eq hf]
  rcases eq_or_lt_of_le t.prop.1 with ht | ht
  · obtain rfl : t = 0 := Subtype.ext ht.symm
    exact SmoothForm.mpullback_congr _ _
      (vectorBundleRescaledFamily_zero_comp_subtypeVal hV hψ hψ0 hψω) σ
  -- for `t > 0` the slice is `m_{1/t} ∘ ψ ∘ m_t`, and `m_c` pulls `ω` back to `c ω`
  set m := vectorBundleScalarDiffeomorph (I := J) (n := ∞) (F := E →L[ℝ] ℝ)
    (V := fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) (fun _ ↦ (t : ℝ)) contMDiff_const
    (fun _ ↦ ht.ne')
  set D := vectorBundleScalarDiffeomorph (I := J) (n := ∞) (F := E →L[ℝ] ℝ)
    (V := fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) (fun _ ↦ (t : ℝ)⁻¹) contMDiff_const
    (fun _ ↦ inv_ne_zero ht.ne')
  set g : V → U := fun z ↦
    ⟨_, mapsTo_vectorBundleScalarDiffeomorph_of_subset_radialCore (IB := J) hV ht z.prop⟩
  have hgm : Subtype.val ∘ g = m ∘ Subtype.val := rfl
  have hg : ContMDiff (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ g :=
    (ContMDiff.subtypeVal_comp_iff U g).1 (m.contMDiff.comp contMDiff_subtypeVal)
  rw [SmoothForm.mpullback_congr _ (D.contMDiff.comp (hψ.comp hg))
      (vectorBundleRescaledFamily_comp_subtypeVal_of_subset_radialCore (IB := J) hV ψ ht),
    ← SmoothForm.mpullback_mpullback _ _ (hψ.comp hg) D.contMDiff,
    ← SmoothForm.mpullback_mpullback _ _ hg hψ,
    mpullback_vectorBundleScalarDiffeomorph_symplecticForm, map_smul, hψω, map_smul,
    SmoothForm.mpullback_mpullback_of_comp_eq hg contMDiff_subtypeVal contMDiff_subtypeVal
      m.contMDiff hgm,
    mpullback_vectorBundleScalarDiffeomorph_symplecticForm, map_smul, smul_smul,
    inv_mul_cancel₀ ht.ne', one_smul]

/-- **The slices of the rescaled family are open embeddings.** Let `L` be a Hausdorff manifold
without boundary, `U` an open set of `T*L` and `ψ : U → T*L` a smooth open embedding that fixes
every point of the zero section lying in `U` and pulls the canonical symplectic form back to its
restriction to `U`. On an open set `V` of covectors whose radial segments lie in `U`, every slice
`z ↦ vectorBundleRescaledFamily ψ (z, t)` of the rescaled family is an open embedding of `V`
into `T*L`. -/
theorem isOpenEmbedding_vectorBundleRescaledFamily
    (hV : (V : Set (CotangentBundle J L)) ⊆ VectorBundle.radialCore U)
    (hψ : ContMDiff (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ ψ)
    (hψe : IsOpenEmbedding ψ)
    (hψ0 : ∀ x (hx : zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) x ∈ U),
      ψ ⟨_, hx⟩ = zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) x)
    (hψω : SmoothForm.mpullback ψ hψ (symplecticForm J L) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (symplecticForm J L))
    (t : unitInterval) :
    IsOpenEmbedding fun z : V ↦ vectorBundleRescaledFamily ψ ((z : CotangentBundle J L), t) := by
  rcases eq_or_lt_of_le t.prop.1 with ht | ht
  · obtain rfl : t = 0 := Subtype.ext ht.symm
    rw [vectorBundleRescaledFamily_zero_comp_subtypeVal hV hψ hψ0 hψω]
    exact V.isOpen.isOpenEmbedding_subtypeVal
  -- for `t > 0` the slice is `m_{1/t} ∘ ψ ∘ m_t`, a composite of open embeddings
  set m := vectorBundleScalarDiffeomorph (I := J) (n := ∞) (F := E →L[ℝ] ℝ)
    (V := fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) (fun _ ↦ (t : ℝ)) contMDiff_const
    (fun _ ↦ ht.ne')
  rw [vectorBundleRescaledFamily_comp_subtypeVal_of_subset_radialCore (IB := J) hV ψ ht]
  refine (Diffeomorph.toHomeomorph _).isOpenEmbedding.comp (hψe.comp ?_)
  refine (U.isOpen.isOpenEmbedding_subtypeVal.of_comp_iff _).1 ?_
  exact m.toHomeomorph.isOpenEmbedding.comp V.isOpen.isOpenEmbedding_subtypeVal

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
        (ψ.comp (SmoothEmbedding.inclusion hU').toContMDiffMap)),
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
  have hsymp := isSymplecticMap_vectorBundleRescaledFamily hV ψ.contMDiff hψ0' hψω
  have hemb := isOpenEmbedding_vectorBundleRescaledFamily hV ψ.contMDiff hψ hψ0' hψω
  refine ⟨U', VectorBundle.radialCore_subset _, hzero,
    { toContMDiffMap := ⟨_, hR⟩
      map_zero_left := fun z ↦ by
        rw [ContMDiffMap.restrict_apply, ContMDiffMap.id_apply]
        exact vectorBundleRescaledFamily_zero_eq_self ψ.contMDiff hψ0' hψω
          (hU (mem_range_self _))
      map_one_left := fun z ↦ by
        rw [ContMDiffMap.comp_apply, SmoothEmbedding.coe_toContMDiffMap,
          SmoothEmbedding.inclusion_apply (VectorBundle.radialCore_subset _)]
        exact vectorBundleRescaledFamily_one ψ ⟨z, VectorBundle.radialCore_subset _ z.prop⟩
      -- every slice has injective differential, since it pulls back a nondegenerate form
      isSmoothEmbedding := fun t ↦ ⟨(hf t).isImmersion_of_injective_mfderiv (by simp)
        ((hsymp t).mfderiv_injective
          (isSymplectic_symplecticForm.isNondegenerate.mpullback_subtype_val U')),
        (hemb t).isEmbedding⟩ },
    SmoothIsotopy.isSymplectic_def.2 fun t ↦ ?_, fun t x ↦ ?_, fun t ↦ hemb t⟩
  · -- the slices of the isotopy are those of the rescaled family, by construction
    exact (SmoothForm.mpullback_eq_iff _).1
      ((SmoothTwoForm.isSymplecticMap_iff_mpullback_eq (hf t)).1 (hsymp t))
  · exact vectorBundleRescaledFamily_zeroSection _ (hψ0 x) t

section TwoEmbeddings

variable [IsManifold J ∞ L]
  {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  [TopologicalSpace HM] {I : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M]
  {Ω : SmoothTwoForm I M} {c : ℝ} {U₀ U₁ : Opens (CotangentBundle J L)} {V₀ V₁ : Opens M}

/-- The map `ι₁⁻¹ ∘ ι₀`, on the open set of points of `U₀` that `ι₀` maps into `V₁`, is an open
embedding that fixes the zero section and preserves the canonical symplectic form. -/
private theorem exists_symm_comp_of_apply_zeroSection_eq (hc : c ≠ 0)
    (ι₀ : U₀ ≃ₘ⟮J.prod 𝓘(ℝ, E →L[ℝ] ℝ), I⟯ V₀) (ι₁ : U₁ ≃ₘ⟮J.prod 𝓘(ℝ, E →L[ℝ] ℝ), I⟯ V₁)
    (h₀ : SmoothForm.mpullback ι₀ ι₀.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal Ω) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (c • symplecticForm J L))
    (h₁ : SmoothForm.mpullback ι₁ ι₁.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal Ω) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (c • symplecticForm J L))
    (hU₀ : range (zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ)) ⊆ U₀)
    (hU₁ : range (zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ)) ⊆ U₁)
    (h : ∀ x, (ι₀ ⟨_, hU₀ (mem_range_self x)⟩ : M) = ι₁ ⟨_, hU₁ (mem_range_self x)⟩) :
    ∃ (W : Opens (CotangentBundle J L)) (hW : W ≤ U₀)
      (hzW : range (zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ)) ⊆ W)
      (ψ : C^∞⟮J.prod 𝓘(ℝ, E →L[ℝ] ℝ), W; J.prod 𝓘(ℝ, E →L[ℝ] ℝ), CotangentBundle J L⟯),
      IsOpenEmbedding ψ ∧
      (∀ x, ψ ⟨_, hzW (mem_range_self x)⟩ =
        zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) x) ∧
      SmoothForm.mpullback ψ ψ.contMDiff (symplecticForm J L) =
        SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (symplecticForm J L) ∧
      ∀ z, ∃ hz : ψ z ∈ U₁, (ι₁ ⟨ψ z, hz⟩ : M) = ι₀ (Opens.inclusion hW z) := by
  -- the open set of the points of `U₀` that `ι₀` maps into `V₁`
  let W : Opens (CotangentBundle J L) := Opens.imageVal
    ⟨(fun z : U₀ ↦ (ι₀ z : M)) ⁻¹' V₁,
      V₁.isOpen.preimage (continuous_subtypeVal.comp ι₀.continuous)⟩
  have hW : W ≤ U₀ := Opens.imageVal_le _
  have hzW : range (zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ)) ⊆ W := by
    rintro _ ⟨x, rfl⟩
    exact Opens.mem_imageVal.2 ⟨hU₀ (mem_range_self x),
      Opens.mem_mk.2 <| mem_preimage.2 <| (h x).symm ▸ (ι₁ _).property⟩
  let k : W → V₁ := fun z ↦ ⟨ι₀ (Opens.inclusion hW z), (Opens.mem_imageVal.1 z.property).2⟩
  have hk : ContMDiff (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I ∞ k := by
    have h₀k : ContMDiff (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I ∞ fun z : W ↦ (ι₀ (Opens.inclusion hW z) : M) :=
      contMDiff_subtypeVal.comp (ι₀.contMDiff.comp (contMDiff_inclusion hW))
    exact (ContMDiff.subtypeVal_comp_iff V₁ k).1 h₀k
  let ψ : C^∞⟮J.prod 𝓘(ℝ, E →L[ℝ] ℝ), W; J.prod 𝓘(ℝ, E →L[ℝ] ℝ), CotangentBundle J L⟯ :=
    ⟨fun z ↦ (ι₁.symm (k z) : CotangentBundle J L),
      contMDiff_subtypeVal.comp (ι₁.symm.contMDiff.comp hk)⟩
  have hke : IsOpenEmbedding k :=
    (V₁.isOpen.isOpenEmbedding_subtypeVal.of_comp_iff k).1
      (V₀.isOpen.isOpenEmbedding_subtypeVal.comp (ι₀.toHomeomorph.isOpenEmbedding.comp
        (Opens.isOpenEmbedding_of_le hW)))
  -- `ψ` pulls `c • ω` back to its restriction, hence also `ω`
  have hψc : SmoothForm.mpullback ψ ψ.contMDiff (c • symplecticForm J L) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (c • symplecticForm J L) := by
    have hψk : SmoothForm.mpullback ψ ψ.contMDiff (c • symplecticForm J L) =
        SmoothForm.mpullback k hk (SmoothForm.mpullback ι₁.symm ι₁.symm.contMDiff
          (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (c • symplecticForm J L))) := by
      rw [SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback]
      exact SmoothForm.mpullback_congr _ _ rfl _
    rw [hψk, SmoothForm.mpullback_symm_eq_of_mpullback_eq h₁,
      SmoothForm.mpullback_mpullback_of_comp_eq hk contMDiff_subtypeVal (contMDiff_inclusion hW)
        (contMDiff_subtypeVal.comp ι₀.contMDiff) rfl, ← SmoothForm.mpullback_mpullback _ _
        ι₀.contMDiff contMDiff_subtypeVal, h₀, SmoothForm.mpullback_mpullback]
    exact SmoothForm.mpullback_congr _ _ rfl _
  refine ⟨W, hW, hzW, ψ,
    U₁.isOpen.isOpenEmbedding_subtypeVal.comp (ι₁.symm.toHomeomorph.isOpenEmbedding.comp hke),
    fun x ↦ ?_, ?_, fun z ↦ ⟨(ι₁.symm (k z)).property, ?_⟩⟩
  · have hkx : k ⟨_, hzW (mem_range_self x)⟩ = ι₁ ⟨_, hU₁ (mem_range_self x)⟩ := Subtype.ext (h x)
    simp only [ψ, ContMDiffMap.coeFn_mk, hkx, Diffeomorph.symm_apply_apply]
  · rw [map_smul, map_smul] at hψc
    exact smul_right_injective _ hc hψc
  · simp only [ψ, ContMDiffMap.coeFn_mk, Subtype.coe_eta, Diffeomorph.apply_symm_apply, k]

/-- Pulling `Ω` back along `ι₁ ∘ q`, for a map `q` into `U₁`, gives `c` times the pullback of the
canonical form along `q`, when `ι₁` pulls `Ω` back to `c` times the canonical form. -/
private theorem mpullback_subtypeVal_comp_comp {P : Type*} [TopologicalSpace P]
    [ChartedSpace (ModelProd H (E →L[ℝ] ℝ)) P] [IsManifold (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ P]
    (ι₁ : U₁ ≃ₘ⟮J.prod 𝓘(ℝ, E →L[ℝ] ℝ), I⟯ V₁)
    (h₁ : SmoothForm.mpullback ι₁ ι₁.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal Ω) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (c • symplecticForm J L))
    {q : P → U₁} (hq : ContMDiff (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ q) :
    SmoothForm.mpullback (Subtype.val ∘ ι₁ ∘ q)
        (contMDiff_subtypeVal.comp (ι₁.contMDiff.comp hq)) Ω =
      c • SmoothForm.mpullback (Subtype.val ∘ q) (contMDiff_subtypeVal.comp hq)
        (symplecticForm J L) := by
  rw [← SmoothForm.mpullback_mpullback _ _ (ι₁.contMDiff.comp hq) contMDiff_subtypeVal,
    ← SmoothForm.mpullback_mpullback _ _ hq ι₁.contMDiff, h₁, SmoothForm.mpullback_mpullback,
    map_smul]

variable [J.Boundaryless] [T2Space L] [FiniteDimensional ℝ E] [FiniteDimensional ℝ EM]
  [I.Boundaryless]

/-- **Uniqueness of Lagrangian neighbourhoods up to isotopy, for a multiple of the canonical
form.** Let `L` be a finite-dimensional Hausdorff manifold without boundary, `M` a manifold
without boundary modelled on a finite-dimensional space, `Ω` a two-form on `M` and `c ≠ 0`. Let
`ι₀ : U₀ ≃ V₀` and `ι₁ : U₁ ≃ V₁` be diffeomorphisms from open sets of `T*L` containing the zero
section onto open sets of `M`, each pulling the restriction of `Ω` back to the restriction of
`c • ω`, `ω` the canonical symplectic form, and taking the same value at every zero covector.
Then there are an open neighbourhood `U ⊆ U₀ ∩ U₁` of the zero section and a smooth isotopy from
the restriction of `ι₀` to `U` to that of `ι₁`, whose slices pull `Ω` back to the restriction of
`c • ω` to `U`, send every zero covector `0_x` to `ι₀ 0_x`, and are open embeddings. -/
theorem exists_smoothIsotopy_of_apply_zeroSection_eq_smul (hc : c ≠ 0)
    (ι₀ : U₀ ≃ₘ⟮J.prod 𝓘(ℝ, E →L[ℝ] ℝ), I⟯ V₀) (ι₁ : U₁ ≃ₘ⟮J.prod 𝓘(ℝ, E →L[ℝ] ℝ), I⟯ V₁)
    (h₀ : SmoothForm.mpullback ι₀ ι₀.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal Ω) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (c • symplecticForm J L))
    (h₁ : SmoothForm.mpullback ι₁ ι₁.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal Ω) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (c • symplecticForm J L))
    (hU₀ : range (zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ)) ⊆ U₀)
    (hU₁ : range (zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ)) ⊆ U₁)
    (h : ∀ x, (ι₀ ⟨_, hU₀ (mem_range_self x)⟩ : M) = ι₁ ⟨_, hU₁ (mem_range_self x)⟩) :
    ∃ (U : Opens (CotangentBundle J L)) (hU : U ≤ U₀ ⊓ U₁)
      (hzero : range (zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ)) ⊆ U)
      (G : SmoothIsotopy
        ((SmoothEmbedding.ofOpens (I := I) (n := ∞) V₀).toContMDiffMap.comp
          (ι₀.toContMDiffMap.comp
            (SmoothEmbedding.inclusion (hU.trans inf_le_left)).toContMDiffMap))
        ((SmoothEmbedding.ofOpens (I := I) (n := ∞) V₁).toContMDiffMap.comp
          (ι₁.toContMDiffMap.comp
            (SmoothEmbedding.inclusion (hU.trans inf_le_right)).toContMDiffMap))),
      G.IsSymplectic
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (c • symplecticForm J L)) Ω ∧
      (∀ (t : unitInterval) x,
        G (t, ⟨_, hzero (mem_range_self x)⟩) = ι₀ ⟨_, hU₀ (mem_range_self x)⟩) ∧
      ∀ t : unitInterval, IsOpenEmbedding fun z : U ↦ G (t, z) := by
  obtain ⟨W, hW, hzW, ψ, hψe, hψ0, hψω, hψι⟩ :=
    exists_symm_comp_of_apply_zeroSection_eq hc ι₀ ι₁ h₀ h₁ hU₀ hU₁ h
  obtain ⟨U', hU'W, hzero', F, hFs, hF0, hFe⟩ :=
    exists_smoothIsotopy_of_eqOn_zeroSection hzW ψ hψe hψ0 hψω
  -- shrink `U'` to the points whose whole track under `F` stays in `U₁`
  have hS : IsOpen {z : U' | ∀ t, F (t, z) ∈ U₁} :=
    isOpen_forall_prodMk_mem (ι := id) continuous_id
      (U₁.isOpen.preimage (F.contMDiff.continuous.comp continuous_swap))
  let U : Opens (CotangentBundle J L) := Opens.imageVal ⟨_, hS⟩
  have hUU' : U ≤ U' := Opens.imageVal_le _
  have hmem : ∀ t (z : U), F (t, Opens.inclusion hUU' z) ∈ U₁ := fun t z ↦
    (Opens.mem_imageVal.1 z.property).2 t
  have hzero : range (zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ)) ⊆ U := by
    rintro _ ⟨x, rfl⟩
    refine Opens.mem_imageVal.2 ⟨hzero' (mem_range_self x), fun t ↦ ?_⟩
    rw [hF0]
    exact hU₁ (mem_range_self x)
  have hU : U ≤ U₀ ⊓ U₁ := fun z hz ↦ ⟨hW (hU'W (hUU' hz)), by
    have := hmem 0 ⟨z, hz⟩
    rwa [F.apply_zero, ContMDiffMap.restrict_apply, ContMDiffMap.id_apply] at this⟩
  -- the isotopy `t ↦ ι₁ ∘ F_{1 - t}`, from `ι₀` to `ι₁`: the reversed isotopy `F`, restricted to
  -- `U`, corestricted to `U₁` and postcomposed with `ι₁`
  have hR (p : unitInterval × U) :
      F.symm.restrict hUU' p = F (unitInterval.symm p.1, Opens.inclusion hUU' p.2) := by
    rw [SmoothIsotopy.restrict_apply, SmoothIsotopy.symm_apply]
  let q := (F.symm.restrict hUU').codRestrict U₁ fun p ↦ (hR p).symm ▸ hmem _ _
  have hqv (p : unitInterval × U) :
      (q p : CotangentBundle J L) = F (unitInterval.symm p.1, Opens.inclusion hUU' p.2) :=
    (SmoothIsotopy.coe_codRestrict_apply _ _ _ _).trans (hR p)
  have hee : Manifold.IsSmoothEmbedding (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I ∞ fun w ↦ (ι₁ w : M) :=
    isSmoothEmbedding_subtypeVal_comp_iff.2
      (ι₁.isSmoothEmbedding (by simp))
  refine ⟨U, hU, hzero, q.postcompSmoothEmbedding (fun w ↦ (ι₁ w : M)) hee (by simp) _ _
    (fun z ↦ ?_) (fun z ↦ ?_), SmoothIsotopy.isSymplectic_def.2 fun t ↦ ?_, fun t x ↦ ?_,
    fun t ↦ ?_⟩
  · -- `F_1 = ψ`, and `ι₁ ∘ ψ = ι₀`
    obtain ⟨hz, hψz⟩ := hψι (Opens.inclusion hU'W (Opens.inclusion hUU' z))
    have hq0 : q (0, z) = ⟨_, hz⟩ := by
      refine Subtype.ext ?_
      rw [hqv, unitInterval.symm_zero, F.apply_one, ContMDiffMap.comp_apply,
        SmoothEmbedding.coe_toContMDiffMap, SmoothEmbedding.inclusion_apply]
    rw [← q.apply_zero, hq0, hψz]
    simp
  · have hq1 : q (1, z) = Opens.inclusion (hU.trans inf_le_right) z := by
      refine Subtype.ext ?_
      rw [hqv, unitInterval.symm_one, F.apply_zero, ContMDiffMap.restrict_apply,
        ContMDiffMap.id_apply]
    rw [← q.apply_one, hq1]
    simp
  · -- the slice is `ι₁ ∘ F_{1 - t}`, and `F_{1 - t}` pulls the canonical form back to its
    -- restriction
    have hqt : ContMDiff (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        fun z ↦ q (t, z) := q.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)
    have key := mpullback_subtypeVal_comp_comp ι₁ h₁ hqt
    have hval : SmoothForm.mpullback (Subtype.val ∘ fun z ↦ q (t, z))
        (contMDiff_subtypeVal.comp hqt) (symplecticForm J L) =
        SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (symplecticForm J L) := by
      have hq : (Subtype.val ∘ fun z ↦ q (t, z)) = fun z ↦ F.symm.restrict hUU' (t, z) :=
        funext fun z ↦ SmoothIsotopy.coe_codRestrict_apply _ _ _ _
      rw [SmoothForm.mpullback_eq_iff, hq,
        SmoothIsotopy.isSymplectic_def.1 (hFs.symm.restrict hUU') t,
        SmoothForm.mpullback_mpullback]
      exact congrArg Subtype.val (SmoothForm.mpullback_congr _ _ rfl _)
    rw [hval, ← map_smul] at key
    simp only [SmoothIsotopy.postcompSmoothEmbedding_apply]
    exact (SmoothForm.mpullback_eq_iff _).1 key
  · -- `F` fixes the zero section, and `ι₁ = ι₀` there
    have hqx : q (t, ⟨_, hzero (mem_range_self x)⟩) = ⟨_, hU₁ (mem_range_self x)⟩ := by
      refine Subtype.ext ?_
      rw [hqv]
      exact hF0 _ x
    rw [SmoothIsotopy.postcompSmoothEmbedding_apply, hqx]
    exact (h x).symm
  · have hFU : IsOpenEmbedding fun z ↦ F (unitInterval.symm t, Opens.inclusion hUU' z) :=
      (hFe _).comp (Opens.isOpenEmbedding_of_le hUU')
    have hqe : IsOpenEmbedding fun z ↦ q (t, z) :=
      (U₁.isOpen.isOpenEmbedding_subtypeVal.of_comp_iff _).1
        ((funext fun z ↦ hqv (t, z) : (Subtype.val ∘ fun z ↦ q (t, z)) =
            fun z ↦ F (unitInterval.symm t, Opens.inclusion hUU' z)) ▸ hFU)
    simp only [SmoothIsotopy.postcompSmoothEmbedding_apply]
    exact V₁.isOpen.isOpenEmbedding_subtypeVal.comp (ι₁.toHomeomorph.isOpenEmbedding.comp hqe)

/-- **Uniqueness of Lagrangian neighbourhoods up to isotopy.** Let `L` be a finite-dimensional
Hausdorff manifold without boundary, `M` a manifold without boundary modelled on a
finite-dimensional space and `Ω` a two-form on `M`. Let `ι₀ : U₀ ≃ V₀` and `ι₁ : U₁ ≃ V₁` be
diffeomorphisms from open sets of `T*L` containing the zero section onto open sets of `M`, each
pulling the restriction of `Ω` back to the restriction of the canonical symplectic form `ω`, and
taking the same value at every zero covector. Then there are an open neighbourhood
`U ⊆ U₀ ∩ U₁` of the zero section and a smooth isotopy from the restriction of `ι₀` to `U` to
that of `ι₁`, whose slices pull `Ω` back to the restriction of `ω` to `U`, send every zero
covector `0_x` to `ι₀ 0_x`, and are open embeddings. -/
theorem exists_smoothIsotopy_of_apply_zeroSection_eq
    (ι₀ : U₀ ≃ₘ⟮J.prod 𝓘(ℝ, E →L[ℝ] ℝ), I⟯ V₀) (ι₁ : U₁ ≃ₘ⟮J.prod 𝓘(ℝ, E →L[ℝ] ℝ), I⟯ V₁)
    (h₀ : SmoothForm.mpullback ι₀ ι₀.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal Ω) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (symplecticForm J L))
    (h₁ : SmoothForm.mpullback ι₁ ι₁.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal Ω) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (symplecticForm J L))
    (hU₀ : range (zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ)) ⊆ U₀)
    (hU₁ : range (zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ)) ⊆ U₁)
    (h : ∀ x, (ι₀ ⟨_, hU₀ (mem_range_self x)⟩ : M) = ι₁ ⟨_, hU₁ (mem_range_self x)⟩) :
    ∃ (U : Opens (CotangentBundle J L)) (hU : U ≤ U₀ ⊓ U₁)
      (hzero : range (zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ)) ⊆ U)
      (G : SmoothIsotopy
        ((SmoothEmbedding.ofOpens (I := I) (n := ∞) V₀).toContMDiffMap.comp
          (ι₀.toContMDiffMap.comp
            (SmoothEmbedding.inclusion (hU.trans inf_le_left)).toContMDiffMap))
        ((SmoothEmbedding.ofOpens (I := I) (n := ∞) V₁).toContMDiffMap.comp
          (ι₁.toContMDiffMap.comp
            (SmoothEmbedding.inclusion (hU.trans inf_le_right)).toContMDiffMap))),
      G.IsSymplectic
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (symplecticForm J L)) Ω ∧
      (∀ (t : unitInterval) x,
        G (t, ⟨_, hzero (mem_range_self x)⟩) = ι₀ ⟨_, hU₀ (mem_range_self x)⟩) ∧
      ∀ t : unitInterval, IsOpenEmbedding fun z : U ↦ G (t, z) := by
  simpa only [one_smul] using exists_smoothIsotopy_of_apply_zeroSection_eq_smul one_ne_zero
    ι₀ ι₁ (by rwa [one_smul]) (by rwa [one_smul]) hU₀ hU₁ h

/-- **Uniqueness of Lagrangian neighbourhoods up to isotopy, for the opposite form.** The
statement of `SymplecticGeometry.CotangentBundle.exists_smoothIsotopy_of_apply_zeroSection_eq`
with the opposite `-ω` of the canonical symplectic form in place of `ω`: two diffeomorphisms
`ι₀`, `ι₁` from open neighbourhoods of the zero section of `T*L` onto open sets of `M`, pulling
the restriction of `Ω` back to that of `-ω` and agreeing on the zero section, are joined on an
open neighbourhood `U` of the zero section by a smooth isotopy of open embeddings whose slices
pull `Ω` back to the restriction of `-ω` to `U` and send `0_x` to `ι₀ 0_x`. -/
theorem exists_smoothIsotopy_of_apply_zeroSection_eq_neg
    (ι₀ : U₀ ≃ₘ⟮J.prod 𝓘(ℝ, E →L[ℝ] ℝ), I⟯ V₀) (ι₁ : U₁ ≃ₘ⟮J.prod 𝓘(ℝ, E →L[ℝ] ℝ), I⟯ V₁)
    (h₀ : SmoothTwoForm.IsSymplectomorphism
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (-symplecticForm J L))
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal Ω) ι₀)
    (h₁ : SmoothTwoForm.IsSymplectomorphism
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (-symplecticForm J L))
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal Ω) ι₁)
    (hU₀ : range (zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ)) ⊆ U₀)
    (hU₁ : range (zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ)) ⊆ U₁)
    (h : ∀ x, (ι₀ ⟨_, hU₀ (mem_range_self x)⟩ : M) = ι₁ ⟨_, hU₁ (mem_range_self x)⟩) :
    ∃ (U : Opens (CotangentBundle J L)) (hU : U ≤ U₀ ⊓ U₁)
      (hzero : range (zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ)) ⊆ U)
      (G : SmoothIsotopy
        ((SmoothEmbedding.ofOpens (I := I) (n := ∞) V₀).toContMDiffMap.comp
          (ι₀.toContMDiffMap.comp
            (SmoothEmbedding.inclusion (hU.trans inf_le_left)).toContMDiffMap))
        ((SmoothEmbedding.ofOpens (I := I) (n := ∞) V₁).toContMDiffMap.comp
          (ι₁.toContMDiffMap.comp
            (SmoothEmbedding.inclusion (hU.trans inf_le_right)).toContMDiffMap))),
      G.IsSymplectic
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (-symplecticForm J L)) Ω ∧
      (∀ (t : unitInterval) x,
        G (t, ⟨_, hzero (mem_range_self x)⟩) = ι₀ ⟨_, hU₀ (mem_range_self x)⟩) ∧
      ∀ t : unitInterval, IsOpenEmbedding fun z : U ↦ G (t, z) := by
  have h₀' := SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq.1 h₀
  have h₁' := SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq.1 h₁
  rw [← neg_one_smul ℝ (symplecticForm J L)] at h₀' h₁' ⊢
  exact exists_smoothIsotopy_of_apply_zeroSection_eq_smul (neg_ne_zero.2 one_ne_zero) ι₀ ι₁ h₀' h₁'
    hU₀ hU₁ h

end TwoEmbeddings

end SymplecticGeometry.CotangentBundle

end
