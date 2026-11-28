/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Geometry.Manifold.Diffeomorph
public import SymplecticGeometry.Topology.FiberBundle.Trivialization
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.MapFiber
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Opens
import SymplecticGeometry.Logic.Equiv.Prod
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Topology.FiberBundle.Trivialization
/-!
# Smoothness after a change of the model fibre

Let `f : P → B` be a map of manifolds and `b₀ : B`. A trivialization `T` of `f` whose model fibre
is the fibre `TauCeti.MapFiber f b₀` of `f` over `b₀` has no smoothness of its own, since that
fibre carries no manifold structure in general. Its smoothness is stated through the inclusion of
the fibre into `P`: `T`, followed by that inclusion, is `C^n` on its source, and the inverse of `T`
is the restriction of a map `B × P → P` that is `C^n` on `T.baseSet ×ˢ f ⁻¹' {b₀}`.

Given a trivialization `e` of `f` with model fibre a manifold `Z` and `b₀ ∈ e.baseSet`,
`Bundle.Trivialization.mapFiberHomeomorph` identifies the fibre over `b₀` with `Z`, and Mathlib's
`Bundle.Trivialization.transFiberHomeomorph` changes the model fibre of `T` to `Z` along it. This
file shows that the result is `C^n` with a `C^n` inverse, in the sense of the two fields of Tau
Ceti's `TauCeti.MapFiber.Atlas.IsContMDiff`, when `T` is `C^n` in the sense above and `e` is `C^n`
with a `C^n` inverse. It also shows that changing the model fibre of a `C^n` trivialization with a
`C^n` inverse by a `C^n` diffeomorphism between manifolds keeps both properties, and so does
changing its fibre coordinate over an open set `U` of the base set by a `C^n` family of
diffeomorphisms of the model fibre, given as a homeomorphism of `U × F` over `U`.

## Main results

* `Bundle.Trivialization.contMDiffOn_transFiberHomeomorph_mapFiberHomeomorph`: the trivialization
  with its fibre changed to `Z` is `C^n` on its source.
* `Bundle.Trivialization.contMDiffOn_transFiberHomeomorph_mapFiberHomeomorph_symm`: its inverse is
  `C^n` on its target.
* `Bundle.Trivialization.contMDiffOn_transFiberHomeomorph_toHomeomorph`,
  `Bundle.Trivialization.contMDiffOn_transFiberHomeomorph_toHomeomorph_symm`: changing the fibre
  of a `C^n` trivialization with `C^n` inverse by a `C^n` diffeomorphism keeps both properties.
* `Bundle.Trivialization.contMDiffOn_transFiberwiseHomeomorph`,
  `Bundle.Trivialization.contMDiffOn_transFiberwiseHomeomorph_symm`: the same for the change of
  fibre coordinate by a `C^n` family over an open set `U` of the base set, given by a
  homeomorphism of `U × F` over `U` that is `C^n` with `C^n` inverse.
* `Bundle.Trivialization.coordChangeDiffeomorph_transFiberwiseHomeomorph_symm_left`, `_right`:
  for `Φ (p, v) = (p, χ p v)` with each `χ p` a `C^n` diffeomorphism of `F`, the coordinate
  changes, as diffeomorphisms of `F`, of the trivialization `e` followed by `Φ⁻¹` with another
  trivialization are those of `e` composed with `χ b` or its inverse. So, for instance, if
  each `χ b` lies in a subgroup of the diffeomorphisms of `F` that contains the coordinate
  changes of `e`, it contains the new ones.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §9.
-/

public section

open Set TauCeti
open scoped Manifold ContDiff

namespace Bundle.Trivialization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {J : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] {I : ModelWithCorners 𝕜 EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {EZ : Type*} [NormedAddCommGroup EZ] [NormedSpace 𝕜 EZ]
  {HZ : Type*} [TopologicalSpace HZ] {IZ : ModelWithCorners 𝕜 EZ HZ}
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace HZ Z]
  {n : WithTop ℕ∞} {f : P → B} {b₀ : B} (T : Trivialization (MapFiber f b₀) f)
  {e : Trivialization Z f} (hb₀ : b₀ ∈ e.baseSet)

/-- Let `T` be a trivialization of `f` with model fibre the fibre of `f` over `b₀`, which followed
by the inclusion of that fibre into `P` is `C^n` on its source. If a trivialization `e` with model
fibre `Z` is `C^n` on its source and `b₀ ∈ e.baseSet`, then `T` with its fibre identified with `Z`
by `e` is `C^n` on its source. -/
theorem contMDiffOn_transFiberHomeomorph_mapFiberHomeomorph
    (hT : ContMDiffOn I (J.prod I) n (fun x ↦ ((T x).1, ((T x).2 : P))) T.source)
    (he : ContMDiffOn I (J.prod IZ) n e e.source) :
    ContMDiffOn I (J.prod IZ) n (T.transFiberHomeomorph (e.mapFiberHomeomorph hb₀))
      (T.transFiberHomeomorph (e.mapFiberHomeomorph hb₀)).source := by
  -- The new trivialization reads `x ↦ ((T x).1, (e (T x).2).2)`.
  have h2 : ContMDiffOn I (J.prod IZ) n (fun x ↦ e (T x).2) T.source :=
    he.comp (contMDiff_snd.comp_contMDiffOn hT) fun x _ ↦ e.mem_source.2 <| by
      rw [(T x).2.property]; exact hb₀
  exact ((contMDiff_fst.comp_contMDiffOn hT).prodMk (contMDiff_snd.comp_contMDiffOn h2)).congr
    fun x _ ↦ by simp [transFiberHomeomorph_apply]

/-- Let `T` be a trivialization of `f` with model fibre the fibre of `f` over `b₀`, whose inverse
is the restriction of a map `g : B × P → P` that is `C^n` on `T.baseSet ×ˢ f ⁻¹' {b₀}`. If the
inverse of a trivialization `e` with model fibre `Z` is `C^n` on its target and
`b₀ ∈ e.baseSet`, then the inverse of `T` with its fibre identified with `Z` by `e` is `C^n` on
its target. -/
theorem contMDiffOn_transFiberHomeomorph_mapFiberHomeomorph_symm {g : B × P → P}
    (hg : ContMDiffOn (J.prod I) I n g (T.baseSet ×ˢ (f ⁻¹' {b₀})))
    (hTg : ∀ b ∈ T.baseSet, ∀ x : MapFiber f b₀, T.toOpenPartialHomeomorph.symm (b, x) = g (b, x))
    (he : ContMDiffOn (J.prod IZ) I n e.toOpenPartialHomeomorph.symm e.target) :
    ContMDiffOn (J.prod IZ) I n
      (T.transFiberHomeomorph (e.mapFiberHomeomorph hb₀)).toOpenPartialHomeomorph.symm
      (T.transFiberHomeomorph (e.mapFiberHomeomorph hb₀)).target := by
  -- The inverse is `(b, v) ↦ g (b, e.symm (b₀, v))`.
  have hin : ContMDiffOn (J.prod IZ) (J.prod I) n
      (fun p : B × Z ↦ (p.1, e.toOpenPartialHomeomorph.symm (b₀, p.2))) (T.baseSet ×ˢ univ) :=
    contMDiffOn_fst.prodMk <|
      ((e.contMDiff_fiberInclusionMap he hb₀).comp contMDiff_snd).contMDiffOn
      |>.congr fun p _ ↦ (e.fiberInclusionMap_apply hb₀ p.2).symm
  refine ((hg.comp hin fun p hp ↦ ⟨hp.1, e.proj_symm_apply' hb₀⟩).congr fun p hp ↦ ?_).mono
    fun p hp ↦ ⟨(mem_target _).1 hp, mem_univ _⟩
  simpa using hTg p.1 hp.1 ⟨_, e.proj_symm_apply' hb₀⟩

section Diffeomorph

variable {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF]
  {HF : Type*} [TopologicalSpace HF] {IF : ModelWithCorners 𝕜 EF HF}
  {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {EF' : Type*} [NormedAddCommGroup EF'] [NormedSpace 𝕜 EF']
  {HF' : Type*} [TopologicalSpace HF'] {IF' : ModelWithCorners 𝕜 EF' HF'}
  {F' : Type*} [TopologicalSpace F'] [ChartedSpace HF' F'] {e : Trivialization F f}

/-- Changing the fibre of a trivialization that is `C^n` on its source by a `C^n` diffeomorphism
`F ≃ F'` gives a trivialization that is `C^n` on its source. -/
theorem contMDiffOn_transFiberHomeomorph_toHomeomorph
    (he : ContMDiffOn I (J.prod IF) n e e.source) (φ : F ≃ₘ^n⟮IF, IF'⟯ F') :
    ContMDiffOn I (J.prod IF') n (e.transFiberHomeomorph φ.toHomeomorph)
      (e.transFiberHomeomorph φ.toHomeomorph).source :=
  ((contMDiff_fst.prodMk (φ.contMDiff.comp contMDiff_snd)).comp_contMDiffOn he).congr
    fun x _ ↦ by rw [transFiberHomeomorph_apply, Diffeomorph.coe_toHomeomorph]; rfl

/-- Changing the fibre of a trivialization whose inverse is `C^n` on its target by a `C^n`
diffeomorphism `F ≃ F'` gives a trivialization whose inverse is `C^n` on its target. -/
theorem contMDiffOn_transFiberHomeomorph_toHomeomorph_symm
    (he : ContMDiffOn (J.prod IF) I n e.toOpenPartialHomeomorph.symm e.target)
    (φ : F ≃ₘ^n⟮IF, IF'⟯ F') :
    ContMDiffOn (J.prod IF') I n
      (e.transFiberHomeomorph φ.toHomeomorph).toOpenPartialHomeomorph.symm
      (e.transFiberHomeomorph φ.toHomeomorph).target := by
  refine (he.comp (contMDiff_fst.prodMk (φ.symm.contMDiff.comp contMDiff_snd)).contMDiffOn
    fun p hp ↦ ?_).congr fun p _ ↦ ?_
  · rw [transFiberHomeomorph_target] at hp
    exact e.mem_target.2 hp.1
  · rw [transFiberHomeomorph_symm_apply, Diffeomorph.coe_toHomeomorph_symm]
    rfl

end Diffeomorph

section Fiberwise

variable {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF]
  {HF : Type*} [TopologicalSpace HF] {IF : ModelWithCorners 𝕜 EF HF}
  {F : Type*} [TopologicalSpace F] [ChartedSpace HF F] {e : Trivialization F f}
  {U : TopologicalSpace.Opens B} (hU : (U : Set B) ⊆ e.baseSet) (Φ : U × F ≃ₜ U × F)
  (hΦ : ∀ q, (Φ q).1 = q.1)

/-- Let `e` be a trivialization that is `C^n` on its source, and `Φ` a homeomorphism of `U × F`
over an open set `U` of its base set. If `Φ` is `C^n`, then `e` followed by `Φ` is `C^n` on its
source. -/
theorem contMDiffOn_transFiberwiseHomeomorph (he : ContMDiffOn I (J.prod IF) n e e.source)
    (hΦs : ContMDiff (J.prod IF) (J.prod IF) n Φ) :
    ContMDiffOn I (J.prod IF) n (e.transFiberwiseHomeomorph hU Φ hΦ)
      (e.transFiberwiseHomeomorph hU Φ hΦ).source := by
  let W : TopologicalSpace.Opens P := ⟨f ⁻¹' U, by
    rw [← transFiberwiseHomeomorph_source e hU Φ hΦ]
    exact (e.transFiberwiseHomeomorph hU Φ hΦ).open_source⟩
  have hWe (w : W) : (w : P) ∈ e.source := e.mem_source.2 (hU w.property)
  -- On `W`, `e` followed by `Φ` is `w ↦ (f w, (e w).2)`, then `Φ`, then the inclusion
  -- `U × F → B × F`.
  have hf : ContMDiff I J n fun w : W ↦ f w :=
    ((contMDiff_fst.comp_contMDiffOn he).comp_contMDiff contMDiff_subtypeVal hWe).congr
      fun w ↦ (e.coe_fst' (hU w.property)).symm
  have hk : ContMDiff I (J.prod IF) n fun w : W ↦ ((⟨f w, w.property⟩ : U), (e w).2) :=
    ((TauCeti.ContMDiff.subtypeVal_comp_iff U _).1 hf).prodMk
      (e.contMDiff_snd_subtypeVal he fun _ hw ↦ hWe ⟨_, hw⟩)
  have h : ContMDiff I (J.prod IF) n fun w : W ↦ e.transFiberwiseHomeomorph hU Φ hΦ w :=
    ((contMDiff_subtypeVal.prodMap contMDiff_id).comp (hΦs.comp hk)).congr fun w ↦ by
      rw [transFiberwiseHomeomorph_apply _ _ _ _ (y := (w : P)) w.property]
      exact Prod.ext (congrArg Subtype.val (hΦ (⟨f w, w.property⟩, (e w).2))).symm rfl
  rw [transFiberwiseHomeomorph_source]
  exact contMDiff_subtype_iff.1 h

/-- Let `e` be a trivialization whose inverse is `C^n` on its target, and `Φ` a homeomorphism of
`U × F` over an open set `U` of its base set. If the inverse of `Φ` is `C^n`, then the inverse
of `e` followed by `Φ` is `C^n` on its target. -/
theorem contMDiffOn_transFiberwiseHomeomorph_symm
    (he : ContMDiffOn (J.prod IF) I n e.toOpenPartialHomeomorph.symm e.target)
    (hΦs : ContMDiff (J.prod IF) (J.prod IF) n Φ.symm) :
    ContMDiffOn (J.prod IF) I n
      (e.transFiberwiseHomeomorph hU Φ hΦ).toOpenPartialHomeomorph.symm
      (e.transFiberwiseHomeomorph hU Φ hΦ).target := by
  let V : TopologicalSpace.Opens (B × F) := ⟨(U : Set B) ×ˢ univ, U.isOpen.prod isOpen_univ⟩
  -- On `V`, the inverse is `q ↦ (q.1, q.2) ∈ U × F`, then `Φ⁻¹`, then the inverse of `e`.
  have hk : ContMDiff (J.prod IF) (J.prod IF) n
      fun q : V ↦ ((⟨q.val.1, q.property.1⟩ : U), q.val.2) :=
    ((TauCeti.ContMDiff.subtypeVal_comp_iff U _).1
      (contMDiff_fst.comp contMDiff_subtypeVal)).prodMk (contMDiff_snd.comp contMDiff_subtypeVal)
  have h : ContMDiff (J.prod IF) I n fun q : V ↦
      (e.transFiberwiseHomeomorph hU Φ hΦ).toOpenPartialHomeomorph.symm q :=
    ((e.contMDiff_symm_val_prod he hU).comp (hΦs.comp hk)).congr fun q ↦ by
      have hΦ' (q : U × F) : (Φ.symm q).1 = q.1 := by
        rw [← Homeomorph.coe_symm_toEquiv]
        exact Equiv.fst_symm_apply_of_forall_fst_apply hΦ q
      rw [Function.comp_apply, Function.comp_apply, hΦ',
        transFiberwiseHomeomorph_symm_apply _ _ _ _ q.property.1]
  rw [transFiberwiseHomeomorph_target]
  exact contMDiff_subtype_iff.1 h

/-! In the rest of this section, `Φ (p, v) = (p, χ p v)` for a family `χ` of `C^n`
diffeomorphisms of `F`, and `e` is followed by the inverse of `Φ`, so that over `b ∈ U` the new
trivialization reads the fibre coordinate `v` of `e` as `(χ b)⁻¹ v`. -/

section Family

variable {Φ} {χ : U → F ≃ₘ^n⟮IF, IF⟯ F} (hχ : ∀ q, Φ q = (q.1, χ q.1 q.2))
include hχ

variable {e' : Trivialization F f} (he : ContMDiffOn I (J.prod IF) n e e.source)
  (he_symm : ContMDiffOn (J.prod IF) I n e.toOpenPartialHomeomorph.symm e.target)
  (he' : ContMDiffOn I (J.prod IF) n e' e'.source)
  (he'_symm : ContMDiffOn (J.prod IF) I n e'.toOpenPartialHomeomorph.symm e'.target)
  (hτ : ContMDiffOn I (J.prod IF) n
    (e.transFiberwiseHomeomorph hU Φ.symm (Homeomorph.fst_symm_apply_of_apply_eq_prodMk hχ))
    (e.transFiberwiseHomeomorph hU Φ.symm
      (Homeomorph.fst_symm_apply_of_apply_eq_prodMk hχ)).source)
  (hτ_symm : ContMDiffOn (J.prod IF) I n
    (e.transFiberwiseHomeomorph hU Φ.symm
      (Homeomorph.fst_symm_apply_of_apply_eq_prodMk hχ)).toOpenPartialHomeomorph.symm
    (e.transFiberwiseHomeomorph hU Φ.symm
      (Homeomorph.fst_symm_apply_of_apply_eq_prodMk hχ)).target)
  {b : B} (hb : b ∈ U) (hb' : b ∈ e'.baseSet)

/-- If `Φ (p, v) = (p, χ p v)`, the coordinate change over `b ∈ U` from `e` followed by the
inverse of `Φ` to a trivialization `e'`, as a diffeomorphism of `F`, is `χ b` followed by the
coordinate change from `e`. -/
theorem coordChangeDiffeomorph_transFiberwiseHomeomorph_symm_left :
    coordChangeDiffeomorph (b := b)
        (e.transFiberwiseHomeomorph hU Φ.symm (Homeomorph.fst_symm_apply_of_apply_eq_prodMk hχ))
        e' hτ hτ_symm he' he'_symm (by rwa [transFiberwiseHomeomorph_baseSet]) hb' =
      (χ ⟨b, hb⟩).trans (e.coordChangeDiffeomorph e' he he_symm he' he'_symm (hU hb) hb') :=
  Diffeomorph.ext fun v ↦ by
    rw [coe_coordChangeDiffeomorph,
      coordChange_transFiberwiseHomeomorph_symm_left e hU (χ := fun p ↦ (χ p).toHomeomorph)
        (by simpa using hχ) e' hb,
      Diffeomorph.coe_trans, coe_coordChangeDiffeomorph, Diffeomorph.coe_toHomeomorph]

/-- If `Φ (p, v) = (p, χ p v)`, the coordinate change over a point `b ∈ U` of the base set of a
trivialization `e'`, from `e'` to `e` followed by the inverse of `Φ`, as a diffeomorphism of `F`,
is the coordinate change to `e` followed by the inverse of `χ b`. -/
theorem coordChangeDiffeomorph_transFiberwiseHomeomorph_symm_right :
    e'.coordChangeDiffeomorph (b := b)
        (e.transFiberwiseHomeomorph hU Φ.symm (Homeomorph.fst_symm_apply_of_apply_eq_prodMk hχ))
        he' he'_symm hτ hτ_symm hb' (by rwa [transFiberwiseHomeomorph_baseSet]) =
      (e'.coordChangeDiffeomorph e he' he'_symm he he_symm hb' (hU hb)).trans
        (χ ⟨b, hb⟩).symm :=
  Diffeomorph.ext fun v ↦ by
    rw [coe_coordChangeDiffeomorph,
      coordChange_transFiberwiseHomeomorph_symm_right e hU (χ := fun p ↦ (χ p).toHomeomorph)
        (by simpa using hχ) e' hb hb',
      Diffeomorph.coe_trans, coe_coordChangeDiffeomorph, Diffeomorph.coe_toHomeomorph_symm]

end Family

end Fiberwise

end Bundle.Trivialization

end
