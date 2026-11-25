/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import SymplecticGeometry.Topology.FiberBundle.ChangeModelFiber
import SymplecticGeometry.Geometry.Manifold.FiberBundle.MapFiber
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
with a `C^n` inverse.

## Main results

* `Bundle.Trivialization.contMDiffOn_transFiberHomeomorph_mapFiberHomeomorph`: the trivialization
  with its fibre changed to `Z` is `C^n` on its source.
* `Bundle.Trivialization.contMDiffOn_transFiberHomeomorph_mapFiberHomeomorph_symm`: its inverse is
  `C^n` on its target.

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
    contMDiffOn_fst.prodMk <| ((e.contMDiff_fiberInclusion he hb₀).comp contMDiff_snd).contMDiffOn
      |>.congr fun p _ ↦ (e.fiberInclusion_apply hb₀ p.2).symm
  refine ((hg.comp hin fun p hp ↦ ⟨hp.1, e.proj_symm_apply' hb₀⟩).congr fun p hp ↦ ?_).mono
    fun p hp ↦ ⟨(mem_target _).1 hp, mem_univ _⟩
  simpa using hTg p.1 hp.1 ⟨_, e.proj_symm_apply' hb₀⟩

end Bundle.Trivialization

end
