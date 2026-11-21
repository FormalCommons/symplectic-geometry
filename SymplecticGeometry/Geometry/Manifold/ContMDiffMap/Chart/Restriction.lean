/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Comp
public import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Analysis.Calculus.ContDiff.FaaDiBruno

/-!
# Chart derivatives of functions that agree on an open set with a `C^n` map on it

Let `U` be an open subset of a manifold `M`, and let `f : M → F` agree on `U` with a `C^n` map
`g : C^n⟮I, U; 𝓘(𝕜, F), F⟯`. At a point of `U`, the coordinate derivatives of `f` in an ambient
chart of `M` are the Faà di Bruno composite of the derivatives of `g` in the chart of `U` with
those of the chart change
(`ContMDiffMap.iteratedFDerivWithin_eq_taylorComp_of_eqOn_opens`). Hence convergence of such maps
`g` in the weak Whitney topology on `U` controls the ambient coordinate derivatives of the
functions `f` at the points of `U`, jointly with the point
(`ContMDiffMap.tendsto_iteratedFDerivWithin_of_eqOn_opens`). Nothing is assumed about `f` off `U`.

These two results adapt Tau Ceti's `ContMDiffMap.iteratedFDerivWithin_eq_restrict_taylorComp`
and `ContMDiffMap.tendsto_iteratedFDerivWithin_of_restrict`
(`TauCeti/Geometry/Manifold/ContMDiffMap/Chart/Restriction.lean`), which are the special case
`g = f.restrict U` of a `C^n` map `f` on all of `M`; the proofs follow theirs step by step. The
weak Whitney topology is Tau Ceti's, following M. Hirsch, *Differential Topology*, GTM 33,
Chapter 2, §1.

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 2, §1
-/

public section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞ω} [IsManifold I n M]

/-- The coordinate derivatives, in an ambient chart at `x`, of a function that agrees on an open
set `U` with a `C^n` map on `U`, through the chart of `U` at a point `y`. -/
theorem iteratedFDerivWithin_eq_taylorComp_of_eqOn_opens (U : Opens M)
    (g : C^n⟮I, U; 𝓘(𝕜, F), F⟯) (f : M → F) (hfg : ∀ y : U, f y = g y) (x : M) (y : U)
    {z : E} (hz : z ∈ (extChartAt I x).target) (hy : (extChartAt I x).symm z ∈ U)
    (hys : (extChartAt I x).symm z ∈ (extChartAt I (y : M)).source) (m : ℕ) (hm : m ≤ n) :
    iteratedFDerivWithin 𝕜 m (f ∘ (extChartAt I x).symm) (extChartAt I x).target z =
      (ftaylorSeriesWithin 𝕜 (g ∘ (extChartAt I y).symm)
        (extChartAt I y).target (extChartAt I (y : M) ((extChartAt I x).symm z))).taylorComp
        (ftaylorSeriesWithin 𝕜 (extChartAt I (y : M) ∘ (extChartAt I x).symm)
          (extChartAt I x).target z) m := by
  set φ := extChartAt I x
  set ψ := extChartAt I y
  set τ : E → E := extChartAt I (y : M) ∘ φ.symm
  have hτ : Tendsto τ (𝓝[φ.target] z) (𝓝[ψ.target] τ z) :=
    U.tendsto_extChartAt_restrict x y hz hy hys
  have hv : τ z ∈ ψ.target := by
    rw [U.extChartAt_target_eq y]
    exact ⟨(extChartAt I (y : M)).map_source hys, by
      simpa only [τ, Function.comp_apply, mem_preimage, (extChartAt I (y : M)).left_inv hys,
        SetLike.mem_coe] using hy⟩
  have hφ := continuousOn_extChartAt_symm (I := I) x z hz
  -- Near `z`, the function is read through the chart of `U` at `y`.
  have heq : ∀ w, φ.symm w ∈ (extChartAt I (y : M)).source → τ w ∈ ψ.target →
      (f ∘ φ.symm) w = ((g ∘ ψ.symm) ∘ τ) w := by
    intro w hws hwt
    have hval : ((ψ.symm (τ w) : U) : M) = φ.symm w := by
      rw [U.coe_extChartAt_symm_apply y hwt]
      exact (extChartAt I (y : M)).left_inv hws
    simp only [Function.comp_apply, ← hfg, hval]
  have hev : f ∘ φ.symm =ᶠ[𝓝[φ.target] z] (g ∘ ψ.symm) ∘ τ := by
    filter_upwards [hφ.eventually ((isOpen_extChartAt_source (I := I) (y : M)).mem_nhds hys),
      (tendsto_nhdsWithin_iff.mp hτ).2] with w hws hwt
    exact heq w hws hwt
  rw [hev.iteratedFDerivWithin_eq (heq z hys hv)]
  have hg : ContDiffWithinAt 𝕜 n (g ∘ ψ.symm) ψ.target (τ z) := by
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp] using
      g.contDiffWithinAt_extChartAt (y := (0 : F)) hv (by simp)
  have hτd : ContDiffWithinAt 𝕜 n τ φ.target z :=
    (id : C^n⟮I, M; I, M⟯).contDiffWithinAt_extChartAt hz hys
  exact iteratedFDerivWithin_comp_of_eventually_mem hg hτd (uniqueDiffOn_extChartAt_target y)
    (uniqueDiffOn_extChartAt_target x) hz (tendsto_nhdsWithin_iff.mp hτ).2 hm

variable [LocallyCompactSpace E]

/-- Convergence in `C^n⟮I, U; 𝓘(𝕜, F), F⟯` of `C^n` maps on an open set `U` controls, jointly
with the point, the coordinate derivatives in any ambient chart of functions on `M` that agree
with them on `U`, at the points of `U`. -/
theorem tendsto_iteratedFDerivWithin_of_eqOn_opens (U : Opens M) {P : Type*} {l : Filter P}
    {g : P → C^n⟮I, U; 𝓘(𝕜, F), F⟯} {g₀ : C^n⟮I, U; 𝓘(𝕜, F), F⟯} (hg : Tendsto g l (𝓝 g₀))
    {f : P → M → F} {f₀ : M → F} (hfg : ∀ p (y : U), f p y = g p y)
    (hfg₀ : ∀ y : U, f₀ y = g₀ y) (x : M) {z : E} (hz : z ∈ (extChartAt I x).target)
    (hy : (extChartAt I x).symm z ∈ U) (m : ℕ) (hm : m ≤ n) :
    Tendsto (fun q : P × E ↦ iteratedFDerivWithin 𝕜 m (f q.1 ∘ (extChartAt I x).symm)
        (extChartAt I x).target q.2)
      (l ×ˢ 𝓝[(extChartAt I x).target] z)
      (𝓝 (iteratedFDerivWithin 𝕜 m (f₀ ∘ (extChartAt I x).symm) (extChartAt I x).target z)) := by
  let y : U := ⟨(extChartAt I x).symm z, hy⟩
  set φ := extChartAt I x
  set τ : E → E := fun w ↦ extChartAt I (y : M) (φ.symm w)
  have hys : φ.symm z ∈ (extChartAt I (y : M)).source := mem_extChartAt_source (y : M)
  have hv : τ z ∈ (extChartAt I y).target := by
    rw [U.extChartAt_target_eq y]
    exact ⟨(extChartAt I (y : M)).map_source hys, by
      simpa only [τ, mem_preimage, (extChartAt I (y : M)).left_inv hys, SetLike.mem_coe] using hy⟩
  have hτ : Tendsto τ (𝓝[φ.target] z) (𝓝[(extChartAt I y).target] τ z) :=
    U.tendsto_extChartAt_restrict x y hz hy hys
  have hjg (k : ℕ) (hk : k ≤ m) :
      Tendsto (fun q : P × E ↦ ftaylorSeriesWithin 𝕜 (g q.1 ∘ (extChartAt I y).symm)
        (extChartAt I y).target (τ q.2) k) (l ×ˢ 𝓝[φ.target] z)
        (𝓝 (ftaylorSeriesWithin 𝕜 (g₀ ∘ (extChartAt I y).symm) (extChartAt I y).target
          (τ z) k)) := by
    have h := (tendsto_iteratedFDerivWithin_extChartAt (f₀ := g₀)
      (y := (0 : F)) hv (by simp) ((Nat.cast_le.mpr hk).trans hm)).comp (hg.prodMap hτ)
    simpa only [ftaylorSeriesWithin, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.id_comp, Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq] using h
  have hjp (k : ℕ) (hk : k ≤ m) :
      Tendsto (fun q : P × E ↦ ftaylorSeriesWithin 𝕜
        (extChartAt I (y : M) ∘ φ.symm) φ.target q.2 k) (l ×ˢ 𝓝[φ.target] z)
        (𝓝 (ftaylorSeriesWithin 𝕜 (extChartAt I (y : M) ∘ φ.symm) φ.target z k)) :=
    (TauCeti.continuousWithinAt_ftaylorSeriesWithin_extChartAt_comp_symm x y hz hys (k := k)
      ((Nat.cast_le.mpr hk).trans hm)).tendsto.comp tendsto_snd
  have hφ := continuousOn_extChartAt_symm (I := I) x z hz
  have hfdb : ∀ᶠ q : P × E in l ×ˢ 𝓝[φ.target] z,
      (ftaylorSeriesWithin 𝕜 (g q.1 ∘ (extChartAt I y).symm) (extChartAt I y).target
        (τ q.2)).taylorComp (ftaylorSeriesWithin 𝕜 (extChartAt I (y : M) ∘ φ.symm)
          φ.target q.2) m =
        iteratedFDerivWithin 𝕜 m (f q.1 ∘ φ.symm) φ.target q.2 := by
    filter_upwards [tendsto_snd.eventually (hφ.eventually (U.isOpen.mem_nhds hy)),
      tendsto_snd.eventually
        (hφ.eventually ((isOpen_extChartAt_source (I := I) (y : M)).mem_nhds hys)),
      tendsto_snd.eventually self_mem_nhdsWithin] with q hU hS hq
    exact (iteratedFDerivWithin_eq_taylorComp_of_eqOn_opens U (g q.1) (f q.1) (hfg q.1) x y hq hU hS
      m hm).symm
  have h := (Filter.Tendsto.taylorComp hjg (fun k _ hk ↦ hjp k hk)).congr' hfdb
  rwa [← iteratedFDerivWithin_eq_taylorComp_of_eqOn_opens U g₀ f₀ hfg₀ x y hz hy hys m hm] at h


end ContMDiffMap

end
