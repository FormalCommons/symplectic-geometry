/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization

import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Pullback
import SymplecticGeometry.Topology.FiberBundle.Basic

/-!
# Continuity of the linearization of a section along its zeros

Let `s` be a `C^n` section, `1 ≤ n`, of a vector bundle `E' → X`, and let `g : Y → X` be a
continuous map whose image lies in the zero set of `s`. On the pull-back along `g` of the tangent
bundle of `X`, the map `(y, v) ↦ (g y, L_{g y} v)` into the total space of `E'` is continuous,
where `L_x = TauCeti.sectionLinearization J id s x` is the intrinsic linearization of `s` at the
zero `x` (`SymplecticGeometry.continuous_sectionLinearization_pullback`).

In a trivialization `e` of `E'`, the fibre coordinate of `L_x v` at a zero `x` is the derivative
at `x` of the fibre coordinate of `s` in `e` (Tau Ceti's
`TauCeti.continuousLinearMapAt_comp_sectionLinearization`), and the differentials of a function
that is `C^1` at a point are continuous there on the pulled-back tangent bundle
(`Bundle.Pullback.continuousAt_mfderiv_apply`).

## Main results

* `SymplecticGeometry.continuous_sectionLinearization_pullback`: the linearization of a section
  along a continuous map into its zero set is continuous on the pulled-back tangent bundle.
-/

public section

open Bundle Function Set
open scoped ContDiff Manifold Topology

open TauCeti

namespace SymplecticGeometry

variable {𝕜 V G X F' Y : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [TopologicalSpace G] {J : ModelWithCorners 𝕜 V G}
  [TopologicalSpace X] [ChartedSpace G X]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {E' : X → Type*} [TopologicalSpace (TotalSpace F' E')] [∀ x, AddCommGroup (E' x)]
  [∀ x, Module 𝕜 (E' x)] [∀ x, TopologicalSpace (E' x)] [FiberBundle F' E']
  [VectorBundle 𝕜 F' E'] [TopologicalSpace Y]
  {n : ℕ∞ω} [IsManifold J 1 X] [ContMDiffVectorBundle n F' E' J] {s : ∀ x, E' x}

/-- **The linearization of a section along its zeros is continuous.** For a `C^n` section `s`,
`1 ≤ n`, and a continuous map `g : Y → X` into the zero set of `s`, the map
`(y, v) ↦ (g y, L_{g y} v)` from the pull-back along `g` of the tangent bundle of `X` to the total
space of `E'` is continuous, where `L_x` is the linearization of `s` at `x`. -/
theorem continuous_sectionLinearization_pullback (hn : 1 ≤ n)
    (hs : ContMDiff J (J.prod 𝓘(𝕜, F')) n fun x ↦ TotalSpace.mk' F' x (s x))
    {g : Y → X} (hg : Continuous g) (hgs : ∀ y, s (g y) = 0) :
    Continuous fun p : TotalSpace V (g *ᵖ (TangentSpace J)) ↦
      TotalSpace.mk' F' (g p.proj)
        (sectionLinearization (F := F') J _root_.id s (g p.proj) p.snd) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  have hproj : Continuous fun p : TotalSpace V (g *ᵖ (TangentSpace J)) ↦ g p.proj :=
    hg.comp (Pullback.continuous_proj V (TangentSpace J) g)
  refine (FiberBundle.continuousAt_totalSpace F' _).2 ⟨hproj.continuousAt, ?_⟩
  set e := trivializationAt F' E' (g p₀.proj)
  -- In `e`, the fibre coordinate of `L_x v` is the derivative at `x` of the fibre coordinate `t`
  -- of `s`, a `C^n` function on the base set of `e`.
  set t : X → F' := fun x ↦ (e ⟨x, s x⟩).2
  have ht (x : X) (hx : x ∈ e.baseSet) : ContMDiffAt J 𝓘(𝕜, F') n t x :=
    ((e.contMDiffAt_iff (f := fun y ↦ TotalSpace.mk' F' y (s y)) (e.mem_source.2 hx)).1
      (hs x)).2
  have key (y : Y) (hy : g y ∈ e.baseSet) (w : TangentSpace J (g y)) :
      (e (TotalSpace.mk' F' (g y) (sectionLinearization (F := F') J _root_.id s (g y) w))).2 =
        mfderiv J 𝓘(𝕜, F') t (g y) w := by
    have hL := DFunLike.congr_fun (continuousLinearMapAt_comp_sectionLinearization
      (b := _root_.id) (s := s) continuousAt_id hy ((ht _ hy).mdifferentiableAt
        (zero_lt_one.trans_le hn).ne') (hgs y)) w
    rwa [ContinuousLinearMap.comp_apply,
      e.continuousLinearMapAt_apply_of_mem 𝕜 (b := _root_.id (g y)) hy, mvfderiv,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      NormedSpace.fromTangentSpace_apply] at hL
  have heq : (fun p : TotalSpace V (g *ᵖ (TangentSpace J)) ↦ (e (TotalSpace.mk' F'
      (g p.proj) (sectionLinearization (F := F') J _root_.id s (g p.proj) p.snd))).2) =ᶠ[𝓝 p₀]
      fun p ↦ mfderiv J 𝓘(𝕜, F') t (g p.proj) p.snd := by
    filter_upwards [hproj.continuousAt.eventually_mem_baseSet_trivializationAt F' E'] with p hp
    exact key p.proj hp p.snd
  exact (Pullback.continuousAt_mfderiv_apply g
    (ht _ (mem_baseSet_trivializationAt F' E' _)) hn).congr heq.symm

end SymplecticGeometry

end
