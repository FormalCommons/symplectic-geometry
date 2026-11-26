/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic
import Mathlib.Geometry.Manifold.Instances.Icc
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition
import SymplecticGeometry.Geometry.Manifold.Flow.TimeDependent
import SymplecticGeometry.Data.Set.Prod
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Real
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Neighborhood
import SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.Extension
import TauCeti.Geometry.Manifold.Flow.TimeDependent
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse
import TauCeti.Geometry.Manifold.SmoothIsotopy.Velocity.Basic

/-!
# Isotopy extension at every time for a family of isotopies

Let `k : Q × [0, 1] × P → M` be a smooth family of smooth isotopies of a boundaryless manifold `P`
into a finite-dimensional, Hausdorff, σ-compact boundaryless manifold `M`, over a parameter
manifold `Q` of the same kind, and let `T ⊆ Q` and `A ⊆ P` be compact. Then there is a family
`ψ q t` of diffeomorphisms of `M`, jointly smooth in `(q, t, y)`, with `ψ q 0` the identity,
fixing every point outside a compact set, such that `ψ q s (k (q, 0, x)) = k (q, s, x)` for
`q ∈ T`, `s ∈ [0, 1]` and `x ∈ A`
(`ContMDiff.exists_contMDiff_diffeomorph_family_forall_apply_eq`).

The proof works with the graph isotopy `(q, y) ↦ (q, k (q, s, y))` of an open neighbourhood `V`
of `T ×ˢ A` into `Q × M`, in three steps; the second and the third keep the parameter fixed.
Steps 2 and 3 adapt the proof of Tau Ceti's `TauCeti.SmoothIsotopy.exists_diffeotopy_apply_eq`,
with the time extension of `SmoothIsotopy/Extension.lean` in place of Tau Ceti's change of time.

1. The graph slices are smooth embeddings of a neighbourhood `V` of `T ×ˢ A`
   (`TauCeti.exists_isOpen_forall_isSmoothEmbedding_of_injOn`): a graph is injective where its
   slices are (`Set.injOn_fst_prod_iff`), and so is its differential (Tau Ceti's
   `MDifferentiableAt.injective_mfderiv_fst_prod_iff`).
2. The family `k` itself extends in time near `T ×ˢ A`
   (`ContMDiff.exists_contMDiffOn_extend_unitInterval`). The graph of the extension keeps the
   parameter fixed by construction, and its slices are embeddings near `T ×ˢ A` for times near
   `[0, 1]` (`TauCeti.exists_pos_forall_isSmoothEmbedding_of_eventuallyEq`). Run at the time of
   a cut-off (`TauCeti.exists_contMDiff_forall_isSmoothEmbedding_comp`), it becomes a motion over
   `ℝ`, stationary outside a bounded interval.
3. Tau Ceti's `TauCeti.exists_ambientVelocityField` gives a compactly supported field `X` on
   `Q × M` along the motion. Its `M`-component at `(q, y)` is a field `Y q` on `M`, jointly smooth
   in `(q, t, y)`. Since the motion keeps `q` fixed, the `M`-component of the motion is a solution
   of `Y q`, so it is the flow of `Y q` (`TauCeti.timeDependentFlowOf_eq_of_forall_hasMFDerivAt`);
   the flows are jointly smooth in the parameter by `TauCeti.contMDiff_timeDependentFlowOf_param`.

The parametric flows need a boundaryless parameter manifold, so the case of the parameter
`unitInterval` (`ContMDiff.exists_contMDiff_diffeomorph_unitInterval_family_forall_apply_eq`)
goes through `Q = ℝ` and `T = [0, 1]`. Near `A`, the family is a family over `ℝ` that agrees with
it on `[0, 1]` (`ContMDiff.exists_contMDiff_real_family_eq`): extend it in the parameter, near
`univ ×ˢ A`, to an open interval `(-δ, 1 + δ)` (`ContMDiff.exists_contMDiffOn_extend_unitInterval`),
and run the extension at a parameter `c q ∈ (-δ, 1 + δ)` with `c` the identity on `[0, 1]`
(`SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_Ioo`). Only the slices with parameters in
`T` need to be embeddings, and there the new family is `k`. The diffeomorphisms for parameters in
`[0, 1]` are those wanted.

A single smooth isotopy is the case of the point `EuclideanSpace ℝ (Fin 0)` as parameter
manifold, with `T = univ` (`TauCeti.SmoothIsotopy.exists_contMDiff_diffeomorph_forall_apply_eq`
and `TauCeti.SmoothIsotopy.exists_diffeotopy_forall_apply_eq`), and a smooth path is in turn a
smooth isotopy of a point, whose slices are smooth embeddings by Tau Ceti's
`TauCeti.isSmoothEmbedding_const_of_subsingleton`
(`ContMDiff.exists_contMDiff_diffeomorph_forall_apply_eq`).

The case of a point as source, for the family `(t, s) ↦ H (t, s)`, gives diffeomorphisms
`ψ t s` of `M` that carry `H (t, 0)` to `H (t, s)`; composing them with a smooth family of
embeddings `e (t, ·)` through `H (t, 0)` gives a two-parameter family of embeddings through `H`
(`ContMDiff.exists_contMDiff_isSmoothEmbedding_unitInterval_family_apply_eq`).

## Main results

* `ContMDiff.exists_contMDiff_diffeomorph_family_forall_apply_eq`: isotopy extension at every
  time for a smooth family of isotopies over a boundaryless parameter manifold, by diffeomorphisms
  jointly smooth in the parameter, the time and the point.
* `TauCeti.exists_contMDiff_diffeomorph_family_of_graph`: the same for a motion of a manifold
  `R` through embeddings `x ↦ (π x, G (t, x))` into `Q × M` that keep a parameter `π x` fixed,
  stationary outside a bounded interval of times; this is step 3.
* `ContMDiff.exists_contMDiff_real_family_eq`: near a compact set, a smooth family over
  `unitInterval` agrees on `[0, 1]` with a smooth family over `ℝ`.
* `ContMDiff.exists_contMDiff_diffeomorph_unitInterval_family_forall_apply_eq`: isotopy extension
  at every time for a smooth family of isotopies with a parameter in `unitInterval`.
* `TauCeti.SmoothIsotopy.exists_contMDiff_diffeomorph_forall_apply_eq`: isotopy extension at every
  time for a single smooth isotopy, by a jointly smooth family of diffeomorphisms over `ℝ`.
* `TauCeti.SmoothIsotopy.exists_diffeotopy_forall_apply_eq`: isotopy extension at every time, by a
  compactly supported diffeotopy.
* `ContMDiff.exists_contMDiff_diffeomorph_forall_apply_eq`: a smooth path is the track of its
  starting point under a jointly smooth family of diffeomorphisms over `ℝ`, with `ψ 0` the
  identity, that fixes every point outside a compact set.
* `ContMDiff.exists_contMDiff_isSmoothEmbedding_unitInterval_family_apply_eq`: a smooth family of
  embeddings `e (t, ·)` and a smooth map `H` of the square with `H (t, 0) = e (t, x₀)` give a
  smooth two-parameter family of embeddings `k (t, s, ·)` with `k (t, 0, ·) = e (t, ·)` and
  `k (t, s, x₀) = H (t, s)`.

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 8, §1, Theorems 1.3 and 1.4.
-/

public section

noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E E' EQ H H' HQ P M Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [FiniteDimensional ℝ EQ]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace HQ]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'} {IQ : ModelWithCorners ℝ EQ HQ}
  [TopologicalSpace P] [ChartedSpace H' P] [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace Q] [ChartedSpace HQ Q]
  [I.Boundaryless] [J.Boundaryless] [IQ.Boundaryless]
  [IsManifold J ∞ P] [IsManifold I ∞ M] [IsManifold IQ ∞ Q]
  [T2Space M] [T2Space Q] [SigmaCompactSpace M] [SigmaCompactSpace Q]

/-- **Isotopy extension for a motion over a parameter.** Let `R` be a boundaryless manifold with a
smooth map `π : R → Q`, and `G : ℝ × R → M` smooth, such that every map `x ↦ (π x, G (t, x))`
is a smooth embedding of `R` into `Q × M`, and such that on a compact `A ⊆ R` the motion is
stationary before a time `a` and after a time `b`. Then there is a family `ψ q t` of
diffeomorphisms of `M`, jointly smooth in `(q, t, y)`, with `ψ q 0` the identity, fixing every
point outside a compact set, such that `ψ (π x) t (G (0, x)) = G (t, x)` for every `t` and
every `x ∈ A`. -/
theorem exists_contMDiff_diffeomorph_family_of_graph {ER HR R : Type*}
    [NormedAddCommGroup ER] [NormedSpace ℝ ER] [TopologicalSpace HR]
    {JR : ModelWithCorners ℝ ER HR} [TopologicalSpace R] [ChartedSpace HR R] [JR.Boundaryless]
    [IsManifold JR ∞ R] {π : R → Q} (hπ : ContMDiff JR IQ ∞ π) {G : ℝ × R → M}
    (hG : ContMDiff (𝓘(ℝ, ℝ).prod JR) I ∞ G)
    (hemb : ∀ t, IsSmoothEmbedding JR (IQ.prod I) ∞ fun x ↦ (π x, G (t, x)))
    {A : Set R} (hA : IsCompact A) {a b : ℝ} (ha : ∀ t ≤ a, ∀ x ∈ A, G (t, x) = G (a, x))
    (hb : ∀ t, b ≤ t → ∀ x ∈ A, G (t, x) = G (b, x)) :
    ∃ ψ : Q → ℝ → M ≃ₘ⟮I, I⟯ M,
      ContMDiff (IQ.prod (𝓘(ℝ, ℝ).prod I)) I ∞ (fun p : Q × ℝ × M ↦ ψ p.1 p.2.1 p.2.2) ∧
      (∀ q y, ψ q 0 y = y) ∧ ∃ K : Set M, IsCompact K ∧ (∀ q t, ∀ y ∉ K, ψ q t y = y) ∧
      ∀ t, ∀ x ∈ A, ψ (π x) t (G (0, x)) = G (t, x) := by
  have : CompleteSpace EQ := FiniteDimensional.completeSpace ℝ EQ
  -- The ambient field `X` on `Q × M`, and its `M`-components `Y q`.
  obtain ⟨X, K, hK, hXK, hX, hvel⟩ := exists_ambientVelocityField (m := ⊤) (n := ⊤)
    (G := fun p ↦ (π p.2, G p)) ((hπ.comp contMDiff_snd).prodMk hG) hemb hA
    (fun t ht x hx ↦ by rw [ha t ht x hx]) (fun t ht x hx ↦ by rw [hb t ht x hx]) le_top le_top
  let Y : Q → ℝ → (y : M) → TangentSpace I y := fun q t y ↦ (X t (q, y)).2
  have hY : ContMDiff ((IQ.prod 𝓘(ℝ, ℝ)).prod I) I.tangent ∞
      (fun p : (Q × ℝ) × M ↦ (⟨p.2, Y p.1.1 p.1.2 p.2⟩ : TangentBundle I M)) :=
    contMDiff_snd.comp ((contMDiff_equivTangentBundleProd (I := IQ) (M := Q) (I' := I)
      (M' := M)).comp (hX.comp (contMDiff_fst.snd.prodMk (contMDiff_fst.fst.prodMk contMDiff_snd))))
  have hYq (q : Q) : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, Y q p.1 p.2⟩ : TangentBundle I M)) :=
    hY.comp ((contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd)
  have hYq₁ (q : Q) := (hYq q).of_le (m := 1) (by simp)
  let C : Set M := Prod.snd '' K
  have hC : IsCompact C := hK.image continuous_snd
  have hYC (q : Q) (t : ℝ) (y : M) (hy : y ∉ C) : Y q t y = 0 := by
    simp only [Y, hXK t (q, y) fun h ↦ hy ⟨_, h, rfl⟩]
    -- The `M`-part of the zero tangent vector of `Q × M` is zero by definition.
    rfl
  have hcomplete (q : Q) :=
    isCompleteVectorField_timeDependentSuspensionField (hYq₁ q) hC (hYC q)
  have hflow := contMDiff_timeDependentFlowOf_param le_top hY hcomplete
  refine ⟨fun q t ↦ timeDependentFlowDiffeomorph (hcomplete q) le_top (hYq q) 0 t,
    (hflow.comp ((contMDiff_fst.prodMk ((contMDiff_const (c := (0 : ℝ))).prodMk
      contMDiff_snd.fst)).prodMk contMDiff_snd.snd)).congr fun p ↦
        timeDependentFlowDiffeomorph_apply ..,
    fun q y ↦ (timeDependentFlowDiffeomorph_apply ..).trans (timeDependentFlowOf_self _ 0 y),
    C, hC, fun q t y hy ↦ (timeDependentFlowDiffeomorph_apply ..).trans
      (timeDependentFlowOf_eq_self_of_forall_eq_zero (hYq₁ q) (fun u ↦ hYC q u y hy) 0 t),
    fun t x hx ↦ ?_⟩
  -- The `M`-component of the motion of `x` solves the equation of `Y (π x)`.
  have hγ (u : ℝ) : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s ↦ G (s, x)) u
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y (π x) u (G (u, x)))) :=
    ((hasMFDerivAt_snd _).comp u (hvel u x hx)).congr_mfderiv
      (ContinuousLinearMap.ext fun _ ↦ rfl)
  rw [timeDependentFlowDiffeomorph_apply]
  exact timeDependentFlowOf_eq_of_forall_hasMFDerivAt (hYq₁ (π x)) hγ 0 t

/-- **Isotopy extension at every time, for a family of isotopies.** Let `k : Q × [0, 1] × P → M`
be smooth, with `Q` a finite-dimensional, Hausdorff, σ-compact boundaryless manifold of
parameters and `M` a finite-dimensional, Hausdorff, σ-compact boundaryless manifold, and let
`T ⊆ Q` and `A ⊆ P` be compact, with every slice `k (q, s, ·)` for `q ∈ T` a smooth embedding.
Then there is a family `ψ q t` of diffeomorphisms of `M`, jointly smooth in `(q, t, y)`, with
`ψ q 0` the identity, fixing every point outside a compact set `K`, such that
`ψ q s (k (q, 0, x)) = k (q, s, x)` for every `q ∈ T`, `s ∈ [0, 1]` and `x ∈ A`. -/
theorem _root_.ContMDiff.exists_contMDiff_diffeomorph_family_forall_apply_eq
    {k : Q × unitInterval × P → M} (hk : ContMDiff (IQ.prod ((𝓡∂ 1).prod J)) I ∞ k)
    {T : Set Q} (hT : IsCompact T) {A : Set P} (hA : IsCompact A)
    (hemb : ∀ q ∈ T, ∀ s, IsSmoothEmbedding J I ∞ fun x ↦ k (q, s, x)) :
    ∃ ψ : Q → ℝ → M ≃ₘ⟮I, I⟯ M,
      ContMDiff (IQ.prod (𝓘(ℝ, ℝ).prod I)) I ∞ (fun p : Q × ℝ × M ↦ ψ p.1 p.2.1 p.2.2) ∧
      (∀ q y, ψ q 0 y = y) ∧ ∃ K : Set M, IsCompact K ∧ (∀ q t, ∀ y ∉ K, ψ q t y = y) ∧
      ∀ q ∈ T, ∀ s : unitInterval, ∀ x ∈ A, ψ q s (k (q, 0, x)) = k (q, s, x) := by
  -- Without a point of `T ×ˢ A`, the identity will do.
  by_cases hTA : (T ×ˢ A).Nonempty
  swap
  · exact ⟨fun _ _ ↦ Diffeomorph.refl I M ∞, (Diffeomorph.refl I M ∞).contMDiff.comp
      contMDiff_snd.snd, fun _ y ↦ congrFun (Diffeomorph.coe_refl I M ∞) y, ∅, isCompact_empty,
      fun _ _ y _ ↦ congrFun (Diffeomorph.coe_refl I M ∞) y,
      fun q hq _ x hx ↦ (hTA ⟨(q, x), hq, hx⟩).elim⟩
  -- `P` is Hausdorff and its model finite-dimensional, since a slice embeds it into `M`.
  obtain ⟨⟨q₀, x₀⟩, hq₀, -⟩ := hTA
  have : T2Space P := (hemb q₀ hq₀ 0).isEmbedding.t2Space
  have : FiniteDimensional ℝ E' := finiteDimensional_of_injective_mfderiv
    ((hemb q₀ hq₀ 0).isImmersion.mfderiv_injective (by simp) x₀)
  -- Step 1: the graph isotopy `g` has embedding slices on an open `V ⊇ T ×ˢ A`.
  let g : unitInterval × (Q × P) → Q × M := fun p ↦ (p.2.1, k (p.2.1, p.1, p.2.2))
  have hg : ContMDiff ((𝓡∂ 1).prod (IQ.prod J)) (IQ.prod I) ∞ g :=
    contMDiff_snd.fst.prodMk (hk.comp (contMDiff_snd.fst.prodMk
      (contMDiff_fst.prodMk contMDiff_snd.snd)))
  obtain ⟨V, hTAV, -, hV⟩ := exists_isOpen_forall_isSmoothEmbedding_of_injOn (G := g) isOpen_univ
    hg.contMDiffOn (hT.prod hA) (subset_univ _)
    (fun s ↦ Set.injOn_fst_prod_iff.2 fun q hq ↦ (hemb q hq s).isEmbedding.injective.injOn)
    fun s p hp ↦ (ContMDiff.mdifferentiableAt (f := fun x : Q × P ↦ k (x.1, s, x.2))
      (hk.comp (contMDiff_fst.prodMk (contMDiff_const.prodMk contMDiff_snd))) (by simp)
        ).injective_mfderiv_fst_prod_iff.2
      ((hemb p.1 hp.1 s).isImmersion.mfderiv_injective (by simp) p.2)
  let A' : Set V := Subtype.val ⁻¹' (T ×ˢ A)
  have hA' : IsCompact A' :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' (hT.prod hA) (by rwa [Subtype.range_coe])
  -- Step 2: extend `k` in time near `A'`, and take the graph `Γ` of the extension, which keeps
  -- the parameter fixed; its slices are embeddings near `A'` for times near `[0, 1]`.
  obtain ⟨δ₀, hδ₀, U, hU, hAU, G, hG, hGk⟩ := ContMDiff.exists_contMDiffOn_extend_unitInterval
    (f := fun p : unitInterval × V ↦ k ((p.2 : Q × P).1, p.1, (p.2 : Q × P).2))
    (hk.comp ((contMDiff_subtypeVal.comp contMDiff_snd).fst.prodMk
      (contMDiff_fst.prodMk (contMDiff_subtypeVal.comp contMDiff_snd).snd))) hA'
  let S : Set (ℝ × V) := Ioo (-δ₀) (1 + δ₀) ×ˢ U
  have hS : IsOpen S := isOpen_Ioo.prod hU
  have hAS : Icc 0 1 ×ˢ A' ⊆ S := prod_mono (Icc_subset_Ioo (by linarith) (by linarith)) hAU
  let Γ : ℝ × V → Q × M := fun p ↦ ((p.2 : Q × P).1, G p)
  have hΓ : ContMDiffOn (𝓘(ℝ).prod (IQ.prod J)) (IQ.prod I) ∞ Γ S :=
    (contMDiff_subtypeVal.comp contMDiff_snd).fst.contMDiffOn.prodMk hG
  have hΓg (t : unitInterval) (x : V) (hx : x ∈ U) : Γ (t, x) = g (t, x) :=
    Prod.ext rfl (hGk t x hx)
  obtain ⟨ε, hε, V₃, hAV₃, hV₃S, hV₃⟩ := exists_pos_forall_isSmoothEmbedding_of_eventuallyEq
    hS hΓ hA' hAS (F := fun p : unitInterval × V ↦ g (p.1, p.2)) hV
    fun t ht ↦ Filter.eventually_of_mem (hU.mem_nhdsSet.2 hAU) fun x hx ↦ hΓg ⟨t, ht⟩ x hx
  -- A motion of `V₃` over `ℝ`, stationary outside a bounded interval.
  obtain ⟨c, hG', hemb', hc_id, hc_lo, hc_hi⟩ :=
    exists_contMDiff_forall_isSmoothEmbedding_comp hε (hΓ.mono hV₃S) hV₃
  let A'' : Set V₃ := Subtype.val ⁻¹' A'
  have hA'' : IsCompact A'' :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hA' (by rwa [Subtype.range_coe])
  -- Step 3: the flows of the `M`-components of the ambient field.
  obtain ⟨ψ, hψ, hψ₀, K, hK, hψK, hψG⟩ := exists_contMDiff_diffeomorph_family_of_graph
    (π := fun x : V₃ ↦ ((x : V) : Q × P).1) (G := fun p ↦ (Γ (c p.1, p.2)).2)
    (contMDiff_fst.comp (contMDiff_subtypeVal.comp contMDiff_subtypeVal))
    (contMDiff_snd.comp hG') hemb' hA'' (a := -(ε / 2)) (b := 1 + ε / 2)
    (fun t ht x _ ↦ by simp only [hc_lo t ht]) (fun t ht x _ ↦ by simp only [hc_hi t ht])
  refine ⟨ψ, hψ, hψ₀, K, hK, hψK, fun q hq s x hx ↦ ?_⟩
  have hqx : ((q, x) : Q × P) ∈ T ×ˢ A := ⟨hq, hx⟩
  let pV : V := ⟨(q, x), hTAV hqx⟩
  have hpV : pV ∈ A' := hqx
  have hΓk (t : unitInterval) : (Γ (c t, pV)).2 = k (q, t, x) := by
    rw [hc_id t t.property, hΓg t pV (hAU hpV)]
  have h := hψG s ⟨pV, hAV₃ hpV⟩ hpV
  rwa [← Set.Icc.coe_zero, hΓk, hΓk] at h

namespace SmoothIsotopy

/-- **Isotopy extension at every time, over `ℝ`.** A smooth isotopy `F` of a boundaryless
manifold through smooth embeddings into a finite-dimensional, Hausdorff, σ-compact boundaryless
manifold `M` is on any compact subset `A` of the source the restriction of a jointly smooth
family `ψ` of diffeomorphisms of `M` over all real times, with `ψ 0 = id`, fixing every point
outside a compact set: `ψ t (f₀ x) = F (t, x)` for every `t ∈ [0, 1]` and every `x ∈ A`. -/
theorem exists_contMDiff_diffeomorph_forall_apply_eq {f₀ f₁ : C^∞⟮J, P; I, M⟯}
    (F : SmoothIsotopy f₀ f₁) {A : Set P} (hA : IsCompact A) :
    ∃ ψ : ℝ → M ≃ₘ⟮I, I⟯ M, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ ψ p.1 p.2) ∧
      (∀ y, ψ 0 y = y) ∧ ∃ K : Set M, IsCompact K ∧ (∀ t, ∀ y ∉ K, ψ t y = y) ∧
      ∀ t : unitInterval, ∀ x ∈ A, ψ t (f₀ x) = F (t, x) := by
  -- The case of the point `EuclideanSpace ℝ (Fin 0)` as parameter manifold.
  obtain ⟨ψ, hψ, hψ₀, K, hK, hψK, hψF⟩ :=
    ContMDiff.exists_contMDiff_diffeomorph_family_forall_apply_eq
      (Q := EuclideanSpace ℝ (Fin 0)) (IQ := 𝓘(ℝ, EuclideanSpace ℝ (Fin 0))) (k := fun p ↦ F p.2)
      (F.contMDiff.comp contMDiff_snd) isCompact_univ hA fun _ _ s ↦ F.isSmoothEmbedding s
  refine ⟨ψ 0, hψ.comp (contMDiff_const.prodMk contMDiff_id), hψ₀ 0, K, hK, hψK 0,
    fun t x hx ↦ ?_⟩
  have h := hψF 0 (mem_univ _) t x hx
  rwa [apply_zero] at h

/-- **Isotopy extension at every time.** A smooth isotopy `F` of a boundaryless manifold through
smooth embeddings into a finite-dimensional, Hausdorff, σ-compact boundaryless manifold `M` is
on any compact subset `A` of the source the restriction of a smooth diffeotopy `Φ` of `M`
fixing every point outside a compact set: `Φ (t, f₀ x) = F (t, x)` for every time `t` and every
`x ∈ A`. The source need not be compact. -/
theorem exists_diffeotopy_forall_apply_eq {f₀ f₁ : C^∞⟮J, P; I, M⟯}
    (F : SmoothIsotopy f₀ f₁) {A : Set P} (hA : IsCompact A) :
    ∃ Φ : Diffeotopy I ∞ M, ∃ K : Set M, IsCompact K ∧ (∀ t, ∀ y ∉ K, Φ (t, y) = y) ∧
      ∀ t, ∀ x ∈ A, Φ (t, f₀ x) = F (t, x) := by
  obtain ⟨ψ, hψ, h₀, K, hK, hψK, hψF⟩ := F.exists_contMDiff_diffeomorph_forall_apply_eq hA
  exact ⟨Diffeotopy.ofReal ψ hψ h₀, K, hK,
    fun t y hy ↦ by rw [Diffeotopy.ofReal_apply, hψK t y hy],
    fun t x hx ↦ by rw [Diffeotopy.ofReal_apply, hψF t x hx]⟩

end SmoothIsotopy

/-- **Pushing a point along a path.** A smooth path `c` in a finite-dimensional, Hausdorff,
σ-compact boundaryless manifold is the track of its starting point under a family `ψ` of
diffeomorphisms over `ℝ`, jointly smooth in time and space, with `ψ 0` the identity, that fixes
every point outside a compact set: `ψ t (c 0) = c t` for every `t ∈ [0, 1]`. -/
theorem _root_.ContMDiff.exists_contMDiff_diffeomorph_forall_apply_eq
    {c : unitInterval → M} (hc : ContMDiff (𝓡∂ 1) I ∞ c) :
    ∃ ψ : ℝ → M ≃ₘ⟮I, I⟯ M, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ ψ p.1 p.2) ∧
      (∀ y, ψ 0 y = y) ∧ ∃ K : Set M, IsCompact K ∧ (∀ t, ∀ y ∉ K, ψ t y = y) ∧
      ∀ t : unitInterval, ψ t (c 0) = c t := by
  -- `c` is a smooth isotopy of the point `EuclideanSpace ℝ (Fin 0)`.
  let Q := EuclideanSpace ℝ (Fin 0)
  let F : SmoothIsotopy (⟨fun _ ↦ c 0, contMDiff_const⟩ : C^∞⟮𝓘(ℝ, Q), Q; I, M⟯)
      ⟨fun _ ↦ c 1, contMDiff_const⟩ :=
    { toContMDiffMap := ⟨fun p ↦ c p.1, hc.comp contMDiff_fst⟩
      map_zero_left := fun _ ↦ rfl
      map_one_left := fun _ ↦ rfl
      isSmoothEmbedding := fun t ↦ isSmoothEmbedding_const_of_subsingleton (by simp) (c t) }
  obtain ⟨ψ, hψ, hψ0, K, hK, hψK, hψc⟩ :=
    F.exists_contMDiff_diffeomorph_forall_apply_eq (isCompact_singleton (x := 0))
  exact ⟨ψ, hψ, hψ0, K, hK, hψK, fun t ↦ hψc t 0 rfl⟩

omit [J.Boundaryless] [SigmaCompactSpace M] in
/-- **A family over `[0, 1]` as a family over `ℝ`.** A smooth map `k : [0, 1] × [0, 1] × P → M`,
into a finite-dimensional, Hausdorff boundaryless manifold, agrees near a compact `A ⊆ P` with a
smooth map over the parameter space `ℝ`: there are an open `V ⊇ A` and a smooth
`k' : ℝ × [0, 1] × V → M` with `k' (a, s, x) = k (a, s, x)` for every `a` and `s` in `[0, 1]`
and `x ∈ V`. -/
theorem _root_.ContMDiff.exists_contMDiff_real_family_eq {k : unitInterval × unitInterval × P → M}
    (hk : ContMDiff ((𝓡∂ 1).prod ((𝓡∂ 1).prod J)) I ∞ k) {A : Set P} (hA : IsCompact A) :
    ∃ V : TopologicalSpace.Opens P, A ⊆ V ∧ ∃ k' : ℝ × unitInterval × V → M,
      ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡∂ 1).prod J)) I ∞ k' ∧
      ∀ (a s : unitInterval) (x : V), k' (a, s, x) = k (a, s, x) := by
  -- Extend `k` in the parameter near `univ ×ˢ A`, and shrink to a product `univ ×ˢ V`.
  obtain ⟨δ, hδ, U, hU, hAU, G, hG, hGk⟩ :=
    hk.exists_contMDiffOn_extend_unitInterval (isCompact_univ.prod hA)
  obtain ⟨u, V, -, hV, hu, hAV, hVU⟩ := generalized_tube_lemma isCompact_univ hA hU hAU
  have hsV (s : unitInterval) (x : P) (hx : x ∈ V) : (s, x) ∈ U := hVU ⟨hu (mem_univ s), hx⟩
  -- Run the extension at a parameter `c q` in `(-δ, 1 + δ)` equal to `q` on `[0, 1]`.
  obtain ⟨c, hc, hc_id, hc_mem, -⟩ :=
    SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_Ioo zero_le_one hδ
  refine ⟨⟨V, hV⟩, hAV, fun p ↦ G (c p.1, p.2.1, p.2.2),
    hG.comp_contMDiff ((hc.contMDiff.comp contMDiff_fst).prodMk
      (contMDiff_snd.fst.prodMk (contMDiff_subtypeVal.comp contMDiff_snd.snd)))
      fun p ↦ ⟨by simpa only [zero_sub] using hc_mem p.1, hsV _ _ p.2.2.property⟩,
    fun a s x ↦ ?_⟩
  simp only [show c a = a from hc_id a.property, hGk a (s, x) (hsV s x x.property)]

/-- **Isotopy extension at every time, for a family of isotopies over `[0, 1]`.** Let
`k : [0, 1] × [0, 1] × P → M` be smooth, with `M` a finite-dimensional, Hausdorff, σ-compact
boundaryless manifold, every slice `k (a, s, ·)` a smooth embedding, and `A ⊆ P` compact. Then
there is a family `ψ a t` of diffeomorphisms of `M`, jointly smooth in `(a, t, y)`, with `ψ a 0`
the identity, fixing every point outside a compact set `K`, such that
`ψ a s (k (a, 0, x)) = k (a, s, x)` for every `a`, `s ∈ [0, 1]` and `x ∈ A`. -/
theorem _root_.ContMDiff.exists_contMDiff_diffeomorph_unitInterval_family_forall_apply_eq
    {k : unitInterval × unitInterval × P → M} (hk : ContMDiff ((𝓡∂ 1).prod ((𝓡∂ 1).prod J)) I ∞ k)
    {A : Set P} (hA : IsCompact A) (hemb : ∀ a s, IsSmoothEmbedding J I ∞ fun x ↦ k (a, s, x)) :
    ∃ ψ : unitInterval → ℝ → M ≃ₘ⟮I, I⟯ M,
      ContMDiff ((𝓡∂ 1).prod (𝓘(ℝ, ℝ).prod I)) I ∞
        (fun p : unitInterval × ℝ × M ↦ ψ p.1 p.2.1 p.2.2) ∧
      (∀ a y, ψ a 0 y = y) ∧ ∃ K : Set M, IsCompact K ∧ (∀ a t, ∀ y ∉ K, ψ a t y = y) ∧
      ∀ a s : unitInterval, ∀ x ∈ A, ψ a s (k (a, 0, x)) = k (a, s, x) := by
  -- The family `k'` over `ℝ` on a neighbourhood `V'` of `A`, equal to `k` on `[0, 1]`.
  obtain ⟨V', hAV, k', hk', hk'k⟩ := hk.exists_contMDiff_real_family_eq hA
  have hA' : IsCompact (Subtype.val ⁻¹' A : Set V') :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hA (by rw [Subtype.range_coe]; exact hAV)
  obtain ⟨ψ, hψ, hψ₀, K, hK, hψK, hψk⟩ :=
    hk'.exists_contMDiff_diffeomorph_family_forall_apply_eq isCompact_Icc hA' fun q hq s ↦ by
      rw [show (fun x : V' ↦ k' (q, s, x)) = fun x : V' ↦ k (⟨q, hq⟩, s, x) from
        funext fun x ↦ hk'k ⟨q, hq⟩ s x]
      exact (hemb ⟨q, hq⟩ s).comp_subtypeVal V'
  -- Restrict `ψ` to parameters in `[0, 1]`.
  refine ⟨fun a ↦ ψ a, hψ.comp ((contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk
      contMDiff_snd), fun a ↦ hψ₀ a, K, hK, fun a ↦ hψK a, fun a s x hx ↦ ?_⟩
  have h := hψk a a.property s ⟨x, hAV hx⟩ hx
  rwa [hk'k, hk'k] at h

omit [J.Boundaryless] [IsManifold J ∞ P] in
/-- **A two-parameter family of embeddings through a map of the square.** Let `M` be a
finite-dimensional, Hausdorff, σ-compact boundaryless manifold, `e : [0, 1] × P → M` smooth with
every slice `e (t, ·)` a smooth embedding of a manifold `P`, `x₀ ∈ P`, and
`H : [0, 1] × [0, 1] → M` smooth with `H (t, 0) = e (t, x₀)` for every `t`. Then there is a
smooth `k : [0, 1] × [0, 1] × P → M` with every slice `k (t, s, ·)` a smooth embedding,
`k (t, 0, x) = e (t, x)` and `k (t, s, x₀) = H (t, s)` for all `t`, `s` and `x`. -/
theorem _root_.ContMDiff.exists_contMDiff_isSmoothEmbedding_unitInterval_family_apply_eq
    {e : unitInterval × P → M} (he : ContMDiff ((𝓡∂ 1).prod J) I ∞ e)
    (hemb : ∀ t, IsSmoothEmbedding J I ∞ fun x ↦ e (t, x)) (x₀ : P)
    {H : unitInterval × unitInterval → M} (hH : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) I ∞ H)
    (hH₀ : ∀ t, H (t, 0) = e (t, x₀)) :
    ∃ k : unitInterval × unitInterval × P → M,
      ContMDiff ((𝓡∂ 1).prod ((𝓡∂ 1).prod J)) I ∞ k ∧
      (∀ t s, IsSmoothEmbedding J I ∞ fun x ↦ k (t, s, x)) ∧
      (∀ t x, k (t, 0, x) = e (t, x)) ∧ ∀ t s, k (t, s, x₀) = H (t, s) := by
  -- Diffeomorphisms `ψ t s` of `M` that push `H (t, 0)` to `H (t, s)`: `H` is a family of
  -- isotopies of the point `EuclideanSpace ℝ (Fin 0)`.
  let Q := EuclideanSpace ℝ (Fin 0)
  obtain ⟨ψ, hψ, hψ₀, -, -, -, hψH⟩ :=
    ContMDiff.exists_contMDiff_diffeomorph_unitInterval_family_forall_apply_eq
      (J := 𝓘(ℝ, Q)) (k := fun p : unitInterval × unitInterval × Q ↦ H (p.1, p.2.1))
      (hH.comp (contMDiff_fst.prodMk contMDiff_snd.fst)) (isCompact_singleton (x := 0))
      fun t s ↦ isSmoothEmbedding_const_of_subsingleton (by simp) (H (t, s))
  refine ⟨fun p ↦ ψ p.1 p.2.1 (e (p.1, p.2.2)),
    hψ.comp (contMDiff_fst.prodMk ((contMDiff_subtypeVal_Icc.comp contMDiff_snd.fst).prodMk
      (he.comp (contMDiff_fst.prodMk contMDiff_snd.snd)))),
    fun t s ↦ isSmoothEmbedding_diffeomorph_comp (hemb t) (ψ t s),
    fun t x ↦ by simp only [Set.Icc.coe_zero, hψ₀], fun t s ↦ ?_⟩
  have h := hψH t s 0 rfl
  rwa [hH₀] at h

end TauCeti

end
