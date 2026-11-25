/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.SmoothEmbedding
import SymplecticGeometry.Geometry.Manifold.Flow.TimeDependent
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Neighborhood
import SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.Extension
import TauCeti.Geometry.Manifold.Flow.TimeDependent
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Prod
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

The proof follows that of `TauCeti.SmoothIsotopy.exists_contMDiff_diffeomorph_forall_apply_eq`,
applied to the graph isotopy `(q, y) ↦ (q, k (q, s, y))` of an open neighbourhood `V` of
`T ×ˢ A` into `Q × M`, in three steps; the second and the third keep the parameter fixed.

1. The graph slices are smooth embeddings of a neighbourhood `V` of `T ×ˢ A`
   (`TauCeti.exists_isOpen_forall_isSmoothEmbedding_of_injOn`, with the differential of a graph
   from `MDifferentiableAt.injective_mfderiv_fst_prod_iff`).
2. The time extension that `TauCeti.SmoothIsotopy.exists_contMDiff_extend` gives for the graph
   isotopy need not keep the parameter fixed outside `[0, 1]`; its `Q`-component is replaced by the
   parameter, and the slices of the new motion are embeddings near `T ×ˢ A` for times near
   `[0, 1]` (`TauCeti.exists_pos_forall_isSmoothEmbedding_of_eventuallyEq`). Run at the time of
   a cut-off (`TauCeti.exists_contMDiff_forall_isSmoothEmbedding_comp`), it becomes a motion over
   `ℝ`, stationary outside a bounded interval.
3. Tau Ceti's `TauCeti.exists_ambientVelocityField` gives a compactly supported field `X` on
   `Q × M` along the motion. Its `M`-component at `(q, y)` is a field `Y q` on `M`, jointly smooth
   in `(q, t, y)`. Since the motion keeps `q` fixed, the `M`-component of the motion is a solution
   of `Y q`, so it is the flow of `Y q` (`TauCeti.timeDependentFlowOf_eq_of_forall_hasMFDerivAt`);
   the flows are jointly smooth in the parameter by `TauCeti.contMDiff_timeDependentFlowOf_param`.

## Main results

* `ContMDiff.exists_contMDiff_diffeomorph_family_forall_apply_eq`: isotopy extension at every
  time for a smooth family of isotopies over a boundaryless parameter manifold, by diffeomorphisms
  jointly smooth in the parameter, the time and the point.
* `TauCeti.exists_contMDiff_diffeomorph_family_of_graph`: the same for a motion of a manifold
  `R` through embeddings `x ↦ (π x, G (t, x))` into `Q × M` that keep a parameter `π x` fixed,
  stationary outside a bounded interval of times; this is step 3.

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
      contMDiff_snd.snd, fun _ _ ↦ rfl, ∅, isCompact_empty, fun _ _ _ _ ↦ rfl,
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
    (fun s p hp p' hp' h ↦ by
      obtain ⟨h₁, h₂⟩ := Prod.ext_iff.1 h
      obtain ⟨q, x⟩ := p
      obtain ⟨q', x'⟩ := p'
      obtain rfl : q = q' := h₁
      exact congrArg (Prod.mk q) ((hemb q hp.1 s).isEmbedding.injective h₂))
    fun s p hp ↦ by
      have hd : MDifferentiableAt (IQ.prod J) I (fun x : Q × P ↦ k (x.1, s, x.2)) p :=
        (hk.comp (contMDiff_fst.prodMk (contMDiff_const.prodMk contMDiff_snd))).mdifferentiableAt
          (by simp)
      exact hd.injective_mfderiv_fst_prod_iff.2
        ((hemb p.1 hp.1 s).isImmersion.mfderiv_injective (by simp) p.2)
  let F := SmoothIsotopy.ofForallIsSmoothEmbedding
    (hg.contMDiffOn (s := univ ×ˢ (V : Set (Q × P)))) hV
    (f₀ := ⟨fun x : V ↦ g (0, x), hg.comp (contMDiff_const.prodMk contMDiff_subtypeVal)⟩)
    (f₁ := ⟨fun x : V ↦ g (1, x), hg.comp (contMDiff_const.prodMk contMDiff_subtypeVal)⟩)
    (fun _ ↦ rfl) fun _ ↦ rfl
  let A' : Set V := Subtype.val ⁻¹' (T ×ˢ A)
  have hA' : IsCompact A' :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' (hT.prod hA) (by rwa [Subtype.range_coe])
  -- Step 2: extend `F` in time, and put the parameter back in the `Q`-component.
  obtain ⟨δ, hδ, V₂, hAV₂, G, hG, hGF, -⟩ := F.exists_contMDiff_extend hA'
  let G₂ : ℝ × V → Q × M := fun p ↦ ((p.2 : Q × P).1, (G p).2)
  have hG₂ : ContMDiffOn (𝓘(ℝ).prod (IQ.prod J)) (IQ.prod I) ∞ G₂
      (Ioo (-δ) (1 + δ) ×ˢ (V₂ : Set V)) :=
    (contMDiff_fst.comp (contMDiff_subtypeVal.comp contMDiff_snd)).contMDiffOn.prodMk
      (contMDiff_snd.comp_contMDiffOn hG)
  have hGg (t : unitInterval) (x : V) (hx : x ∈ V₂) : G (t, x) = g (t, x) :=
    (hGF t x hx).trans (SmoothIsotopy.ofForallIsSmoothEmbedding_apply _ _ _ _ _)
  have hG₂F (t : unitInterval) (x : V) (hx : x ∈ V₂) : G₂ (t, x) = g (t, x) :=
    Prod.ext rfl (by simp only [G₂, hGg t x hx])
  obtain ⟨ε, hε, V₃, hAV₃, hV₃W, hV₃⟩ := exists_pos_forall_isSmoothEmbedding_of_eventuallyEq
    (isOpen_Ioo.prod V₂.isOpen) hG₂ hA'
    (fun p hp ↦ ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, hAV₂ hp.2⟩)
    (F := fun p : unitInterval × V ↦ g (p.1, p.2)) hV
    fun t ht ↦ Filter.eventually_of_mem (V₂.isOpen.mem_nhdsSet.2 hAV₂) fun x hx ↦
      hG₂F ⟨t, ht⟩ x hx
  -- A motion of `V₃` over `ℝ`, stationary outside a bounded interval.
  obtain ⟨c, hG', hemb', hc_id, hc_lo, hc_hi⟩ :=
    exists_contMDiff_forall_isSmoothEmbedding_comp hε (hG₂.mono hV₃W) hV₃
  let A'' : Set V₃ := Subtype.val ⁻¹' A'
  have hA'' : IsCompact A'' :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hA' (by rwa [Subtype.range_coe])
  -- Step 3: the flows of the `M`-components of the ambient field.
  obtain ⟨ψ, hψ, hψ₀, K, hK, hψK, hψG⟩ := exists_contMDiff_diffeomorph_family_of_graph
    (π := fun x : V₃ ↦ ((x : V) : Q × P).1) (G := fun p ↦ (G₂ (c p.1, p.2)).2)
    (contMDiff_fst.comp (contMDiff_subtypeVal.comp contMDiff_subtypeVal))
    (contMDiff_snd.comp hG') hemb' hA'' (a := -(ε / 2)) (b := 1 + ε / 2)
    (fun t ht x _ ↦ by simp only [hc_lo t ht]) (fun t ht x _ ↦ by simp only [hc_hi t ht])
  refine ⟨ψ, hψ, hψ₀, K, hK, hψK, fun q hq s x hx ↦ ?_⟩
  have hqx : ((q, x) : Q × P) ∈ T ×ˢ A := ⟨hq, hx⟩
  let pV : V := ⟨(q, x), hTAV hqx⟩
  have hpV : pV ∈ A' := hqx
  have hGk (t : unitInterval) : (G₂ (c t, pV)).2 = k (q, t, x) := by
    rw [hc_id t t.property, hG₂F t pV (hAV₂ hpV)]
  have h := hψG s ⟨pV, hAV₃ hpV⟩ hpV
  rwa [← Set.Icc.coe_zero, hGk, hGk] at h

end TauCeti

end
