/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Geometry.Manifold.Instances.Icc
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition
import SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.Extension
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Frame
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.ModelSpace
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
import TauCeti.Topology.Algebra.Module.Alternating.Basic

/-!
# A family of maps along a ball with prescribed ends

Let `B(r)` be the closed ball `Metric.closedBall 0 r` of `StdSpace (Fin n)`, `ω₀` the standard
form, and `σ` a two-form on `M`, of dimension `2 n`, that is nondegenerate at each point. Given
symplectic embeddings `j₀`, `j₁` of a ball `B(r)` and a family `e` over `[0, 1]` of symplectic
embeddings of a smaller ball `B(r₀)`, `0 ≤ r₀ < r`, with `e 0 = j₀` and `e 1 = j₁` on `B(r₀)`,
this file builds a family `k` of maps, jointly smooth near `[0, 1] × B(r₀)`, that is `e` on
`B(r₀)` at every time, pulls `σ` back to `ω₀` at every point of `B(r₀)`, and whose ends are `j₀`
and `j₁` on a whole neighbourhood of `B(r₀)`
(`SymplecticGeometry.IsSymplecticBallFamily.exists_contMDiffOn_eqOn_mpullback_eq`). These are the
first two steps of the proof of the symplectic ball extension of McDuff–Salamon, Theorem 3.3.1;
Moser's argument then makes the slices of `k` symplectic near `B(r₀)`.

The proof has two steps.

1. *A family that is right along `B(r₀)`, with the right ends to first order.* For `r₀ > 0`, this
   is `e` itself: two maps that agree on `B(r₀)` have the same derivative there, since the ball is
   convex with nonempty interior. For `r₀ = 0`, `e` is only a path of centres `c`. A compactly
   supported diffeotopy `Ψ` pushes `c 0` along `c`
   (`ContMDiff.exists_diffeotopy_forall_apply_eq`), and the family is `Ψ t ∘ j₀ ∘ P t`, where
   `P` is a smooth path of linear maps from `1` to a frame `B` that makes the derivative at `0`
   that of `j₁` at time `1`. The path `P` trivializes the forms `(Ψ t ∘ j₀)^* σ` at `0`
   (`SymplecticGeometry.exists_contDiff_path_apply_eq_stdForm`); for this the times of `Ψ` are
   first extended past both ends of `[0, 1]` (`TauCeti.SmoothIsotopy.exists_contMDiff_extend`).
2. *The ends* (`SymplecticGeometry.exists_contMDiffOn_forall_eq_mfderiv_eq`). If the slice `k'_0`
   of such a family agrees with `j₀` to first order along a compact set `K`, then `k'_0` is a
   local diffeomorphism near `K`, and `g₀ = k'_0⁻¹ ∘ j₀` is the identity, with derivative the
   identity, along `K`; likewise `g₁` at time `1`. The family `k t = k' t ∘ ((1 - t) g₀ + t g₁)`
   agrees with `k'` on `K` to first order, and has the ends `j₀` and `j₁` near `K`.

## Main results

* `SymplecticGeometry.exists_contMDiffOn_forall_eq_mfderiv_eq`: correcting the ends of a family
  of maps along a compact set.
* `SymplecticGeometry.IsSymplecticBallFamily.exists_contMDiffOn_eqOn_mpullback_eq`: a family
  along `B(r₀)` with prescribed ends.

## Implementation notes

The form on `M` is called `σ`, since `ω` is a token once the scope `ContDiff` is open.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 3.3.1.
-/

public section

noncomputable section

open Set Function Filter Metric
open scoped ContDiff Manifold Topology

namespace SymplecticGeometry

open TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {σ : SmoothTwoForm I M}

/-- A first-order right inverse near a compact set. Let `f` and `j` be smooth on an open
`U ⊇ K`, with `K` compact and the model of `M` of dimension `2 n`, and let `f` and `j` agree on `K`
with the same derivative there, `j` being injective on `K` with injective derivative along `K`.
Then there is a map `g`, smooth on an open `W ⊇ K` and mapping it into `U`, with `f ∘ g = j` on
`W`, which is the identity with derivative the identity along `K`. -/
private theorem exists_comp_eq_of_mfderiv_eq [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]
    (hdim : Module.finrank ℝ E = 2 * n) {K U : Set (StdSpace (Fin n))} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {f j : StdSpace (Fin n) → M}
    (hf : ContMDiffOn 𝓘(ℝ, StdSpace (Fin n)) I ∞ f U)
    (hj : ContMDiffOn 𝓘(ℝ, StdSpace (Fin n)) I ∞ j U) (hfj : ∀ z ∈ K, f z = j z)
    (hd : ∀ z ∈ K, mfderiv 𝓘(ℝ, StdSpace (Fin n)) I f z = mfderiv 𝓘(ℝ, StdSpace (Fin n)) I j z)
    (himm : ∀ z ∈ K, Injective (mfderiv 𝓘(ℝ, StdSpace (Fin n)) I j z)) (hinj : InjOn j K) :
    ∃ g : StdSpace (Fin n) → StdSpace (Fin n), ∃ W, IsOpen W ∧ K ⊆ W ∧
      ContDiffOn ℝ ∞ g W ∧ MapsTo g W U ∧ (∀ z ∈ W, f (g z) = j z) ∧ (∀ z ∈ K, g z = z) ∧
      ∀ z ∈ K, fderiv ℝ g z = ContinuousLinearMap.id ℝ _ := by
  -- `f` is a local diffeomorphism at each point of `K`, and injective on `K`.
  have hloc (z : StdSpace (Fin n)) (hz : z ∈ K) :
      IsLocalDiffeomorphAt 𝓘(ℝ, StdSpace (Fin n)) I ∞ f z :=
    isLocalDiffeomorphAt_of_injective_mfderiv hf hU (hKU hz) BoundarylessManifold.isInteriorPoint
      (by simp) (hd z hz ▸ himm z hz) (by rw [finrank_stdSpace, Fintype.card_fin, hdim])
  have hinjf : InjOn f K := fun x hx y hy h ↦ hinj hx hy (by rwa [← hfj x hx, ← hfj y hy])
  obtain ⟨V₁, hV₁o, hKV₁, hV₁inj, hV₁loc⟩ :=
    hinjf.exists_isOpen_superset_isLocalDiffeomorphOn hK hloc
  set V := V₁ ∩ U
  have hVo : IsOpen V := hV₁o.inter hU
  have hVinj : InjOn f V := hV₁inj.mono inter_subset_left
  have hVloc : IsLocalDiffeomorphOn 𝓘(ℝ, StdSpace (Fin n)) I ∞ f V :=
    fun x ↦ hV₁loc ⟨x, x.property.1⟩
  have hfV : IsOpen (f '' V) := hVloc.isLocalHomeomorphOn.isOpen_image hVo
  set g := invFunOn f V ∘ j
  set W := U ∩ j ⁻¹' (f '' V)
  have hmem (z : StdSpace (Fin n)) (hz : z ∈ W) : ∃ a ∈ V, f a = j z := hz.2
  have hgf (z : StdSpace (Fin n)) (hz : z ∈ W) : f (g z) = j z := invFunOn_eq (hmem z hz)
  have hKW : K ⊆ W := fun z hz ↦ ⟨hKU hz, z, ⟨hKV₁ hz, hKU hz⟩, hfj z hz⟩
  have hgK (z : StdSpace (Fin n)) (hz : z ∈ K) : g z = z := by
    simp only [g, comp_apply, ← hfj z hz]
    exact hVinj.leftInvOn_invFunOn ⟨hKV₁ hz, hKU hz⟩
  have hWo : IsOpen W := hj.continuousOn.isOpen_inter_preimage hU hfV
  have hg : ContMDiffOn 𝓘(ℝ, StdSpace (Fin n)) 𝓘(ℝ, StdSpace (Fin n)) ∞ g W :=
    (hVloc.contMDiffOn_invFunOn hVo hVinj).comp (hj.mono inter_subset_left) fun z hz ↦ hz.2
  refine ⟨g, W, hWo, hKW, contMDiffOn_iff_contDiffOn.1 hg,
    fun z hz ↦ (invFunOn_mem (hmem z hz)).2, hgf, hgK, fun z hz ↦ ?_⟩
  -- Differentiating `f ∘ g = j` at `z ∈ K`, where `g z = z`, gives `df ∘ dg = dj = df`.
  have hgd : MDifferentiableAt 𝓘(ℝ, StdSpace (Fin n)) 𝓘(ℝ, StdSpace (Fin n)) g z :=
    (hg.contMDiffAt (hWo.mem_nhds (hKW hz))).mdifferentiableAt (by simp)
  have hfd : MDifferentiableAt 𝓘(ℝ, StdSpace (Fin n)) I f (g z) := by
    rw [hgK z hz]
    exact (hf.contMDiffAt (hU.mem_nhds (hKU hz))).mdifferentiableAt (by simp)
  have hcomp : f ∘ g =ᶠ[𝓝 z] j :=
    Filter.eventually_of_mem (hWo.mem_nhds (hKW hz)) fun y hy ↦ hgf y hy
  have hchain := mfderiv_comp z hfd hgd
  rw [hcomp.mfderiv_eq, ← hd z hz] at hchain
  have hfg : mfderiv 𝓘(ℝ, StdSpace (Fin n)) I f (g z) = mfderiv 𝓘(ℝ, StdSpace (Fin n)) I f z := by
    rw [hgK z hz]
  rw [hfg, mfderiv_eq_fderiv] at hchain
  ext1 v
  -- `tangentSpaceCast` and `NormedSpace.fromTangentSpace` in `hchain` are identities by definition.
  exact (hd z hz ▸ himm z hz) (by exact (congrArg (fun L ↦ L v) hchain).symm)

/-- **Correcting the ends of a family.** Let `k'` be a family of maps `StdSpace (Fin n) → M`
over `[0, 1]`, jointly smooth on `[0, 1] × U` for an open `U` containing a compact `K`, the model
of `M` having dimension `2 n`. Let `j₀` and `j₁` be smooth on `U`, injective on `K` with injective
derivative along `K`, and let the slice of `k'` at time `0` (`1`) agree with `j₀` (`j₁`) on `K`,
with the same derivative there. Then there is a family `k`, jointly smooth on `[0, 1] × W` for an
open `W ⊇ K`, that agrees with `k'` on `K` at every time, with the same derivative along `K`, and
whose slices at times `0` and `1` are `j₀` and `j₁` on `W`. -/
theorem exists_contMDiffOn_forall_eq_mfderiv_eq [FiniteDimensional ℝ E] [I.Boundaryless]
    [T2Space M] (hdim : Module.finrank ℝ E = 2 * n) {K U : Set (StdSpace (Fin n))}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) {k' : unitInterval × StdSpace (Fin n) → M}
    (hk' : ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) I ∞ k' (univ ×ˢ U))
    {j₀ j₁ : StdSpace (Fin n) → M} (hj₀ : ContMDiffOn 𝓘(ℝ, StdSpace (Fin n)) I ∞ j₀ U)
    (hj₁ : ContMDiffOn 𝓘(ℝ, StdSpace (Fin n)) I ∞ j₁ U)
    (h₀ : ∀ z ∈ K, k' (0, z) = j₀ z) (h₁ : ∀ z ∈ K, k' (1, z) = j₁ z)
    (hd₀ : ∀ z ∈ K, mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k' (0, z)) z =
      mfderiv 𝓘(ℝ, StdSpace (Fin n)) I j₀ z)
    (hd₁ : ∀ z ∈ K, mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k' (1, z)) z =
      mfderiv 𝓘(ℝ, StdSpace (Fin n)) I j₁ z)
    (himm₀ : ∀ z ∈ K, Injective (mfderiv 𝓘(ℝ, StdSpace (Fin n)) I j₀ z))
    (himm₁ : ∀ z ∈ K, Injective (mfderiv 𝓘(ℝ, StdSpace (Fin n)) I j₁ z))
    (hinj₀ : InjOn j₀ K) (hinj₁ : InjOn j₁ K) :
    ∃ k : unitInterval × StdSpace (Fin n) → M, ∃ W, IsOpen W ∧ K ⊆ W ∧
      ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) I ∞ k (univ ×ˢ W) ∧
      (∀ t, ∀ z ∈ K, k (t, z) = k' (t, z)) ∧
      (∀ t, ∀ z ∈ K, mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k (t, z)) z =
        mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k' (t, z)) z) ∧
      (∀ z ∈ W, k (0, z) = j₀ z) ∧ ∀ z ∈ W, k (1, z) = j₁ z := by
  have hslice (t : unitInterval) :
      ContMDiffOn 𝓘(ℝ, StdSpace (Fin n)) I ∞ (fun z ↦ k' (t, z)) U :=
    hk'.comp (contMDiffOn_const.prodMk contMDiffOn_id) fun z hz ↦ ⟨mem_univ _, hz⟩
  -- Right inverses `g₀`, `g₁` of the end slices against `j₀`, `j₁`, near `K`.
  obtain ⟨g₀, W₀, hW₀, hKW₀, hg₀, -, hg₀j, hg₀K, hg₀d⟩ :=
    exists_comp_eq_of_mfderiv_eq hdim hK hU hKU (hslice 0) hj₀ h₀ hd₀ himm₀ hinj₀
  obtain ⟨g₁, W₁, hW₁, hKW₁, hg₁, -, hg₁j, hg₁K, hg₁d⟩ :=
    exists_comp_eq_of_mfderiv_eq hdim hK hU hKU (hslice 1) hj₁ h₁ hd₁ himm₁ hinj₁
  -- The segment `G t = (1 - t) g₀ + t g₁`, which is the identity on `K`.
  set G : unitInterval × StdSpace (Fin n) → StdSpace (Fin n) :=
    fun p ↦ (1 - (p.1 : ℝ)) • g₀ p.2 + (p.1 : ℝ) • g₁ p.2
  have hGK (t : unitInterval) (z : StdSpace (Fin n)) (hz : z ∈ K) : G (t, z) = z := by
    simp only [G, hg₀K z hz, hg₁K z hz, ← add_smul, sub_add_cancel, one_smul]
  have hc : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) 𝓘(ℝ) ∞
      (fun p : unitInterval × StdSpace (Fin n) ↦ (p.1 : ℝ)) :=
    contMDiff_subtypeVal_Icc.comp contMDiff_fst
  have hW₀₁ : IsOpen (W₀ ∩ W₁) := hW₀.inter hW₁
  have hG : ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) 𝓘(ℝ, StdSpace (Fin n)) ∞ G
      (univ ×ˢ (W₀ ∩ W₁)) :=
    ((contMDiff_const.sub hc).contMDiffOn.smul ((contMDiffOn_iff_contDiffOn.2 hg₀).comp
      contMDiffOn_snd fun p (hp : p ∈ univ ×ˢ (W₀ ∩ W₁)) ↦ hp.2.1)).add
      (hc.contMDiffOn.smul ((contMDiffOn_iff_contDiffOn.2 hg₁).comp
      contMDiffOn_snd fun p (hp : p ∈ univ ×ˢ (W₀ ∩ W₁)) ↦ hp.2.2))
  -- A neighbourhood `W` of `K` on which `G t` stays in `U` at every time.
  obtain ⟨u, W, -, hW, hu, hKW, hWN⟩ := generalized_tube_lemma isCompact_univ hK
    (hG.continuousOn.isOpen_inter_preimage (isOpen_univ.prod hW₀₁) hU)
    fun p (hp : p ∈ univ ×ˢ K) ↦ ⟨⟨mem_univ _, hKW₀ hp.2, hKW₁ hp.2⟩, by
      rw [mem_preimage, ← Prod.mk.eta (p := p), hGK _ _ hp.2]; exact hKU hp.2⟩
  have hWN' : univ ×ˢ W ⊆ univ ×ˢ (W₀ ∩ W₁) ∩ G ⁻¹' U :=
    (prod_mono hu subset_rfl).trans hWN
  have hG₀ (z : StdSpace (Fin n)) : G (0, z) = g₀ z := by simp [G]
  have hG₁ (z : StdSpace (Fin n)) : G (1, z) = g₁ z := by simp [G]
  refine ⟨fun p ↦ k' (p.1, G p), W, hW, hKW,
    hk'.comp (contMDiffOn_fst.prodMk (hG.mono fun p hp ↦ (hWN' hp).1))
      fun p hp ↦ ⟨mem_univ _, (hWN' hp).2⟩,
    fun t z hz ↦ by simp only [hGK t z hz], fun t z hz ↦ ?_,
    fun z hz ↦ by simp only [hG₀, hg₀j z (hWN' (mk_mem_prod (mem_univ 0) hz)).1.2.1],
    fun z hz ↦ by simp only [hG₁, hg₁j z (hWN' (mk_mem_prod (mem_univ 1) hz)).1.2.2]⟩
  -- Along `K`, the slice `k' t ∘ G t` has the derivative of `k' t`, since `d (G t) = id`.
  have hg₀z : DifferentiableAt ℝ g₀ z :=
    (hg₀.contDiffAt (hW₀.mem_nhds (hKW₀ hz))).differentiableAt (by simp)
  have hg₁z : DifferentiableAt ℝ g₁ z :=
    (hg₁.contDiffAt (hW₁.mem_nhds (hKW₁ hz))).differentiableAt (by simp)
  have hGf : HasFDerivAt (fun z ↦ G (t, z)) (ContinuousLinearMap.id ℝ (StdSpace (Fin n))) z := by
    have h := (hg₀z.hasFDerivAt.const_smul (1 - (t : ℝ))).add
      (hg₁z.hasFDerivAt.const_smul (t : ℝ))
    rwa [hg₀d z hz, hg₁d z hz, ← add_smul, sub_add_cancel, one_smul] at h
  have hGd : fderiv ℝ (fun z ↦ G (t, z)) z = ContinuousLinearMap.id ℝ _ := hGf.fderiv
  have hGz : MDifferentiableAt 𝓘(ℝ, StdSpace (Fin n)) 𝓘(ℝ, StdSpace (Fin n))
      (fun z ↦ G (t, z)) z :=
    hGf.differentiableAt.mdifferentiableAt
  have hk'z : MDifferentiableAt 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k' (t, z)) (G (t, z)) := by
    rw [hGK t z hz]
    exact ((hslice t).contMDiffAt (hU.mem_nhds (hKU hz))).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp (g := fun z ↦ k' (t, z)) z hk'z hGz
  have hk'G : mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k' (t, z)) (G (t, z)) =
      mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k' (t, z)) z := by
    rw [hGK t z hz]
  rw [hk'G, mfderiv_eq_fderiv, hGd] at hchain
  exact hchain

/-- Frames along a family of immersions at `0`. Let `F : ℝ × StdSpace (Fin n) → M` be smooth on
`univ ×ˢ O`, for an open `O ∋ 0`, into a manifold of dimension `2 n` with a nondegenerate form `σ`,
let each slice `F s` be an immersion at `0`, let `F 0` pull `σ` back to `ω₀` at `0`, and let `B`
be a linear map with `(d (F 1)_0 ∘ B)^* σ = ω₀`. Then a smooth path `P` of linear maps from `1` to
`B` satisfies `(d (F t)_0 ∘ P t)^* σ = ω₀` for every `t`. -/
private theorem exists_contDiff_path_mpullback_eq [FiniteDimensional ℝ E]
    (hσ : σ.IsNondegenerate) (hdim : Module.finrank ℝ E = 2 * n)
    {F : ℝ × StdSpace (Fin n) → M} {O : Set (StdSpace (Fin n))} (hO : IsOpen O)
    (h0O : (0 : StdSpace (Fin n)) ∈ O)
    (hF : ContMDiffOn 𝓘(ℝ, ℝ × StdSpace (Fin n)) I ∞ F (univ ×ˢ O))
    (himm : ∀ s, Injective (mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ F (s, z)) 0))
    (h₀ : ∀ v w : StdSpace (Fin n),
      mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ F (0, z)) σ.val 0 ![v, w] = stdForm (Fin n) v w)
    {B : StdSpace (Fin n) →L[ℝ] StdSpace (Fin n)}
    (hB : ∀ v w : StdSpace (Fin n),
      mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ F (1, z)) σ.val 0 ![B v, B w] =
        stdForm (Fin n) v w) :
    ∃ P : ℝ → StdSpace (Fin n) →L[ℝ] StdSpace (Fin n), ContDiff ℝ ∞ P ∧ P 0 = 1 ∧ P 1 = B ∧
      ∀ t, ∀ v w : StdSpace (Fin n),
        mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ F (t, z)) σ.val 0 ![P t v, P t w] =
          stdForm (Fin n) v w := by
  -- The slices of the pulled-back form `Γ = F^* σ` on `ℝ × StdSpace (Fin n)` give the forms.
  set Γ : ℝ × StdSpace (Fin n) → (ℝ × StdSpace (Fin n)) [⋀^Fin 2]→L[ℝ] ℝ :=
    mpullback 𝓘(ℝ, ℝ × StdSpace (Fin n)) I F σ.val
  have hΓ : ContDiffOn ℝ ∞ Γ (univ ×ˢ O) := σ.contDiffOn_mpullback (isOpen_univ.prod hO) hF
  have hslice (s : ℝ) (v w : StdSpace (Fin n)) :
      mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ F (s, z)) σ.val 0 ![v, w] =
        Γ (s, 0) ![(0, v), (0, w)] := by
    have hι : HasFDerivAt (fun z : StdSpace (Fin n) ↦ (s, z))
        ((0 : StdSpace (Fin n) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ _)) 0 :=
      (hasFDerivAt_const s 0).prodMk (hasFDerivAt_id 0)
    have hFd : MDifferentiableAt 𝓘(ℝ, ℝ × StdSpace (Fin n)) I F (s, 0) :=
      (hF.contMDiffAt ((isOpen_univ.prod hO).mem_nhds ⟨mem_univ _, h0O⟩)).mdifferentiableAt
        (by simp)
    rw [show (fun z ↦ F (s, z)) = F ∘ fun z ↦ (s, z) from rfl,
      mpullback_comp_at hι.differentiableAt.mdifferentiableAt hFd]
    simp only [mpullback_apply, mfderiv_eq_fderiv, hι.fderiv]
    refine Eq.trans ?_ (mpullback_apply F σ.val (s, 0) ![(0, v), (0, w)]).symm
    congr 1
    funext i
    fin_cases i <;> rfl
  -- The forms `κ s = (F s)^* σ` at `0`, as bilinear maps.
  set L : (StdSpace (Fin n) [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] StdSpace (Fin n) →L[ℝ] ℝ :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := StdSpace (Fin n)) (F := ℝ)
      (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hL (γ : StdSpace (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) (v w : StdSpace (Fin n)) :
      L.comp γ.curryLeft v w = γ ![v, w] := by
    simp only [L, LinearIsometryEquiv.toContinuousLinearEquiv_symm, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv,
      ContinuousAlternatingMap.ofSubsingletonLIE_symm_apply,
      ContinuousAlternatingMap.ofSubsingleton_symm_apply_apply,
      ContinuousAlternatingMap.curryLeft_apply_apply]
    congr 1
    funext i
    fin_cases i <;> rfl
  set κ : ℝ → StdSpace (Fin n) →L[ℝ] StdSpace (Fin n) →L[ℝ] ℝ := fun s ↦
    L.comp (mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ F (s, z)) σ.val 0 :
      StdSpace (Fin n) [⋀^Fin 2]→L[ℝ] ℝ).curryLeft
  have hκ (s : ℝ) (v w : StdSpace (Fin n)) :
      κ s v w = mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ F (s, z)) σ.val 0 ![v, w] :=
    hL _ v w
  have hκ' (s : ℝ) (v w : StdSpace (Fin n)) :
      κ s v w = σ.val (F (s, 0)) ![mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ F (s, z)) 0 v,
        mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ F (s, z)) 0 w] :=
    (hκ s v w).trans (mpullback_apply_pair _ _ _ _ _)
  have hκc : ContDiff ℝ ∞ κ := by
    rw [contDiff_clm_apply_iff]
    intro v
    rw [contDiff_clm_apply_iff]
    intro w
    simp only [hκ, hslice]
    exact (ContinuousAlternatingMap.apply ℝ (ℝ × StdSpace (Fin n)) ℝ ![(0, v), (0, w)]
      ).contDiff.comp
      (hΓ.comp_contDiff (contDiff_id.prodMk contDiff_const) fun s ↦ ⟨mem_univ _, h0O⟩)
  have hskew (s : ℝ) (v w : StdSpace (Fin n)) : κ s v w = -κ s w v := by
    rw [hκ, hκ]
    exact ContinuousAlternatingMap.apply_vecCons_swap _ w v
  -- `κ s` is `σ` at `F (s, 0)` read through an isomorphism, so it is nondegenerate.
  have hfin : Module.finrank ℝ (StdSpace (Fin n)) = Module.finrank ℝ E := by
    rw [finrank_stdSpace, Fintype.card_fin, hdim]
  have hsurj (s : ℝ) : Surjective (mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ F (s, z)) 0) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 (himm s)
  have hnd (s : ℝ) : (κ s).toBilinForm.Nondegenerate := by
    let e := LinearEquiv.ofBijective
      (mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ F (s, z)) 0).toLinearMap ⟨himm s, hsurj s⟩
    have heq : (κ s).toBilinForm =
        LinearMap.BilinForm.congr e.symm (σ.bilinFormAt (F (s, 0))) := by
      ext v w
      -- `toBilinForm` and `congr` evaluate by definition; `rw` with their lemmas fails, since
      -- the vectors live in a tangent space that is only definitionally `StdSpace (Fin n)`.
      change κ s v w = σ.bilinFormAt (F (s, 0)) (e.symm.symm v) (e.symm.symm w)
      rw [LinearEquiv.symm_symm, hκ', SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply]
      -- `e` applies the derivative (`LinearEquiv.ofBijective_apply`).
      rfl
    rw [heq]
    exact (hσ.nondegenerate_bilinFormAt (F (s, 0))).congr e.symm
  obtain ⟨P, hP, hP0, hP1, hPκ⟩ := exists_contDiff_path_apply_eq_stdForm (n := ⊤)
    (hκc.of_le (by simp)) hskew hnd (fun v w ↦ (hκ 0 v w).trans (h₀ v w))
    fun v w ↦ (hκ 1 _ _).trans (hB v w)
  exact ⟨P, hP.of_le (by simp), hP0, hP1, fun t v w ↦ (hκ t _ _).symm.trans (hPκ t v w)⟩

/-- The case `r₀ = 0`: a family of maps that sends `0` along a path of centres `c` from `j₀ 0` to
`j₁ 0`, pulls `σ` back to `ω₀` at `0`, starts at `j₀` near `0`, and ends with the derivative of
`j₁` at `0`. -/
private theorem exists_contMDiffOn_mpullback_eq_of_path [FiniteDimensional ℝ E] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] (hσ : σ.IsNondegenerate) (hdim : Module.finrank ℝ E = 2 * n)
    {r : ℝ} (hr : 0 < r) {j₀ j₁ : StdSpace (Fin n) → M} (hj₀ : IsSymplecticBallEmbedding σ r j₀)
    (hj₁ : IsSymplecticBallEmbedding σ r j₁) {c : unitInterval → M}
    (hc : ContMDiff (𝓡∂ 1) I ∞ c) (hc₀ : c 0 = j₀ 0) (hc₁ : c 1 = j₁ 0) :
    ∃ k : unitInterval × StdSpace (Fin n) → M, ∃ U, IsOpen U ∧ (0 : StdSpace (Fin n)) ∈ U ∧
      ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) I ∞ k (univ ×ˢ U) ∧
      (∀ t, k (t, 0) = c t) ∧
      (∀ t, mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k (t, z)) σ.val 0 =
        (stdForm (Fin n)).constSmooth.val 0) ∧
      (∀ z ∈ U, k (0, z) = j₀ z) ∧
      mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k (1, z)) 0 =
        mfderiv 𝓘(ℝ, StdSpace (Fin n)) I j₁ 0 := by
  obtain ⟨U₀, hU₀, hKU₀, hj₀U⟩ := hj₀.exists_contMDiffOn
  have h0r : (0 : StdSpace (Fin n)) ∈ closedBall 0 r := mem_closedBall_self hr.le
  have h0U₀ : (0 : StdSpace (Fin n)) ∈ U₀ := hKU₀ h0r
  have hω₀ (v w : StdSpace (Fin n)) :
      (stdForm (Fin n)).constSmooth.val 0 ![v, w] = stdForm (Fin n) v w :=
    (SmoothBundleForm.eval₂_apply _ _ _ _).symm.trans
      (SymplecticForm.constSmooth_apply (stdForm (Fin n)) 0 v w)
  -- `Ψ` pushes `c 0` along `c`.
  obtain ⟨Ψ, -, -, -, hΨ⟩ := ContMDiff.exists_diffeotopy_forall_apply_eq hc
  -- `Ψ` as an isotopy of `M`, extended by `G` past both ends of `[0, 1]` near `c 0`.
  let Fψ : SmoothIsotopy (ContMDiffMap.id : C^∞⟮I, M; I, M⟯) ⟨Ψ.final, Ψ.final.contMDiff⟩ :=
    { toContMDiffMap := ⟨Ψ, Ψ.contMDiff⟩
      map_zero_left := Ψ.apply_zero
      map_one_left := fun x ↦ (Ψ.final_apply x).symm
      isSmoothEmbedding := fun t ↦ by
        have h := isSmoothEmbedding_diffeomorph (Ψ.timeSlice t)
        rwa [show ⇑(Ψ.timeSlice t) = fun x ↦ Ψ (t, x) from funext (Ψ.timeSlice_apply t)] at h }
  obtain ⟨δ, hδ, V, hcV, G, hG, hGΨ, hGemb⟩ :=
    Fψ.exists_contMDiff_extend (isCompact_singleton (x := c 0))
  obtain ⟨c', hc', hc'id, hc'mem, -⟩ := exists_contDiff_eqOn_id_Icc_mem_Ioo zero_le_one hδ
  have hc'mem' (s : ℝ) : c' s ∈ Ioo (-δ) (1 + δ) := by simpa using hc'mem s
  have hc'I (t : unitInterval) : c' t = t := hc'id t.property
  have hj₀V : j₀ 0 ∈ V := hc₀ ▸ hcV rfl
  -- `F s = G (c' s) ∘ j₀` on the open `O ∋ 0`; it is `Ψ t ∘ j₀` near `0` for `t ∈ [0, 1]`.
  set O := U₀ ∩ j₀ ⁻¹' V
  have hO : IsOpen O := hj₀U.continuousOn.isOpen_inter_preimage hU₀ V.isOpen
  have h0O : (0 : StdSpace (Fin n)) ∈ O := ⟨h0U₀, hj₀V⟩
  set F : ℝ × StdSpace (Fin n) → M := fun p ↦ G (c' p.1, j₀ p.2)
  have hF : ContMDiffOn 𝓘(ℝ, ℝ × StdSpace (Fin n)) I ∞ F (univ ×ˢ O) :=
    hG.comp ((hc'.comp contDiff_fst).contMDiff.contMDiffOn.prodMk
      (hj₀U.comp contDiff_snd.contMDiff.contMDiffOn
        fun p (hp : p ∈ univ ×ˢ O) ↦ hp.2.1)) fun p hp ↦ ⟨hc'mem' p.1, hp.2.2⟩
  have hFΨ (t : unitInterval) : (fun z ↦ F ((t : ℝ), z)) =ᶠ[𝓝 0] fun z ↦ Ψ (t, j₀ z) :=
    Filter.eventually_of_mem (hO.mem_nhds h0O) fun z hz ↦ by
      simp only [F, hc'I t]
      exact hGΨ t _ hz.2
  -- The slices of `F` are immersions at `0`, since those of `G` are embeddings near `c 0`.
  have hAinj (s : ℝ) : Injective (mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ F (s, z)) 0) := by
    have hGs : ContMDiffOn I I ∞ (fun x ↦ G (c' s, x)) V :=
      hG.comp (contMDiffOn_const.prodMk contMDiffOn_id) fun x hx ↦ ⟨hc'mem' s, hx⟩
    have hGd (x : M) (hx : x ∈ V) : MDifferentiableAt I I (fun x ↦ G (c' s, x)) x :=
      (hGs.contMDiffAt (V.isOpen.mem_nhds hx)).mdifferentiableAt (by simp)
    have hj₀d : MDifferentiableAt 𝓘(ℝ, StdSpace (Fin n)) I j₀ 0 :=
      (hj₀U.contMDiffAt (hU₀.mem_nhds h0U₀)).mdifferentiableAt (by simp)
    rw [show (fun z ↦ F (s, z)) = (fun x ↦ G (c' s, x)) ∘ j₀ from rfl,
      mfderiv_comp 0 (hGd _ hj₀V) hj₀d, ContinuousLinearMap.coe_comp]
    refine Injective.comp (fun u u' h ↦ ?_) (hj₀.injective_mfderiv hr h0r)
    -- Read the derivative of `G (c' s)` through the inclusion of `V`.
    have himm := (hGemb (c' s) (hc'mem' s)).isImmersion.mfderiv_injective (by simp)
      ⟨j₀ 0, hj₀V⟩
    have hcomp (u : TangentSpace I (⟨j₀ 0, hj₀V⟩ : V)) :
        mfderiv I I (fun x : V ↦ G (c' s, x)) ⟨j₀ 0, hj₀V⟩ u =
          mfderiv I I (fun x ↦ G (c' s, x)) (j₀ 0) u := by
      rw [show (fun x : V ↦ G (c' s, x)) = (fun x ↦ G (c' s, x)) ∘ Subtype.val from rfl,
        mfderiv_comp (⟨j₀ 0, hj₀V⟩ : V) (hGd _ hj₀V)
          ((contMDiff_subtypeVal (n := 1)).mdifferentiableAt one_ne_zero),
        ContinuousLinearMap.comp_apply, Manifold.mfderiv_subtype_val,
        ContinuousLinearEquiv.coe_coe, Manifold.tangentSpaceOpenEquiv_apply]
    exact himm ((hcomp u).trans (h.trans (hcomp u').symm))
  -- The end frame `B = (d (F 1)_0)⁻¹ ∘ d (j₁)_0`.
  set A₁ := mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ F (1, z)) 0
  have hfin : Module.finrank ℝ (StdSpace (Fin n)) = Module.finrank ℝ E := by
    rw [finrank_stdSpace, Fintype.card_fin, hdim]
  let e₁ := LinearEquiv.ofBijective A₁.toLinearMap ⟨hAinj 1,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 (hAinj 1)⟩
  let B : StdSpace (Fin n) →L[ℝ] StdSpace (Fin n) :=
    (e₁.symm.toLinearMap ∘ₗ (mfderiv 𝓘(ℝ, StdSpace (Fin n)) I j₁ 0).toLinearMap
      ).toContinuousLinearMap
  have hAB (v : StdSpace (Fin n)) : A₁ (B v) = mfderiv 𝓘(ℝ, StdSpace (Fin n)) I j₁ 0 v :=
    e₁.apply_symm_apply _
  have hF10 : F (1, 0) = j₁ 0 := by
    rw [show F (1, 0) = Ψ (1, j₀ 0) from (hFΨ 1).self_of_nhds, ← hc₀, hΨ, hc₁]
  have hF0 : (fun z ↦ F (0, z)) =ᶠ[𝓝 0] j₀ := by
    filter_upwards [hFΨ 0] with z hz
    exact hz.trans (Ψ.apply_zero _)
  obtain ⟨P, hP, hP0, hP1, hPF⟩ := exists_contDiff_path_mpullback_eq hσ hdim hO h0O hF hAinj
    (fun v w ↦ by rw [hF0.mpullback_eq, hj₀.mpullback_eq (mem_ball_self hr)]; exact hω₀ v w)
    (B := B) fun v w ↦ by
      refine (mpullback_apply_pair _ _ _ (B v) (B w)).trans ?_
      rw [hAB, hAB, ← hω₀, ← hj₁.mpullback_eq (mem_ball_self hr), hF10]
      exact (mpullback_apply_pair _ _ _ _ _).symm
  -- The family `k t = Ψ t ∘ j₀ ∘ P t`, smooth where `P t z` stays in `U₀`.
  have hPc : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) 𝓘(ℝ, StdSpace (Fin n)) ∞
      (fun p : unitInterval × StdSpace (Fin n) ↦ P p.1 p.2) :=
    (hP.contMDiff.comp (contMDiff_subtypeVal_Icc.comp contMDiff_fst)).clm_apply contMDiff_snd
  obtain ⟨u, W, -, hW, hu, h0W, hWU⟩ := generalized_tube_lemma isCompact_univ
    (isCompact_singleton (x := (0 : StdSpace (Fin n)))) (hU₀.preimage hPc.continuous)
    fun p (hp : p ∈ univ ×ˢ {0}) ↦ by
      rw [mem_preimage, mem_singleton_iff.1 hp.2, map_zero]
      exact h0U₀
  have hΨj (t : unitInterval) :
      MDifferentiableAt 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ Ψ (t, j₀ z)) 0 :=
    ((Ψ.contMDiff.comp_contMDiffOn (contMDiffOn_const.prodMk hj₀U)).contMDiffAt
      (hU₀.mem_nhds h0U₀)).mdifferentiableAt (by simp)
  refine ⟨fun p ↦ Ψ (p.1, j₀ (P p.1 p.2)), W, hW, h0W rfl,
    Ψ.contMDiff.comp_contMDiffOn (contMDiffOn_fst.prodMk (hj₀U.comp hPc.contMDiffOn
      fun p (hp : p ∈ univ ×ˢ W) ↦ hWU (mk_mem_prod (hu (mem_univ p.1)) hp.2))),
    fun t ↦ by simp only [map_zero, ← hc₀, hΨ], fun t ↦ ?_,
    fun z _ ↦ by
      -- Restate the goal with `Ψ` applied, which elaboration of `fun p ↦ …` had unfolded.
      change Ψ (0, j₀ (P ((0 : unitInterval) : ℝ) z)) = j₀ z
      rw [Set.Icc.coe_zero, hP0]
      exact Ψ.apply_zero _,
    ?_⟩
  · -- `(k t)^* σ = (P t)^* (F t)^* σ = ω₀` at `0`.
    have hcomp : (fun z ↦ Ψ (t, j₀ (P t z))) = (fun z ↦ Ψ (t, j₀ z)) ∘ P t := rfl
    ext m
    have hm : m = ![m 0, m 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hcomp, mpullback_comp_at (P t).differentiableAt.mdifferentiableAt
      (by rw [map_zero]; exact hΨj t), hm, mpullback_apply_pair, mfderiv_eq_fderiv,
      (P t).fderiv, map_zero, ← (hFΨ t).mpullback_eq]
    exact (hPF t (m 0) (m 1)).trans (hω₀ _ _).symm
  · -- `d (k 1)_0 = d (Ψ 1 ∘ j₀)_0 ∘ B = d (j₁)_0`.
    have hcomp : (fun z ↦ Ψ ((1 : unitInterval), j₀ (P ((1 : unitInterval) : ℝ) z))) =
        (fun z ↦ Ψ (1, j₀ z)) ∘ B := by
      rw [Set.Icc.coe_one, hP1]
      rfl
    rw [hcomp, mfderiv_comp 0 (by rw [map_zero]; exact hΨj 1)
      B.differentiableAt.mdifferentiableAt, mfderiv_eq_fderiv, B.fderiv, map_zero]
    ext v
    exact (DFunLike.congr_fun (hFΨ 1).mfderiv_eq (B v)).symm.trans (hAB v)

/-- **A family of maps along a ball with prescribed ends.** Let `M` have dimension `2 n` and carry
a two-form `σ` that is nondegenerate at each point, let `j₀`, `j₁` be symplectic embeddings of
`B(r)`, and let `e` be an `IsSymplecticBallFamily` of radius `r₀`, `0 ≤ r₀ < r`, with `e 0 = j₀` and
`e 1 = j₁` on `B(r₀)`. Then there is a family `k`, jointly smooth on `[0, 1] × U` for an open
`U ⊇ B(r₀)`, that agrees with `e` on `B(r₀)` at every time, whose slices pull `σ` back to `ω₀` at
every point of `B(r₀)`, and whose slices at times `0` and `1` are `j₀` and `j₁` on `U`. -/
theorem IsSymplecticBallFamily.exists_contMDiffOn_eqOn_mpullback_eq
    [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (hσ : σ.IsNondegenerate) (hdim : Module.finrank ℝ E = 2 * n) {r₀ r : ℝ} (hr₀ : 0 ≤ r₀)
    (hr₀r : r₀ < r) {j₀ j₁ : StdSpace (Fin n) → M} (hj₀ : IsSymplecticBallEmbedding σ r j₀)
    (hj₁ : IsSymplecticBallEmbedding σ r j₁) {e : unitInterval × StdSpace (Fin n) → M}
    (he : IsSymplecticBallFamily σ r₀ e)
    (he₀ : ∀ z ∈ closedBall 0 r₀, e (0, z) = j₀ z)
    (he₁ : ∀ z ∈ closedBall 0 r₀, e (1, z) = j₁ z) :
    ∃ k : unitInterval × StdSpace (Fin n) → M, ∃ U, IsOpen U ∧ closedBall 0 r₀ ⊆ U ∧
      ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) I ∞ k (univ ×ˢ U) ∧
      (∀ t, ∀ z ∈ closedBall 0 r₀, k (t, z) = e (t, z)) ∧
      (∀ t, ∀ z ∈ closedBall 0 r₀, mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k (t, z))
        σ.val z = (stdForm (Fin n)).constSmooth.val z) ∧
      (∀ z ∈ U, k (0, z) = j₀ z) ∧ ∀ z ∈ U, k (1, z) = j₁ z := by
  have hr : 0 < r := hr₀.trans_lt hr₀r
  have hKr : closedBall (0 : StdSpace (Fin n)) r₀ ⊆ closedBall 0 r :=
    closedBall_subset_closedBall hr₀r.le
  obtain ⟨U₀, hU₀, hKU₀, hj₀U⟩ := hj₀.exists_contMDiffOn
  obtain ⟨U₁, hU₁, hKU₁, hj₁U⟩ := hj₁.exists_contMDiffOn
  have himm₀ (z : StdSpace (Fin n)) (hz : z ∈ closedBall 0 r₀) :=
    hj₀.injective_mfderiv hr (hKr hz)
  have himm₁ (z : StdSpace (Fin n)) (hz : z ∈ closedBall 0 r₀) :=
    hj₁.injective_mfderiv hr (hKr hz)
  -- A family `k'` that is right along `B(r₀)`, smooth on `[0, 1] × U'`, with `k'_0 = j₀` and
  -- `k'_1 = j₁` to first order along `B(r₀)`.
  obtain ⟨k', U', hU', hKU', hk', hk'e, hk'σ, hk'₀, hk'₁, hd₀, hd₁⟩ :
      ∃ k' : unitInterval × StdSpace (Fin n) → M, ∃ U', IsOpen U' ∧ closedBall 0 r₀ ⊆ U' ∧
        ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) I ∞ k' (univ ×ˢ U') ∧
        (∀ t, ∀ z ∈ closedBall 0 r₀, k' (t, z) = e (t, z)) ∧
        (∀ t, ∀ z ∈ closedBall 0 r₀, mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k' (t, z))
          σ.val z = (stdForm (Fin n)).constSmooth.val z) ∧
        (∀ z ∈ closedBall 0 r₀, k' (0, z) = j₀ z) ∧ (∀ z ∈ closedBall 0 r₀, k' (1, z) = j₁ z) ∧
        (∀ z ∈ closedBall 0 r₀, mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k' (0, z)) z =
          mfderiv 𝓘(ℝ, StdSpace (Fin n)) I j₀ z) ∧
        ∀ z ∈ closedBall 0 r₀, mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k' (1, z)) z =
          mfderiv 𝓘(ℝ, StdSpace (Fin n)) I j₁ z := by
    rcases hr₀.lt_or_eq with hr₀ | rfl
    · -- For `r₀ > 0`, `e` itself: its ends agree with `j₀` and `j₁` on the ball, so to first
      -- order, and its slices pull `σ` back to `ω₀` on the closed ball.
      obtain ⟨Ue, hUe, hKUe, heU⟩ := he.exists_contMDiffOn
      set U' := Ue ∩ U₀ ∩ U₁
      have hKU' : closedBall (0 : StdSpace (Fin n)) r₀ ⊆ U' :=
        subset_inter (subset_inter hKUe (hKr.trans hKU₀)) (hKr.trans hKU₁)
      have hU' : IsOpen U' := (hUe.inter hU₀).inter hU₁
      have hint : (interior (closedBall (0 : StdSpace (Fin n)) r₀)).Nonempty :=
        ((nonempty_ball.2 hr₀).mono ball_subset_interior_closedBall)
      have hslice (t : unitInterval) (z : StdSpace (Fin n)) (hz : z ∈ closedBall 0 r₀) :
          MDifferentiableAt 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ e (t, z)) z :=
        ((heU.comp (contMDiffOn_const.prodMk contMDiffOn_id) fun z hz ↦ ⟨mem_univ _, hz⟩
          ).contMDiffAt (hUe.mem_nhds (hKUe hz))).mdifferentiableAt (by simp)
      have heqd {j : StdSpace (Fin n) → M} (i : unitInterval)
          (hej : ∀ z ∈ closedBall 0 r₀, e (i, z) = j z) {z : StdSpace (Fin n)}
          (hz : z ∈ closedBall 0 r₀) (hj : MDifferentiableAt 𝓘(ℝ, StdSpace (Fin n)) I j z) :
          mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ e (i, z)) z =
            mfderiv 𝓘(ℝ, StdSpace (Fin n)) I j z := by
        have hu : UniqueMDiffWithinAt 𝓘(ℝ, StdSpace (Fin n)) (closedBall 0 r₀) z :=
          uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2
            (uniqueDiffWithinAt_convex (convex_closedBall 0 r₀) hint (subset_closure hz))
        exact hu.eq (f := fun z ↦ e (i, z)) (hslice i z hz).hasMFDerivAt.hasMFDerivWithinAt
          (hj.hasMFDerivAt.hasMFDerivWithinAt.congr_mono (fun y hy ↦ hej y hy) (hej z hz)
            subset_rfl)
      have hjd {j : StdSpace (Fin n) → M} {V : Set (StdSpace (Fin n))} (hV : IsOpen V)
          (hKV : closedBall 0 r₀ ⊆ V) (hjV : ContMDiffOn 𝓘(ℝ, StdSpace (Fin n)) I ∞ j V)
          (z : StdSpace (Fin n)) (hz : z ∈ closedBall 0 r₀) :
          MDifferentiableAt 𝓘(ℝ, StdSpace (Fin n)) I j z :=
        (hjV.contMDiffAt (hV.mem_nhds (hKV hz))).mdifferentiableAt (by simp)
      exact ⟨e, U', hU', hKU', heU.mono (prod_mono subset_rfl
          (inter_subset_left.trans inter_subset_left)),
        fun _ _ _ ↦ rfl,
        fun t z hz ↦ (he.isSymplecticBallEmbedding t).mpullback_eq_of_mem_closedBall hr₀ hz,
        he₀, he₁,
        fun z hz ↦ heqd 0 he₀ hz (hjd hU₀ (hKr.trans hKU₀) hj₀U z hz),
        fun z hz ↦ heqd 1 he₁ hz (hjd hU₁ (hKr.trans hKU₁) hj₁U z hz)⟩
    · -- For `r₀ = 0`, the family of embeddings along the path of centres.
      obtain ⟨Ue, -, hKUe, heU⟩ := he.exists_contMDiffOn
      have h0 : (0 : StdSpace (Fin n)) ∈ closedBall 0 0 := mem_closedBall_self le_rfl
      obtain ⟨k', U', hU', h0U', hk', hk'c, hk'σ, hk'₀, hk'₁⟩ :=
        exists_contMDiffOn_mpullback_eq_of_path (c := fun t ↦ e (t, 0)) hσ hdim hr hj₀ hj₁
          (heU.comp_contMDiff (contMDiff_id.prodMk contMDiff_const) fun t ↦
            ⟨mem_univ _, hKUe h0⟩) (he₀ 0 h0) (he₁ 0 h0)
      have hd₀ : mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k' (0, z)) 0 =
          mfderiv 𝓘(ℝ, StdSpace (Fin n)) I j₀ 0 :=
        Filter.EventuallyEq.mfderiv_eq (Filter.eventually_of_mem (hU'.mem_nhds h0U') hk'₀)
      simp only [closedBall_zero, mem_singleton_iff, forall_eq, singleton_subset_iff]
      exact ⟨k', U', hU', h0U', hk', hk'c, hk'σ, hk'₀ 0 h0U', by rw [hk'c, he₁ 0 h0], hd₀,
        hk'₁⟩
  -- Correct the ends.
  obtain ⟨k, W, hW, hKW, hk, hkk', hkd, hk₀, hk₁⟩ :=
    exists_contMDiffOn_forall_eq_mfderiv_eq hdim (isCompact_closedBall 0 r₀)
      ((hU'.inter hU₀).inter hU₁) (subset_inter (subset_inter hKU' (hKr.trans hKU₀))
      (hKr.trans hKU₁)) (hk'.mono (prod_mono subset_rfl (inter_subset_left.trans
      inter_subset_left))) (hj₀U.mono (inter_subset_left.trans inter_subset_right))
      (hj₁U.mono inter_subset_right) hk'₀ hk'₁ hd₀ hd₁ himm₀ himm₁
      (hj₀.injOn.mono hKr) (hj₁.injOn.mono hKr)
  exact ⟨k, W, hW, hKW, hk, fun t z hz ↦ (hkk' t z hz).trans (hk'e t z hz),
    fun t z hz ↦ by
      have h : mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k (t, z)) σ.val z =
          mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k' (t, z)) σ.val z := by
        ext v
        rw [mpullback_apply, mpullback_apply, hkd t z hz, hkk' t z hz]
      rw [h, hk'σ t z hz],
    hk₀, hk₁⟩

end SymplecticGeometry

end
