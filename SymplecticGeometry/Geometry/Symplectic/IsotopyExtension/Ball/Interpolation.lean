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
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.RightInverse
import SymplecticGeometry.Geometry.Manifold.MFDeriv.UniqueDifferential
import SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.Extension
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Frame
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.ModelSpace
import TauCeti.Geometry.Manifold.SmoothIsotopy.Diffeotopy
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
   convex with nonempty interior (`UniqueMDiffWithinAt.mfderiv_eq_of_eqOn`). For `r₀ = 0`, `e` is
   only a path of centres `c`. A compactly supported diffeotopy `Ψ` pushes `c 0` along `c`
   (`ContMDiff.exists_diffeotopy_forall_apply_eq`), and the family is `Ψ t ∘ j₀ ∘ P t`, where
   `P` is a smooth path of linear maps from `1` to a frame `B` that makes the derivative at `0`
   that of `j₁` at time `1`. The path `P` trivializes the forms `(Ψ t ∘ j₀)^* σ` at `0`
   (`SymplecticGeometry.exists_contDiff_path_apply_eq_stdForm`); for this the times of `Ψ` are
   first extended past both ends of `[0, 1]` (`TauCeti.SmoothIsotopy.exists_contMDiff_extend`).
2. *The ends* (`SymplecticGeometry.exists_contMDiffOn_forall_eq_mfderiv_eq`, the step of
   McDuff–Salamon's Theorem A.2.1(iii) that keeps both ends). If the slice `k'_0` of such a family
   agrees with `j₀` to first order along a compact set `K`, then `k'_0` is a local diffeomorphism
   near `K`, and `g₀ = k'_0⁻¹ ∘ j₀` is the identity, with derivative the identity, along `K`;
   likewise `g₁` at time `1`. The family `k t = k' t ∘ ((1 - t) g₀ + t g₁)` agrees with `k'` on
   `K` to first order, and has the ends `j₀` and `j₁` near `K`. Two maps with the same value and
   derivative at a point pull `σ` back to the same form there
   (`TauCeti.mpullback_apply_eq_of_mfderiv_eq`), so `k` is still right along `B(r₀)`.

## Main results

* `SymplecticGeometry.IsSymplecticBallFamily.exists_contMDiffOn_eqOn_mpullback_eq`: a family
  along `B(r₀)` with prescribed ends.

## Implementation notes

The form on `M` is called `σ`, since `ω` is a token once the scope `ContDiff` is open.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 3.3.1 and Theorem A.2.1(iii).
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

/-- A diffeotopy `Ψ` composed with a map `j₀`, near `0`, with times extended past both ends of
`[0, 1]`. Let `j₀` be smooth on an open `U₀ ∋ 0`, with injective derivative at `0`. Then there is
a map `F : ℝ × StdSpace (Fin n) → M`, smooth on `univ ×ˢ O` for an open `O ∋ 0`, whose slice at
each `t ∈ [0, 1]` is `Ψ t ∘ j₀` near `0`, and whose slices are all immersions at `0`. -/
private theorem exists_contMDiffOn_eventuallyEq_diffeotopy_comp [FiniteDimensional ℝ E]
    [I.Boundaryless] [T2Space M] (Ψ : Diffeotopy I ∞ M) {U₀ : Set (StdSpace (Fin n))}
    (hU₀ : IsOpen U₀) (h0U₀ : (0 : StdSpace (Fin n)) ∈ U₀) {j₀ : StdSpace (Fin n) → M}
    (hj₀U : ContMDiffOn 𝓘(ℝ, StdSpace (Fin n)) I ∞ j₀ U₀)
    (himm : Injective (mfderiv 𝓘(ℝ, StdSpace (Fin n)) I j₀ 0)) :
    ∃ F : ℝ × StdSpace (Fin n) → M, ∃ O, IsOpen O ∧ (0 : StdSpace (Fin n)) ∈ O ∧
      ContMDiffOn 𝓘(ℝ, ℝ × StdSpace (Fin n)) I ∞ F (univ ×ˢ O) ∧
      (∀ t : unitInterval, (fun z ↦ F ((t : ℝ), z)) =ᶠ[𝓝 0] fun z ↦ Ψ (t, j₀ z)) ∧
      ∀ s, Injective (mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ F (s, z)) 0) := by
  -- `Ψ` as an isotopy of `M`, extended by `G` past both ends of `[0, 1]` near `j₀ 0`.
  obtain ⟨δ, hδ, V, hcV, G, hG, hGΨ, hGemb⟩ :=
    (Ψ.smoothIsotopy ContMDiffMap.id Manifold.IsSmoothEmbedding.id).exists_contMDiff_extend
      (isCompact_singleton (x := j₀ 0))
  obtain ⟨c', hc', hc'id, hc'mem, -⟩ := exists_contDiff_eqOn_id_Icc_mem_Ioo zero_le_one hδ
  have hc'mem' (s : ℝ) : c' s ∈ Ioo (-δ) (1 + δ) := by simpa using hc'mem s
  have hj₀V : j₀ 0 ∈ V := hcV rfl
  -- `F s = G (c' s) ∘ j₀` on the open `O ∋ 0`.
  set O := U₀ ∩ j₀ ⁻¹' V
  have hO : IsOpen O := hj₀U.continuousOn.isOpen_inter_preimage hU₀ V.isOpen
  refine ⟨fun p ↦ G (c' p.1, j₀ p.2), O, hO, ⟨h0U₀, hj₀V⟩,
    hG.comp ((hc'.comp contDiff_fst).contMDiff.contMDiffOn.prodMk
      (hj₀U.comp contDiff_snd.contMDiff.contMDiffOn
        fun p (hp : p ∈ univ ×ˢ O) ↦ hp.2.1)) fun p hp ↦ ⟨hc'mem' p.1, hp.2.2⟩,
    fun t ↦ Filter.eventually_of_mem (hO.mem_nhds ⟨h0U₀, hj₀V⟩) fun z hz ↦ ?_, fun s ↦ ?_⟩
  · simp only [hc'id t.property]
    exact (hGΨ t _ hz.2).trans (Ψ.smoothIsotopy_apply _ _ _)
  -- The slices are immersions at `0`, since those of `G` are embeddings near `j₀ 0`.
  have hGs : ContMDiffOn I I ∞ (fun x ↦ G (c' s, x)) V :=
    hG.comp (contMDiffOn_const.prodMk contMDiffOn_id) fun x hx ↦ ⟨hc'mem' s, hx⟩
  have hj₀d : MDifferentiableAt 𝓘(ℝ, StdSpace (Fin n)) I j₀ 0 :=
    (hj₀U.contMDiffAt (hU₀.mem_nhds h0U₀)).mdifferentiableAt (by simp)
  rw [show (fun z ↦ G (c' s, j₀ z)) = (fun x ↦ G (c' s, x)) ∘ j₀ from rfl,
    mfderiv_comp 0 ((hGs.contMDiffAt (V.isOpen.mem_nhds hj₀V)).mdifferentiableAt (by simp)) hj₀d,
    ContinuousLinearMap.coe_comp]
  refine Injective.comp (fun u u' h ↦ ?_) himm
  -- Read the derivative of `G (c' s)` through the inclusion of `V`.
  have hres (w : TangentSpace I (j₀ 0)) :=
    Manifold.mfderiv_comp_subtype_val_apply (I := I) (J := I) (f := fun x ↦ G (c' s, x))
      (x := ⟨j₀ 0, hj₀V⟩) w
  exact (hGemb (c' s) (hc'mem' s)).isImmersion.mfderiv_injective (by simp) (x := ⟨j₀ 0, hj₀V⟩)
    ((hres u).trans (h.trans (hres u').symm))

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
  obtain ⟨F, O, hO, h0O, hF, hFΨ, hAinj⟩ :=
    exists_contMDiffOn_eventuallyEq_diffeotopy_comp Ψ hU₀ h0U₀ hj₀U (hj₀.injective_mfderiv hr h0r)
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

/-- For `r₀ > 0`, a slice of an `IsSymplecticBallFamily` of radius `r₀` that agrees on `B(r₀)`
with a map `j`, smooth on a neighbourhood of `B(r₀)`, has the derivative of `j` at each point of
`B(r₀)`. -/
private theorem IsSymplecticBallFamily.mfderiv_eq_of_eqOn {r₀ : ℝ} (hr₀ : 0 < r₀)
    {e : unitInterval × StdSpace (Fin n) → M} (he : IsSymplecticBallFamily σ r₀ e)
    (i : unitInterval) {j : StdSpace (Fin n) → M} {V : Set (StdSpace (Fin n))} (hV : IsOpen V)
    (hKV : closedBall 0 r₀ ⊆ V) (hjV : ContMDiffOn 𝓘(ℝ, StdSpace (Fin n)) I ∞ j V)
    (hej : ∀ z ∈ closedBall 0 r₀, e (i, z) = j z) {z : StdSpace (Fin n)}
    (hz : z ∈ closedBall 0 r₀) :
    mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ e (i, z)) z =
      mfderiv 𝓘(ℝ, StdSpace (Fin n)) I j z := by
  obtain ⟨Ue, hUe, hKUe, heU⟩ := he.exists_contMDiffOn
  refine (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffWithinAt_convex
    (convex_closedBall 0 r₀) ((nonempty_ball.2 hr₀).mono ball_subset_interior_closedBall)
    (subset_closure hz))).mfderiv_eq_of_eqOn hz ?_
    ((hjV.contMDiffAt (hV.mem_nhds (hKV hz))).mdifferentiableAt (by simp)) hej
  exact ((heU.comp (contMDiffOn_const.prodMk contMDiffOn_id) fun z hz ↦ ⟨mem_univ _, hz⟩
    ).contMDiffAt (hUe.mem_nhds (hKUe hz))).mdifferentiableAt (by simp)

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
      exact ⟨e, Ue, hUe, hKUe, heU, fun _ _ _ ↦ rfl,
        fun t z hz ↦ (he.isSymplecticBallEmbedding t).mpullback_eq_of_mem_closedBall hr₀ hz,
        he₀, he₁, fun z hz ↦ he.mfderiv_eq_of_eqOn hr₀ 0 hU₀ (hKr.trans hKU₀) hj₀U he₀ hz,
        fun z hz ↦ he.mfderiv_eq_of_eqOn hr₀ 1 hU₁ (hKr.trans hKU₁) hj₁U he₁ hz⟩
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
    exists_contMDiffOn_forall_eq_mfderiv_eq (by rw [finrank_stdSpace, Fintype.card_fin, hdim])
      (isCompact_closedBall 0 r₀)
      ((hU'.inter hU₀).inter hU₁) (subset_inter (subset_inter hKU' (hKr.trans hKU₀))
      (hKr.trans hKU₁)) (hk'.mono (prod_mono subset_rfl (inter_subset_left.trans
      inter_subset_left))) (hj₀U.mono (inter_subset_left.trans inter_subset_right))
      (hj₁U.mono inter_subset_right) hk'₀ hk'₁ hd₀ hd₁ himm₀ himm₁
      (hj₀.injOn.mono hKr) (hj₁.injOn.mono hKr)
  exact ⟨k, W, hW, hKW, hk, fun t z hz ↦ (hkk' t z hz).trans (hk'e t z hz),
    fun t z hz ↦ (mpullback_apply_eq_of_mfderiv_eq (f := fun z ↦ k (t, z)) (hkk' t z hz)
      (hkd t z hz) σ.val).trans (hk'σ t z hz), hk₀, hk₁⟩

end SymplecticGeometry

end
