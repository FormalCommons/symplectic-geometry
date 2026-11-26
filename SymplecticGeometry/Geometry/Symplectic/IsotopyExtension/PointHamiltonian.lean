/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Velocity
import SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.Family
import SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.Transport

/-!
# Functions whose differential at `H (t, s)` is `σ (∂ₛ H (t, s), ·)`

Let `σ` be a two-form on a Hausdorff, σ-compact, boundaryless manifold `M`, and
`H : [0, 1] × [0, 1] → M` smooth. Given a smooth family `e (t, ·)` of embeddings of an open subset
`P` of a vector space of the dimension of `M`, with `e (t, x₀) = H (t, 0)`, this file builds a
smooth function `F (t, y, s)` on `[0, 1] × M × [0, 1]`, supported in a compact subset of any given
open neighbourhood of the image of `H`, whose differential in `y` at `H (t, s)` is the contraction
`σ (∂ₛ H (t, s), ·)` (`SymplecticGeometry.exists_contMDiff_mfderiv_eq_velocity_contraction`).
When `σ` is nondegenerate, a Hamiltonian vector field of `F (t, ·, s)` therefore takes the value
`∂ₛ H (t, s)` at `H (t, s)`, which is what the flow of `F (t, ·, ·)` needs in order to move
`H (t, 0)` along `s ↦ H (t, s)`. Moreover `F (t, ·, ·) = 0` whenever `H (t, ·)` is constant.

The construction:

1. The embeddings `e (t, ·)` are moved along `H` into a two-parameter family of embeddings
   `k (t, s, ·)` of `P` with `k (t, s, x₀) = H (t, s)`
   (`ContMDiff.exists_contMDiff_isSmoothEmbedding_unitInterval_family_apply_eq`).
2. The slices at `x₀` of the velocity forms of the isotopies `s ↦ k (t, s, ·)`, read as linear
   functions `h (t, s, ·)` on `P`, are jointly smooth
   (`SymplecticGeometry.isSmoothFamily_velocityForm`).
3. A function `F` with `F (t, k (t, s, ·), s) = h (t, s, ·)` near `x₀`
   (`ContMDiff.exists_contMDiff_unitInterval_family_comp_eventuallyEq`). Differentiating at `x₀`,
   where the differential of `k (t, s, ·)` is onto, gives the claim.

## Main results

* `SymplecticGeometry.exists_contMDiff_mfderiv_eq_velocity_contraction`: a smooth family of
  compactly supported functions whose differentials at `H (t, s)` are `σ (∂ₛ H (t, s), ·)`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 3.3.1.
-/

public section

noncomputable section

open Set Function Filter Manifold TopologicalSpace
open scoped ContDiff Manifold Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : TauCeti.SmoothTwoForm I M} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

namespace SymplecticGeometry

open TauCeti

/-- **Functions whose differential at `H (t, s)` is `σ (∂ₛ H (t, s), ·)`.** Let `σ` be a
two-form on a Hausdorff, σ-compact, boundaryless manifold `M` modelled on `E`, and let
`H : [0, 1] × [0, 1] → M` be smooth. Let `P` be an open subset of a real normed space `E'` with
`dim E' = dim E`, and `e : [0, 1] × P → M` smooth with every slice `e (t, ·)` a smooth embedding
and `e (t, x₀) = H (t, 0)`. Let `W ⊆ M` be open and contain every `H (t, s)`. Then there are a
smooth `F : [0, 1] × M × [0, 1] → ℝ` and a compact `C ⊆ W` such that
* `F (t, y, s) = 0` for `y ∉ C`;
* `F (t, ·, ·) = 0` for every `t` such that `H (t, s) = H (t, 0)` for all `s`;
* for all `t` and `s`, the differential of `F (t, ·, s)` at `H (t, s)` is
  `v ↦ σ (∂ₛ H (t, s), v)`. -/
theorem exists_contMDiff_mfderiv_eq_velocity_contraction [FiniteDimensional ℝ E]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (hd : Module.finrank ℝ E' = Module.finrank ℝ E)
    {H : unitInterval × unitInterval → M} (hH : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) I ∞ H)
    {P : Opens E'} {e : unitInterval × P → M} (he : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E')) I ∞ e)
    (hemb₀ : ∀ t, IsSmoothEmbedding 𝓘(ℝ, E') I ∞ fun x ↦ e (t, x)) {x₀ : P}
    (heH : ∀ t, e (t, x₀) = H (t, 0))
    {W : Set M} (hW : IsOpen W) (hHW : ∀ t s, H (t, s) ∈ W) :
    ∃ (F : unitInterval × M × unitInterval → ℝ) (C : Set M),
      ContMDiff ((𝓡∂ 1).prod (I.prod (𝓡∂ 1))) 𝓘(ℝ) ∞ F ∧ IsCompact C ∧ C ⊆ W ∧
      (∀ t y s, y ∉ C → F (t, y, s) = 0) ∧
      (∀ t, (∀ s, H (t, s) = H (t, 0)) → ∀ y s, F (t, y, s) = 0) ∧
      ∀ t s (v : TangentSpace I (H (t, s))),
        σ.val (H (t, s)) ![mfderiv (𝓡∂ 1) I (fun u ↦ H (t, u)) s 1, v] =
          mfderiv I 𝓘(ℝ) (fun y ↦ F (t, y, s)) (H (t, s)) v := by
  -- Step 1: the embeddings `e (t, ·)`, moved along `H`.
  obtain ⟨k, hk, hemb, -, hkH⟩ :=
    ContMDiff.exists_contMDiff_isSmoothEmbedding_unitInterval_family_apply_eq he hemb₀ x₀ hH
      fun t ↦ (heH t).symm
  -- The isotopies `s ↦ k (t, s, ·)`.
  let g : unitInterval → unitInterval → C^∞⟮𝓘(ℝ, E'), P; I, M⟯ := fun t s ↦
    ⟨fun x ↦ k (t, s, x), (hemb t s).isImmersion.contMDiff⟩
  let kt : ∀ t, SmoothIsotopy (g t 0) (g t 1) := fun t ↦
    { toContMDiffMap := ⟨fun p ↦ k (t, p.1, p.2), hk.comp (contMDiff_const.prodMk contMDiff_id)⟩
      map_zero_left := fun _ ↦ rfl
      map_one_left := fun _ ↦ rfl
      isSmoothEmbedding := hemb t }
  have hkt (t : unitInterval) (p : unitInterval × P) : ⇑(kt t) p = k (t, p.1, p.2) := rfl
  -- Step 2: the velocity forms at `x₀`, as linear functions `h` on `P`.
  let α : unitInterval × unitInterval → SmoothForm 𝓘(ℝ, E') P ℝ 1 := fun q ↦
    SmoothForm.mpullback (Prod.mk q.2) (contMDiff_const.prodMk contMDiff_id)
      ((kt q.1).velocityForm σ)
  let L : unitInterval × unitInterval → E' →L[ℝ] ℝ := fun q ↦
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E') (F := ℝ) (0 : Fin 1)).symm
      ((α q).val x₀)
  have hL (q : unitInterval × unitInterval) (v : TangentSpace 𝓘(ℝ, E') x₀) :
      L q v = (α q).val x₀ ![v] := by
    rw [Matrix.vec_single_eq_const]
    exact (congrArg (· v) (ContinuousAlternatingMap.ofSubsingletonLIE_symm_apply (𝕜 := ℝ)
      (E := E') (F := ℝ) (0 : Fin 1) ((α q).val x₀))).trans
      (ContinuousAlternatingMap.ofSubsingleton_symm_apply_apply _ _ _ _ _ _)
  have hvel (t s : unitInterval) :
      mfderiv (𝓡∂ 1) I (fun u ↦ k (t, u, x₀)) s 1 = mfderiv (𝓡∂ 1) I (fun u ↦ H (t, u)) s 1 :=
    congrArg (fun f ↦ mfderiv (𝓡∂ 1) I f s 1) (funext fun u ↦ hkH t u)
  have hLσ (t s : unitInterval) (v : E') :
      L (t, s) v = σ.val (k (t, s, x₀)) ![mfderiv (𝓡∂ 1) I (fun u ↦ H (t, u)) s 1,
        mfderiv 𝓘(ℝ, E') I (fun y ↦ k (t, s, y)) x₀ v] := by
    rw [hL (t, s) v, SmoothIsotopy.mpullback_prodMk_velocityForm σ (kt t) s x₀ v, ← hvel]
    -- `kt t (s, x)` is `k (t, s, x)` by definition (`hkt`), also in the base points of the
    -- tangent spaces, which `rw` cannot reach.
    rfl
  let h : unitInterval × unitInterval × P → ℝ := fun p ↦ L (p.1, p.2.1) (p.2.2 : E')
  have hh : ContMDiff ((𝓡∂ 1).prod ((𝓡∂ 1).prod 𝓘(ℝ, E'))) 𝓘(ℝ) ∞ h := by
    have hLs : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, E' →L[ℝ] ℝ) ∞ L :=
      (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E') (F := ℝ)
        (0 : Fin 1)).symm.contDiff.contMDiff.comp
        ((isSmoothFamily_velocityForm σ (Ĝ := fun q ↦ k (q.1.1, q.1.2, q.2))
          (hk.comp ((contMDiff_fst.comp contMDiff_fst).prodMk
            ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd))) kt
          fun t p ↦ hkt t p).contMDiff_val_apply x₀)
    exact (hLs.comp (contMDiff_fst.prodMk contMDiff_snd.fst)).clm_apply
      (contMDiff_subtypeVal.comp contMDiff_snd.snd)
  -- Step 3: a function `F` that reads `h` along `k`.
  obtain ⟨F, C, hF, hC, hCW, hFC, hFk, hF0⟩ :=
    hk.exists_contMDiff_unitInterval_family_comp_eventuallyEq hd (isCompact_singleton (x := x₀))
      hemb hh hW fun a s x hx ↦ by rw [hx, hkH]; exact hHW a s
  refine ⟨F, C, hF, hC, hCW, hFC, fun t ht ↦ hF0 t fun s y ↦ ?_, fun t s v ↦ ?_⟩
  · -- If `H (t, ·)` is constant, its velocity vanishes, and so does `h (t, ·, ·)`.
    have h0 : mfderiv (𝓡∂ 1) I (fun u ↦ H (t, u)) s 1 = 0 := by
      rw [show (fun u ↦ H (t, u)) = fun _ ↦ H (t, 0) from funext ht, mfderiv_const]
      -- the zero map, applied to `1`
      rfl
    exact (hLσ t s y).trans (ContinuousAlternatingMap.map_coord_zero _ 0 h0)
  · -- Differentiate `F (t, k (t, s, ·), s) = h (t, s, ·)` at `x₀`, where `dk` is onto.
    have hloc : IsLocalDiffeomorph 𝓘(ℝ, E') I ∞ (fun y ↦ k (t, s, y)) :=
      (hemb t s).isImmersion.isLocalDiffeomorph hd (by simp)
    obtain ⟨w, rfl⟩ := ((hloc x₀).isInvertible_mfderiv (by simp)).surjective v
    have hkd : MDifferentiableAt 𝓘(ℝ, E') I (fun y ↦ k (t, s, y)) x₀ :=
      (hk.comp (contMDiff_const.prodMk (contMDiff_const.prodMk contMDiff_id))).mdifferentiableAt
        (by simp)
    have hFd : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ F (t, y, s)) (k (t, s, x₀)) :=
      (hF.comp (contMDiff_const.prodMk (contMDiff_id.prodMk contMDiff_const))).mdifferentiableAt
        (by simp)
    have key : σ.val (k (t, s, x₀)) ![mfderiv (𝓡∂ 1) I (fun u ↦ H (t, u)) s 1,
        mfderiv 𝓘(ℝ, E') I (fun y ↦ k (t, s, y)) x₀ w] =
        mfderiv I 𝓘(ℝ) (fun y ↦ F (t, y, s)) (k (t, s, x₀))
          (mfderiv 𝓘(ℝ, E') I (fun y ↦ k (t, s, y)) x₀ w) := by
      refine (hLσ t s w).symm.trans (Eq.trans ?_ (mfderiv_comp_apply x₀ hFd hkd w))
      rw [show (fun y ↦ F (t, y, s)) ∘ (fun y ↦ k (t, s, y)) = fun y ↦ F (t, k (t, s, y), s)
        from rfl, (hFk t s x₀ rfl).mfderiv_eq,
        show (fun y : P ↦ h (t, s, y)) = L (t, s) ∘ Subtype.val from rfl]
      exact ((Manifold.mfderiv_comp_subtype_val_apply (I := 𝓘(ℝ)) (f := ⇑(L (t, s))) w).trans
        (DFunLike.congr_fun (L (t, s)).mfderiv_eq w)).symm
    exact (hkH t s) ▸ key

end SymplecticGeometry

end
