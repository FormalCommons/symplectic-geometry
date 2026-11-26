/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod
import SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.Family
import SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.Transport
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Isotopy
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Velocity
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Hamiltonians that move a two-parameter family of points

Let `σ` be a two-form on a Hausdorff, σ-compact, boundaryless manifold `M` of dimension `2n`, and
`H : [0, 1] × [0, 1] → M` smooth. Given a smooth family of symplectic balls `e (t, ·)` centred at
`H (t, 0)`, this file builds a smooth function `F (t, y, s)` on `[0, 1] × M × [0, 1]`, supported
in a compact subset of any given open neighbourhood of the image of `H`, whose differential in `y`
at `H (t, s)` is the contraction `σ (∂ₛ H (t, s), ·)`
(`SymplecticGeometry.exists_contMDiff_mfderiv_eq_velocity_contraction`). When `σ` is
nondegenerate, a Hamiltonian vector field of `F (t, ·, s)` therefore takes the value
`∂ₛ H (t, s)` at `H (t, s)`, which is what the flow of `F (t, ·, ·)` needs in order to move
`H (t, 0)` along `s ↦ H (t, s)`. Moreover `F (t, ·, ·) = 0` whenever `H (t, ·)` is constant.

The construction:

1. The balls `e (t, ·)` are, near `B(r)`, a smooth family of embeddings of an open set `P`
   (`SymplecticGeometry.IsSymplecticBallFamily.exists_smoothIsotopy`). They are moved along `H`
   into a two-parameter family of embeddings `k (t, s, ·)` of `P` with `k (t, s, 0) = H (t, s)`
   (`ContMDiff.exists_contMDiff_isSmoothEmbedding_unitInterval_family_apply_eq`).
2. The velocity forms of the isotopies `s ↦ k (t, s, ·)`, at `0`, read as linear functions
   `h (t, s, ·)` on `P`, are jointly smooth
   (`SymplecticGeometry.contMDiff_mpullback_prodMk_velocityForm_apply`).
3. A function `F` with `F (t, k (t, s, ·), s) = h (t, s, ·)` near `0`
   (`ContMDiff.exists_contMDiff_unitInterval_family_comp_eventuallyEq`). Differentiating at `0`,
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

open Set Function Metric Filter
open scoped ContDiff Manifold Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : TauCeti.SmoothTwoForm I M}

namespace SymplecticGeometry

open TauCeti

variable {n : ℕ}

/-- **Hamiltonians whose vector fields move a two-parameter family of points.** Let `σ` be a
two-form on a Hausdorff, σ-compact, boundaryless manifold `M` of dimension `2n`, let
`H : [0, 1] × [0, 1] → M` be smooth, and let `e (t, ·)` be a smooth family of symplectic balls of
radius `r > 0` with `e (t, 0) = H (t, 0)`. Let `W ⊆ M` be open and contain every `H (t, s)`.
Then there are a smooth `F : [0, 1] × M × [0, 1] → ℝ` and a compact `C ⊆ W` such that
* `F (t, y, s) = 0` for `y ∉ C`;
* `F (t, ·, ·) = 0` for every `t` such that `H (t, s) = H (t, 0)` for all `s`;
* for all `t` and `s`, the differential of `F (t, ·, s)` at `H (t, s)` is
  `v ↦ σ (∂ₛ H (t, s), v)`. -/
theorem exists_contMDiff_mfderiv_eq_velocity_contraction [FiniteDimensional ℝ E]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] (hdim : Module.finrank ℝ E = 2 * n)
    {H : unitInterval × unitInterval → M} (hH : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) I ∞ H)
    {r : ℝ} (hr : 0 < r) {e : unitInterval × StdSpace (Fin n) → M}
    (he : IsSymplecticBallFamily σ r e) (heH : ∀ t, e (t, 0) = H (t, 0))
    {W : Set M} (hW : IsOpen W) (hHW : ∀ t s, H (t, s) ∈ W) :
    ∃ (F : unitInterval × M × unitInterval → ℝ) (C : Set M),
      ContMDiff ((𝓡∂ 1).prod (I.prod (𝓡∂ 1))) 𝓘(ℝ) ∞ F ∧ IsCompact C ∧ C ⊆ W ∧
      (∀ t y s, y ∉ C → F (t, y, s) = 0) ∧
      (∀ t, (∀ s, H (t, s) = H (t, 0)) → ∀ y s, F (t, y, s) = 0) ∧
      ∀ t s (v : TangentSpace I (H (t, s))),
        σ.val (H (t, s)) ![mfderiv (𝓡∂ 1) I (fun u ↦ H (t, u)) s 1, v] =
          mfderiv I 𝓘(ℝ) (fun y ↦ F (t, y, s)) (H (t, s)) v := by
  -- Step 1: the balls as embeddings of `P`, moved along `H`.
  obtain ⟨P, hrP, f₀, f₁, k₀, hk₀⟩ := he.exists_smoothIsotopy hr
  let x₀ : P := ⟨0, hrP (mem_closedBall_self hr.le)⟩
  obtain ⟨k, hk, hemb, -, hkH⟩ :=
    ContMDiff.exists_contMDiff_isSmoothEmbedding_unitInterval_family_apply_eq k₀.contMDiff
      (fun t ↦ k₀.isSmoothEmbedding t) x₀ hH fun t ↦ by rw [hk₀]; exact (heH t).symm
  have hd : Module.finrank ℝ (StdSpace (Fin n)) = Module.finrank ℝ E := by
    simp [hdim, two_mul]
  -- The isotopies `s ↦ k (t, s, ·)`.
  let g : unitInterval → unitInterval → C^∞⟮𝓘(ℝ, StdSpace (Fin n)), P; I, M⟯ := fun t s ↦
    ⟨fun x ↦ k (t, s, x), (hemb t s).isImmersion.contMDiff⟩
  let kt : ∀ t, SmoothIsotopy (g t 0) (g t 1) := fun t ↦
    { toContMDiffMap := ⟨fun p ↦ k (t, p.1, p.2), hk.comp (contMDiff_const.prodMk contMDiff_id)⟩
      map_zero_left := fun _ ↦ rfl
      map_one_left := fun _ ↦ rfl
      isSmoothEmbedding := hemb t }
  have hkt (t : unitInterval) (p : unitInterval × P) : ⇑(kt t) p = k (t, p.1, p.2) := rfl
  -- Step 2: the velocity forms at `x₀`, as linear functions `h` on `P`.
  let L : unitInterval × unitInterval → StdSpace (Fin n) →L[ℝ] ℝ := fun q ↦
    ((SmoothForm.mpullback (Prod.mk q.2) (contMDiff_const.prodMk contMDiff_id)
      ((kt q.1).velocityForm σ)).val x₀).toContinuousMultilinearMap.toContinuousLinearMap 0 0
  have hL (q : unitInterval × unitInterval) (v : StdSpace (Fin n)) :
      L q v = (SmoothForm.mpullback (Prod.mk q.2) (contMDiff_const.prodMk contMDiff_id)
        ((kt q.1).velocityForm σ)).val x₀ ![v] := by
    -- `L q v` is the form on the family that is `v` at the one index.
    change (SmoothForm.mpullback (Prod.mk q.2) (contMDiff_const.prodMk contMDiff_id)
      ((kt q.1).velocityForm σ)).val x₀ (Function.update 0 0 v) = _
    congr 1
    funext j
    fin_cases j
    exact Function.update_self _ _ _
  have hvel (t s : unitInterval) :
      mfderiv (𝓡∂ 1) I (fun u ↦ k (t, u, x₀)) s 1 = mfderiv (𝓡∂ 1) I (fun u ↦ H (t, u)) s 1 :=
    congrArg (fun f ↦ mfderiv (𝓡∂ 1) I f s 1) (funext fun u ↦ hkH t u)
  have hLσ (t s : unitInterval) (v : StdSpace (Fin n)) :
      L (t, s) v = σ.val (k (t, s, x₀)) ![mfderiv (𝓡∂ 1) I (fun u ↦ H (t, u)) s 1,
        mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun y ↦ k (t, s, y)) x₀ v] := by
    rw [hL, SmoothIsotopy.mpullback_prodMk_velocityForm σ (kt t) s x₀ v, ← hvel]
    -- `kt t (s, x)` is `k (t, s, x)` by definition (`hkt`), also in the base points of the
    -- tangent spaces, which `rw` cannot reach.
    rfl
  let h : unitInterval × unitInterval × P → ℝ := fun p ↦ L (p.1, p.2.1) (p.2.2 : StdSpace (Fin n))
  have hh : ContMDiff ((𝓡∂ 1).prod ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n)))) 𝓘(ℝ) ∞ h := by
    convert (contMDiff_mpullback_prodMk_velocityForm_apply σ (Ĝ := fun q ↦ k (q.1.1, q.1.2, q.2))
      (hk.comp ((contMDiff_fst.comp contMDiff_fst).prodMk
        ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd))) kt (fun t p ↦ hkt t p)
      x₀).comp ((contMDiff_fst.prodMk contMDiff_snd.fst).prodMk
        (contMDiff_subtypeVal.comp contMDiff_snd.snd)) using 1
    funext p
    exact hL _ _
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
    have hloc : IsLocalDiffeomorph 𝓘(ℝ, StdSpace (Fin n)) I ∞ (fun y ↦ k (t, s, y)) :=
      (hemb t s).isImmersion.isLocalDiffeomorph hd (by simp)
    obtain ⟨w, rfl⟩ := ((hloc x₀).isInvertible_mfderiv (by simp)).surjective v
    have hkd : MDifferentiableAt 𝓘(ℝ, StdSpace (Fin n)) I (fun y ↦ k (t, s, y)) x₀ :=
      (hk.comp (contMDiff_const.prodMk (contMDiff_const.prodMk contMDiff_id))).mdifferentiableAt
        (by simp)
    have hFd : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ F (t, y, s)) (k (t, s, x₀)) :=
      (hF.comp (contMDiff_const.prodMk (contMDiff_id.prodMk contMDiff_const))).mdifferentiableAt
        (by simp)
    have key : σ.val (k (t, s, x₀)) ![mfderiv (𝓡∂ 1) I (fun u ↦ H (t, u)) s 1,
        mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun y ↦ k (t, s, y)) x₀ w] =
        mfderiv I 𝓘(ℝ) (fun y ↦ F (t, y, s)) (k (t, s, x₀))
          (mfderiv 𝓘(ℝ, StdSpace (Fin n)) I (fun y ↦ k (t, s, y)) x₀ w) := by
      refine (hLσ t s w).symm.trans (Eq.trans ?_ (mfderiv_comp_apply x₀ hFd hkd w))
      rw [show (fun y ↦ F (t, y, s)) ∘ (fun y ↦ k (t, s, y)) = fun y ↦ F (t, k (t, s, y), s)
        from rfl, (hFk t s x₀ rfl).mfderiv_eq,
        show (fun y : P ↦ h (t, s, y)) = L (t, s) ∘ Subtype.val from rfl]
      exact ((Manifold.mfderiv_comp_subtype_val_apply (I := 𝓘(ℝ)) (f := ⇑(L (t, s))) w).trans
        (DFunLike.congr_fun (L (t, s)).mfderiv_eq w)).symm
    exact (hkH t s) ▸ key

end SymplecticGeometry

end
