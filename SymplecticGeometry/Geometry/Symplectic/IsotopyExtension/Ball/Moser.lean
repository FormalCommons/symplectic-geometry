/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Opens
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Poincare
import SymplecticGeometry.Geometry.Symplectic.Manifold.Family
import SymplecticGeometry.Geometry.Symplectic.Moser.Family
import SymplecticGeometry.Topology.MetricSpace.ProperSpace.Lemmas
import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Symplectic.Manifold.Opens

/-!
# Moser's correction of a family of balls

Let `B(r)` be the closed ball `Metric.closedBall 0 r` of `StdSpace (Fin n)`, with the standard
form `ω₀ = (stdForm (Fin n)).constSmooth`, and `σ` a closed two-form on `M`. Let
`k : [0, 1] × StdSpace (Fin n) → M` be smooth on `[0, 1] × U` for an open `U ⊇ B(r₀)`, with every
slice `k_t` injective on `B(r₀)`, such that `k_t^* σ = ω₀` at the points of `B(r₀)` for every
`t`, and on all of `U` for `t = 0, 1`. Then
`SymplecticGeometry.exists_isSymplecticBallFamily_eqOn_of_mpullback_eq` changes `k` away from
`B(r₀)`, keeping its two ends, into a smooth family of symplectic embeddings of a larger ball
(`SymplecticGeometry.IsSymplecticBallFamily`). This is the step of McDuff–Salamon,
Theorem 3.3.1, that makes a family of embeddings symplectic near the ball, by Moser's argument
with a parameter.

The proof works on an open ball `B ⊇ B(r₀)` inside `U`, as a manifold. There the forms
`α_t = k_t^* σ - ω₀` are closed, form a smooth family, vanish on `B(r₀)`, and vanish for
`t = 0, 1`. Their parametric radial primitives `β_t`
(`SymplecticGeometry.exists_isSmoothFamily_mextDerivₗ_eq_of_starConvex`) vanish on `B(r₀)`,
since the segments from `0` to its points stay in it, and for `t = 0, 1`. Along `B(r₀)` the
segment from `ω₀` to `k_t^* σ` is constantly `ω₀`, so Moser's argument with a parameter
(`TauCeti.SmoothTwoForm.exists_diffeotopy_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub`) gives
a diffeotopy `χ` of `B` that fixes `B(r₀)`, is the identity at `t = 0, 1`, and pulls every
`k_t^* σ` back to `ω₀` on one neighbourhood of `B(r₀)`. The family equal to `k_t ∘ χ_t` on `B`
and to `k_t` elsewhere is smooth on `[0, 1] × B` (`ContMDiffOn.dite_comp_of_opens`),
and its slices pull `σ` back to `ω₀` near `B(r₀)` and are injective on it, so they are symplectic
embeddings of one larger ball (`SymplecticGeometry.exists_lt_isSymplecticBallFamily_of_injOn`).

The pulled-back forms `k_t^* σ` are compared with `ω₀` as forms on `ℝ²ⁿ`, not on `M`, as the
errata [McDuffSalamon2019Errata] (p. 114) correct the source.

## Main results

* `SymplecticGeometry.exists_isSymplecticBallFamily_eqOn_of_mpullback_eq`: a smooth family that
  is symplectic along `B(r₀)` and at both ends agrees, on `B(r₀)` and at both ends, with a smooth
  family of symplectic embeddings of a larger ball.

## Implementation notes

The form on `M` is called `σ`, since `ω` is a token once the scope `ContDiff` is open.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 3.3.1 and Appendix A.2.
* [D. McDuff and D. Salamon, *Errata for Introduction to Symplectic Topology, Third
  Edition*][McDuffSalamon2019Errata], p. 114.
-/

public section

noncomputable section

open Set Function Filter Metric TopologicalSpace
open scoped ContDiff Manifold Topology

namespace SymplecticGeometry

open TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {σ : SmoothTwoForm I M}

/-- The first step of `exists_isSymplecticBallFamily_eqOn_of_mpullback_eq`: parametric radial
primitives. Let `κ` be a smooth family over `[0, 1]` of maps from an open set `B`, star-convex
about `0`, such that `κ_t^* σ = ω₀` at the points of `B(r₀)` and, for `t = 0, 1`, everywhere.
Then there is a one-form `β` on `[0, 1] × B` whose slices satisfy `dβ_t = κ_t^* σ - ω₀`, vanish
for `t = 0, 1`, and vanish at the points of `B(r₀)`, where `κ_t^* σ - ω₀` vanishes too. -/
private theorem exists_mextDeriv_eq_mpullback_sub (hσ : σ.IsClosed) {r₀ : ℝ} (hr₀ : 0 ≤ r₀)
    {B : Opens (StdSpace (Fin n))} (hB : StarConvex ℝ 0 (B : Set (StdSpace (Fin n))))
    {κ : unitInterval × B → M} (hκ : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) I ∞ κ)
    (hK : ∀ t, ∀ x : B, (x : StdSpace (Fin n)) ∈ closedBall 0 r₀ →
      mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun x ↦ κ (t, x)) σ.val x =
        (stdForm (Fin n)).constSmooth.val x)
    (h₀ : ∀ x, mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun x ↦ κ (0, x)) σ.val x =
      (stdForm (Fin n)).constSmooth.val x)
    (h₁ : ∀ x, mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun x ↦ κ (1, x)) σ.val x =
      (stdForm (Fin n)).constSmooth.val x) :
    ∃ β : SmoothForm ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) (unitInterval × B) ℝ 1,
      (∀ t, mextDeriv
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).val =
          (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
            (SmoothForm.mpullback κ hκ σ) -
            SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
              (stdForm (Fin n)).constSmooth).val) ∧
      SmoothForm.mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) β = 0 ∧
      SmoothForm.mpullback (Prod.mk 1) (contMDiff_const.prodMk contMDiff_id) β = 0 ∧
      ∀ t, ∀ x : B, (x : StdSpace (Fin n)) ∈ closedBall 0 r₀ →
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).val x = 0 ∧
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
          (SmoothForm.mpullback κ hκ σ) -
          SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
            (stdForm (Fin n)).constSmooth).val x = 0 := by
  set τ := SmoothForm.mpullback κ hκ σ
  set ω₀B := SmoothForm.mpullback (Subtype.val : B → StdSpace (Fin n)) contMDiff_subtypeVal
    (stdForm (Fin n)).constSmooth
  -- The closed forms `α_t = κ_t^* σ - ω₀`.
  set α : unitInterval → SmoothTwoForm 𝓘(ℝ, StdSpace (Fin n)) B := fun t ↦
    SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) τ - ω₀B
  have hα {t : unitInterval} {x : B}
      (h : mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun x ↦ κ (t, x)) σ.val x =
        (stdForm (Fin n)).constSmooth.val x) : (α t).val x = 0 := by
    rw [AddSubgroupClass.coe_sub, Pi.sub_apply, sub_eq_zero,
      SmoothForm.coe_mpullback_subtype_val_apply]
    simp only [τ, SmoothForm.mpullback_mpullback, SmoothForm.coe_mpullback]
    exact h
  have hα₀ : α 0 = 0 := Subtype.ext <| funext fun x ↦ hα (h₀ x)
  have hα₁ : α 1 = 0 := Subtype.ext <| funext fun x ↦ hα (h₁ x)
  have hαs : IsSmoothFamily (𝓡∂ 1) α :=
    (isSmoothFamily_def.2 ⟨τ, fun _ ↦ rfl⟩).sub (isSmoothFamily_const ω₀B)
  have hcl (t : unitInterval) : mextDerivₗ 𝓘(ℝ, StdSpace (Fin n)) 2 (α t) = 0 :=
    (SmoothForm.isClosed_iff_mextDerivₗ_eq_zero _).1 (((hσ.mpullback _ _).mpullback _ _).sub
      ((SymplecticForm.isClosed_constSmooth _).mpullback _ _))
  -- Their radial primitives.
  obtain ⟨β, hβs, hdβ, hβ0, hβz⟩ := exists_isSmoothFamily_mextDerivₗ_eq_of_starConvex hB hαs hcl
  obtain ⟨β', hβ'⟩ := isSmoothFamily_def.1 hβs
  refine ⟨β', fun t ↦ by rw [hβ' t, ← mextDerivₗ_apply, hdβ t], by rw [hβ' 0, hβz 0 hα₀],
    by rw [hβ' 1, hβz 1 hα₁], fun t x hx ↦ ⟨?_, hα (hK t x hx)⟩⟩
  rw [hβ' t]
  exact hβ0 t x fun y hy ↦ hα <| hK t y <|
    (convex_closedBall 0 r₀).segment_subset (mem_closedBall_self hr₀) hx hy

/-- The last step of `exists_isSymplecticBallFamily_eqOn_of_mpullback_eq`. Let `χ` be a diffeotopy
of an open set `B ⊇ B(r₀)` that fixes the points of `B(r₀)`, such that the maps `k_t ∘ χ_t` pull
`σ` back to `ω₀` on an open set containing `B(r₀)`. Then the family equal to `k_t ∘ χ_t` on `B`
and to `k_t` elsewhere is a smooth family of symplectic embeddings of a ball larger than `B(r₀)`,
which agrees with `k` on `B(r₀)` at all times, and everywhere at every time `t` at which `χ_t` is
the identity. -/
private theorem exists_isSymplecticBallFamily_of_diffeotopy [FiniteDimensional ℝ E]
    [I.Boundaryless] [T2Space M] {r₀ : ℝ} {B : Opens (StdSpace (Fin n))}
    (hKB : closedBall (0 : StdSpace (Fin n)) r₀ ⊆ B) {k : unitInterval × StdSpace (Fin n) → M}
    (hk : ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) I ∞ k (univ ×ˢ B))
    (hinj : ∀ t, InjOn (fun z ↦ k (t, z)) (closedBall 0 r₀))
    (χ : Diffeotopy 𝓘(ℝ, StdSpace (Fin n)) ∞ B)
    (hχK : ∀ t, ∀ x : B, (x : StdSpace (Fin n)) ∈ closedBall 0 r₀ → χ (t, x) = x) {O : Set B}
    (hOo : IsOpen O) (hKO : ∀ x : B, (x : StdSpace (Fin n)) ∈ closedBall 0 r₀ → x ∈ O)
    (hO : ∀ t, ∀ x ∈ O, mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun x : B ↦ k (t, χ (t, x))) σ.val x =
      (stdForm (Fin n)).constSmooth.val x) :
    ∃ r, r₀ < r ∧ ∃ k', IsSymplecticBallFamily σ r k' ∧
      (∀ t, ∀ z ∈ closedBall 0 r₀, k' (t, z) = k (t, z)) ∧
      ∀ t, (∀ x, χ (t, x) = x) → ∀ z, k' (t, z) = k (t, z) := by
  classical
  set k' : unitInterval × StdSpace (Fin n) → M := fun p ↦
    if h : p.2 ∈ B then k (p.1, χ (p.1, ⟨p.2, h⟩)) else k p
  have hk' : ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) I ∞ k' (univ ×ˢ B) :=
    ContMDiffOn.dite_comp_of_opens χ.contMDiff hk
  have hk'B (t : unitInterval) (x : B) : k' (t, x) = k (t, χ (t, x)) := dite_eq_left x.property
  have hk'K (t : unitInterval) {z : StdSpace (Fin n)} (hz : z ∈ closedBall 0 r₀) :
      k' (t, z) = k (t, z) :=
    (hk'B t ⟨z, hKB hz⟩).trans (congrArg (fun x : B ↦ k (t, x)) (hχK t ⟨z, hKB hz⟩ hz))
  -- On the open set `O' ⊇ B(r₀)`, the image of `O`, every `k'_t` pulls `σ` back to `ω₀`.
  obtain ⟨O', hO'⟩ : ∃ O', O' = Subtype.val '' O := ⟨_, rfl⟩
  have hO'B : O' ⊆ B := by
    rintro _ hz
    obtain ⟨x, -, rfl⟩ := hO' ▸ hz
    exact x.property
  have hpull (t : unitInterval) (z : StdSpace (Fin n)) (hz : z ∈ O') :
      mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k' (t, z)) σ.val z =
        (stdForm (Fin n)).constSmooth.val z := by
    obtain ⟨x, hxO, rfl⟩ := hO' ▸ hz
    have hd : MDifferentiableAt 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k' (t, z)) x :=
      (((hk'.comp (contMDiffOn_const.prodMk contMDiffOn_id) fun _ hz ↦ ⟨mem_univ t, hz⟩) x
        x.property).contMDiffAt (B.isOpen.mem_nhds x.property)).mdifferentiableAt (by simp)
    rw [← mpullback_subtype_val_apply (U := B)
      (mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k' (t, z)) σ.val) x,
      ← mpullback_comp_at ((contMDiff_subtypeVal (n := 1)).mdifferentiableAt one_ne_zero) hd,
      show (fun z ↦ k' (t, z)) ∘ Subtype.val = fun x : B ↦ k (t, χ (t, x)) from
        funext (hk'B t)]
    exact hO t x hxO
  obtain ⟨r, hr, hfam⟩ := exists_lt_isSymplecticBallFamily_of_injOn
    (hO' ▸ B.isOpen.isOpenMap_subtypeVal O hOo) (fun z hz ↦ hO' ▸ ⟨⟨z, hKB hz⟩, hKO _ hz, rfl⟩)
    (hk'.mono (prod_mono subset_rfl hO'B))
    (fun t x hx y hy h ↦ hinj t hx hy (by simpa only [hk'K t hx, hk'K t hy] using h)) hpull
  refine ⟨r, hr, k', hfam, fun t z hz ↦ hk'K t hz, fun t ht z ↦ ?_⟩
  by_cases hz : z ∈ B
  · exact (hk'B t ⟨z, hz⟩).trans (congrArg (fun x : B ↦ k (t, x)) (ht _))
  · exact dite_eq_right hz

/-- **Moser's correction of a family of balls.** Let `σ` be a closed two-form, `0 ≤ r₀`, and `k`
a smooth family over `[0, 1]` of maps from an open neighbourhood `U` of `B(r₀)` that are injective
on `B(r₀)`. Suppose that every `k_t` pulls `σ` back to `ω₀` at the points of `B(r₀)`, and that `k_0`
and `k_1` do so on all of `U`. Then there is a smooth family `k'` of symplectic embeddings of a
closed ball `B(r)` of radius `r > r₀` that agrees with `k` on `B(r₀)` at all times, and
everywhere at the times `0` and `1`. -/
theorem exists_isSymplecticBallFamily_eqOn_of_mpullback_eq
    [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] (hσ : σ.IsClosed) {r₀ : ℝ}
    (hr₀ : 0 ≤ r₀) {k : unitInterval × StdSpace (Fin n) → M} {U : Set (StdSpace (Fin n))}
    (hU : IsOpen U) (hKU : closedBall 0 r₀ ⊆ U)
    (hk : ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) I ∞ k (univ ×ˢ U))
    (hinj : ∀ t, InjOn (fun z ↦ k (t, z)) (closedBall 0 r₀))
    (hK : ∀ t, ∀ z ∈ closedBall 0 r₀, mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k (t, z))
      σ.val z = (stdForm (Fin n)).constSmooth.val z)
    (h₀ : ∀ z ∈ U, mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k (0, z)) σ.val z =
      (stdForm (Fin n)).constSmooth.val z)
    (h₁ : ∀ z ∈ U, mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k (1, z)) σ.val z =
      (stdForm (Fin n)).constSmooth.val z) :
    ∃ r, r₀ < r ∧ ∃ k', IsSymplecticBallFamily σ r k' ∧
      (∀ t, ∀ z ∈ closedBall 0 r₀, k' (t, z) = k (t, z)) ∧
      (∀ z, k' (0, z) = k (0, z)) ∧ ∀ z, k' (1, z) = k (1, z) := by
  set ω₀ := (stdForm (Fin n)).constSmooth
  -- An open ball `B ⊇ B(r₀)` inside `U`.
  obtain ⟨ρ, hρ, hρU⟩ := exists_lt_ball_subset_of_closedBall_subset hU hKU
  set B : Opens (StdSpace (Fin n)) := ⟨ball 0 ρ, isOpen_ball⟩
  have hBU : (B : Set (StdSpace (Fin n))) ⊆ U := hρU
  have hKB : closedBall (0 : StdSpace (Fin n)) r₀ ⊆ B := closedBall_subset_ball hρ
  -- The family `k` on `[0, 1] × B`.
  set κ : unitInterval × B → M := fun p ↦ k (p.1, p.2)
  have hκ : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) I ∞ κ :=
    hk.comp_contMDiff (contMDiff_fst.prodMk (contMDiff_subtypeVal.comp contMDiff_snd))
      fun p ↦ ⟨mem_univ _, hBU p.2.property⟩
  have hκt (t : unitInterval) {x : B}
      (h : mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k (t, z)) σ.val x = ω₀.val x) :
      mpullback 𝓘(ℝ, StdSpace (Fin n)) I (fun x ↦ κ (t, x)) σ.val x = ω₀.val x := by
    have hkt : MDifferentiableAt 𝓘(ℝ, StdSpace (Fin n)) I (fun z ↦ k (t, z)) x :=
      (((hk.comp (contMDiffOn_const.prodMk contMDiffOn_id) fun _ hz ↦ ⟨mem_univ t, hz⟩) x
        (hBU x.property)).contMDiffAt (hU.mem_nhds (hBU x.property))).mdifferentiableAt
          (by simp)
    rw [show (fun x ↦ κ (t, x)) = (fun z ↦ k (t, z)) ∘ Subtype.val from rfl,
      mpullback_comp_at ((contMDiff_subtypeVal (n := 1)).mdifferentiableAt one_ne_zero) hkt,
      mpullback_subtype_val_apply]
    exact h
  -- The primitives `β_t` of `κ_t^* σ - ω₀`.
  obtain ⟨β, hβ, hβ₀, hβ₁, hβK⟩ := exists_mextDeriv_eq_mpullback_sub hσ hr₀
    ((convex_ball 0 _).starConvex (mem_ball_self (hr₀.trans_lt hρ))) hκ
    (fun t x hx ↦ hκt t (hK t x hx)) (fun x ↦ hκt 0 (h₀ x (hBU x.property)))
    fun x ↦ hκt 1 (h₁ x (hBU x.property))
  set K : Set B := Subtype.val ⁻¹' closedBall 0 r₀ with hK_def
  have hKc : IsCompact K := by
    rw [hK_def, Subtype.isCompact_iff, image_preimage_eq_of_subset (by rwa [Subtype.range_coe])]
    exact isCompact_closedBall 0 r₀
  -- Moser's argument with a parameter on `B`. Along `B(r₀)` the segments from `ω₀` to the
  -- `κ_t^* σ` are constant, hence nondegenerate.
  obtain ⟨χ, hχK, -, hχid, hχ⟩ :=
    SmoothTwoForm.exists_diffeotopy_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub
      ((SymplecticForm.isClosed_constSmooth _).mpullback _ _) _ β hβ hβ₀ hKc
      (fun t x hx ↦ (hβK t x hx).1)
      fun t x hx s _ ↦ SmoothTwoForm.nondegenerate_bilinFormAt_add_smul_sub_of_eq (hβK t x hx).2
        (((SymplecticForm.isNondegenerate_constSmooth _).mpullback_subtype_val B
          ).nondegenerate_bilinFormAt x) s
  obtain ⟨O, hOo, hKO, hO⟩ := eventually_nhdsSet_iff_exists.1 hχ
  obtain ⟨r, hr, k', hk', hk'K, hk'id⟩ := exists_isSymplecticBallFamily_of_diffeotopy (σ := σ) hKB
    (hk.mono (prod_mono subset_rfl hBU)) hinj χ hχK hOo hKO fun t x hx ↦ by
      have h := hO x hx t
      simp only [SmoothForm.coe_mpullback, SmoothForm.mpullback_mpullback] at h
      rw [show (κ ∘ Prod.mk t) ∘ χ.timeSlice t = fun x ↦ k (t, χ (t, x)) from
        funext fun x ↦ by rw [comp_apply, Diffeotopy.timeSlice_apply]; rfl] at h
      exact h.trans (mpullback_subtype_val_apply _ x)
  exact ⟨r, hr, k', hk', hk'K, hk'id 0 (χ.apply_zero ·),
    hk'id 1 (hχid 1 hβ₁)⟩

end SymplecticGeometry

end
