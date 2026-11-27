/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.NormedSpace
import SymplecticGeometry.Geometry.Symplectic.HPrinciple.CollarPrimitive
import SymplecticGeometry.Geometry.Symplectic.HPrinciple.HandleCore.Approximation
import SymplecticGeometry.Geometry.Symplectic.HPrinciple.HandleCore.Collar
import SymplecticGeometry.Geometry.Symplectic.HPrinciple.HandleCore.CompressionIsotopy
import TauCeti.Geometry.Manifold.Instances.Icc

/-!
# The handle-core lemma

Let `D = (Fin m → ℝ) × (Fin k → ℝ)` with the sup norms, `0 < k`, with the cube
`Q = closedBall 0 1` and the attaching faces `A = sphere 0 1 ×ˢ closedBall 0 1`. Let `τ` be a
smooth family of two-forms on `D` over a finite-dimensional normed space `L`, nondegenerate on `Q`
for the parameters of a compact `K ⊆ L`, and `β` a smooth family of one-forms with `dβ l = τ l` on
a fixed open `W ⊇ A` for those parameters.
`SymplecticGeometry.exists_homotopy_exact_of_exact_near_attaching` deforms `τ`, smoothly in the
parameter and in time, through forms nondegenerate on `Q` and equal to `τ` near `A`, to forms
exact on all of `D`; a parameter at which `τ` is exact near `Q` stays exact near `Q`. This is the
working lemma behind McDuff–Salamon's Lemma 7.3.2, for a core of any dimension.

## The construction

In place of McDuff–Salamon's induction on the dimension of the core, the proof follows
Eliashberg–Mishachev's approximation-and-compression argument (§10.2).

1. Let `r > 0` be a nondegeneracy margin of `τ` over `K × Q`
   (`SymplecticGeometry.IsSmoothFamily.exists_pos_forall_nondegenerate`).
2. Holonomic approximation of the formal primitive of `τ` near the core
   (`SymplecticGeometry.exists_diffeotopy_norm_mextDerivₗ_sub_lt_near_core`) gives a slab width
   `ε₀`, a family of diffeotopies `H`, a smooth family `β'` of one-forms equal to `β` on the slab
   `1 - ε₀ < ‖u‖`, and an open set `V` around the moved core on which `dβ'` is within `r` of `τ`.
3. Composing `H` with the compression of the cube onto a thin tube around its core
   (`SymplecticGeometry.exists_isotopy_mapsTo_of_diffeotopy`) gives isotopies `e l s` of `D`,
   preserving `Q`, the identity where `1 - ε₀ / 2 < ‖u‖`, with `e l 1` mapping `Q` into the slice
   of `V` over `l` or into the slab, where `dβ' l = dβ l = τ l`.

The homotopy is `σ (l, t) = (e l (a t))^* ((1 - b t) • τ l + b t • dβ' l)` for smooth steps `a`
and `b`, with `b` starting once `a` has reached `1`, as in the one-dimensional case
(`SymplecticGeometry.exists_homotopy_exact_of_closed_near_attaching_fin_one`), whose assembly this
proof follows. At time `1` it is `d ((e l 1)^* β' l)`.

## Removing the common collar

`SymplecticGeometry.exists_homotopy_exact_of_forall_exact_near_attaching` asks only that each
`τ l`, `l ∈ K`, have a primitive on some neighbourhood of `A` of its own, with no smooth
dependence on `l`. The collar correction
(`SymplecticGeometry.exists_isSmoothFamily_collarCorrection`) gives a smooth family `η`,
vanishing near `A`, small on `Q` and with `τ l - η l` exact on one product collar for every
`l ∈ K`; the finite good cover of that collar
(`SymplecticGeometry.exists_isSmoothFamily_mextDerivₗ_eq_near_sphere_prod_closedBall`) then gives
the family `β` that the working lemma takes, for `τ - η`. The homotopy is
`σ' (l, b t) + (1 - a t) • η l`, with `σ'` the working lemma's homotopy for `τ - η` and the same
smooth steps: it runs the straight line from `τ l` to `τ l - η l`, then `σ'`, and needs no
gluing, since each step is constant while the other moves.

## Main results

* `SymplecticGeometry.exists_homotopy_exact_of_exact_near_attaching`
* `SymplecticGeometry.exists_homotopy_exact_of_forall_exact_near_attaching`: the handle-core
  lemma, McDuff–Salamon's Lemma 7.3.2.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Lemma 7.3.2.
* [Y. Eliashberg and N. Mishachev, *Introduction to the h-principle*][EliashbergMishachev2002],
  §10.2.
-/

public section

open Set Metric Filter TauCeti
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

variable {m k : ℕ} {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

/-- **The handle-core working lemma.** On `D = (Fin m → ℝ) × (Fin k → ℝ)` with the sup norms and
`0 < k`, let `Q = closedBall 0 1` be the cube and `A = sphere 0 1 ×ˢ closedBall 0 1` its attaching
faces.
Let `τ` be a smooth family of two-forms and `β` a smooth family of one-forms on `D`, over a
finite-dimensional normed space `L`, and `K ⊆ L` compact, such that for `l ∈ K` the form `τ l` is
nondegenerate on `Q` and equal to `dβ l` on the open set `W ⊇ A`. Then there is a smooth family
`σ` of two-forms over `L × [0, 1]` with `σ (l, 0) = τ l` such that:

* `σ (l, t)` is nondegenerate on `Q` for `l ∈ K` and every `t`;
* `σ (l, t) = τ l` on a neighbourhood `W'` of `A`, the same for all `l ∈ K` and all `t`;
* `σ (l, 1)` is exact on `D`, for every `l`;
* if `τ l` has a primitive on a neighbourhood of `Q`, then so does every `σ (l, t)`. -/
theorem exists_homotopy_exact_of_exact_near_attaching (hk : 0 < k) {K : Set L}
    (hK : IsCompact K) {τ : L → SmoothTwoForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ))
      ((Fin m → ℝ) × (Fin k → ℝ))} (hτ : IsSmoothFamily 𝓘(ℝ, L) τ)
    (hnd : ∀ l ∈ K, ∀ x ∈ closedBall (0 : (Fin m → ℝ) × (Fin k → ℝ)) 1,
      ((τ l).bilinFormAt x).Nondegenerate)
    {β : L → SmoothForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)) ℝ 1}
    (hβ : IsSmoothFamily 𝓘(ℝ, L) β) {W : Set ((Fin m → ℝ) × (Fin k → ℝ))} (hW : IsOpen W)
    (hAW : sphere (0 : Fin m → ℝ) 1 ×ˢ closedBall (0 : Fin k → ℝ) 1 ⊆ W)
    (hτβ : ∀ l ∈ K, ∀ x ∈ W,
      (mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 (β l)).val x = (τ l).val x) :
    ∃ σ : L × unitInterval →
        SmoothTwoForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)),
      IsSmoothFamily (𝓘(ℝ, L).prod (𝓡∂ 1)) σ ∧
      (∀ l, σ (l, 0) = τ l) ∧
      (∀ l ∈ K, ∀ t, ∀ x ∈ closedBall (0 : (Fin m → ℝ) × (Fin k → ℝ)) 1,
        ((σ (l, t)).bilinFormAt x).Nondegenerate) ∧
      (∃ W' ∈ 𝓝ˢ (sphere (0 : Fin m → ℝ) 1 ×ˢ closedBall (0 : Fin k → ℝ) 1), ∀ l ∈ K, ∀ t,
        ∀ x ∈ W', (σ (l, t)).val x = (τ l).val x) ∧
      (∀ l, ∃ γ : SmoothForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)) ℝ 1,
        mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 γ = σ (l, 1)) ∧
      ∀ l, (∃ V ∈ 𝓝ˢ (closedBall (0 : (Fin m → ℝ) × (Fin k → ℝ)) 1),
          ∃ γ : SmoothForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)) ℝ 1,
            ∀ x ∈ V, (mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 γ).val x = (τ l).val x) →
        ∀ t, ∃ V ∈ 𝓝ˢ (closedBall (0 : (Fin m → ℝ) × (Fin k → ℝ)) 1),
          ∃ γ : SmoothForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)) ℝ 1,
            ∀ x ∈ V, (mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 γ).val x =
              (σ (l, t)).val x := by
  -- The nondegeneracy margin.
  obtain ⟨r, hr, hnd'⟩ := hτ.exists_pos_forall_nondegenerate hK (isCompact_closedBall _ _) hnd
  -- Holonomic approximation near the core, then the compression of the cube.
  obtain ⟨ε₀, hε₀, hε₀₁, hslab, H, β', V, hHfst, hβ', hV, hHid, hKV, happrox⟩ :=
    exists_diffeotopy_norm_mextDerivₗ_sub_lt_near_core hk hK hτ hβ hW hAW hτβ hr
  obtain ⟨e, he, hediff, he0, heQ, heA, he1⟩ := exists_isotopy_mapsTo_of_diffeotopy hε₀
    (by linarith) H hHfst (fun t p hp ↦ (hHid t p hp).1) hK hV hKV
  -- On the slab next to the faces, `dβ' = dβ`, which is `τ` on `W`.
  have hS : IsOpen {x : (Fin m → ℝ) × (Fin k → ℝ) | 1 - ε₀ < ‖x.1‖} :=
    isOpen_lt continuous_const continuous_fst.norm
  have hdβ' (l : L) (x : (Fin m → ℝ) × (Fin k → ℝ)) (hx : 1 - ε₀ < ‖x.1‖) :
      (mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 (β' l)).val x =
        (mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 (β l)).val x := by
    rw [mextDerivₗ_apply, mextDerivₗ_apply]
    exact mextDeriv_congr_of_eventuallyEq
      (eventually_of_mem (hS.mem_nhds hx) fun y hy ↦ (hHid 0 (l, y) (Or.inl hy)).2)
  -- The smooth steps in time.
  set a : unitInterval → ℝ := fun t ↦ Real.smoothTransition (2 * (t : ℝ))
  set b : unitInterval → ℝ := fun t ↦ Real.smoothTransition (2 * (t : ℝ) - 1)
  have ha : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ a :=
    (Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)).contMDiff.comp
      contMDiff_subtypeVal_Icc
  have hb : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ b :=
    (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub
      contDiff_const)).contMDiff.comp contMDiff_subtypeVal_Icc
  set a' : unitInterval → unitInterval := fun t ↦
    ⟨a t, Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have ha' : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ a' :=
    contMDiff_iff_comp_subtypeVal_Icc.2 ⟨ha.continuous.subtype_mk _, ha⟩
  have hab (t : unitInterval) (h : b t ≠ 0) : a' t = 1 := by
    have : ¬ 2 * (t : ℝ) - 1 ≤ 0 := fun h' ↦ h (Real.smoothTransition.zero_of_nonpos h')
    exact Subtype.ext (Real.smoothTransition.one_of_one_le (by linarith))
  have hb₁ (t : unitInterval) : |b t| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  -- The isotopies, run at the speed `a`, as one smooth map of the parameter and the point.
  set f : (L × unitInterval) × ((Fin m → ℝ) × (Fin k → ℝ)) → (Fin m → ℝ) × (Fin k → ℝ) :=
    fun q ↦ e ((q.1.1, a' q.1.2), q.2) with hfdef
  have hf : ContMDiff ((𝓘(ℝ, L).prod (𝓡∂ 1)).prod 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)))
      𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ∞ f :=
    he.comp (((contMDiff_fst.comp contMDiff_fst).prodMk
      (ha'.comp (contMDiff_snd.comp contMDiff_fst))).prodMk contMDiff_snd)
  have hfp (p : L × unitInterval) : ContMDiff 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ))
      𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ∞ fun x ↦ f (p, x) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  -- The forms moved from `τ` to `dβ'`, before the isotopy.
  set ν : L × unitInterval →
      SmoothTwoForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)) :=
    fun p ↦ (1 - b p.2) • τ p.1 + b p.2 • mextDerivₗ _ 1 (β' p.1) with hνdef
  have hν : IsSmoothFamily (𝓘(ℝ, L).prod (𝓡∂ 1)) ν :=
    ((hτ.comp Prod.fst contMDiff_fst).fun_smul
        (contMDiff_const.sub (hb.comp contMDiff_snd))).add
      ((hβ'.mextDeriv.comp Prod.fst contMDiff_fst).fun_smul (hb.comp contMDiff_snd))
  have hνval (p : L × unitInterval) (x : (Fin m → ℝ) × (Fin k → ℝ)) :
      (ν p).val x = (τ p.1).val x + b p.2 •
        ((mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 (β' p.1)).val x - (τ p.1).val x) := by
    simp only [hνdef, SmoothBundleForm.add_apply, SmoothBundleForm.smul_apply]
    module
  -- Pullback along a map that is the identity near `x` does not change the value at `x`.
  have hid (p : L × unitInterval)
      (θ : SmoothTwoForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)))
      {x : (Fin m → ℝ) × (Fin k → ℝ)} (hx : (fun y ↦ f (p, y)) =ᶠ[𝓝 x] id) :
      (SmoothForm.mpullback _ (hfp p) θ).val x = θ.val x := by
    rw [SmoothForm.coe_mpullback, hx.mpullback_eq, TauCeti.mpullback_id]
  have hSε : IsOpen {x : (Fin m → ℝ) × (Fin k → ℝ) | 1 - ε₀ / 2 < ‖x.1‖} :=
    isOpen_lt continuous_const continuous_fst.norm
  refine ⟨fun p ↦ SmoothForm.mpullback _ (hfp p) (ν p), hν.mpullback_family hf, fun l ↦ ?_,
    fun l hl t x hx ↦ ?_, ⟨W ∩ {x | 1 - ε₀ / 2 < ‖x.1‖}, ?_, fun l hl t x hx ↦ ?_⟩,
    fun l ↦ ?_, fun l ⟨U, hU, γ, hγ⟩ t ↦ ?_⟩
  · -- At time `0` nothing moves.
    have hb0 : b 0 = 0 := Real.smoothTransition.zero_of_nonpos (by simp)
    have ha0 : a' 0 = 0 := Subtype.ext (Real.smoothTransition.zero_of_nonpos (by simp))
    refine Subtype.ext (funext fun x ↦ ?_)
    rw [hid (l, 0) _ (Eventually.of_forall fun y ↦ by simp [hfdef, ha0, he0]), hνval, hb0,
      zero_smul, add_zero]
  · -- Nondegeneracy on the cube.
    set y := f ((l, t), x)
    have hyQ : y ∈ closedBall (0 : (Fin m → ℝ) × (Fin k → ℝ)) 1 := heQ (l, a' t) hx
    obtain ⟨φ, hφ⟩ := hediff (l, a' t)
    have hdf : (mfderiv 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ))
        (fun x ↦ f ((l, t), x)) x).IsInvertible := by
      have := φ.isLocalDiffeomorph.isInvertible_mfderiv (by simp) x
      rwa [hφ] at this
    have hpull : mpullback 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ))
        (fun x ↦ f ((l, t), x)) (ν (l, t)).val x =
        (SmoothForm.mpullback _ (hfp (l, t)) (ν (l, t))).val x := by
      rw [SmoothForm.coe_mpullback]
    refine (SmoothTwoForm.nondegenerate_bilinFormAt_iff_of_isInvertible_mfderiv hdf hpull).1 ?_
    refine hnd' l hl y hyQ _ ?_
    -- Stated in `D [⋀^Fin 2]→L[ℝ] ℝ`, whose instances give the norm, rather than in the tangent
    -- space that `hνval` is stated in, so that `rw` finds them; the two types agree by definition.
    have hsub {u v w : ((Fin m → ℝ) × (Fin k → ℝ)) [⋀^Fin 2]→L[ℝ] ℝ} {c : ℝ}
        (h : u = v + c • w) : ‖u - v‖ ≤ |c| * ‖w‖ := by
      rw [h, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    refine (hsub (hνval (l, t) y)).trans_lt ?_
    rcases eq_or_ne (b t) 0 with h0 | h0
    · rw [h0, abs_zero, zero_mul]
      exact hr
    refine (mul_le_of_le_one_left (norm_nonneg _) (hb₁ t)).trans_lt ?_
    have hy1 : y ∈ {x | (l, x) ∈ V} ∪ {x | 1 - ε₀ < ‖x.1‖} := by
      have := he1 l hl hx
      rwa [← hab t h0] at this
    rcases hy1 with hyV | hyS
    · exact happrox (l, y) hyV hl
    · have hyS' : 1 - ε₀ < ‖y.1‖ := hyS
      rw [hdβ' l y hyS, hτβ l hl y (hslab y hyQ (by linarith)), sub_self]
      exact (norm_zero (E := ((Fin m → ℝ) × (Fin k → ℝ)) [⋀^Fin 2]→L[ℝ] ℝ)).trans_lt hr
  · -- A fixed neighbourhood of the faces.
    refine (hW.inter hSε).mem_nhdsSet.2 fun x hx ↦ ⟨hAW hx, ?_⟩
    rw [mem_ofPred_eq, mem_sphere_zero_iff_norm.1 hx.1]
    linarith
  · have hnear : (fun y ↦ f ((l, t), y)) =ᶠ[𝓝 x] id :=
      eventually_of_mem (hSε.mem_nhds hx.2) fun y hy ↦ heA _ y hy
    have hx₁ : 1 - ε₀ < ‖x.1‖ := by have := hx.2; simp only [mem_ofPred_eq] at this; linarith
    rw [hid (l, t) _ hnear, hνval, hdβ' l x hx₁, hτβ l hl x hx.1, sub_self, smul_zero, add_zero]
  · -- At time `1` the form is exact.
    have hb1 : b 1 = 1 := Real.smoothTransition.one_of_one_le (by norm_num)
    refine ⟨SmoothForm.mpullback _ (hfp (l, 1)) (β' l), ?_⟩
    rw [SmoothForm.mextDerivₗ_mpullback]
    simp only [hνdef, hb1, sub_self, zero_smul, one_smul, zero_add]
  · -- Forms exact near the cube stay exact near the cube.
    have hνγ : ∀ y ∈ U, (mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1
        ((1 - b t) • γ + b t • β' l)).val y = (ν (l, t)).val y := fun y hy ↦ by
      simp only [map_add, map_smul, SmoothBundleForm.add_apply, SmoothBundleForm.smul_apply,
        hγ y hy, hνdef]
    obtain ⟨V', hV', h'⟩ :=
      SmoothForm.exists_mem_nhdsSet_mextDerivₗ_mpullback_eq (hfp (l, t)) (heQ (l, a' t)) hU hνγ
    exact ⟨V', hV', _, h'⟩

/-- **Relative extension of exact forms over a handle core.** On
`D = (Fin m → ℝ) × (Fin k → ℝ)` with the sup norms and `0 < k`, let `Q = closedBall 0 1` be the
cube and `A = sphere 0 1 ×ˢ closedBall 0 1` its attaching faces. Let `τ` be a smooth family of
two-forms on `D` over a finite-dimensional normed space `L`, and `K ⊆ L` compact, such that for
`l ∈ K` the form `τ l` is nondegenerate on `Q` and has a primitive on some neighbourhood of `A`,
which may depend on `l`. Then there is a smooth family `σ` of two-forms over `L × [0, 1]` with
`σ (l, 0) = τ l` such that:

* `σ (l, t)` is nondegenerate on `Q` for `l ∈ K` and every `t`;
* for each `l ∈ K`, `σ (l, t) = τ l` on a neighbourhood of `A` that does not depend on `t`;
* `σ (l, 1)` is exact on `D`, for every `l`;
* if `l ∈ K` and `τ l` has a primitive on a neighbourhood of `Q`, then so does every `σ (l, t)`.

Milestone: *Relative extension of exact symplectic forms over a handle core*. -/
theorem exists_homotopy_exact_of_forall_exact_near_attaching (hk : 0 < k) {K : Set L}
    (hK : IsCompact K) {τ : L → SmoothTwoForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ))
      ((Fin m → ℝ) × (Fin k → ℝ))} (hτ : IsSmoothFamily 𝓘(ℝ, L) τ)
    (hnd : ∀ l ∈ K, ∀ x ∈ closedBall (0 : (Fin m → ℝ) × (Fin k → ℝ)) 1,
      ((τ l).bilinFormAt x).Nondegenerate)
    (hex : ∀ l ∈ K, ∃ W ∈ 𝓝ˢ (sphere (0 : Fin m → ℝ) 1 ×ˢ closedBall (0 : Fin k → ℝ) 1),
      ∃ β : SmoothForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)) ℝ 1,
        ∀ x ∈ W, (mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 β).val x = (τ l).val x) :
    ∃ σ : L × unitInterval →
        SmoothTwoForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)),
      IsSmoothFamily (𝓘(ℝ, L).prod (𝓡∂ 1)) σ ∧
      (∀ l, σ (l, 0) = τ l) ∧
      (∀ l ∈ K, ∀ t, ∀ x ∈ closedBall (0 : (Fin m → ℝ) × (Fin k → ℝ)) 1,
        ((σ (l, t)).bilinFormAt x).Nondegenerate) ∧
      (∀ l ∈ K, ∃ W' ∈ 𝓝ˢ (sphere (0 : Fin m → ℝ) 1 ×ˢ closedBall (0 : Fin k → ℝ) 1), ∀ t,
        ∀ x ∈ W', (σ (l, t)).val x = (τ l).val x) ∧
      (∀ l, ∃ γ : SmoothForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)) ℝ 1,
        mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 γ = σ (l, 1)) ∧
      ∀ l ∈ K, (∃ V ∈ 𝓝ˢ (closedBall (0 : (Fin m → ℝ) × (Fin k → ℝ)) 1),
          ∃ γ : SmoothForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)) ℝ 1,
            ∀ x ∈ V, (mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 γ).val x = (τ l).val x) →
        ∀ t, ∃ V ∈ 𝓝ˢ (closedBall (0 : (Fin m → ℝ) × (Fin k → ℝ)) 1),
          ∃ γ : SmoothForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)) ℝ 1,
            ∀ x ∈ V, (mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 γ).val x =
              (σ (l, t)).val x := by
  -- Step 0: the correction `η` makes `τ - η` exact on one product collar for all of `K`.
  obtain ⟨ε, hε, hε₁, η, hη, hηK⟩ := exists_isSmoothFamily_collarCorrection hτ hK hnd hex
  -- Steps 1 to 3: a smooth family of primitives of `τ - η` near the attaching faces.
  obtain ⟨β, hβ, W, hW, hAW, hτβ⟩ :=
    exists_isSmoothFamily_mextDerivₗ_eq_near_sphere_prod_closedBall hε hε₁ (hτ.sub hη)
      (K := K) fun l hl ↦ by
        obtain ⟨γ, hγ⟩ := (hηK l hl).2.2.1
        rw [exactForms_succ]
        refine ⟨SmoothForm.mpullback _ contMDiff_subtypeVal γ, ?_⟩
        rw [SmoothForm.mextDerivₗ_mpullback]
        refine Subtype.ext (funext fun x ↦ ?_)
        rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback]
        exact mpullback_apply_congr (hγ x x.property)
  -- The working lemma, applied to `τ - η`.
  obtain ⟨σ', hσ', hσ'0, hσ'nd, ⟨W', hW', hσ'W'⟩, hσ'1, hσ'rel⟩ :=
    exists_homotopy_exact_of_exact_near_attaching hk hK (hτ.sub hη)
      (fun l hl x hx ↦ by simpa using (hηK l hl).2.1 1 ⟨zero_le_one, le_rfl⟩ x hx) hβ hW hAW
      hτβ
  -- The smooth steps in time: first `a` runs the line from `τ` to `τ - η`, then `b'` runs the
  -- working lemma's homotopy.
  set a : unitInterval → ℝ := fun t ↦ (collaredFirstHalf le_rfl t : ℝ)
  set b' : unitInterval → unitInterval := ⇑(collaredSecondHalf (n := ∞) le_rfl)
  have ha : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ a :=
    contMDiff_subtypeVal_Icc.comp (collaredFirstHalf le_rfl).contMDiff
  have hb' : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ b' := (collaredSecondHalf le_rfl).contMDiff
  have ha₀ (t : unitInterval) : a t ∈ Icc (0 : ℝ) 1 := (collaredFirstHalf le_rfl t).property
  have hab (t : unitInterval) : b' t = 0 ∨ a t = 1 := by
    rcases le_total (t : ℝ) (1 / 2) with h | h
    · exact Or.inl (collaredSecondHalf_eq_zero_of_le le_rfl (by linarith))
    · exact Or.inr (congrArg Subtype.val (collaredFirstHalf_eq_one_of_ge le_rfl (by linarith)))
  set σ : L × unitInterval →
      SmoothTwoForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)) :=
    fun p ↦ σ' (p.1, b' p.2) + (1 - a p.2) • η p.1 with hσdef
  -- Before `b'` starts, `σ` is the line from `τ` to `τ - η`; once `a` is done, it is `σ'`.
  have hσline (l : L) {t : unitInterval} (h : b' t = 0) : σ (l, t) = τ l - a t • η l := by
    simp only [hσdef, h, hσ'0]
    module
  have hσwork (l : L) {t : unitInterval} (h : a t = 1) : σ (l, t) = σ' (l, b' t) := by
    simp only [hσdef, h, sub_self, zero_smul, add_zero]
  refine ⟨σ, (hσ'.comp (fun p ↦ (p.1, b' p.2)) (contMDiff_fst.prodMk
      (hb'.comp contMDiff_snd))).add ((hη.comp Prod.fst contMDiff_fst).fun_smul
      (contMDiff_const.sub (ha.comp contMDiff_snd))), fun l ↦ ?_, fun l hl t x hx ↦ ?_,
    fun l hl ↦ ?_, fun l ↦ ?_, fun l hl hQ t ↦ ?_⟩
  · have ha0 : a 0 = 0 := congrArg Subtype.val (collaredFirstHalf_zero le_rfl)
    rw [hσline l (collaredSecondHalf_zero le_rfl), ha0, zero_smul, sub_zero]
  · rcases hab t with h | h
    · rw [hσline l h]
      exact (hηK l hl).2.1 (a t) (ha₀ t) x hx
    · rw [hσwork l h]
      exact hσ'nd l hl _ x hx
  · -- Near `A`, `η l` vanishes and `σ'` is `τ - η`.
    refine ⟨W' ∩ {x | (η l).val x = 0}, Filter.inter_mem hW' (hηK l hl).1, fun t x hx ↦ ?_⟩
    have h0 : (η l).val x = 0 := hx.2
    simp only [hσdef, SmoothBundleForm.add_apply, SmoothBundleForm.smul_apply,
      hσ'W' l hl _ x hx.1, SmoothBundleForm.sub_apply, h0, smul_zero, sub_zero, add_zero]
  · have hb1 : b' 1 = 1 := collaredSecondHalf_one le_rfl
    rw [hσwork l (congrArg Subtype.val (collaredFirstHalf_one le_rfl)), hb1]
    exact hσ'1 l
  · rcases hab t with h | h
    · rw [hσline l h]
      exact (hηK l hl).2.2.2 hQ (a t) (ha₀ t)
    · rw [hσwork l h]
      refine hσ'rel l ?_ _
      simpa using (hηK l hl).2.2.2 hQ 1 ⟨zero_le_one, le_rfl⟩

end SymplecticGeometry

end
