/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Analysis.SpecialFunctions.SmoothSegmentPath
public import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
public import TauCeti.Geometry.Symplectic.Transport
public import TauCeti.Topology.Algebra.Module.BilinearForm
public import SymplecticGeometry.Topology.Algebra.Module.BilinearForm
public import TauCeti.Analysis.ODE.DysonSeries
import SymplecticGeometry.Analysis.ODE.DysonSeries
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothSegmentPath
import SymplecticGeometry.Analysis.Calculus.Deriv.ContinuousLinearMap
import TauCeti.Analysis.Calculus.ContDiff.FDerivApply
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Calculus.FDeriv.Mul
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Analysis.ODE.Regularity
import SymplecticGeometry.Analysis.Normed.Operator.BoundedSMul

/-!
# The linear Moser lemma

Let `ω t` be a family of skew-symmetric continuous bilinear forms on a real Banach space `V`,
continuously differentiable in `t ∈ ℝ`, whose contractions `V → V*` are invertible (in finite
dimension: which are nondegenerate). The *Moser generator*

`A t = -(1/2) (ω t)⁻¹ ∘ ω̇ t : V → V`

is the unique operator with `ω t (A t x) y = -(1/2) ω̇ t x y`. By skew-symmetry of `ω̇ t`, this
gives `ω̇ t x y + ω t (A t x) y + ω t x (A t y) = 0`, so the solution `Ψ` of the linear equation
`Ψ' t = A t ∘ Ψ t` with `Ψ 0 = 1`, which is Tau Ceti's left Dyson series `dysonSeriesLeft A`,
satisfies `ω t (Ψ t u) (Ψ t v) = ω 0 u v` for all `t`. Each `Ψ t` is invertible, and `Ψ` is as
smooth as `ω`.

The same argument applies to a `C¹` path `J t` of complex structures, `J t * J t = -1`, in a
real Banach algebra. Now the generator is `A t = (1/2) J t * J̇ t`, and its left Dyson series
`Ψ` satisfies `Ψ t * J 0 = J t * Ψ t`: it conjugates `J 0` to `J t`. In the algebra
`V →L[ℝ] V` this gives the statement for a path of Tau Ceti's `AlmostComplexStructure V` on a
finite-dimensional space: `J t` is the transport of `J 0` along an invertible `Ψ t`.

Both generators are formulas in the family and its derivative, with no auxiliary choice such as
an inner product.

## Main definitions

* `SymplecticGeometry.moserGenerator`: the generator `-(1/2) (ω t)⁻¹ ∘ ω̇ t` of a path of forms.
* `SymplecticGeometry.complexMoserGenerator`: the generator `(1/2) J t * J̇ t` of a path of
  complex structures.
* `SymplecticGeometry.invertibleSegments`: the pairs `(a, b)` of forms whose convex combinations
  are all invertible.
* `SymplecticGeometry.segmentMoserFlow`: the time-one propagator of the Moser generator of
  Tau Ceti's path `TauCeti.smoothSegmentPath a b`, `t ↦ a + β t • (b - a)` with
  `β = Real.smoothTransition`.

## Main results

* `SymplecticGeometry.apply_dysonSeriesLeft_moserGenerator`: the propagator of the Moser
  generator pulls `ω t` back to `ω 0`.
* `SymplecticGeometry.exists_contDiff_isUnit_apply_eq`: the linear Moser lemma on a
  finite-dimensional real vector space.
* `SymplecticGeometry.moserGenerator_conj`,
  `SymplecticGeometry.dysonSeriesLeft_moserGenerator_conj`:
  moving the forms along a linear isomorphism `e` conjugates the generator and its propagator
  by `e`.
* `SymplecticGeometry.contDiffOn_parametric_moserGenerator`,
  `SymplecticGeometry.contDiffOn_parametric_dysonSeriesLeft_moserGenerator`: for a family of
  paths of forms that is `Cⁿ⁺¹` jointly in a parameter from an open set and the time, the
  generator and its propagator are `Cⁿ` jointly in both.
* `SymplecticGeometry.isOpen_invertibleSegments`, `SymplecticGeometry.apply_segmentMoserFlow`,
  `SymplecticGeometry.contDiffOn_segmentMoserFlow`, `SymplecticGeometry.segmentMoserFlow_conj`:
  the pairs with invertible segments are open, and on them the flow pulls `b` back to `a`, is
  smooth in `(a, b)`, and is natural under linear isomorphisms.
* `SymplecticGeometry.dysonSeriesLeft_complexMoserGenerator_mul`: the propagator of the complex
  Moser generator conjugates `J 0` to `J t`.
* `SymplecticGeometry.exists_contDiff_isUnit_mul_eq_mul`: the analogue for complex structures in
  a real Banach algebra.
* `SymplecticGeometry.exists_contDiff_transport_eq`: the analogue for a path of almost complex
  structures on a finite-dimensional real space.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Corollary 2.5.14 and Exercise 2.5.18; Theorem 2.6.3, which applies the linear Moser flow
  fibrewise, and so uses its naturality and its smooth dependence on parameters.
-/

public section

noncomputable section

namespace SymplecticGeometry

open TauCeti

section Forms

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The Moser generator of a path `ω` of bilinear forms: the operator
`-(1/2) (ω t)⁻¹ ∘ ω̇ t`, where `(ω t)⁻¹` is the inverse of the contraction `V → V*` (zero if
`ω t` is not invertible). -/
def moserGenerator (ω : ℝ → V →L[ℝ] V →L[ℝ] ℝ) (t : ℝ) : V →L[ℝ] V :=
  -(2⁻¹ : ℝ) • ((ω t).inverse ∘L deriv ω t)

theorem moserGenerator_def (ω : ℝ → V →L[ℝ] V →L[ℝ] ℝ) (t : ℝ) :
    moserGenerator ω t = -(2⁻¹ : ℝ) • ((ω t).inverse ∘L deriv ω t) := (rfl)

variable {ω : ℝ → V →L[ℝ] V →L[ℝ] ℝ}

/-- Contraction with `ω t` turns the Moser generator into `-(1/2) ω̇ t`. -/
theorem comp_moserGenerator {t : ℝ} (ht : (ω t).IsInvertible) :
    ω t ∘L moserGenerator ω t = -(2⁻¹ : ℝ) • deriv ω t := by
  rw [moserGenerator_def, ContinuousLinearMap.comp_smul, ← ContinuousLinearMap.comp_assoc,
    ht.self_comp_inverse, ContinuousLinearMap.id_comp]

/-- The defining property of the Moser generator: `ω t (A t x) = -(1/2) ω̇ t x`. -/
theorem apply_moserGenerator {t : ℝ} (ht : (ω t).IsInvertible) (x : V) :
    ω t (moserGenerator ω t x) = -(2⁻¹ : ℝ) • deriv ω t x :=
  congr($(comp_moserGenerator ht) x)

/-- The Moser generator is the only operator `A` with `ω t ∘ A = -(1/2) ω̇ t`. -/
theorem eq_moserGenerator_iff {t : ℝ} (ht : (ω t).IsInvertible) {A : V →L[ℝ] V} :
    A = moserGenerator ω t ↔ ω t ∘L A = -(2⁻¹ : ℝ) • deriv ω t := by
  refine ⟨fun h => h ▸ comp_moserGenerator ht, fun h => ?_⟩
  ext x
  exact ht.injective (by rw [apply_moserGenerator ht]; exact congr($h x))

section Conj

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Naturality of the Moser generator.** Moving a path of forms along a linear isomorphism
`e : V ≃L[ℝ] W`, to `(v, w) ↦ ω t (e⁻¹ v) (e⁻¹ w)`, conjugates its Moser generator by `e`. -/
theorem moserGenerator_conj (e : V ≃L[ℝ] W) (ω : ℝ → V →L[ℝ] V →L[ℝ] ℝ) (t : ℝ) :
    moserGenerator (fun s => e.bilinearCongr (ω s)) t =
      e.conjContinuousAlgEquiv (moserGenerator ω t) := by
  set A : (V →L[ℝ] ℝ) ≃L[ℝ] (W →L[ℝ] ℝ) := e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  set Φ : (V →L[ℝ] V →L[ℝ] ℝ) ≃L[ℝ] (W →L[ℝ] W →L[ℝ] ℝ) := e.bilinearCongr
  have hΦ : (fun s => Φ (ω s)) = Φ ∘ ω := rfl
  have hd : deriv (Φ ∘ ω) t = Φ (deriv ω t) := by
    have h := ContinuousLinearEquiv.comp_fderiv (𝕜 := ℝ) (E := V →L[ℝ] V →L[ℝ] ℝ)
      (F := W →L[ℝ] W →L[ℝ] ℝ) Φ (f := ω) (x := t)
    exact congr($h 1)
  have hc (σ : V →L[ℝ] V →L[ℝ] ℝ) : Φ σ = (A : _ →L[ℝ] _) ∘L σ ∘L (e.symm : W →L[ℝ] V) := by
    ext v w
    simp [Φ, A]
  rw [hΦ, moserGenerator_def, moserGenerator_def, hd, Function.comp_apply, hc, hc,
    ContinuousLinearMap.inverse_equiv_comp, ContinuousLinearMap.inverse_comp_equiv]
  ext w
  simp

end Conj

variable [CompleteSpace V]

/-- The Moser generator of a `Cⁿ⁺¹` path of invertible forms is `Cⁿ`. -/
theorem contDiff_moserGenerator {n : WithTop ℕ∞} (hω : ContDiff ℝ (n + 1) ω)
    (hinv : ∀ t, (ω t).IsInvertible) : ContDiff ℝ n (moserGenerator ω) := by
  have hinv' : ContDiff ℝ n fun t => (ω t).inverse := (hω.of_le le_self_add).clm_inverse hinv
  have hd : ContDiff ℝ n (deriv ω) := (contDiff_succ_iff_deriv.1 hω).2.2
  rw [show moserGenerator ω = fun t => -(2⁻¹ : ℝ) • ((ω t).inverse ∘L deriv ω t) from
    funext (moserGenerator_def ω)]
  exact (hinv'.clm_comp hd).const_smul _

/-- The Moser generator of a `C¹` path of invertible forms is continuous. -/
theorem continuous_moserGenerator (hω : ContDiff ℝ 1 ω) (hinv : ∀ t, (ω t).IsInvertible) :
    Continuous (moserGenerator ω) :=
  (contDiff_moserGenerator (n := 0) (by rwa [zero_add]) hinv).continuous

/-- **The linear Moser lemma, explicit form.** For a `C¹` path `ω` of skew-symmetric forms with
invertible contractions on a real Banach space, the propagator `Ψ = dysonSeriesLeft A` of the
Moser generator `A = moserGenerator ω` satisfies `ω t (Ψ t u) (Ψ t v) = ω 0 u v`. -/
theorem apply_dysonSeriesLeft_moserGenerator (hω : ContDiff ℝ 1 ω)
    (hinv : ∀ t, (ω t).IsInvertible) (hskew : ∀ t v w, ω t v w = -ω t w v) (t : ℝ) (u v : V) :
    ω t (dysonSeriesLeft (moserGenerator ω) t u) (dysonSeriesLeft (moserGenerator ω) t v) =
      ω 0 u v := by
  set A := moserGenerator ω
  set Ψ := dysonSeriesLeft A
  have hA := continuous_moserGenerator hω hinv
  have hd := hω.differentiable one_ne_zero
  have hf (s : ℝ) : HasDerivAt (fun s => ω s (Ψ s u) (Ψ s v)) 0 s := by
    have h := HasDerivAt.clm_apply (c := ω) (u := fun s => Ψ s u) (hd s).hasDerivAt
      (hasDerivAt_dysonSeriesLeft_apply hA u s)
    have h2 := HasDerivAt.clm_apply (c := fun s => ω s (Ψ s u)) (u := fun s => Ψ s v) h
      (hasDerivAt_dysonSeriesLeft_apply hA v s)
    convert h2 using 1
    rw [add_apply, apply_moserGenerator (hinv s), hskew s (Ψ s u) (A s _),
      apply_moserGenerator (hinv s), smul_apply,
      smul_apply, smul_eq_mul, smul_eq_mul,
      deriv_apply_apply_eq_neg (.of_forall hskew) (Ψ s v)]
    ring
  simpa [Ψ] using TauCeti.is_const_of_hasDerivAt_zero hf t 0

/-- The propagator of the Moser generator of a `Cⁿ⁺¹` path of invertible forms is `Cⁿ⁺¹`. -/
theorem contDiff_dysonSeriesLeft_moserGenerator {n : ℕ∞} (hω : ContDiff ℝ (n + 1) ω)
    (hinv : ∀ t, (ω t).IsInvertible) :
    ContDiff ℝ (n + 1) (dysonSeriesLeft (moserGenerator ω)) := by
  have hA := contDiff_moserGenerator hω hinv
  exact contDiff_succ_of_hasDerivAt_clm_apply ((ContinuousLinearMap.mul ℝ _).contDiff.comp hA)
    fun t => by simpa using hasDerivAt_dysonSeriesLeft hA.continuous t

/-- **Naturality of the linear Moser flow.** Moving a `C¹` path of invertible forms along a linear
isomorphism `e : V ≃L[ℝ] W` conjugates the propagator of its Moser generator by `e`. -/
theorem dysonSeriesLeft_moserGenerator_conj {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] (e : V ≃L[ℝ] W) (hω : ContDiff ℝ 1 ω) (hinv : ∀ t, (ω t).IsInvertible)
    (t : ℝ) :
    dysonSeriesLeft
        (moserGenerator fun s => e.bilinearCongr (ω s)) t =
      e.conjContinuousAlgEquiv (dysonSeriesLeft (moserGenerator ω) t) := by
  have h : moserGenerator (fun s => e.bilinearCongr (ω s)) =
      fun s => e.conjContinuousAlgEquiv (moserGenerator ω s) :=
    funext fun s => moserGenerator_conj e ω s
  rw [h]
  exact (map_dysonSeriesLeft e.conjContinuousAlgEquiv.continuous
    (continuous_moserGenerator hω hinv) t).symm

section Parametric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E}
  {ω : E → ℝ → V →L[ℝ] V →L[ℝ] ℝ}

/-- The Moser generator of a family of paths of invertible forms that is `Cⁿ⁺¹` jointly in a
parameter from an open set `U` of a normed space and the time is `Cⁿ` jointly in both. -/
theorem contDiffOn_parametric_moserGenerator {n : WithTop ℕ∞} (hU : IsOpen U)
    (hω : ContDiffOn ℝ (n + 1) (Function.uncurry ω) (U ×ˢ Set.univ))
    (hinv : ∀ x ∈ U, ∀ t, (ω x t).IsInvertible) :
    ContDiffOn ℝ n (fun q : E × ℝ => moserGenerator (ω q.1) q.2) (U ×ˢ Set.univ) := by
  have hO : IsOpen (U ×ˢ (Set.univ : Set ℝ)) := hU.prod isOpen_univ
  -- The time derivative is the derivative of `Function.uncurry ω` in the direction `(0, 1)`.
  have hderiv (q : E × ℝ) (hq : q ∈ U ×ˢ Set.univ) :
      deriv (ω q.1) q.2 = fderiv ℝ (Function.uncurry ω) q (0, 1) :=
    (TauCeti.hasDerivAt_slice_right (u := Function.uncurry ω)
      ((hω.contDiffAt (hO.mem_nhds hq)).differentiableAt (by simp))).deriv
  have hD : ContDiffOn ℝ n (fun q => fderiv ℝ (Function.uncurry ω) q (0, 1)) (U ×ˢ Set.univ) :=
    hω.fderiv_apply_of_isOpen hO le_rfl (0, 1)
  have hI : ContDiffOn ℝ n (fun q : E × ℝ => (ω q.1 q.2).inverse) (U ×ˢ Set.univ) :=
    (hω.of_le le_self_add).clm_inverse fun q hq => hinv q.1 hq.1 q.2
  refine ((hI.clm_comp hD).const_smul (-(2⁻¹ : ℝ))).congr fun q hq => ?_
  rw [moserGenerator_def, hderiv q hq]

/-- **Smooth dependence of the linear Moser flow on parameters.** For a family of paths `ω x` of
invertible forms that is `Cⁿ⁺¹` jointly in a parameter `x` from an open set `U` of a normed space
and the time, the propagator `dysonSeriesLeft (moserGenerator (ω x)) t` is `Cⁿ` jointly in `x`
and `t`. -/
theorem contDiffOn_parametric_dysonSeriesLeft_moserGenerator {n : ℕ∞} (hU : IsOpen U)
    (hω : ContDiffOn ℝ (n + 1) (Function.uncurry ω) (U ×ˢ Set.univ))
    (hinv : ∀ x ∈ U, ∀ t, (ω x t).IsInvertible) :
    ContDiffOn ℝ n (fun q : E × ℝ => dysonSeriesLeft (moserGenerator (ω q.1)) q.2)
      (U ×ˢ Set.univ) :=
  contDiffOn_parametric_dysonSeriesLeft hU (p := fun x => moserGenerator (ω x))
    (contDiffOn_parametric_moserGenerator hU hω hinv)

end Parametric

section Segment

variable (V) in
/-- The pairs `(a, b)` of bilinear forms on `V` all of whose convex combinations
`(1 - s) • a + s • b`, `0 ≤ s ≤ 1`, have invertible contractions `V → V*`. -/
def invertibleSegments : Set ((V →L[ℝ] V →L[ℝ] ℝ) × (V →L[ℝ] V →L[ℝ] ℝ)) :=
  {p | ∀ s ∈ Set.Icc (0 : ℝ) 1, ((1 - s) • p.1 + s • p.2).IsInvertible}

omit [CompleteSpace V] in
@[simp]
theorem mem_invertibleSegments_iff {p : (V →L[ℝ] V →L[ℝ] ℝ) × (V →L[ℝ] V →L[ℝ] ℝ)} :
    p ∈ invertibleSegments V ↔
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ((1 - s) • p.1 + s • p.2).IsInvertible :=
  Iff.rfl

/-- On a Banach space, the pairs of bilinear forms whose segment consists of invertible forms
form an open set. -/
theorem isOpen_invertibleSegments : IsOpen (invertibleSegments V) := by
  refine isOpen_iff_eventually.2 fun p hp ↦
    isCompact_Icc.eventually_forall_of_forall_eventually fun s hs ↦ ?_
  have hc : ContDiff ℝ 0 fun q : ((V →L[ℝ] V →L[ℝ] ℝ) × (V →L[ℝ] V →L[ℝ] ℝ)) × ℝ ↦
      (1 - q.2) • q.1.1 + q.2 • q.1.2 :=
    ((contDiff_const.sub contDiff_snd).smul contDiff_fst.fst).add
      (contDiff_snd.smul contDiff_fst.snd)
  exact hc.continuous.continuousAt.eventually (hp s hs).eventually_nhds

/-- The time-one linear Moser flow from `a` to `b`: the propagator at time `1` of the Moser
generator of the path `TauCeti.smoothSegmentPath a b`, that is `t ↦ a + β t • (b - a)`, where `β`
is `Real.smoothTransition`. For a pair of skew forms in `invertibleSegments V` it pulls `b` back
to `a` (`apply_segmentMoserFlow`). -/
def segmentMoserFlow (a b : V →L[ℝ] V →L[ℝ] ℝ) : V →L[ℝ] V :=
  dysonSeriesLeft (moserGenerator (TauCeti.smoothSegmentPath a b)) 1

omit [CompleteSpace V] in
theorem segmentMoserFlow_def (a b : V →L[ℝ] V →L[ℝ] ℝ) :
    segmentMoserFlow a b = dysonSeriesLeft (moserGenerator (TauCeti.smoothSegmentPath a b)) 1 :=
  (rfl)

variable {a b : V →L[ℝ] V →L[ℝ] ℝ}

omit [CompleteSpace V] in
/-- Along the path of `segmentMoserFlow`, every form is invertible when the pair is in
`invertibleSegments V`, since the path stays on the segment from `a` to `b`. -/
private theorem isInvertible_segmentPath (hp : (a, b) ∈ invertibleSegments V) (t : ℝ) :
    (TauCeti.smoothSegmentPath a b t).IsInvertible := by
  obtain ⟨s, hs, h⟩ := (segment_eq_image ℝ a b).subset (TauCeti.smoothSegmentPath_mem_segment a b t)
  exact h ▸ hp s hs

/-- **The linear Moser flow of a segment.** For skew forms `a`, `b` all of whose convex
combinations are invertible, `segmentMoserFlow a b` pulls `b` back to `a`. -/
theorem apply_segmentMoserFlow (hp : (a, b) ∈ invertibleSegments V)
    (ha : ∀ v w, a v w = -a w v) (hb : ∀ v w, b v w = -b w v) (u v : V) :
    b (segmentMoserFlow a b u) (segmentMoserFlow a b v) = a u v := by
  rw [segmentMoserFlow_def]
  have h := apply_dysonSeriesLeft_moserGenerator (TauCeti.contDiff_smoothSegmentPath a b)
    (isInvertible_segmentPath hp)
    (fun t v w ↦ by simp [TauCeti.smoothSegmentPath_def, ha v w, hb v w]; ring) 1 u v
  rwa [TauCeti.smoothSegmentPath_of_one_le a b le_rfl,
    TauCeti.smoothSegmentPath_of_nonpos a b le_rfl] at h

/-- The linear Moser flow of a pair in `invertibleSegments V` is invertible. -/
theorem isUnit_segmentMoserFlow (hp : (a, b) ∈ invertibleSegments V) :
    IsUnit (segmentMoserFlow a b) :=
  isUnit_dysonSeriesLeft (continuous_moserGenerator (TauCeti.contDiff_smoothSegmentPath a b)
    (isInvertible_segmentPath hp)) 1

/-- The linear Moser flow of a segment is smooth in the pair of forms, on the open set
`invertibleSegments V`. -/
theorem contDiffOn_segmentMoserFlow {n : ℕ∞} :
    ContDiffOn ℝ n (fun p : (V →L[ℝ] V →L[ℝ] ℝ) × (V →L[ℝ] V →L[ℝ] ℝ) ↦ segmentMoserFlow p.1 p.2)
      (invertibleSegments V) := by
  have hω : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) (Function.uncurry
      fun (p : (V →L[ℝ] V →L[ℝ] ℝ) × (V →L[ℝ] V →L[ℝ] ℝ)) (t : ℝ) ↦
        TauCeti.smoothSegmentPath p.1 p.2 t)
      (invertibleSegments V ×ˢ Set.univ) :=
    (contDiff_fst.fst.smoothSegmentPath contDiff_fst.snd contDiff_snd).contDiffOn
  have h := contDiffOn_parametric_dysonSeriesLeft_moserGenerator (n := ⊤)
    isOpen_invertibleSegments hω fun p hp t ↦ isInvertible_segmentPath hp t
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (V →L[ℝ] V →L[ℝ] ℝ) × (V →L[ℝ] V →L[ℝ] ℝ) ↦ (p, (1 : ℝ)))
      (invertibleSegments V) := contDiffOn_id.prodMk contDiffOn_const
  refine ((h.comp h1 fun p hp ↦ ⟨hp, Set.mem_univ _⟩).of_le (by exact_mod_cast le_top)).congr
    fun p _ ↦ ?_
  simp only [Function.comp_apply, segmentMoserFlow_def]

/-- **Naturality of the linear Moser flow of a segment.** Moving both forms along a linear
isomorphism `e : V ≃L[ℝ] W` conjugates their linear Moser flow by `e`. -/
theorem segmentMoserFlow_conj {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] (e : V ≃L[ℝ] W) (hp : (a, b) ∈ invertibleSegments V) :
    segmentMoserFlow (e.bilinearCongr a) (e.bilinearCongr b) =
      e.conjContinuousAlgEquiv (segmentMoserFlow a b) := by
  rw [segmentMoserFlow_def, segmentMoserFlow_def, ← dysonSeriesLeft_moserGenerator_conj e
    (TauCeti.contDiff_smoothSegmentPath a b) (isInvertible_segmentPath hp)]
  congr 2
  ext1 t
  rw [TauCeti.map_smoothSegmentPath]

end Segment

/-- **The linear Moser lemma.** On a finite-dimensional real space `V`, a `Cⁿ⁺¹` path `t ↦ ω t`
of skew forms, each nondegenerate, is trivialized by a `Cⁿ⁺¹` path `Ψ` of invertible operators:
`Ψ 0 = 1` and `(Ψ t)^* (ω t) = ω 0` for every `t`. The path given
is `dysonSeriesLeft (moserGenerator ω)` (see `apply_dysonSeriesLeft_moserGenerator`), and the
statement holds in every order of differentiability `n + 1 ≥ 1`; the smooth case is `n = ⊤`,
since `⊤ + 1 = ⊤`.

Milestone: *Linear Moser lemma*. -/
theorem exists_contDiff_isUnit_apply_eq [FiniteDimensional ℝ V] {n : ℕ∞}
    (hω : ContDiff ℝ (n + 1) ω) (hskew : ∀ t v w, ω t v w = -ω t w v)
    (hnd : ∀ t, (ω t).toBilinForm.Nondegenerate) :
    ∃ Ψ : ℝ → V →L[ℝ] V, ContDiff ℝ (n + 1) Ψ ∧ Ψ 0 = 1 ∧ (∀ t, IsUnit (Ψ t)) ∧
      ∀ t v w, ω t (Ψ t v) (Ψ t w) = ω 0 v w := by
  have hinv (t : ℝ) : (ω t).IsInvertible :=
    ContinuousLinearMap.isInvertible_iff_nondegenerate_toBilinForm.2 (hnd t)
  have h1 : ContDiff ℝ 1 ω := hω.of_le le_add_self
  exact ⟨_, contDiff_dysonSeriesLeft_moserGenerator hω hinv, dysonSeriesLeft_zero _,
    isUnit_dysonSeriesLeft (continuous_moserGenerator h1 hinv),
    apply_dysonSeriesLeft_moserGenerator h1 hinv hskew⟩

end Forms

section ComplexStructures

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]

/-- The Moser generator of a path `J` of complex structures: `(1/2) J t * J̇ t`. -/
def complexMoserGenerator (J : ℝ → B) (t : ℝ) : B :=
  (2⁻¹ : ℝ) • (J t * deriv J t)

theorem complexMoserGenerator_def (J : ℝ → B) (t : ℝ) :
    complexMoserGenerator J t = (2⁻¹ : ℝ) • (J t * deriv J t) := (rfl)

variable {J : ℝ → B}

/-- The complex Moser generator of a `Cⁿ⁺¹` path is `Cⁿ`. -/
theorem contDiff_complexMoserGenerator {n : WithTop ℕ∞} (hJ : ContDiff ℝ (n + 1) J) :
    ContDiff ℝ n (complexMoserGenerator J) :=
  ((hJ.of_le le_self_add).mul (contDiff_succ_iff_deriv.1 hJ).2.2).const_smul (2⁻¹ : ℝ)

/-- The complex Moser generator of a `C¹` path is continuous. -/
theorem continuous_complexMoserGenerator (hJ : ContDiff ℝ 1 J) :
    Continuous (complexMoserGenerator J) :=
  (contDiff_complexMoserGenerator (n := 0) (by rwa [zero_add])).continuous

/-- The complex Moser generator `A` of a path of complex structures satisfies
`J̇ t + J t * A t = A t * J t`. -/
theorem deriv_add_mul_complexMoserGenerator (hsq : ∀ t, J t * J t = -1) (t : ℝ) :
    deriv J t + J t * complexMoserGenerator J t = complexMoserGenerator J t * J t := by
  have h := TauCeti.mul_fderiv_add_fderiv_mul_eq_zero (𝕜 := ℝ) (x := t) (.of_forall hsq) 1
  rw [fderiv_apply_one_eq_deriv] at h
  have h' : J t * deriv J t * J t = deriv J t := by
    rw [mul_assoc, eq_neg_of_add_eq_zero_right h, mul_neg, ← mul_assoc, hsq, neg_one_mul, neg_neg]
  rw [complexMoserGenerator_def, mul_smul_comm, smul_mul_assoc, h', ← mul_assoc, hsq,
    neg_one_mul, smul_neg]
  module

variable [CompleteSpace B]

/-- **The linear Moser lemma for complex structures, explicit form.** For a `C¹` path `J` of
complex structures in a real Banach algebra, the propagator `Ψ = dysonSeriesLeft A` of the
complex Moser generator `A = complexMoserGenerator J` satisfies `Ψ t * J 0 = J t * Ψ t`. -/
theorem dysonSeriesLeft_complexMoserGenerator_mul (hJ : ContDiff ℝ 1 J)
    (hsq : ∀ t, J t * J t = -1) (t : ℝ) :
    dysonSeriesLeft (complexMoserGenerator J) t * J 0 =
      J t * dysonSeriesLeft (complexMoserGenerator J) t := by
  set A := complexMoserGenerator J
  set Ψ := dysonSeriesLeft A
  have hA : Continuous A := continuous_complexMoserGenerator hJ
  have hd := hJ.differentiable one_ne_zero
  -- The defect `E t = J t * Ψ t - Ψ t * J 0` solves `E' = A E` and vanishes at `0`.
  have hE (s : ℝ) : HasDerivAt (fun s => J s * Ψ s - Ψ s * J 0)
      (A s * (J s * Ψ s - Ψ s * J 0)) s := by
    refine (((hd s).hasDerivAt.mul (hasDerivAt_dysonSeriesLeft hA s)).sub
      ((hasDerivAt_dysonSeriesLeft hA s).mul_const (J 0))).congr_deriv ?_
    rw [mul_sub, ← mul_assoc, ← mul_assoc, ← deriv_add_mul_complexMoserGenerator hsq s,
      add_mul, mul_assoc, mul_assoc]
  have h := eq_dysonSeriesLeft_mul hA hE t
  rw [show Ψ 0 = 1 from dysonSeriesLeft_zero A, mul_one, one_mul, sub_self, mul_zero,
    sub_eq_zero] at h
  exact h.symm

/-- The propagator of the complex Moser generator of a `Cⁿ⁺¹` path is `Cⁿ⁺¹`. -/
theorem contDiff_dysonSeriesLeft_complexMoserGenerator {n : ℕ∞} (hJ : ContDiff ℝ (n + 1) J) :
    ContDiff ℝ (n + 1) (dysonSeriesLeft (complexMoserGenerator J)) := by
  have hA := contDiff_complexMoserGenerator hJ
  exact contDiff_succ_of_hasDerivAt_clm_apply ((ContinuousLinearMap.mul ℝ _).contDiff.comp hA)
    fun t => by simpa using hasDerivAt_dysonSeriesLeft hA.continuous t

/-- **The linear Moser lemma for complex structures.** A `Cⁿ⁺¹` path `J t` of complex structures
in a real Banach algebra, such as the operators on a real Banach space, is conjugate to `J 0` by
a `Cⁿ⁺¹` path `Ψ t` of units with `Ψ 0 = 1`: `Ψ t * J 0 = J t * Ψ t`. The path given is
`dysonSeriesLeft (complexMoserGenerator J)`. -/
theorem exists_contDiff_isUnit_mul_eq_mul {n : ℕ∞} (hJ : ContDiff ℝ (n + 1) J)
    (hsq : ∀ t, J t * J t = -1) :
    ∃ Ψ : ℝ → B, ContDiff ℝ (n + 1) Ψ ∧ Ψ 0 = 1 ∧ (∀ t, IsUnit (Ψ t)) ∧
      ∀ t, Ψ t * J 0 = J t * Ψ t := by
  have h1 : ContDiff ℝ 1 J := hJ.of_le le_add_self
  exact ⟨_, contDiff_dysonSeriesLeft_complexMoserGenerator hJ, dysonSeriesLeft_zero _,
    isUnit_dysonSeriesLeft (continuous_complexMoserGenerator h1),
    dysonSeriesLeft_complexMoserGenerator_mul h1 hsq⟩

end ComplexStructures

section AlmostComplexStructures

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The linear Moser lemma for almost complex structures.** On a finite-dimensional real space
`V`, let `J t` be almost complex structures whose endomorphisms form a `Cⁿ⁺¹` path in the
operator norm. Then a `Cⁿ⁺¹` path `Ψ t` of continuous linear automorphisms of `V`, with `Ψ 0` the
identity, transports `J 0` to `J t`: `J t = Ψ t ∘ J 0 ∘ (Ψ t)⁻¹`. -/
theorem exists_contDiff_transport_eq {n : ℕ∞} {J : ℝ → AlmostComplexStructure V}
    (hJ : ContDiff ℝ (n + 1) fun t => LinearMap.toContinuousLinearMap (J t).toLinearMap) :
    ∃ Ψ : ℝ → V ≃L[ℝ] V, ContDiff ℝ (n + 1) (fun t => (Ψ t : V →L[ℝ] V)) ∧
      Ψ 0 = ContinuousLinearEquiv.refl ℝ V ∧
      ∀ t, (J 0).transport (Ψ t).toLinearEquiv = J t := by
  obtain ⟨Ψ, hΨ, h0, hu, hc⟩ := exists_contDiff_isUnit_mul_eq_mul hJ
    fun t => (J t).toContinuousLinearMap_mul_self
  set e : ℝ → V ≃L[ℝ] V := fun t => ContinuousLinearEquiv.unitsEquiv ℝ V (hu t).unit
  have he (t : ℝ) : (e t : V →L[ℝ] V) = Ψ t := by
    ext v
    simp [e, ContinuousLinearEquiv.unitsEquiv_apply]
  refine ⟨e, ?_, ?_, fun t => ?_⟩
  · simpa only [he] using hΨ
  · ext v
    simp [← ContinuousLinearEquiv.coe_coe, he, h0]
  · ext v
    have h := congr($(hc t) ((e t).symm v))
    rw [← he] at h
    simpa using h

end AlmostComplexStructures

end SymplecticGeometry

end

end
