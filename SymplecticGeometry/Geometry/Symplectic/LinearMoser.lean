/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Topology.Algebra.Module.BilinearForm
public import SymplecticGeometry.Analysis.ODE.DysonSeries
import Mathlib.Analysis.Calculus.Deriv.Mul

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

The same argument applies to a differentiable path `J t` of complex structures, `J t * J t = -1`,
in a real Banach algebra. Now the generator is `A t = (1/2) J t * J̇ t`, and its left Dyson series
`Ψ` satisfies `Ψ t * J 0 = J t * Ψ t`: it conjugates `J 0` to `J t`.

Both constructions use no choice beyond the data: the generators are given by formulas in the
family and its derivative. In particular they are compatible with isomorphisms of the data and
can be applied fibrewise to a family of such paths.

## Main definitions

* `SymplecticGeometry.moserGenerator`: the generator `-(1/2) (ω t)⁻¹ ∘ ω̇ t` of a path of forms.
* `SymplecticGeometry.complexMoserGenerator`: the generator `(1/2) J t * J̇ t` of a path of
  complex structures.

## Main results

* `SymplecticGeometry.apply_dysonSeriesLeft_moserGenerator`: the propagator of the Moser
  generator pulls `ω t` back to `ω 0`.
* `SymplecticGeometry.exists_contDiff_isUnit_apply_eq`: the linear Moser lemma on a
  finite-dimensional real vector space.
* `SymplecticGeometry.dysonSeriesLeft_complexMoserGenerator_mul`: the propagator of the complex
  Moser generator conjugates `J 0` to `J t`.
* `SymplecticGeometry.exists_contDiff_isUnit_mul_eq_mul`: the analogue for complex structures.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Corollary 2.5.14 and Exercise 2.5.18.
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

/-- The derivative of a differentiable path of skew-symmetric forms is skew-symmetric. -/
theorem deriv_apply_apply_eq_neg (hω : Differentiable ℝ ω)
    (hskew : ∀ t v w, ω t v w = -ω t w v) (t : ℝ) (v w : V) :
    deriv ω t v w = -deriv ω t w v := by
  have hev (a b : V) : HasDerivAt (fun s => ω s a b) (deriv ω t a b) t := by
    have h := HasDerivAt.clm_apply (c := ω) (u := fun _ => a) (hω t).hasDerivAt
      (hasDerivAt_const t a)
    simpa using HasDerivAt.clm_apply (c := fun s => ω s a) (u := fun _ => b) h
      (hasDerivAt_const t b)
  have h : (fun s => ω s v w) = fun s => -ω s w v := funext fun s => hskew s v w
  exact (hev v w).unique (by rw [h]; exact (hev w v).neg)

variable [CompleteSpace V]

/-- The Moser generator of a `Cⁿ⁺¹` path of invertible forms is `Cⁿ`. -/
theorem contDiff_moserGenerator {n : WithTop ℕ∞} (hω : ContDiff ℝ (n + 1) ω)
    (hinv : ∀ t, (ω t).IsInvertible) : ContDiff ℝ n (moserGenerator ω) := by
  have hinv' : ContDiff ℝ n fun t => (ω t).inverse := by
    refine contDiff_iff_contDiffAt.2 fun t => ?_
    obtain ⟨e, he⟩ := hinv t
    have h := contDiffAt_map_inverse (𝕜 := ℝ) (n := n) e
    rw [he] at h
    exact h.comp t (hω.of_le le_self_add).contDiffAt
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
      deriv_apply_apply_eq_neg hd hskew s (Ψ s v)]
    ring
  have hconst := is_const_of_deriv_eq_zero (fun s => (hf s).differentiableAt)
    fun s => (hf s).deriv
  simpa [Ψ] using hconst t 0

/-- The propagator of the Moser generator of a `Cⁿ⁺¹` path of invertible forms is `Cⁿ⁺¹`. -/
theorem contDiff_dysonSeriesLeft_moserGenerator {n : ℕ∞} (hω : ContDiff ℝ (n + 1) ω)
    (hinv : ∀ t, (ω t).IsInvertible) : ContDiff ℝ (n + 1) (dysonSeriesLeft (moserGenerator ω)) :=
  contDiff_add_one_dysonSeriesLeft (contDiff_moserGenerator hω hinv)

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

/-- The derivative of a differentiable path of complex structures anticommutes with it. -/
theorem deriv_mul_add_mul_deriv_eq_zero (hJ : Differentiable ℝ J) (hsq : ∀ t, J t * J t = -1)
    (t : ℝ) : deriv J t * J t + J t * deriv J t = 0 := by
  have h : J * J = fun _ => -1 := funext hsq
  have h' := (hJ t).hasDerivAt.mul (hJ t).hasDerivAt
  rw [h] at h'
  exact h'.unique (hasDerivAt_const t (-1 : B))

/-- The complex Moser generator `A` of a path of complex structures satisfies
`J̇ t + J t * A t = A t * J t`. -/
theorem deriv_add_mul_complexMoserGenerator (hJ : Differentiable ℝ J)
    (hsq : ∀ t, J t * J t = -1) (t : ℝ) :
    deriv J t + J t * complexMoserGenerator J t = complexMoserGenerator J t * J t := by
  have h := deriv_mul_add_mul_deriv_eq_zero hJ hsq t
  have h' : J t * deriv J t * J t = deriv J t := by
    rw [mul_assoc, eq_neg_of_add_eq_zero_left h, mul_neg, ← mul_assoc, hsq, neg_one_mul, neg_neg]
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
  have hA : Continuous A := (contDiff_complexMoserGenerator (n := 0) (by rwa [zero_add])).continuous
  have hd := hJ.differentiable one_ne_zero
  -- The defect `E t = J t * Ψ t - Ψ t * J 0` solves `E' = A E` and vanishes at `0`.
  have hE (s : ℝ) : HasDerivAt (fun s => J s * Ψ s - Ψ s * J 0)
      (A s * (J s * Ψ s - Ψ s * J 0)) s := by
    refine (((hd s).hasDerivAt.mul (hasDerivAt_dysonSeriesLeft hA s)).sub
      ((hasDerivAt_dysonSeriesLeft hA s).mul_const (J 0))).congr_deriv ?_
    rw [mul_sub, ← mul_assoc, ← mul_assoc, ← deriv_add_mul_complexMoserGenerator hd hsq s,
      add_mul, mul_assoc, mul_assoc]
  have h := eq_dysonSeriesLeft_mul hA hE t
  rw [show Ψ 0 = 1 from dysonSeriesLeft_zero A, mul_one, one_mul, sub_self, mul_zero,
    sub_eq_zero] at h
  exact h.symm

/-- The propagator of the complex Moser generator of a `Cⁿ⁺¹` path is `Cⁿ⁺¹`. -/
theorem contDiff_dysonSeriesLeft_complexMoserGenerator {n : ℕ∞} (hJ : ContDiff ℝ (n + 1) J) :
    ContDiff ℝ (n + 1) (dysonSeriesLeft (complexMoserGenerator J)) :=
  contDiff_add_one_dysonSeriesLeft (contDiff_complexMoserGenerator hJ)

/-- **The linear Moser lemma for complex structures.** A `Cⁿ⁺¹` path `J t` of complex structures
in a real Banach algebra, such as the operators on a real Banach space, is conjugate to `J 0` by
a `Cⁿ⁺¹` path `Ψ t` of units with `Ψ 0 = 1`: `J t = Ψ t * J 0 * (Ψ t)⁻¹`. The path given is
`dysonSeriesLeft (complexMoserGenerator J)`. -/
theorem exists_contDiff_isUnit_mul_eq_mul {n : ℕ∞} (hJ : ContDiff ℝ (n + 1) J)
    (hsq : ∀ t, J t * J t = -1) :
    ∃ Ψ : ℝ → B, ContDiff ℝ (n + 1) Ψ ∧ Ψ 0 = 1 ∧ (∀ t, IsUnit (Ψ t)) ∧
      ∀ t, Ψ t * J 0 = J t * Ψ t := by
  have h1 : ContDiff ℝ 1 J := hJ.of_le le_add_self
  exact ⟨_, contDiff_dysonSeriesLeft_complexMoserGenerator hJ, dysonSeriesLeft_zero _,
    isUnit_dysonSeriesLeft
      (contDiff_complexMoserGenerator (n := 0) (by rwa [zero_add])).continuous,
    dysonSeriesLeft_complexMoserGenerator_mul h1 hsq⟩

end ComplexStructures

end SymplecticGeometry

end

end
