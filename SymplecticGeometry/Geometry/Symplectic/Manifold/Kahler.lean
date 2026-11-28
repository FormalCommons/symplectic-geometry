/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Kahler
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.CompatibleMetric
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.LeviCivita
import SymplecticGeometry.Geometry.Symplectic.Manifold.Nijenhuis
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Metric
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Metric

/-!
# The Kähler condition through the Levi-Civita derivative of `J`

Let `σ` be a smooth two-form and `J` a smooth almost complex structure on a manifold `M`, let
`⟪·, ·⟫` be a Riemannian metric on `TM` with `⟪u, v⟫ = σ(u, J v)`, and let `∇` be a Levi-Civita
connection of that metric. Write `∇J` for Tau Ceti's induced connection
`cov.hom cov J.toEndomorphism` applied to `J`, `dσ` for `mextDeriv σ.val` and `N_J` for Tau Ceti's
Nijenhuis tensor `J.nijenhuis`.

The sign of the formula below depends on two conventions. The Nijenhuis tensor is
`N_J(X, Y) = [JX, JY] - [X, Y] - J[JX, Y] - J[X, JY]`, where `[·, ·]` is Mathlib's `mlieBracket` of
vector fields (the commutator of derivations); this is the `N_J` of [McDuffSalamon2017], and the
negative of that of [Moroianu2007]. The exterior derivative `dσ` carries no normalising factor.
This file proves

* the formula of [McDuffSalamon2017], equation (4.2.4), relating the three:
  `⟪N_J(u, v), w⟫ = dσ(J u, v, w) + dσ(u, J v, w) + 2 ⟪J ((∇_w J) u), v⟫`;
* that `J` is parallel, `∇J = 0`, if and only if `σ` is closed and `N_J = 0`
  ([McDuffSalamon2017], Lemma 4.2.5; [Moroianu2007], Lemma 5.4 and Theorem 5.5, where the
  condition is stated without the integrability theorem);
* equivalently, that `∇J = 0` if and only if `σ` is a Kähler form for `J`.

Both are then stated for a two-form compatible with `J` and the Levi-Civita connection of the
metric `g_J = σ(·, J ·)`.

## Main results

In the namespace `TauCeti.SmoothAlmostComplexStructure`, for a metric with
`⟪u, v⟫ = σ(u, J v)` and a Levi-Civita connection `∇`:

* `inner_nijenhuis_eq`: the formula for `⟪N_J(u, v), w⟫`.
* `hom_toEndomorphism_eq_zero_iff`: `∇J = 0 ↔ dσ = 0 ∧ N_J = 0`.
* `hom_toEndomorphism_eq_zero_iff_isKahler`: `∇J = 0 ↔ σ.IsKahler J`.

In the namespace `TauCeti.SmoothTwoForm`:

* `Compatible.inner_nijenhuis_and_leviCivita_hom_eq_zero_iff`: the formula and the equivalence
  for a compatible pair and the Levi-Civita connection of `g_J`.
* `Compatible.leviCivita_hom_toEndomorphism_eq_zero_iff_isKahler`: the Kähler form of it.

## Implementation notes

With `α(u, v, w) = ⟪(∇_u J) v, w⟫`, the identities of `AlmostComplex/LeviCivita.lean` say that
`α` is skew in its last two arguments (`inner_hom_apply_eq_neg`), that
`α(u, J v, w) = α(u, v, J w)` (`inner_hom_apply_apply_eq`), and that `dσ` is the
cyclic sum of `α`; the formula of `N_J` through a torsion-free connection
(`nijenhuis_eq_hom_toEndomorphism`) expresses `⟪N_J(u, v), w⟫` through `α`. Both sides of the
formula then reduce to the same four terms of `α`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Lemma 4.2.5 and equation (4.2.4).
* [A. Moroianu, *Lectures on Kähler Geometry*][Moroianu2007], Lemma 5.4 and Theorem 5.5.
-/

public section

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

namespace SmoothAlmostComplexStructure

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
  {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}

/-- If `⟪u, v⟫ = σ(u, J v)` and `∇` is a Levi-Civita connection, the Nijenhuis tensor of `J` is
related to `dσ` and `∇J` by
`⟪N_J(u, v), w⟫ = dσ(J u, v, w) + dσ(u, J v, w) + 2 ⟪J ((∇_w J) u), v⟫`.
Here `N_J(X, Y) = [JX, JY] - [X, Y] - J[JX, Y] - J[X, JY]` for Mathlib's `mlieBracket`, and `dσ` has
no normalising factor. -/
theorem inner_nijenhuis_eq (hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v))
    (hcov : cov.IsLeviCivitaConnection) (x : M) (u v w : TangentSpace I x) :
    ⟪J.nijenhuis x u v, w⟫ =
      mextDeriv σ.val x ![J x u, v, w] + mextDeriv σ.val x ![u, J x v, w] +
        2 * ⟪J x (cov.hom cov J.toEndomorphism x w u), v⟫ := by
  set D := cov.hom cov J.toEndomorphism x
  -- `α(a, b, c) = ⟪(∇_a J) b, c⟫` is skew in `b, c`.
  have hskew (a b c : TangentSpace I x) : ⟪D a b, c⟫ = -⟪D a c, b⟫ := by
    rw [inner_hom_apply_eq_neg hJ hcov.isMetricCompatible, real_inner_comm]
  rw [J.nijenhuis_eq_hom_toEndomorphism cov (congr_fun hcov.torsion x),
    mextDeriv_apply_eq_inner hJ hcov, mextDeriv_apply_eq_inner hJ hcov,
    inner_apply_left_eq_neg hJ, inner_hom_apply_apply_eq hJ x w u v, hskew v w (J x u),
    hskew (J x v) w u]
  simp only [inner_add_left, inner_sub_left]
  ring

/-- If `⟪u, v⟫ = σ(u, J v)` and `∇` is a Levi-Civita connection, then `J` is parallel,
`∇J = 0`, if and only if `σ` is closed and the Nijenhuis tensor of `J` vanishes. -/
theorem hom_toEndomorphism_eq_zero_iff (hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v))
    (hcov : cov.IsLeviCivitaConnection) :
    cov.hom cov J.toEndomorphism = 0 ↔ σ.IsClosed ∧ J.nijenhuis = 0 := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hσ, hN⟩ ↦ ?_⟩
  · refine σ.isClosed_iff_forall_mextDeriv_apply_eq_zero.2 fun x ↦ ?_
    ext a
    have ha : a = ![a 0, a 1, a 2] := (FinVec.etaExpand_eq _).symm
    rw [ha, mextDeriv_apply_eq_inner hJ hcov, h]
    simp
  · funext x
    ext u v
    rw [J.nijenhuis_eq_hom_toEndomorphism cov (congr_fun hcov.torsion x), h]
    simp
  · have hcl := σ.isClosed_iff_forall_mextDeriv_apply_eq_zero.1 hσ
    funext x
    ext w u : 2
    -- `J ((∇_w J) u)` is orthogonal to every `v`, by the formula for `N_J`.
    have h : J x (cov.hom cov J.toEndomorphism x w u) = 0 :=
      ext_inner_right ℝ fun v ↦ by
        have := inner_nijenhuis_eq hJ hcov x u v w
        rw [hN, hcl x] at this
        simpa using this.symm
    have h' := congrArg (J x) h
    rw [J.apply_apply] at h'
    simpa using h'

/-- If `⟪u, v⟫ = σ(u, J v)` and `∇` is a Levi-Civita connection, then `J` is parallel,
`∇J = 0`, if and only if `σ` is a Kähler form for `J`. -/
theorem hom_toEndomorphism_eq_zero_iff_isKahler (hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v))
    (hcov : cov.IsLeviCivitaConnection) :
    cov.hom cov J.toEndomorphism = 0 ↔ σ.IsKahler J := by
  rw [hom_toEndomorphism_eq_zero_iff hJ hcov, SmoothTwoForm.isKahler_iff,
    and_iff_right (SmoothTwoForm.compatible_of_inner_eq hJ)]

end SmoothAlmostComplexStructure

namespace SmoothTwoForm

variable {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}

/-- Let `σ` be a smooth two-form compatible with a smooth almost complex structure `J`, and let
`∇` be the Levi-Civita connection of the metric `g_J(u, v) = σ(u, J v)`. Then
* `g_J(N_J(u, v), w) = dσ(J u, v, w) + dσ(u, J v, w) + 2 g_J(J ((∇_w J) u), v)` for all
  `u v w : T_x M`;
* `∇J = 0` if and only if `σ` is closed and the Nijenhuis tensor `N_J` vanishes.

Milestone: *Parallel almost complex structures and the Kähler condition*. -/
theorem Compatible.inner_nijenhuis_and_leviCivita_hom_eq_zero_iff (hJ : σ.Compatible J) :
    letI := hJ.riemannianBundle
    (∀ x (u v w : TangentSpace I x),
      ⟪J.nijenhuis x u v, w⟫ =
        mextDeriv σ.val x ![J x u, v, w] + mextDeriv σ.val x ![u, J x v, w] +
          2 * ⟪J x ((CovariantDerivative.leviCivitaConnection I M).hom
            (CovariantDerivative.leviCivitaConnection I M) J.toEndomorphism x w u), v⟫) ∧
    ((CovariantDerivative.leviCivitaConnection I M).hom
        (CovariantDerivative.leviCivitaConnection I M) J.toEndomorphism = 0 ↔
      σ.IsClosed ∧ J.nijenhuis = 0) := by
  let := hJ.riemannianBundle
  have hg := hJ.inner_riemannianBundle
  have hL := CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I (M := M)
  exact ⟨SmoothAlmostComplexStructure.inner_nijenhuis_eq hg hL,
    SmoothAlmostComplexStructure.hom_toEndomorphism_eq_zero_iff hg hL⟩

/-- Let `σ` be a smooth two-form compatible with a smooth almost complex structure `J`, and let
`∇` be the Levi-Civita connection of the metric `g_J(u, v) = σ(u, J v)`. Then `∇J = 0` if and
only if `σ` is a Kähler form for `J`. -/
theorem Compatible.leviCivita_hom_toEndomorphism_eq_zero_iff_isKahler (hJ : σ.Compatible J) :
    letI := hJ.riemannianBundle
    (CovariantDerivative.leviCivitaConnection I M).hom
        (CovariantDerivative.leviCivitaConnection I M) J.toEndomorphism = 0 ↔
      σ.IsKahler J := by
  rw [hJ.inner_nijenhuis_and_leviCivita_hom_eq_zero_iff.2, isKahler_iff, and_iff_right hJ]

end SmoothTwoForm

end TauCeti

end
