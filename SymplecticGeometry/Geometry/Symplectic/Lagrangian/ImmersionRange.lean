/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Symplectic.Lagrangian.Manifold

/-!
# Ranges of Lagrangian immersions

Given a manifold `M` with a nondegenerate two-form `σ`, and a natural number `r`, this file
names the sets of `M` that are swept out by a Lagrangian immersion (Tau Ceti's
`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianImmersion`) from a Hausdorff, second countable
smooth manifold modelled on `EuclideanSpace ℝ (Fin r)`. Such a set is an immersed Lagrangian
submanifold, possibly with self-intersections; the injective variant rules those out.

The source manifold lives in an explicit universe `u`, which the statements give as
`IsLagrangianImmersionRange.{u}`. Since a Lagrangian immersion has a source of half the dimension
of `M`, a set satisfies either predicate only when `2 * r = finrank ℝ E`.

## Main definitions

* `TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianImmersionRange`: `A` is the range of a
  Lagrangian immersion whose source is a second countable Hausdorff manifold modelled on
  `EuclideanSpace ℝ (Fin r)`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.IsInjectiveLagrangianImmersionRange`: the same, with an
  injective immersion.

## Main results

* `isLagrangianImmersionRange_range`, `isInjectiveLagrangianImmersionRange_range`: the range of
  such an immersion satisfies the predicate; these are the constructors.
* `IsInjectiveLagrangianImmersionRange.isLagrangianImmersionRange`: the injective predicate implies
  the other one.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.4
-/

public section

universe u

open Set Manifold Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {r : ℕ} {A : Set M}

variable (hσ : σ.IsNondegenerate) (r : ℕ) (A : Set M) in
/-- A set `A` of `M` is the **range of a Lagrangian immersion** for `σ` of dimension `r` if there
are a Hausdorff, second countable smooth manifold `S` in the universe `u`, modelled on
`EuclideanSpace ℝ (Fin r)`, and a Lagrangian immersion `ι : S → M` for `σ` with `range ι = A`. -/
def IsLagrangianImmersionRange : Prop :=
  ∃ (S : Type u) (_ : TopologicalSpace S) (_ : ChartedSpace (EuclideanSpace ℝ (Fin r)) S),
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) ∞ S ∧ T2Space S ∧ SecondCountableTopology S ∧
    ∃ ι : S → M, hσ.IsLagrangianImmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) ι ∧ range ι = A

variable (hσ : σ.IsNondegenerate) (r : ℕ) (A : Set M) in
/-- A set `A` of `M` is the **range of an injective Lagrangian immersion** for `σ` of dimension
`r` if there are a Hausdorff, second countable smooth manifold `S` in the universe `u`, modelled
on `EuclideanSpace ℝ (Fin r)`, and an injective Lagrangian immersion `ι : S → M` for `σ` with
`range ι = A`. -/
def IsInjectiveLagrangianImmersionRange : Prop :=
  ∃ (S : Type u) (_ : TopologicalSpace S) (_ : ChartedSpace (EuclideanSpace ℝ (Fin r)) S),
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) ∞ S ∧ T2Space S ∧ SecondCountableTopology S ∧
    ∃ ι : S → M, hσ.IsLagrangianImmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) ι ∧
      Function.Injective ι ∧ range ι = A

variable {hσ : σ.IsNondegenerate}

theorem isLagrangianImmersionRange_def :
    hσ.IsLagrangianImmersionRange.{u} r A ↔
      ∃ (S : Type u) (_ : TopologicalSpace S) (_ : ChartedSpace (EuclideanSpace ℝ (Fin r)) S),
        IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) ∞ S ∧ T2Space S ∧ SecondCountableTopology S ∧
        ∃ ι : S → M, hσ.IsLagrangianImmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) ι ∧ range ι = A :=
  Iff.rfl

theorem isInjectiveLagrangianImmersionRange_def :
    hσ.IsInjectiveLagrangianImmersionRange.{u} r A ↔
      ∃ (S : Type u) (_ : TopologicalSpace S) (_ : ChartedSpace (EuclideanSpace ℝ (Fin r)) S),
        IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) ∞ S ∧ T2Space S ∧ SecondCountableTopology S ∧
        ∃ ι : S → M, hσ.IsLagrangianImmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) ι ∧
          Function.Injective ι ∧ range ι = A :=
  Iff.rfl

/-- The range of a Lagrangian immersion whose source is a second countable Hausdorff manifold
modelled on `EuclideanSpace ℝ (Fin r)` satisfies `IsLagrangianImmersionRange r`. -/
theorem isLagrangianImmersionRange_range {S : Type u} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin r)) S] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) ∞ S]
    [T2Space S] [SecondCountableTopology S] {ι : S → M}
    (hι : hσ.IsLagrangianImmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) ι) :
    hσ.IsLagrangianImmersionRange.{u} r (range ι) :=
  ⟨S, _, _, inferInstance, inferInstance, inferInstance, ι, hι, rfl⟩

/-- The range of an injective Lagrangian immersion whose source is a second countable Hausdorff
manifold modelled on `EuclideanSpace ℝ (Fin r)` satisfies
`IsInjectiveLagrangianImmersionRange r`. -/
theorem isInjectiveLagrangianImmersionRange_range {S : Type u} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin r)) S] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) ∞ S]
    [T2Space S] [SecondCountableTopology S] {ι : S → M}
    (hι : hσ.IsLagrangianImmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) ι) (hinj : Function.Injective ι) :
    hσ.IsInjectiveLagrangianImmersionRange.{u} r (range ι) :=
  ⟨S, _, _, inferInstance, inferInstance, inferInstance, ι, hι, hinj, rfl⟩

/-- The range of an injective Lagrangian immersion is the range of a Lagrangian immersion. -/
theorem IsInjectiveLagrangianImmersionRange.isLagrangianImmersionRange
    (h : hσ.IsInjectiveLagrangianImmersionRange.{u} r A) :
    hσ.IsLagrangianImmersionRange.{u} r A := by
  obtain ⟨S, _, _, hS, hT2, hSC, ι, hι, -, rfl⟩ := h
  exact isLagrangianImmersionRange_range hι

end TauCeti.SmoothTwoForm.IsNondegenerate

end
