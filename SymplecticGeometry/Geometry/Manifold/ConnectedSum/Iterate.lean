/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import SymplecticGeometry.Geometry.Manifold.Complex.Orientation
public import SymplecticGeometry.Geometry.Manifold.ConnectedSum.OrientationPreserving
public import SymplecticGeometry.Geometry.Manifold.ModelTransport.Remodel
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Geometry.Manifold.Instances.Projectivization
import SymplecticGeometry.Geometry.Manifold.ConnectedSum.EulerCharacteristic
import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.ComplexProjective
import TauCeti.Geometry.Manifold.Morse.CWModel

/-!
# Iterated connected sums with the reversed complex projective plane

Blowing up an oriented four-manifold `M` at a point gives, up to orientation-preserving
diffeomorphism, the oriented connected sum `M # ℙ²‾` of `M` with the complex projective plane with
its orientation reversed; blowing up at `N` points one after another gives an iterated sum
`M # N ℙ²‾`. This file records such iterated sums by a predicate and computes their Euler
characteristic, `χ(M # N ℙ²‾) = χ(M) + N`.

Tau Ceti's oriented connected sum `TauCeti.OrientedConnectedSum` glues two manifolds modelled on
the same real inner product space. The summands are therefore charted on the Hermitian space
`EuclideanSpace ℂ (Fin 2)`, not on `Fin 2 → ℂ`, whose sup norm comes from no inner product. The
projective plane `ℙ ℂ (Fin 3 → ℂ)` is re-modelled there (`SymplecticGeometry.Remodel`) along the
complex-linear identification of `Fin 2 → ℂ` with `EuclideanSpace ℂ (Fin 2)`, and keeps its complex
orientation. All orientations are indexed by `Fin 4`.

## Main definitions

* `SymplecticGeometry.ProjectivePlane`: the complex projective plane, charted on
  `EuclideanSpace ℂ (Fin 2)`, with its orientation `SymplecticGeometry.ProjectivePlane.orientation`.
* `SymplecticGeometry.IsReversedProjectiveSum oM oX N`: the oriented four-manifold `X` is an
  iterated oriented connected sum of the oriented four-manifold `M` with `N` copies of the
  reversed projective plane.

## Main results

* `SymplecticGeometry.isReversedProjectiveSum_zero_iff`,
  `SymplecticGeometry.isReversedProjectiveSum_succ_iff`: the two cases of the definition.
* `SymplecticGeometry.IsReversedProjectiveSum.succ`: a sum with one more copy.
* `SymplecticGeometry.IsReversedProjectiveSum.eulerChar_eq`: `χ(X) = χ(M) + N`, from the formula
  for the Euler characteristic of a connected sum
  (`TauCeti.ConnectedSum.eulerChar_orientedConnectedSum`) and `χ(ℙ²) = 3`
  (`TauCeti.eulerChar_projectivization_complex`).

## References

* [A. Kosinski, *Differential Manifolds*][Kosinski1993], Chapter VI, Section 1.
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], Section 7.1.
-/

public section

noncomputable section

open Module TauCeti
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace SymplecticGeometry

/-- The **complex projective plane** `ℙ ℂ (Fin 3 → ℂ)`, charted on the Hermitian space
`EuclideanSpace ℂ (Fin 2)`: its homogeneous-ratio charts are followed by the complex-linear
identification of `Fin 2 → ℂ` with `EuclideanSpace ℂ (Fin 2)`. -/
abbrev ProjectivePlane : Type :=
  Remodel (EuclideanSpace.equiv (Fin 2) ℂ).symm.toDiffeomorph (ℙ ℂ (Fin 3 → ℂ))

namespace ProjectivePlane

/-- The projective plane is a smooth real manifold, the one underlying its complex structure. -/
instance : IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ ProjectivePlane :=
  (inferInstance : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 2)) ∞ ProjectivePlane).restrictScalars ℝ

/-- The complex orientation of the projective plane, indexed by `Fin 4`: the canonical
orientation of a complex manifold, `SymplecticGeometry.complexManifoldOrientationOfFinrank`. -/
def orientation : Manifold.Orientation 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ProjectivePlane (Fin 4) :=
  complexManifoldOrientationOfFinrank (EuclideanSpace ℂ (Fin 2)) ProjectivePlane
    (r := 1) (by simp)

theorem orientation_def :
    orientation = complexManifoldOrientationOfFinrank (EuclideanSpace ℂ (Fin 2)) ProjectivePlane
      (r := 1) (by simp) :=
  (rfl)

instance : FiniteCWType ProjectivePlane :=
  FiniteCWType.of_isManifold ProjectivePlane 𝓘(ℝ, EuclideanSpace ℂ (Fin 2))

/-- The Euler characteristic of the projective plane is `3`. -/
theorem eulerChar_eq : eulerChar ProjectivePlane = 3 := by
  have := FiniteCWType.of_isManifold (ℙ ℂ (Fin 3 → ℂ)) 𝓘(ℝ, Fin 2 → ℂ)
  rw [← (remodelHomeomorph _ _).eulerChar_eq, eulerChar_projectivization_complex]
  simp

end ProjectivePlane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The oriented four-manifold `X`, charted on `EuclideanSpace ℂ (Fin 2)` with orientation `oX`,
is an **iterated connected sum of the oriented manifold `M` with `N` copies of the reversed
projective plane**, `M # N ℙ²‾`. For `N = 0`, there is a diffeomorphism from `M` to `X` which
preserves the orientations `oM` and `oX` everywhere. For `N + 1`, there is a compact Hausdorff
nonempty oriented manifold `Y`, charted on `EuclideanSpace ℂ (Fin 2)`, which is such a sum with
`N` copies, and a diffeomorphism from `X` to the oriented connected sum
`TauCeti.OrientedConnectedSum oY (-ProjectivePlane.orientation)` which preserves the orientations
`oX` and `TauCeti.OrientedConnectedSum.orientation` everywhere.

The manifold `M` may have another model than `X`, such as the model of a symplectic
four-manifold. Tau Ceti's `TauCeti.IsIteratedConnectedSum` is not used: it records unoriented
sums of manifolds charted on `EuclideanSpace ℝ (Fin n)`, starting from the sphere, while the
summand here must keep its reversed orientation, and the sum starts from `M`. -/
def IsReversedProjectiveSum (oM : Manifold.Orientation I M (Fin 4)) :
    {X : Type} → [TopologicalSpace X] → [ChartedSpace (EuclideanSpace ℂ (Fin 2)) X] →
      [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ X] →
      Manifold.Orientation 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) X (Fin 4) → ℕ → Prop
  | X, _, _, _, oX, 0 =>
    ∃ φ : M ≃ₘ^∞⟮I, 𝓘(ℝ, EuclideanSpace ℂ (Fin 2))⟯ X,
      ∀ x, Manifold.Orientation.IsOrientationPreservingAt oM oX φ x
  | X, _, _, _, oX, N + 1 =>
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (_ : CompactSpace Y) (_ : Nonempty Y)
      (_ : ChartedSpace (EuclideanSpace ℂ (Fin 2)) Y)
      (_ : IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ Y)
      (oY : Manifold.Orientation 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) Y (Fin 4)),
      IsReversedProjectiveSum oM oY N ∧
        ∃ φ : X ≃ₘ^∞⟮𝓘(ℝ, EuclideanSpace ℂ (Fin 2)), 𝓘(ℝ, EuclideanSpace ℂ (Fin 2))⟯
            OrientedConnectedSum oY (-ProjectivePlane.orientation),
          ∀ x, Manifold.Orientation.IsOrientationPreservingAt oX
            (OrientedConnectedSum.orientation oY (-ProjectivePlane.orientation)) φ x

variable {oM : Manifold.Orientation I M (Fin 4)}
  {X : Type} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin 2)) X]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ X]
  {oX : Manifold.Orientation 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) X (Fin 4)}

/-- A manifold is a sum of `M` with no copy of the reversed projective plane exactly when it is
diffeomorphic to `M` by an orientation-preserving diffeomorphism. -/
theorem isReversedProjectiveSum_zero_iff :
    IsReversedProjectiveSum oM oX 0 ↔
      ∃ φ : M ≃ₘ^∞⟮I, 𝓘(ℝ, EuclideanSpace ℂ (Fin 2))⟯ X,
        ∀ x, Manifold.Orientation.IsOrientationPreservingAt oM oX φ x :=
  Iff.rfl

/-- A manifold is a sum of `M` with `N + 1` copies of the reversed projective plane exactly when
it is orientation-preservingly diffeomorphic to the oriented connected sum of a compact Hausdorff
nonempty sum with `N` copies and the reversed projective plane. -/
theorem isReversedProjectiveSum_succ_iff {N : ℕ} :
    IsReversedProjectiveSum oM oX (N + 1) ↔
      ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (_ : CompactSpace Y) (_ : Nonempty Y)
        (_ : ChartedSpace (EuclideanSpace ℂ (Fin 2)) Y)
        (_ : IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ Y)
        (oY : Manifold.Orientation 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) Y (Fin 4)),
        IsReversedProjectiveSum oM oY N ∧
          ∃ φ : X ≃ₘ^∞⟮𝓘(ℝ, EuclideanSpace ℂ (Fin 2)), 𝓘(ℝ, EuclideanSpace ℂ (Fin 2))⟯
              OrientedConnectedSum oY (-ProjectivePlane.orientation),
            ∀ x, Manifold.Orientation.IsOrientationPreservingAt oX
              (OrientedConnectedSum.orientation oY (-ProjectivePlane.orientation)) φ x :=
  Iff.rfl

/-- If the compact Hausdorff nonempty oriented manifold `Y` is a sum of `M` with `N` copies of
the reversed projective plane, and `X` is orientation-preservingly diffeomorphic to the oriented
connected sum of `Y` and the reversed projective plane, then `X` is a sum of `M` with `N + 1`
copies. -/
theorem IsReversedProjectiveSum.succ {Y : Type} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [Nonempty Y] [ChartedSpace (EuclideanSpace ℂ (Fin 2)) Y]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ Y]
    {oY : Manifold.Orientation 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) Y (Fin 4)} {N : ℕ}
    (h : IsReversedProjectiveSum oM oY N)
    (φ : X ≃ₘ^∞⟮𝓘(ℝ, EuclideanSpace ℂ (Fin 2)), 𝓘(ℝ, EuclideanSpace ℂ (Fin 2))⟯
      OrientedConnectedSum oY (-ProjectivePlane.orientation))
    (hφ : ∀ x, Manifold.Orientation.IsOrientationPreservingAt oX
      (OrientedConnectedSum.orientation oY (-ProjectivePlane.orientation)) φ x) :
    IsReversedProjectiveSum oM oX (N + 1) :=
  ⟨Y, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, oY, h, φ, hφ⟩

/-- Every oriented manifold charted on `EuclideanSpace ℂ (Fin 2)` is a sum of itself with no copy
of the reversed projective plane, by the identity. -/
theorem isReversedProjectiveSum_refl : IsReversedProjectiveSum oX oX 0 :=
  ⟨Diffeomorph.refl _ _ _, Manifold.Orientation.isOrientationPreservingAt_id oX⟩

/-- **The Euler characteristic of `M # N ℙ²‾`.** If `M` has finite CW type and `X` is a sum of
`M` with `N` copies of the reversed projective plane, then `χ(X) = χ(M) + N`. The finite CW type
of `X` enters as an instance argument; for compact `X`, `TauCeti.FiniteCWType.of_isManifold`
provides it. -/
theorem IsReversedProjectiveSum.eulerChar_eq [FiniteCWType M] :
    ∀ {N : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin 2)) X]
      [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ X]
      {oX : Manifold.Orientation 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) X (Fin 4)} [FiniteCWType X],
      IsReversedProjectiveSum oM oX N → eulerChar X = eulerChar M + N
  | 0, _, _, _, _, _, _, ⟨φ, _⟩ => by
    rw [φ.symm.toHomeomorph.eulerChar_eq, Nat.cast_zero, add_zero]
  | N + 1, _, _, _, _, _, _, ⟨Y, _, _, _, _, _, _, oY, hY, φ, _⟩ => by
    have := FiniteCWType.of_isManifold Y 𝓘(ℝ, EuclideanSpace ℂ (Fin 2))
    have := FiniteCWType.of_isManifold (OrientedConnectedSum oY (-ProjectivePlane.orientation))
      𝓘(ℝ, EuclideanSpace ℂ (Fin 2))
    rw [φ.toHomeomorph.eulerChar_eq, ConnectedSum.eulerChar_orientedConnectedSum,
      IsReversedProjectiveSum.eulerChar_eq hY, ProjectivePlane.eulerChar_eq,
      finrank_real_of_complex, finrank_euclideanSpace_fin]
    push_cast
    ring

end SymplecticGeometry

end
