/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Geometry.Manifold.ConnectedSum.Oriented
import SymplecticGeometry.Geometry.Manifold.ConnectedSum.Neck
import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.MayerVietoris
import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere
import TauCeti.Geometry.Manifold.Morse.CWModel.Puncture
import TauCeti.Topology.Homotopy.PuncturedStarConvex

/-!
# The Euler characteristic of a connected sum

For compact Hausdorff boundaryless smooth manifolds `M` and `N` of dimension `n`, glued along
open coordinate balls `e₁ : E → M` and `e₂ : E → N`, the connected sum
`TauCeti.ConnectedSum e₁ e₂` has Euler characteristic
`χ(M # N) = χ(M) + χ(N) - 1 - (-1) ^ n`.

## Main results

* `TauCeti.ConnectedSum.finiteCWType_puncture`, `TauCeti.ConnectedSum.eulerChar_puncture`: a
  compact manifold with the centre of a coordinate ball removed has finite CW type, and Euler
  characteristic `χ(M) - (-1) ^ n`.
* `TauCeti.ConnectedSum.eulerChar_connectedSum`: the formula for `TauCeti.ConnectedSum e₁ e₂`.
* `TauCeti.ConnectedSum.eulerChar_orientedConnectedSum`: the formula for Tau Ceti's oriented
  connected sum `TauCeti.OrientedConnectedSum oM oN`.

The finite CW type of the summands and of the connected sum enters as instance arguments; since
`TauCeti.FiniteCWType` is a proposition, any proof will do. For the summands
`TauCeti.FiniteCWType.of_isManifold` provides one, and for the connected sum too when it is a
smooth manifold, as it is when `e₁` and `e₂` are smooth local diffeomorphisms
(`TauCeti.ConnectedSum.isManifold`).

## Proof

The two punctured summands are open subspaces of the connected sum
(`TauCeti.ConnectedSum.isOpenEmbedding_inl`, `TauCeti.ConnectedSum.isOpenEmbedding_inr`) which
cover it. The first is homeomorphic to `M ∖ {e₁ 0}`, of Euler characteristic `χ(M) - (-1) ^ n`
(`TauCeti.ConnectedSum.eulerChar_puncture`, from `Set.Finite.eulerChar_compl_of_isManifold`),
and likewise for the second. They meet in the image of `E ∖ {0}` under `v ↦ e₁ v`
(`TauCeti.ConnectedSum.neckHomeomorph`), which is homotopy equivalent to the unit sphere of `E`
(`TauCeti.complSingletonHomotopyEquivSphere`), of Euler characteristic `1 - (-1) ^ n`
(`TauCeti.eulerChar_sphere_eq_one_sub`). Additivity of the Euler characteristic along an open
cover (`TauCeti.eulerChar_add_eulerChar_inter_of_union_eq_univ`) gives the formula. As in the
proof of `TauCeti.eulerChar_compl_of_finite`, the punctured model space is first carried to a
Euclidean space in the universe of the connected sum.

## References

* [A. Kosinski, *Differential Manifolds*][Kosinski1993], Chapter VI, Section 1.
-/

public section

open Set Function Topology Module EuclideanGeometry Metric
open scoped Manifold ContDiff

universe u v w

namespace TauCeti.ConnectedSum

section Puncture

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type w} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]

include I in
/-- A compact boundaryless manifold with the centre of a coordinate ball removed has finite CW
type. -/
theorem finiteCWType_puncture (e : E → M) : FiniteCWType (puncture e) :=
  have := (Set.finite_singleton (e 0)).finiteCWType_compl_of_isManifold I
  (Homeomorph.setCongr (coe_puncture e) : puncture e ≃ₜ ({e 0}ᶜ : Set M)).finiteCWType

include I in
/-- **The Euler characteristic of a punctured summand.** Removing the centre of a coordinate
ball `e : E → M` from a compact boundaryless manifold `M` lowers its Euler characteristic by
`(-1) ^ dim E`. -/
theorem eulerChar_puncture (e : E → M) [FiniteCWType M] [FiniteCWType (puncture e)] :
    eulerChar (puncture e) = eulerChar M - (-1) ^ finrank ℝ E := by
  have hS := Set.finite_singleton (e 0)
  have := hS.finiteCWType_compl_of_isManifold I
  let h : puncture e ≃ₜ ({e 0}ᶜ : Set M) := Homeomorph.setCongr (coe_puncture e)
  rw [h.eulerChar_eq, hS.eulerChar_compl_of_isManifold I, ncard_singleton, Nat.cast_one,
    mul_one]

end Puncture

section InnerProduct

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type w} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]
  {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  [CompactSpace N]
  {e₁ : E → M} {e₂ : E → N}

include I in
/-- **The Euler characteristic of a connected sum.** Let `M` and `N` be compact Hausdorff smooth
manifolds modelled on a boundaryless real model `I` over a real inner product space `E`, and let
`e₁ : E → M` and `e₂ : E → N` be open embeddings. If `M`, `N` and their connected sum along
`e₁` and `e₂` have finite CW type, then `χ(M # N) = χ(M) + χ(N) - 1 - (-1) ^ dim E`. -/
theorem eulerChar_connectedSum (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂)
    [FiniteCWType M] [FiniteCWType N] [FiniteCWType (ConnectedSum e₁ e₂)] :
    eulerChar (ConnectedSum e₁ e₂) =
      eulerChar M + eulerChar N - 1 - (-1) ^ finrank ℝ E := by
  have : Nonempty M := ⟨e₁ 0⟩
  have : FiniteDimensional ℝ E := FiniteDimensional.of_locallyCompact_manifold M I
  set U := range (inl e₁ e₂)
  set V := range (inr e₁ e₂)
  -- The two punctured summands.
  have := finiteCWType_puncture I e₁
  have := finiteCWType_puncture I e₂
  let eU := (isOpenEmbedding_inl h₁ h₂).isEmbedding.toHomeomorph
  let eV := (isOpenEmbedding_inr h₁ h₂).isEmbedding.toHomeomorph
  have := eU.symm.finiteCWType
  have := eV.symm.finiteCWType
  -- The punctured model space, carried to a Euclidean space in universe `u`.
  let E' := EuclideanSpace ℝ (ULift.{u} (Fin (finrank ℝ E)))
  have hE' : finrank ℝ E' = finrank ℝ E := by simp [E']
  let L : E ≃L[ℝ] E' := ContinuousLinearEquiv.ofFinrankEq hE'.symm
  let eI : (U ∩ V : Set (ConnectedSum e₁ e₂)) ≃ₜ ({0}ᶜ : Set E') :=
    (neckHomeomorph h₁ h₂).symm.trans (L.toHomeomorph.subtype fun v ↦ by simp)
  have := (complSingletonHomotopyEquivSphere (0 : E')).finiteCWType
  have := eI.finiteCWType
  have key := eulerChar_add_eulerChar_inter_of_union_eq_univ
    (isOpenEmbedding_inl h₁ h₂).isOpen_range (isOpenEmbedding_inr h₁ h₂).isOpen_range
    (range_inl_union_range_inr e₁ e₂)
  rw [← eU.eulerChar_eq, ← eV.eulerChar_eq, eI.eulerChar_eq,
    (complSingletonHomotopyEquivSphere (0 : E')).eulerChar_eq, eulerChar_sphere_eq_one_sub, hE',
    eulerChar_puncture I e₁, eulerChar_puncture I e₂] at key
  linear_combination key

end InnerProduct

end TauCeti.ConnectedSum

namespace TauCeti

section Oriented

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  [CompactSpace M] [Nonempty M]
  {N : Type u} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N] [T2Space N]
  [CompactSpace N] [Nonempty N]
  {ι : Type*} [Fintype ι]

/-- **The Euler characteristic of an oriented connected sum.** For compact Hausdorff oriented
smooth manifolds `M` and `N` modelled on a nonzero finite-dimensional real inner product space
`E`, if `M`, `N` and `M # N` have finite CW type, then
`χ(M # N) = χ(M) + χ(N) - 1 - (-1) ^ dim E`. -/
theorem ConnectedSum.eulerChar_orientedConnectedSum (oM : Manifold.Orientation 𝓘(ℝ, E) M ι)
    (oN : Manifold.Orientation 𝓘(ℝ, E) N ι) [FiniteCWType M] [FiniteCWType N]
    [FiniteCWType (OrientedConnectedSum oM oN)] :
    eulerChar (OrientedConnectedSum oM oN) =
      eulerChar M + eulerChar N - 1 - (-1) ^ finrank ℝ E := by
  have h₁ := OrientedConnectedSum.isOpenEmbedding_ballLeft oM oN
  have h₂ := OrientedConnectedSum.isOpenEmbedding_ballRight oM oN
  let := ConnectedSum.chartedSpace (H := E) h₁ h₂
  let φ := (OrientedConnectedSum.diffeomorphConnectedSum oM oN).toHomeomorph
  have := φ.symm.finiteCWType
  rw [φ.eulerChar_eq, ConnectedSum.eulerChar_connectedSum 𝓘(ℝ, E) h₁ h₂]

end Oriented

end TauCeti
