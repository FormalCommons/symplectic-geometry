/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.Clutching
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FreeLoop.Basic

/-!
# The first Chern number from unit sections with transitions `ζ ^ k`

Let `L` be a complex line bundle over a compact surface `M` whose fibres are complex inner product
spaces, and `P = TauCeti.OrthonormalFrameBundle.Fiber ℂ F L ℂ` its principal `Circle`-bundle of
unitary frames, so that a section of `P` is a unit section of `L`. Let `φ i`, for `i` in a finite
type `ι`, be coordinate discs with pairwise disjoint closed discs. Suppose that sections `σ i` of
`P`, continuous on the closed discs, and a section `σout`, continuous on the complement of the open
discs, are related on the `i`-th boundary circle by `σout = σ i • ζ ^ k i`, for integers `k i`.
Then the first Chern number of `L` is `∑ i, k i`
(`SymplecticGeometry.Bundle.chernNumber_eq_sum_of_boundaryCircle_eq_zpow_smul`).

This is the disc clutching formula `SymplecticGeometry.Bundle.chernNumber_eq_sum_degree_clutching`
for the frames `SymplecticGeometry.Bundle.unitFrame` of the sections: the normalized determinant
of their transition is the quotient of the two sections in `Circle`
(`SymplecticGeometry.Bundle.normalizedDet_clutchingTransition_unitFrame`), here `ζ ↦ ζ ^ k i`,
whose degree is `k i` (Tau Ceti's `ContinuousMap.circleDegree_zpow`).

It is enough that the relation holds on a collar `ρ < ‖z‖ < 1` inside each disc, read as
`σout (φ i z) = σ i (φ i z) • (φ i).phase (φ i z) ^ k i` with the angular coordinate
`SymplecticGeometry.CoordinateDisc.phase`, which is `z / ‖z‖` at `φ i z` for `z ≠ 0`, when
`σout` is continuous on the complement of the images of the closed discs of radius `ρ`: the
quotient of the two sections is continuous, so by continuity along the rays
(`SymplecticGeometry.CoordinateDisc.apply_boundaryCircle_eq_of_continuousOn`) the relation holds
on the boundary circles (`SymplecticGeometry.Bundle.boundaryCircle_eq_zpow_smul_of_collar`,
`SymplecticGeometry.Bundle.chernNumber_eq_sum_of_collar_eq_zpow_smul`).

## Main results

* `SymplecticGeometry.Bundle.chernNumber_eq_sum_of_boundaryCircle_eq_zpow_smul`: the first Chern
  number is the sum of the exponents of the transitions on the boundary circles.
* `SymplecticGeometry.Bundle.chernNumber_eq_sum_of_collar_eq_zpow_smul`: the same, for
  transitions `(z / ‖z‖) ^ k i` on collars of the boundary circles.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7
  (the first Chern number of a bundle over a surface from the transitions of trivializations
  over discs and over their complement).
-/

public section

noncomputable section

open Bundle Complex Function Module MulOpposite Set TauCeti TauCeti.OrthonormalFrameBundle
  TauCeti.PrincipalBundle

namespace SymplecticGeometry

namespace Bundle

variable {M : Type} [TopologicalSpace M] [T2Space M] {EM : Type} [NormedAddCommGroup EM]
  [NormedSpace ℝ EM] [FiniteDimensional ℝ EM] [ChartedSpace EM M]
  {o : HomologicalOrientation M EM 2} {ι : Type*} {φ : ι → CoordinateDisc o}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

section Collar

variable {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E]
  [ContinuousFiberNorm F E] [Fact (finrank ℂ F = 1)]

/-- **Transitions on a collar extend to the boundary circle.** Let `φ` be a coordinate disc,
`ρ < 1`, and `σ`, `σout` sections of the circle bundle of unitary frames of a Hermitian line
bundle, continuous on the images under `φ` of the half-open annulus `ρ < ‖z‖ ≤ 1`. If
`σout (φ z) = σ (φ z) • φ.phase (φ z) ^ k` on the open annulus `ρ < ‖z‖ < 1`, where the
angular coordinate `φ.phase (φ z)` is `z / ‖z‖` for `z ≠ 0`, then `σout = σ • ζ ^ k`
at each point `ζ` of the boundary circle. -/
theorem boundaryCircle_eq_zpow_smul_of_collar {φ : CoordinateDisc o} {ρ : ℝ}
    (hρ : ρ < 1) {σ σout : ∀ x, Fiber ℂ F E ℂ x}
    (hσ : ContinuousOn (fun x ↦ TotalSpace.mk' Circle x (σ x))
      (φ '' {z | ρ < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ ≤ 1}))
    (hσout : ContinuousOn (fun x ↦ TotalSpace.mk' Circle x (σout x))
      (φ '' {z | ρ < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ ≤ 1}))
    (k : ℤ) (hk : ∀ z : CoordinateDisc.ball, ρ < ‖(z : ℂ)‖ → ‖(z : ℂ)‖ < 1 →
      σout (φ z) = op (φ.phase (φ z) ^ k) • σ (φ z)) (ζ : Circle) :
    σout (φ.boundaryCircle ζ) = op (ζ ^ k) • σ (φ.boundaryCircle ζ) := by
  refine (division_eq_iff.1 (φ.apply_boundaryCircle_eq_of_continuousOn hρ (hσ.division hσout)
    fun z hz hz1 hζ ↦ ?_)).symm
  rw [division_eq_iff, hk z hz hz1, hζ]

end Collar

section ChernNumber

variable {E : M → Type} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E]
  [ContinuousFiberNorm F E] [Fact (finrank ℂ F = 1)]
  {σ : ι → ∀ x, Fiber ℂ F E ℂ x} {σout : ∀ x, Fiber ℂ F E ℂ x}

/-- **The first Chern number of a Hermitian line bundle from unit sections with transitions
`ζ ^ k`.** Let `φ i`, for `i` in a finite type `ι`, be coordinate discs of a compact surface with
pairwise disjoint closed discs, `σ i` sections of the circle bundle of unitary frames of a
Hermitian line bundle `E`, continuous on the closed disc of `φ i`, and `σout` a section continuous
on the complement of the open discs. If `σout = σ i • ζ ^ k i` at each point `ζ` of the `i`-th
boundary circle, then the first Chern number of `E` is `∑ i, k i`. -/
theorem chernNumber_eq_sum_of_boundaryCircle_eq_zpow_smul [Fintype ι] [CompactSpace M]
    [FiniteDimensional ℂ F]
    (hn : finrank ℝ EM = 2) (hφ : Pairwise (Disjoint on fun i ↦ (φ i).disc))
    (hσ : ∀ i, ContinuousOn (fun x ↦ TotalSpace.mk' Circle x (σ i x)) (φ i).disc)
    (hσout : ContinuousOn (fun x ↦ TotalSpace.mk' Circle x (σout x)) (discComplement φ))
    (k : ι → ℤ) (hk : ∀ i (ζ : Circle),
      σout ((φ i).boundaryCircle ζ) = op (ζ ^ k i) • σ i ((φ i).boundaryCircle ζ)) :
    chernNumber o hn F E = ∑ i, k i := by
  have hF : finrank ℂ F = 1 := Fact.out
  let e : F ≃L[ℂ] ℂ := ContinuousLinearEquiv.ofFinrankEq (by simp [hF])
  rw [chernNumber_eq_sum_degree_clutching hφ (Φ := fun i x ↦ unitFrame e (σ i x))
    (Φout := fun x ↦ unitFrame e (σout x)) (fun i ↦ continuous_unitFrame e (hσ i))
    (continuous_unitFrame e hσout) hn]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Circle.degree_toBasedLoop, ← ContinuousMap.circleDegree_zpow (k i)]
  congr 1
  ext ζ
  simp only [ContinuousMap.coe_mk, normalizedDet_clutchingTransition_unitFrame]
  exact congrArg _ (division_eq_iff.2 (hk i ζ).symm)

/-- **The first Chern number from unit sections with transitions `(z / ‖z‖) ^ k` on collars.**
Let `φ i`, for `i` in a finite type `ι`, be coordinate discs of a compact surface with pairwise
disjoint closed discs, `ρ < 1`, `σ i` sections of the circle bundle of unitary frames of a
Hermitian line bundle `E`, continuous on the closed disc of `φ i`, and `σout` a section continuous
on the complement of the images `φ i '' {‖z‖ ≤ ρ}`. If
`σout (φ i z) = σ i (φ i z) • (φ i).phase (φ i z) ^ k i` whenever `ρ < ‖z‖ < 1`, where the
angular coordinate `(φ i).phase (φ i z)` is `z / ‖z‖` for `z ≠ 0`, then the first Chern number of
`E` is `∑ i, k i`. -/
theorem chernNumber_eq_sum_of_collar_eq_zpow_smul [Fintype ι] [CompactSpace M]
    [FiniteDimensional ℂ F] (hn : finrank ℝ EM = 2)
    (hφ : Pairwise (Disjoint on fun i ↦ (φ i).disc)) {ρ : ℝ} (hρ : ρ < 1)
    (hσ : ∀ i, ContinuousOn (fun x ↦ TotalSpace.mk' Circle x (σ i x)) (φ i).disc)
    (hσout : ContinuousOn (fun x ↦ TotalSpace.mk' Circle x (σout x))
      (⋃ i, φ i '' {z | ‖(z : ℂ)‖ ≤ ρ})ᶜ)
    (k : ι → ℤ) (hk : ∀ i (z : CoordinateDisc.ball), ρ < ‖(z : ℂ)‖ → ‖(z : ℂ)‖ < 1 →
      σout (φ i z) = op ((φ i).phase (φ i z) ^ k i) • σ i (φ i z)) :
    chernNumber o hn F E = ∑ i, k i := by
  refine chernNumber_eq_sum_of_boundaryCircle_eq_zpow_smul hn hφ hσ
    (hσout.mono fun x hx ↦ ?_) k fun i ↦ boundaryCircle_eq_zpow_smul_of_collar hρ
      ((hσ i).mono fun _ ⟨z, hz, h⟩ ↦ h ▸ (φ i).apply_mem_disc_iff.2 hz.2) (hσout.mono ?_)
      (k i) (hk i)
  · -- The complement of the open discs misses the images of the discs of radius `ρ`.
    simp only [mem_compl_iff, mem_iUnion, not_exists]
    rintro j ⟨z, hz, rfl⟩
    exact (mem_discComplement_iff φ).1 hx j
      ((φ j).apply_mem_openDisc_iff.2 (hz.trans_lt hρ))
  · -- The half-open annulus of the `i`-th disc misses the images of the discs of radius `ρ`.
    rintro _ ⟨z, hz, rfl⟩
    simp only [mem_compl_iff, mem_iUnion, not_exists]
    rintro j ⟨w, hw : ‖(w : ℂ)‖ ≤ ρ, hwz⟩
    obtain rfl | hij := eq_or_ne j i
    · rw [(φ j).injective hwz] at hw
      exact (lt_irrefl _ (hz.1.trans_le hw)).elim
    · exact (hφ hij).ne_of_mem ((φ j).apply_mem_disc_iff.2 (hw.trans hρ.le))
        ((φ i).apply_mem_disc_iff.2 hz.2) hwz

end ChernNumber

end Bundle

end SymplecticGeometry

end
