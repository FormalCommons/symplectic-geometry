/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Basic
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.OfBundle
public import TauCeti.Topology.VectorBundle.FiniteRank.Monoidal
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Naturality
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Tensor
import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Tensor

/-!
# Chern classes of complex finite-rank cores

A complex finite-rank core `A : TauCeti.FiniteRankBundleCore ℂ B` has the Chern classes
`chernClass (Fin A.rank → ℂ) A.core.Fiber k` of its bundle. This file computes them for the cores
that come from bundles, for the trivial cores, and, in degree two, for the tensor product of two
cores of rank one, over a compact base.

## Main results

* `TauCeti.FiniteRankBundleCore.chernClass_ofBundleOfFinrankEq`: the core of a bundle `E` has the
  Chern classes of `E`;
* `TauCeti.FiniteRankBundleCore.chernClass_trivial`: the Chern classes of a trivial core vanish in
  positive degree;
* `TauCeti.FiniteRankBundleCore.chernClass_one_tensorObj`: over a compact normal base,
  `c₁(A ⊗ D) = c₁(A) + c₁(D)` for cores of rank one, from
  `SymplecticGeometry.Bundle.chernClass_one_tensorProduct` through the fibrewise identification
  `TauCeti.FiniteRankBundleCore.tensorFiberEquiv`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press (1974), §14.
-/

public section

open Bundle CategoryTheory MonoidalCategory Module SymplecticGeometry.Bundle
open scoped TensorProduct TauCeti.ModuleTopology

namespace TauCeti.FiniteRankBundleCore

variable {B : Type} [TopologicalSpace B] [CompactSpace B]

/-- The core `ofBundleOfFinrankEq ℂ G E h` of a complex vector bundle `E` has the Chern classes
of `E`. -/
@[simp]
theorem chernClass_ofBundleOfFinrankEq
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
    (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, Module ℝ (E b)]
    [∀ b, IsScalarTower ℝ ℂ (E b)] [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace G E)] [FiberBundle G E] [VectorBundle ℂ G E]
    {n : ℕ} (h : finrank ℂ G = n) (k : ℕ) :
    chernClass (Fin (ofBundleOfFinrankEq ℂ G E h).rank → ℂ)
        (ofBundleOfFinrankEq ℂ G E h).core.Fiber k = chernClass G E k :=
  chernClass_congr _ ((ofBundleOfFinrankEqHomeomorph ℂ G E h).continuous.congr fun p ↦
    ofBundleOfFinrankEqHomeomorph_apply ℂ G E h p) k

/-- The Chern classes of a trivial core vanish in positive degree. -/
@[simp]
theorem chernClass_trivial (n : ℕ) {k : ℕ} (hk : k ≠ 0) :
    chernClass (Fin (trivial ℂ B n).rank → ℂ) (trivial ℂ B n).core.Fiber k = 0 := by
  rw [← SymplecticGeometry.Bundle.chernClass_trivial B (Fin n → ℂ) hk]
  exact chernClass_congr (E := (trivial ℂ B n).core.Fiber) (E' := Bundle.Trivial B (Fin n → ℂ))
    (fun _ ↦ ContinuousLinearEquiv.refl ℂ (Fin n → ℂ))
    ((Bundle.Trivial.isInducing_toProd B (Fin n → ℂ)).continuous_iff.2
      ((trivial ℂ B n).core.continuous_proj.prodMk continuous_trivial_snd)) k

/-- **The first Chern class of a tensor product of line cores.** Over a compact normal base, the
first Chern class of the tensor product `A ⊗ D` of two complex cores of rank one is
`c₁(A) + c₁(D)`. -/
theorem chernClass_one_tensorObj [NormalSpace B] {A D : FiniteRankBundleCore ℂ B}
    (hA : A.rank = 1) (hD : D.rank = 1) :
    chernClass (Fin (A ⊗ D).rank → ℂ) (A ⊗ D).core.Fiber 1 =
      chernClass (Fin A.rank → ℂ) A.core.Fiber 1 +
        chernClass (Fin D.rank → ℂ) D.core.Fiber 1 := by
  rw [← chernClass_one_tensorProduct (by simp [hA]) (by simp [hD])]
  exact chernClass_congr (tensorFiberEquiv A D) (continuous_tensorFiberEquiv A D) 1

end TauCeti.FiniteRankBundleCore

end
