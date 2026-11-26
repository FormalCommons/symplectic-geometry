/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Smul

/-!
# Maps out of the total space of a real vector bundle, up to homotopy

The total space of a real vector bundle `E → B` deformation retracts onto its zero section
(Tau Ceti's `TauCeti.VectorBundle.totalSpaceHomotopyEquiv`). So a continuous map `g` out of the
total space is homotopic to its restriction to the zero section composed with the projection:
if `g ∘ zeroSection = f`, then `g` is homotopic to `f ∘ π`
(`TauCeti.VectorBundle.homotopic_comp_zeroSection_proj`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.D (the total space of a vector bundle deformation retracts onto its zero section).
-/

public section

open Bundle

namespace TauCeti.VectorBundle

variable {B F Y : Type*} [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  [TopologicalSpace Y]

/-- A continuous map `g` out of the total space of a real vector bundle that restricts to `f` on
the zero section is homotopic to `f ∘ π`. -/
theorem homotopic_comp_zeroSection_proj (g : C(TotalSpace F E, Y)) {f : C(B, Y)}
    (hg : ∀ b, g (zeroSection F E b) = f b) :
    g.Homotopic (f.comp ⟨π F E, FiberBundle.continuous_proj F E⟩) := by
  convert (ContinuousMap.Homotopic.refl g).comp
    (totalSpaceHomotopyEquiv F E).left_inv.symm using 1
  · simp
  · ext v; simp [hg]

end TauCeti.VectorBundle
