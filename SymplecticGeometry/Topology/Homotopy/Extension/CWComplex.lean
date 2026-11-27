/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import TauCeti.Topology.Homotopy.Extension.Basic
import TauCeti.Topology.Homotopy.Extension.CWComplex

/-!
# The base of a relative CW structure on a whole space

Tau Ceti's `TauCeti.hasHomotopyExtensionProperty_base` says that the base `D` of a relative CW
complex `C` has the homotopy extension property inside the subtype `C`. When `C` is the whole
space, this file reads it in the space itself
(`TauCeti.hasHomotopyExtensionProperty_base_univ`), which is the form in which a relative CW
model `X` over the image of an embedding is usually given.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 0.16.
-/

public section

open Set Topology

namespace TauCeti

/-- **The base of a relative CW structure on a whole space is a cofibration.** If a space `X` is a
CW complex relative to `D`, then `D` has the homotopy extension property in `X`. -/
theorem hasHomotopyExtensionProperty_base_univ {X : Type*} [TopologicalSpace X] [T2Space X]
    {D : Set X} [RelCWComplex (univ : Set X) D] : HasHomotopyExtensionProperty D := by
  have := (hasHomotopyExtensionProperty_base (C := (univ : Set X)) (D := D)).image
    (Homeomorph.Set.univ X)
  convert this using 1
  ext x
  simp

end TauCeti

end
