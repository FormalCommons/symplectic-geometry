/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Topology.ComplexProjectiveSpace.Projectivization
public import TauCeti.Topology.ComplexProjectiveSpace.Sphere2

/-!
# The complex projective line as the topological two-sphere

This file gives a homeomorphism `Projectivization.homeomorphTopCatSphere` from the complex
projective line `ℙ ℂ (Fin 2 → ℂ)` to `TopCat.sphere 2`, the two-sphere on which Tau Ceti computes
singular cohomology. It is the composite of three homeomorphisms of Tau Ceti: the one between the
projectivization and the sphere-quotient model `TauCeti.ComplexProjectiveSpace 1`, the one induced
by the Hopf map from that model to the unit sphere of `ℝ³`
(`TauCeti.ComplexProjectiveSpace.homeomorphSphere2`), and the one from that unit sphere to
`TopCat.sphere 2` (`TauCeti.sphereHomeomorphTopCatSphere`).
-/

public section

open scoped LinearAlgebra.Projectivization

namespace Projectivization

open TauCeti

universe u

/-- A homeomorphism from the complex projective line `ℙ ℂ (Fin 2 → ℂ)` to the two-sphere
`TopCat.sphere 2`, in any universe. -/
noncomputable def homeomorphTopCatSphere : ℙ ℂ (Fin 2 → ℂ) ≃ₜ TopCat.sphere.{u} 2 :=
  (ComplexProjectiveSpace.homeomorphProjectivization 1).symm.trans
    (ComplexProjectiveSpace.homeomorphSphere2.trans (sphereHomeomorphTopCatSphere (by simp)))

theorem homeomorphTopCatSphere_def :
    homeomorphTopCatSphere.{u} = (ComplexProjectiveSpace.homeomorphProjectivization 1).symm.trans
      (ComplexProjectiveSpace.homeomorphSphere2.trans (sphereHomeomorphTopCatSphere (by simp))) :=
  (rfl)

end Projectivization

end
