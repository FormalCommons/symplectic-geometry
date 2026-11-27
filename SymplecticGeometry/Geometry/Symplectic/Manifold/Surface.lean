/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Orientation.PositiveForm
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Symplectic.Manifold.Surface
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# Area forms positive for an orientation of a surface

Let `M` be a surface with an orientation `o`. A two-form on `M` that is positive for `o` at a
point `x` does not vanish at `x`, and on a two-dimensional tangent space an alternating form is
nondegenerate exactly when it is nonzero
(`LinearMap.BilinForm.IsAlt.nondegenerate_iff_ne_zero_of_finrank_eq_two`). So its bilinear form at
`x` is nondegenerate (`TauCeti.Manifold.Orientation.IsPositiveAt.nondegenerate_bilinFormAt`, whose
proof is the pointwise step of Tau Ceti's
`TauCeti.SmoothTwoForm.isNondegenerate_iff_forall_ne_zero_of_finrank_eq_two`), and
a two-form positive for `o` everywhere is symplectic
(`TauCeti.Manifold.Orientation.IsPositive.isSymplectic`), closedness being automatic in dimension
two (`TauCeti.SmoothTwoForm.isSymplectic_iff_forall_ne_zero_of_finrank_eq_two`).

Positivity is kept along the segment `ω₀ + s (σ - ω₀)`, `s ∈ [0, 1]`, between two forms positive
for `o` (`TauCeti.Manifold.Orientation.IsPositiveAt.add_smul_sub`). Hence every form of that
segment is nondegenerate at each point where `ω₀` and `σ` are positive
(`TauCeti.SmoothTwoForm.nondegenerate_bilinFormAt_add_smul_sub`), and symplectic when they are
positive everywhere (`TauCeti.SmoothTwoForm.isSymplectic_add_smul_sub`). This is the input of
Moser's argument for area forms along that segment.

## Main results

* `TauCeti.Manifold.Orientation.IsPositiveAt.nondegenerate_bilinFormAt`: a two-form positive for
  an orientation of a surface at `x` is nondegenerate at `x`.
* `TauCeti.Manifold.Orientation.IsPositive.isSymplectic`: a two-form positive for an orientation
  of a surface is symplectic.
* `TauCeti.SmoothTwoForm.nondegenerate_bilinFormAt_add_smul_sub` and
  `TauCeti.SmoothTwoForm.isSymplectic_add_smul_sub`: the same for the forms of the segment between
  two forms positive for the orientation.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 1.3.
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.2.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {o : Manifold.Orientation I M (Fin 2)}

namespace Manifold.Orientation

variable {σ : SmoothTwoForm I M}

/-- On a surface with an orientation `o`, a two-form positive for `o` at `x` is nondegenerate at
`x`. -/
theorem IsPositiveAt.nondegenerate_bilinFormAt {x : M} (h : o.IsPositiveAt σ.val x) :
    (σ.bilinFormAt x).Nondegenerate := by
  -- `TangentSpace I x` is the model space `E` by definition
  have hx : Module.finrank ℝ (TangentSpace I x) = 2 := by simpa using o.card_eq.symm
  rw [(SmoothForm.isAlt_bilinFormAt σ x).nondegenerate_iff_ne_zero_of_finrank_eq_two hx, ne_eq,
    SmoothForm.bilinFormAt_eq_zero_iff]
  exact h.ne_zero

/-- On a surface with an orientation `o`, a two-form positive for `o` is symplectic. -/
theorem IsPositive.isSymplectic (h : o.IsPositive σ.val) : σ.IsSymplectic :=
  (SmoothTwoForm.isSymplectic_iff_forall_ne_zero_of_finrank_eq_two
    (by simpa using o.card_eq.symm)).2 h.ne_zero

end Manifold.Orientation

namespace SmoothTwoForm

variable {ω₀ σ : SmoothTwoForm I M} {s : ℝ}

/-- On a surface with an orientation `o`, if the two-forms `ω₀` and `σ` are positive for `o` at
`x`, then every form `ω₀ + s (σ - ω₀)`, `s ∈ [0, 1]`, of the segment between them is
nondegenerate at `x`. -/
theorem nondegenerate_bilinFormAt_add_smul_sub {x : M} (hω : o.IsPositiveAt ω₀.val x)
    (hσ : o.IsPositiveAt σ.val x) (hs : s ∈ Set.Icc 0 1) :
    ((ω₀ + s • (σ - ω₀)).bilinFormAt x).Nondegenerate :=
  Manifold.Orientation.IsPositiveAt.nondegenerate_bilinFormAt (o := o) <| by
    simpa using hω.add_smul_sub hσ hs

/-- On a surface with an orientation `o`, if the two-forms `ω₀` and `σ` are positive for `o`, then
every form `ω₀ + s (σ - ω₀)`, `s ∈ [0, 1]`, of the segment between them is symplectic. -/
theorem isSymplectic_add_smul_sub (hω : o.IsPositive ω₀.val) (hσ : o.IsPositive σ.val)
    (hs : s ∈ Set.Icc 0 1) : (ω₀ + s • (σ - ω₀)).IsSymplectic :=
  Manifold.Orientation.IsPositive.isSymplectic (o := o) <| by
    simpa using hω.add_smul_sub hσ hs

end SmoothTwoForm

end TauCeti

end
