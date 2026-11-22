/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Complex
public import SymplecticGeometry.Topology.VectorBundle.Orientation.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LocalIndex
public import TauCeti.Topology.VectorBundle.Orientation.SectionIndex.Degree

/-!
# Local indices of sections of the trivial plane bundle

A section of the trivial bundle `M × ℂ` over a surface `M` is a map `g : M → ℂ`. Orient the bundle
by `Complex.orientation` on every fibre. Then the local index of the section at an isolated zero
`z` (`TauCeti.VectorBundleOrientation.sectionIndex`) is the local index of the map `g` at `z`
(`TauCeti.HomologicalOrientation.localIndex`), for the canonical orientation of `ℂ` as target
(`TauCeti.VectorBundleOrientation.sectionIndex_trivial_eq_localIndex`). The two indices only see
the local orientation of `M` at `z`, so they may be taken for two homological orientations of `M`,
possibly with different models, that agree at `z`.

Both indices are the factor by which `g`, on a neighbourhood isolating `z`, multiplies the local
orientation at `z`: for the section index by
`TauCeti.VectorBundleOrientation.localHomologyMap_eq_sectionIndex_smul`, in the identity
trivialization of `M × ℂ`, which reads the orientation of every fibre as itself
(`Bundle.Trivial.mapOrientation_trivialization`), and for the local index by
`TauCeti.HomologicalOrientation.localIndex_eq_iff`. The local orientation of `ℂ` at the origin
selected by `Complex.orientation` is that of its canonical orientation
(`TauCeti.complexHomologicalOrientation_apply_zero`). The computation in the identity
trivialization follows the step of the proof of
`TauCeti.VectorBundleOrientation.sum_sectionIndex_eq_boundaryDegree` that reads indices in the
trivial bundle.

## Main results

* `TauCeti.VectorBundleOrientation.sectionIndex_trivial_eq_localIndex`: the local index of a
  section of `M × ℂ` is the local index of the map it defines.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 (the Euler class and indices of sections at isolated zeros).
-/

public section

noncomputable section

open Bundle Module Set

namespace TauCeti.VectorBundleOrientation

variable {M E E' : Type} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [ChartedSpace E' M]

/-- **Local indices of sections of `M × ℂ`.** Let `g : M → ℂ` be continuous, read as a section of
the trivial bundle `M × ℂ` oriented by `Complex.orientation`, and let `z` be a zero of `g` with an
open neighbourhood `U` containing no other zero. Let `oM` and `oM'` be homological orientations of
the surface `M` that agree at `z`. Then the local index of the section at `z`, for `oM`, is the
local index of the map `g` at `z`, for `oM'` and the canonical orientation of `ℂ`. -/
theorem sectionIndex_trivial_eq_localIndex (oM : HomologicalOrientation M E 2)
    (oM' : HomologicalOrientation M E' 2) {z : M} (hoz : oM z = oM' z) (g : C(M, ℂ))
    (hs : Continuous fun x ↦ TotalSpace.mk' ℂ (E := Bundle.Trivial M ℂ) x (g x)) (hgz : g z = 0)
    {U : Set M} (hU : IsOpen U) (hzU : z ∈ U) (hUz : ∀ x ∈ U, g x = 0 → x = z) :
    (trivial M Complex.orientation).sectionIndex Complex.finrank_real_complex oM hs z =
      oM'.localIndex (complexHomologicalOrientation ℂ) g z := by
  have h := localHomologyMap_eq_sectionIndex_smul (trivial M Complex.orientation)
    Complex.finrank_real_complex oM hs (Bundle.Trivial.trivialization M ℂ) hU hzU hUz
    (fun _ _ ↦ by simp) (ω := Complex.orientation) (fun _ _ ↦ by simp) (g.restrict U)
    (fun x ↦ by simp) (fun x hx ↦ Subtype.ext (hUz x x.property (by simpa using hx)))
  rw [hoz, ← complexHomologicalOrientation_apply_zero] at h
  exact (((oM'.localIndex_eq_iff (complexHomologicalOrientation ℂ) Complex.finrank_real_complex g
    hgz hU hzU hUz).2 h)).symm

end TauCeti.VectorBundleOrientation
