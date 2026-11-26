/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
public import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization
public import TauCeti.Topology.VectorBundle.Complex.Structure
import SymplecticGeometry.Topology.VectorBundle.Complex.Structure

/-!
# Sections of a real vector bundle with a complex structure

Let `J` be a continuous complex structure on a real vector bundle `V`, so that `J.Fiber` is a
complex vector bundle with the same fibres. A section `s` of `V` along a map `b : M → B` is read
as the section `y ↦ (J.fiberEquiv (b y)).symm (s y)` of `J.Fiber`. At a zero `x` of `s` where `s`
is differentiable:

* `TauCeti.Bundle.ContinuousComplexStructure.mdifferentiableAt_trivializationAt_fiberEquiv_symm`:
  the section of `J.Fiber` is differentiable at `x`, read in the trivialization of `J.Fiber` at
  `b x`;
* `TauCeti.Bundle.ContinuousComplexStructure.sectionLinearization_fiberEquiv_symm`: its
  linearization `TauCeti.sectionLinearization` at `x` is that of `s` followed by
  `(J.fiberEquiv (b x)).symm`.

Near `x`, the reading of the section of `J.Fiber` is that of `s` followed by a family of linear
maps that is only continuous
(`TauCeti.Bundle.ContinuousComplexStructure.eventuallyEq_trivializationAt_fiberEquiv_symm_apply_snd`
in `SymplecticGeometry.Topology.VectorBundle.Complex.Structure`), so the proofs use that `s`
vanishes at `x`, through Tau Ceti's `TauCeti.mdifferentiableAt_of_eventuallyEq_clm_apply` and
`TauCeti.mvfderiv_eq_comp_of_eventuallyEq_clm_apply`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (complex vector bundles as real bundles with a complex structure).
-/

public section

open Bundle Module TauCeti
open scoped Manifold VectorBundle.ComplexToReal

namespace TauCeti.Bundle.ContinuousComplexStructure

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)]
  [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousSMul ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  (J : ContinuousComplexStructure F V)
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ F = 2 * finrank ℂ G)]
  {b : M → B} {s : ∀ y, V (b y)} {x : M}

/-- At a zero `x` of a section `s` of `V` along `b`, differentiable at `x`, the section
`y ↦ (J.fiberEquiv (b y)).symm (s y)` of `J.Fiber` is differentiable at `x`, read in the
trivialization of `J.Fiber` at `b x`. -/
theorem mdifferentiableAt_trivializationAt_fiberEquiv_symm (hb : ContinuousAt b x)
    (hs : MDifferentiableAt IM 𝓘(ℝ, F) (fun y ↦ (trivializationAt F V (b x) ⟨b y, s y⟩).2) x)
    (hx : s x = 0) :
    MDifferentiableAt IM 𝓘(ℝ, G)
      (fun y ↦ (trivializationAt G J.Fiber (b x) ⟨b y, (J.fiberEquiv (b y)).symm (s y)⟩).2) x :=
  mdifferentiableAt_of_eventuallyEq_clm_apply
    (J.eventuallyEq_trivializationAt_fiberEquiv_symm_apply_snd G hb (s := s))
    (J.continuousAt_modelEquiv_symm_comp_inverse_complexLinearPart G hb) hs (by
      rw [hx]
      exact congrArg Prod.snd ((trivializationAt F V (b x)).zeroSection ℝ
        (mem_baseSet_trivializationAt F V (b x))))

/-- At a zero `x` of a section `s` of `V` along `b`, differentiable at `x`, the linearization of
the section `y ↦ (J.fiberEquiv (b y)).symm (s y)` of `J.Fiber` is the linearization of `s`
followed by `(J.fiberEquiv (b x)).symm`. -/
theorem sectionLinearization_fiberEquiv_symm (hb : ContinuousAt b x)
    (hs : MDifferentiableAt IM 𝓘(ℝ, F) (fun y ↦ (trivializationAt F V (b x) ⟨b y, s y⟩).2) x)
    (hx : s x = 0) :
    sectionLinearization (F := G) IM b (fun y ↦ (J.fiberEquiv (b y)).symm (s y)) x =
      ((J.fiberEquiv (b x)).symm : V (b x) →L[ℝ] J.Fiber (b x)).comp
        (sectionLinearization (F := F) IM b s x) := by
  set e := trivializationAt G J.Fiber (b x)
  set eV := trivializationAt F V (b x)
  have hzV : b x ∈ eV.baseSet := mem_baseSet_trivializationAt F V (b x)
  have hze : b x ∈ e.baseSet := mem_baseSet_trivializationAt G J.Fiber (b x)
  ext v
  rw [sectionLinearization_def, sectionLinearization_def,
    mvfderiv_eq_comp_of_eventuallyEq_clm_apply
      (J.eventuallyEq_trivializationAt_fiberEquiv_symm_apply_snd G hb (s := s))
      (J.continuousAt_modelEquiv_symm_comp_inverse_complexLinearPart G hb) hs
      (by rw [hx]; exact congrArg Prod.snd (eV.zeroSection ℝ hzV))]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [Trivialization.symmL_apply _ hze,
    ← e.symm_apply_apply_mk hze ((J.fiberEquiv (b x)).symm _),
    J.trivializationAt_fiberEquiv_symm_apply_snd G (J.mem_unitSet_self (b x)),
    Trivialization.symmL_apply _ hzV, eV.apply_mk_symm hzV]

end TauCeti.Bundle.ContinuousComplexStructure

end
