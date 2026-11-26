/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Generic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.Geometry.Manifold.VectorBundle.Section.SmoothZero
public import SymplecticGeometry.Topology.VectorBundle.ZeroSet

/-!
# Sections with closed discrete zero sets

Over a boundaryless manifold `M` modelled on a finite-dimensional real space `X`, consider a
smooth real vector bundle `V` whose rank equals `dim X`. A smooth section whose intrinsic
linearization is surjective at each zero has Fredholm index zero there, so its zero set is a
`0`-dimensional manifold (Tau Ceti's `TauCeti.exists_isManifold_sectionZero_of_contMDiff`):
a discrete subset of `M`. This holds as well over `ℂ`, and for `C^n` sections with `n ≠ 0`. The
zero set is also closed, as the zero set of any continuous section is
(`VectorBundle.isClosed_setOfPred_eq_zero`). No compactness of `M` is needed, unlike in Tau Ceti's
`TauCeti.finite_sectionZero_of_contMDiff`. The proofs of closedness and of discreteness adapt
the corresponding steps in the proof of that lemma.

Together with Tau Ceti's parametric transversality for affine families
(`ContMDiffSection.mem_residual_setOf_isRegular_affineFamily`), this shows that a finite family
of smooth sections spanning every fibre has a linear combination whose zero set is closed and
discrete.

## Main results

* `ContMDiffSection.isClosed_setOfPred_eq_zero`: the zero set of a section is closed.
* `ContMDiffSection.isDiscrete_setOfPred_eq_zero_of_surjective`: in rank equal to the dimension,
  the zero set of a section with surjective linearization at its zeros is discrete.
* `ContMDiffSection.mem_residual_setOfPred_isDiscrete_zero_affineFamily`: for a residual set of
  parameters, the affine perturbation of a section by a spanning family has a discrete zero set.
* `ContMDiffSection.exists_mem_span_isClosed_isDiscrete_zero`: a spanning family has a linear
  combination whose zero set is closed and discrete.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 3.
* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix A.3.
-/

public section

open Bundle Function Module Set
open scoped Manifold ContDiff Topology

namespace ContMDiffSection

section Closed

variable {𝕜 EM HM M F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] {n : ℕ∞ω}

/-- The zero set of a `C^n` section of a vector bundle is closed. -/
theorem isClosed_setOfPred_eq_zero (t : ContMDiffSection IM F n V) : IsClosed {x | t x = 0} :=
  VectorBundle.isClosed_setOfPred_eq_zero 𝕜 (b := id) t.contMDiff.continuous

end Closed

section Discrete

variable {𝕜 X M F : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [FiniteDimensional 𝕜 X] [TopologicalSpace M] [ChartedSpace X M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] {n : ℕ∞ω} [IsManifold 𝓘(𝕜, X) n M]
  [ContMDiffVectorBundle n F V 𝓘(𝕜, X)]

/-- Over a boundaryless manifold modelled on `X`, the zero set of a `C^n` section, `n ≠ 0`, of a
bundle of rank `dim X` is discrete if the intrinsic linearization of the section is surjective at
each zero. -/
theorem isDiscrete_setOfPred_eq_zero_of_surjective (hn : n ≠ 0) (hdim : finrank 𝕜 X = finrank 𝕜 F)
    (t : ContMDiffSection 𝓘(𝕜, X) F n V)
    (ht : ∀ x, t x = 0 → Surjective (TauCeti.sectionLinearization (F := F) 𝓘(𝕜, X) id t x)) :
    IsDiscrete {x | t x = 0} := by
  have := FiniteDimensional.completeSpace 𝕜 X
  have := FiniteDimensional.completeSpace 𝕜 F
  have hFred (x : M) (hx : t x = 0) :
      ContinuousLinearMap.IsFredholm (TauCeti.sectionLinearization (F := F) 𝓘(𝕜, X) id t x) := by
    have hc := (contMDiffAt_totalSpace_iff.mp (t.contMDiff x)).2
    exact (TauCeti.isFredholm_sectionLinearization_iff continuousAt_id
      (mem_baseSet_trivializationAt F V x) (hc.mdifferentiableAt hn) hx).mpr
        (ContinuousLinearMap.isFredholm_of_finiteDimensional _)
  obtain ⟨cs, -, -, -⟩ := TauCeti.exists_isManifold_sectionZero_of_contMDiff (n := 0)
    (I := 𝓘(𝕜, X)) hn (fun x _ ↦ t.contMDiff x) hFred ht fun x _ ↦ by
      rw [TauCeti.index_sectionLinearization_of_finiteDimensional, hdim, sub_self, Nat.cast_zero]
  let := cs
  exact isDiscrete_iff_discreteTopology.mpr (ChartedSpace.discreteTopology (Fin 0 → 𝕜) _)

end Discrete

section AffineFamily

variable {X M F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [TopologicalSpace M] [ChartedSpace X M] [IsManifold 𝓘(ℝ, X) ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, X)]
  [SecondCountableTopology M] {ι : Type*}

/-- Over a second-countable boundaryless manifold modelled on `X`, let `V` be a bundle of rank
`dim X` and `s` a finite family of smooth sections spanning every fibre. For a residual set of
parameters `a`, the section `s₀ + ∑ i, a i • s i` has a discrete zero set. -/
theorem mem_residual_setOfPred_isDiscrete_zero_affineFamily [Fintype ι]
    (hdim : finrank ℝ X = finrank ℝ F)
    (s₀ : ContMDiffSection 𝓘(ℝ, X) F ∞ V) (s : ι → ContMDiffSection 𝓘(ℝ, X) F ∞ V)
    (hspan : ∀ x, Submodule.span ℝ (range fun i ↦ s i x) = ⊤) :
    {a | IsDiscrete {x | affineFamily s₀ s a x = 0}} ∈ residual (ι → ℝ) := by
  filter_upwards [mem_residual_setOf_isRegular_affineFamily s₀ s hspan] with a ha
  exact isDiscrete_setOfPred_eq_zero_of_surjective (by simp) hdim _
    (TauCeti.isRegularSectionParameter_iff.mp ha)

/-- Over a second-countable boundaryless manifold modelled on a finite-dimensional space `X`,
let `V` be a smooth bundle of rank `dim X` and `s` a finite family of smooth sections spanning
every fibre. Some smooth section in the span of `s` has a closed and discrete zero set. -/
theorem exists_mem_span_isClosed_isDiscrete_zero [Finite ι] (hdim : finrank ℝ X = finrank ℝ F)
    (s : ι → ContMDiffSection 𝓘(ℝ, X) F ∞ V)
    (hspan : ∀ x, Submodule.span ℝ (range fun i ↦ s i x) = ⊤) :
    ∃ t ∈ Submodule.span ℝ (range s), IsClosed {x | t x = 0} ∧ IsDiscrete {x | t x = 0} := by
  have := Fintype.ofFinite ι
  obtain ⟨a, ha⟩ := (dense_of_mem_residual
    (mem_residual_setOfPred_isDiscrete_zero_affineFamily hdim 0 s hspan)).nonempty
  refine ⟨affineFamily 0 s a, (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨a, ?_⟩,
    isClosed_setOfPred_eq_zero _, ha⟩
  ext x
  simp only [coe_sum, Finset.sum_apply, coe_smul, Pi.smul_apply, affineFamily_apply, coe_zero,
    Pi.zero_apply, zero_add]

end AffineFamily

end ContMDiffSection

end
