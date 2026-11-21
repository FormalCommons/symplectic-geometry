/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Generic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.SmoothZero

/-!
# Sections with closed discrete zero sets

Over a boundaryless manifold `M` modelled on a finite-dimensional real space `X`, consider a
smooth real vector bundle `V` whose rank equals `dim X`. A smooth section whose intrinsic
linearization is surjective at each zero has Fredholm index zero there, so its zero set is a
`0`-dimensional manifold (Tau Ceti's `TauCeti.exists_isManifold_sectionZero_of_contMDiff`):
a discrete subset of `M`. It is also closed, as the zero set of any continuous section is. No
compactness of `M` is needed, unlike in Tau Ceti's `TauCeti.finite_sectionZero_of_contMDiff`.

Together with Tau Ceti's parametric transversality for affine families
(`ContMDiffSection.mem_residual_setOf_isRegular_affineFamily`), this shows that a finite family
of smooth sections spanning every fibre has a linear combination whose zero set is closed and
discrete.

## Main results

* `ContMDiffSection.isClosed_setOf_eq_zero`: the zero set of a section is closed.
* `ContMDiffSection.isDiscrete_setOf_eq_zero_of_surjective`: in rank equal to the dimension,
  the zero set of a section with surjective linearization at its zeros is discrete.
* `ContMDiffSection.mem_residual_setOf_isDiscrete_zero_affineFamily`: for a residual set of
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
theorem isClosed_setOf_eq_zero (t : ContMDiffSection IM F n V) : IsClosed {x | t x = 0} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  let e := trivializationAt F V x
  have hxe : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
  have heq (y : M) (hy : y ∈ e.baseSet) : (e ⟨y, t y⟩).2 = 0 ↔ t y = 0 := by
    rw [e.apply_eq_prod_continuousLinearEquivAt 𝕜 y hy]
    exact (e.continuousLinearEquivAt 𝕜 y hy).map_eq_zero_iff
  have hc : ContinuousAt (fun y ↦ (e ⟨y, t y⟩).2) x :=
    (e.continuousOn.continuousAt (e.open_source.mem_nhds (e.mem_source.2 hxe))).snd.comp
      t.contMDiff.continuous.continuousAt
  filter_upwards [hc.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds (mt (heq x hxe).1 hx)),
    e.open_baseSet.mem_nhds hxe] with y hy hye
  exact mt (heq y hye).2 hy

end Closed

section Discrete

variable {X M F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [TopologicalSpace M] [ChartedSpace X M] [IsManifold 𝓘(ℝ, X) ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, X)]

/-- Over a boundaryless manifold modelled on `X`, the zero set of a smooth section of a bundle
of rank `dim X` is discrete if the intrinsic linearization of the section is surjective at each
zero. -/
theorem isDiscrete_setOf_eq_zero_of_surjective (hdim : finrank ℝ X = finrank ℝ F)
    (t : ContMDiffSection 𝓘(ℝ, X) F ∞ V)
    (ht : ∀ x, t x = 0 → Surjective (TauCeti.sectionLinearization (F := F) 𝓘(ℝ, X) id t x)) :
    IsDiscrete {x | t x = 0} := by
  have hFred (x : M) (hx : t x = 0) :
      ContinuousLinearMap.IsFredholm (TauCeti.sectionLinearization (F := F) 𝓘(ℝ, X) id t x) := by
    have hc := (contMDiffAt_totalSpace_iff.mp (t.contMDiff x)).2
    exact (TauCeti.isFredholm_sectionLinearization_iff continuousAt_id
      (mem_baseSet_trivializationAt F V x) (hc.mdifferentiableAt (by simp)) hx).mpr
        (ContinuousLinearMap.isFredholm_of_finiteDimensional _)
  obtain ⟨cs, -, -, -⟩ := TauCeti.exists_isManifold_sectionZero_of_contMDiff (n := 0)
    (I := 𝓘(ℝ, X)) (by simp) (fun x _ ↦ t.contMDiff x) hFred ht fun x _ ↦ by
      rw [TauCeti.index_sectionLinearization_of_finiteDimensional, hdim, sub_self, Nat.cast_zero]
  let := cs
  exact isDiscrete_iff_discreteTopology.mpr (ChartedSpace.discreteTopology (Fin 0 → ℝ) _)

variable [SecondCountableTopology M] {ι : Type*}

/-- Over a second-countable boundaryless manifold modelled on `X`, let `V` be a bundle of rank
`dim X` and `s` a finite family of smooth sections spanning every fibre. For a residual set of
parameters `a`, the section `s₀ + ∑ i, a i • s i` has a discrete zero set. -/
theorem mem_residual_setOf_isDiscrete_zero_affineFamily [Fintype ι]
    (hdim : finrank ℝ X = finrank ℝ F)
    (s₀ : ContMDiffSection 𝓘(ℝ, X) F ∞ V) (s : ι → ContMDiffSection 𝓘(ℝ, X) F ∞ V)
    (hspan : ∀ x, Submodule.span ℝ (range fun i ↦ s i x) = ⊤) :
    {a | IsDiscrete {x | affineFamily s₀ s a x = 0}} ∈ residual (ι → ℝ) := by
  filter_upwards [mem_residual_setOf_isRegular_affineFamily s₀ s hspan] with a ha
  exact isDiscrete_setOf_eq_zero_of_surjective hdim _
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
    (mem_residual_setOf_isDiscrete_zero_affineFamily hdim 0 s hspan)).nonempty
  refine ⟨affineFamily 0 s a, ?_, isClosed_setOf_eq_zero _, ha⟩
  have heq : affineFamily 0 s a = ∑ i, a i • s i := by
    ext x
    have h := congrFun (map_sum (coeAddHom 𝓘(ℝ, X) F ∞ V) (fun i ↦ a i • s i) Finset.univ) x
    simp only [coeAddHom_apply, Finset.sum_apply] at h
    simp [h]
  rw [heq]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Discrete

end ContMDiffSection

end
