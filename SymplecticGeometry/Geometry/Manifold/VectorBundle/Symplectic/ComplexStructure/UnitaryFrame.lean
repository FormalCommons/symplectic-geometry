/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Matrix.SymplecticGroup.ComplexStructure
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.ComplexStructure.Basic

/-!
# Unitary symplectic frames

Let `(V, ω)` be a vector bundle with a two-form, `J` a complex structure on `V` compatible with
`ω`, and `Ψ` a symplectic frame of `V` along a continuous map `f : X → M`: linear isomorphisms
`Ψ x : StdSpace ι ≃L[ℝ] V (f x)` that carry `ω₀ = stdForm ι` to `ω` and depend continuously on
`x`. This file shows that `Ψ` can be made unitary by a continuous change of frame in the symplectic
group: there is a continuous `P : X → Sp(2n)` such that `Ψ x ∘ P x` carries the standard complex
structure `J₀` to `J`.

Read through `Ψ x`, the structure `J (f x)` becomes a complex structure on `StdSpace ι` compatible
with `ω₀`, and its pairings `ω₀(v, ·)` are those of `ω` with sections of `V`, so they depend
continuously on `x`. The change of frame is then
`SymplecticGeometry.exists_continuous_GLSymplectic_smul_stdComplexStructure_eq`.

## Main results

* `SymplecticGeometry.Bundle.ContMDiffTwoForm.Compatible.exists_continuous_GLSymplectic_unitary`:
  a symplectic frame of `ω` along `f` becomes unitary for a compatible `J` after a continuous
  change of frame in the symplectic group.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
  and the proof of Theorem 2.7.1
-/

public section

open _root_.Bundle Matrix

namespace SymplecticGeometry.Bundle.ContMDiffTwoForm

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n m : ℕ∞}
  {ω : ContMDiffTwoForm I n F V} {J : ContMDiffComplexStructure I m F V}
  {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*} [TopologicalSpace X] {f : X → M}
  {Ψ : ∀ x, StdSpace ι ≃L[ℝ] V (f x)}

/-- **Unitary symplectic frames.** Let `J` be a complex structure compatible with the two-form
`ω`, and `Ψ` a symplectic frame of `ω` along a map `f : X → M`: linear isomorphisms
`Ψ x : StdSpace ι ≃L[ℝ] V (f x)`, continuous on `X × StdSpace ι` as maps to the total space,
with `ω(Ψ x v, Ψ x w) = ω₀(v, w)`. Then there is a continuous map `P` from `X` to the symplectic
group such that the frame `Ψ x ∘ P x` is unitary: it intertwines the standard complex structure
`J₀` with `J`. -/
theorem Compatible.exists_continuous_GLSymplectic_unitary (hJ : ω.Compatible J)
    (hΨ : Continuous fun p : X × StdSpace ι ↦ TotalSpace.mk' F (f p.1) (Ψ p.1 p.2))
    (hΨω : ∀ x v w, ω.bilinFormAt (f x) (Ψ x v) (Ψ x w) = stdForm ι v w) :
    ∃ P : X → TauCeti.GLSymplectic ι ℝ, Continuous P ∧ ∀ x v,
      J (f x) (Ψ x (toEuclideanLin ((P x : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) v)) =
        Ψ x (toEuclideanLin ((P x : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
          (stdComplexStructure ι v)) := by
  have hω := hJ.isNondegenerate
  -- `J (f x)` read through the frame `Ψ x`.
  let K : X → TauCeti.AlmostComplexStructure (StdSpace ι) := fun x ↦
    (J.almostComplexStructureAt (f x)).transport (Ψ x).symm.toLinearEquiv
  have hKapply (x : X) (v : StdSpace ι) : K x v = (Ψ x).symm (J (f x) (Ψ x v)) := by
    simp [K, ContMDiffComplexStructure.almostComplexStructureAt_apply]
  have hK (x : X) : (stdForm ι).Compatible (K x) := by
    have he : (stdForm ι).IsSymplectomorphism (hω.symplecticFormAt (f x))
        (Ψ x).toLinearEquiv :=
      TauCeti.SymplecticForm.isSymplectomorphism_iff.2 fun v w ↦ by
        simpa [IsNondegenerate.symplecticFormAt_apply, bilinFormAt_apply] using hΨω x v w
    exact (TauCeti.SymplecticForm.IsSymplectomorphism.compatible_transport_iff he.symm _).2
      (hJ.compatibleAt (f x))
  have hf : Continuous f := (FiberBundle.continuous_proj F V).comp
    (hΨ.comp (continuous_id.prodMk (continuous_const (y := (0 : StdSpace ι)))))
  have hsec (v : StdSpace ι) : Continuous fun x ↦ TotalSpace.mk' F (f x) (Ψ x v) :=
    hΨ.comp (continuous_id.prodMk continuous_const)
  have hcont (v w : StdSpace ι) : Continuous fun x ↦ stdForm ι v (K x w) := by
    have h (x : X) : stdForm ι v (K x w) = ω.flat (f x) (Ψ x v) (J (f x) (Ψ x w)) := by
      rw [← hΨω x v (K x w), hKapply, ContinuousLinearEquiv.apply_symm_apply, flat_apply,
        bilinFormAt_apply]
    have hJw : Continuous fun x ↦ TotalSpace.mk' F (f x) (J (f x) (Ψ x w)) :=
      (J.toEndomorphism.contMDiff.continuous.comp hf).clm_bundle_apply (hsec w)
    have hpair := (ω.contMDiff_flat.continuous.comp hf).clm_bundle_apply₂ (E₃ := Trivial M ℝ)
      (hsec v) hJw
    -- The scalar is the second component of a point of the trivial line bundle.
    exact ((continuous_snd.comp (Trivial.isInducing_toProd M ℝ).continuous).comp hpair).congr
      fun x ↦ (h x).symm
  obtain ⟨P, hP, hPK⟩ := exists_continuous_GLSymplectic_smul_stdComplexStructure_eq hK hcont
  refine ⟨P, hP, fun x v ↦ ?_⟩
  have h := congrArg (fun L : TauCeti.AlmostComplexStructure (StdSpace ι) ↦
    L (toEuclideanLin ((P x : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) v)) (hPK x)
  simp only [TauCeti.AlmostComplexStructure.generalLinearGroup_smul_apply, hKapply] at h
  rw [← (Ψ x).apply_symm_apply (J (f x) _), ← h]
  have hP0 := (P x : GL (ι ⊕ ι) ℝ).det_ne_zero
  rw [← toEuclideanCLE_apply _ hP0 v, ← toEuclideanCLE_symm_apply _ hP0,
    ContinuousLinearEquiv.symm_apply_apply]

end SymplecticGeometry.Bundle.ContMDiffTwoForm

end
