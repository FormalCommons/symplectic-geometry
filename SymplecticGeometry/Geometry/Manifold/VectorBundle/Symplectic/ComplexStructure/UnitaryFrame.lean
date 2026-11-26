/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.ComplexStructure.Basic
public import TauCeti.Analysis.Matrix.SymplecticGroup.Maslov
public import TauCeti.Analysis.Complex.NormalizedDeterminant
import SymplecticGeometry.Analysis.Matrix.SymplecticGroup.ComplexStructure
import SymplecticGeometry.Analysis.Matrix.SymplecticGroup.Maslov
import SymplecticGeometry.Topology.Algebra.Matrix.GeneralLinearGroup
import SymplecticGeometry.Topology.VectorBundle.Complex.Structure

/-!
# Unitary symplectic frames

Let `(V, ω)` be a vector bundle with a two-form, `J` a complex structure on `V` compatible with
`ω`, and `Ψ` a symplectic frame of `V` along a map `f : X → M`: linear isomorphisms
`Ψ x : StdSpace ι ≃L[ℝ] V (f x)` that carry `ω₀ = stdForm ι` to `ω` and depend continuously on
`x` as maps into the total space. This file shows that `Ψ` can be made unitary by a continuous
change of frame in the symplectic group: there is a continuous `P : X → Sp(2n)` such that
`Ψ x ∘ P x` carries the standard complex structure `J₀` to `J`.

Read through `Ψ x`, the structure `J (f x)` becomes a complex structure on `StdSpace ι` compatible
with `ω₀`, and its pairings `ω₀(v, ·)` are those of `ω` with sections of `V`, so they depend
continuously on `x`. The change of frame is then
`SymplecticGeometry.exists_continuous_GLSymplectic_smul_stdComplexStructure_eq`.

Read on `ι → ℂ` through real and imaginary parts (`TauCeti.complexToRealEuclidean`), the unitary
frame `Ψ ∘ P` carries multiplication by `i` to `J`, so it is a continuous frame of the complex
bundle `(V, J)` (`TauCeti.Bundle.ContinuousComplexStructure.frameOfCommute`). If two such frames
come from real frames `Ψ₁`, `Ψ₂` of one fibre with `Ψ₂ = Ψ₁ ∘ A`, by changes of frame `P₁` and
`P₂`, the complex transition between them is `P₁⁻¹ A P₂`, which is complex-linear, so its
normalized complex determinant is its Maslov phase `ρ(P₁⁻¹ A P₂)`
(`TauCeti.GLSymplectic.maslovPhase_eq_normalizedDet`).

## Main results

* `SymplecticGeometry.Bundle.ContMDiffTwoForm.Compatible.exists_continuous_GLSymplectic_unitary`:
  a symplectic frame of `ω` along `f` becomes unitary for a compatible `J` after a continuous
  change of frame in the symplectic group.
* `Compatible.exists_continuous_GLSymplectic_complexFrame`, in the same namespace: the same change
  of frame gives a continuous frame of the complex bundle `(V, J)`.
* `TauCeti.Bundle.ContinuousComplexStructure.maslovPhase_inv_mul_mul_eq_normalizedDet`: the
  Maslov phase of the transition `P₁⁻¹ A P₂` is the normalized determinant of the complex
  transition.

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


/-- **Complex frames from symplectic frames.** Let `J` be a complex structure compatible with the
two-form `ω`, and `Ψ` a symplectic frame of `ω` along `f : X → M`, as in
`Compatible.exists_continuous_GLSymplectic_unitary`. Then there are a continuous map `P` from `X`
to the symplectic group and a frame `Θ` of the complex bundle `(V, J)` along `f`, by
complex-linear isomorphisms `Θ x : (ι → ℂ) ≃ (V, J)_{f x}` continuous as maps to its total space,
such that `Θ x v = Ψ x (P x (Re v, Im v))` in `V (f x)`. -/
theorem Compatible.exists_continuous_GLSymplectic_complexFrame [FiniteDimensional ℝ F]
    [Fact (Module.finrank ℝ F = 2 * Module.finrank ℂ (ι → ℂ))] (hJ : ω.Compatible J)
    (hΨ : Continuous fun p : X × StdSpace ι ↦ TotalSpace.mk' F (f p.1) (Ψ p.1 p.2))
    (hΨω : ∀ x v w, ω.bilinFormAt (f x) (Ψ x v) (Ψ x w) = stdForm ι v w) :
    ∃ (P : X → TauCeti.GLSymplectic ι ℝ)
      (Θ : ∀ x, (ι → ℂ) ≃L[ℂ] J.toContinuousComplexStructure.Fiber (f x)), Continuous P ∧
      (Continuous fun p : X × (ι → ℂ) ↦
        TotalSpace.mk' (ι → ℂ) (E := J.toContinuousComplexStructure.Fiber) (f p.1) (Θ p.1 p.2)) ∧
      ∀ x v, J.toContinuousComplexStructure.fiberEquiv (f x) (Θ x v) =
        Ψ x (toEuclideanLin ((P x : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
          (TauCeti.complexToRealEuclidean ι v)) := by
  obtain ⟨P, hP, hPJ⟩ := hJ.exists_continuous_GLSymplectic_unitary hΨ hΨω
  -- The unitary frame `Ψ ∘ P`, read on `ι → ℂ` through real and imaginary parts.
  let Φ : ∀ x, (ι → ℂ) ≃L[ℝ] V (f x) := fun x ↦ (TauCeti.complexToRealEuclidean ι).trans
    ((toEuclideanCLE _ (P x : GL (ι ⊕ ι) ℝ).det_ne_zero).trans (Ψ x))
  have hΦ (x : X) (v : ι → ℂ) : Φ x v =
      Ψ x (toEuclideanLin ((P x : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
        (TauCeti.complexToRealEuclidean ι v)) := by
    rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
      toEuclideanCLE_apply]
  have hΦI (x : X) (v : ι → ℂ) :
      Φ x (Complex.I • v) = J.toContinuousComplexStructure (f x) (Φ x v) := by
    rw [hΦ, hΦ, ContMDiffComplexStructure.toContinuousComplexStructure_apply, hPJ,
      stdComplexStructure_complexToRealEuclidean]
  have hPc : Continuous fun q : X × StdSpace ι ↦
      toEuclideanLin ((P q.1 : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) q.2 :=
    ((((GeneralLinearGroup.continuous_contRep ℝ _).comp (continuous_subtypeVal.comp hP)).comp
      continuous_fst).clm_apply continuous_snd).congr fun q ↦ by simp
  refine ⟨P, J.toContinuousComplexStructure.frameOfCommute Φ hΦI, hP,
    J.toContinuousComplexStructure.continuous_frameOfCommute Φ hΦI (ι → ℂ) ?_, fun x v ↦ ?_⟩
  · exact (hΨ.comp (continuous_fst.prodMk (hPc.comp (continuous_fst.prodMk
      ((TauCeti.complexToRealEuclidean ι).continuous.comp continuous_snd))))).congr fun q ↦ by
        simp only [Function.comp_apply, hΦ]
  · rw [TauCeti.Bundle.ContinuousComplexStructure.fiberEquiv_frameOfCommute, hΦ]

end SymplecticGeometry.Bundle.ContMDiffTwoForm

namespace TauCeti.Bundle.ContinuousComplexStructure

open SymplecticGeometry

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)]
  [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousSMul ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  (J : ContinuousComplexStructure F V) {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Maslov phase of a transition of unitary frames.** Let `Ψ₁` and `Ψ₂` be real frames of
the fibre `V b`, with `Ψ₂ = Ψ₁ ∘ A` for a symplectic matrix `A`, and `Θ₁`, `Θ₂` frames of the
fibre of the complex bundle `(V, J)` at `b` that are `Ψ₁ ∘ P₁` and `Ψ₂ ∘ P₂` for symplectic
matrices `P₁`, `P₂`, read on `ι → ℂ` through real and imaginary parts. Then `ρ(P₁⁻¹ A P₂)` is the
normalized complex determinant of the complex transition `Θ₁⁻¹ ∘ Θ₂`. -/
theorem maslovPhase_inv_mul_mul_eq_normalizedDet {b : B} {Ψ₁ Ψ₂ : StdSpace ι ≃L[ℝ] V b}
    {Θ₁ Θ₂ : (ι → ℂ) ≃L[ℂ] J.Fiber b} {P₁ A P₂ : GLSymplectic ι ℝ}
    (h₁ : ∀ v, J.fiberEquiv b (Θ₁ v) =
      Ψ₁ (toEuclideanLin ((P₁ : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
        (complexToRealEuclidean ι v)))
    (h₂ : ∀ v, J.fiberEquiv b (Θ₂ v) =
      Ψ₂ (toEuclideanLin ((P₂ : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
        (complexToRealEuclidean ι v)))
    (hA : ∀ v, Ψ₂ v = Ψ₁ (toEuclideanLin ((A : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) v)) :
    GLSymplectic.maslovPhase (P₁⁻¹ * A * P₂) = (Θ₂.trans Θ₁.symm).normalizedDet := by
  refine GLSymplectic.maslovPhase_eq_normalizedDet _ fun v ↦
    ((toEuclideanCLE _ (P₁ : GL (ι ⊕ ι) ℝ).det_ne_zero).trans Ψ₁).injective ?_
  simp only [ContinuousLinearEquiv.trans_apply, toEuclideanCLE_apply]
  rw [← h₁, ContinuousLinearEquiv.apply_symm_apply, h₂, hA]
  simp only [Subgroup.coe_mul, Units.val_mul, toLpLin_mul_same, LinearMap.comp_apply,
    Subgroup.coe_inv, coe_units_inv]
  simp only [← toEuclideanCLM_apply,
    toEuclideanCLM_apply_toEuclideanCLM_nonsing_inv_apply (P₁ : GL (ι ⊕ ι) ℝ).det_ne_zero]

end TauCeti.Bundle.ContinuousComplexStructure

end
