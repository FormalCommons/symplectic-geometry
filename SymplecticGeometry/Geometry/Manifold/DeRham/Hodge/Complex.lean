/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DeRham.Hodge.Basic
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Complexification
public import TauCeti.Geometry.Manifold.DeRham.ComplexCoefficients

/-!
# Complex harmonic forms

Complex-valued smooth forms are the scalar extension of real ones
(`TauCeti.SmoothForm.complexificationEquiv`). On an oriented Riemannian manifold of dimension
`m = k + l`, this file extends the real Hodge Laplacian and Hodge star of Tau Ceti to complex
forms by base change along that equivalence, so that they act on real and imaginary parts
separately, and transfers the Hodge theorem of `DeRham/Hodge/Basic.lean` to complex forms and
complex de Rham cohomology.

## Main definitions

* `TauCeti.SmoothForm.complexHodgeLaplacian`: the complex-linear Hodge Laplacian of complex
  `k`-forms, with `mapCoeff_reCLM_complexHodgeLaplacian` and
  `mapCoeff_imCLM_complexHodgeLaplacian`.
* `TauCeti.SmoothForm.complexHodgeStar`: the complex-linear (not conjugate-linear) Hodge star
  from complex `k`-forms to complex `l`-forms, with `mapCoeff_reCLM_complexHodgeStar` and
  `mapCoeff_imCLM_complexHodgeStar`.
* `TauCeti.complexHarmonicForms`: the kernel of `complexHodgeLaplacian`, equivalently the complex
  forms whose real and imaginary parts are harmonic.
* `TauCeti.complexHarmonicForms.toComplexDeRhamCohomology`: the complex de Rham class of a
  complex harmonic form.

## Main results

* `TauCeti.complexHarmonicForms.toComplexDeRhamCohomology_bijective`: on a closed oriented
  Riemannian manifold, every complex de Rham class has exactly one harmonic representative.
* `TauCeti.exists_mem_complexHarmonicForms_add_complexHodgeLaplacian`: every complex form is
  `h + Δγ` with `h` harmonic.
* `TauCeti.finrank_complexDeRhamCohomology`: the complex dimension of complex de Rham cohomology
  is the real dimension of real de Rham cohomology.

The definitions by base change follow Tau Ceti's treatment of the exterior derivative,
`TauCeti.SmoothForm.complexificationEquiv_baseChange_mextDerivₗ`.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §6.
* [J.-P. Demailly, *Complex Analytic and Differential Geometry*][Demailly2012], Chapter VI.
-/

public section

noncomputable section

open Bundle Module
open scoped Manifold ContDiff TensorProduct

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

namespace SmoothForm

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {m k l : ℕ}

/-! ### The complex Hodge Laplacian -/

/-- The Hodge Laplacian of complex-valued `k`-forms on an oriented Riemannian manifold of
dimension `m = k + l`: the base change to `ℂ` of the real Hodge Laplacian, read through
`complexificationEquiv`. It is the real Laplacian on real and imaginary parts. -/
def complexHodgeLaplacian (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :
    SmoothForm I M ℂ k →ₗ[ℂ] SmoothForm I M ℂ k :=
  complexificationEquiv.toLinearMap ∘ₗ (hodgeLaplacian o hkl).baseChange ℂ ∘ₗ
    complexificationEquiv.symm.toLinearMap

/-- The complex Hodge Laplacian is the base change of the real one. -/
theorem complexHodgeLaplacian_def (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :
    complexHodgeLaplacian (I := I) o hkl =
      complexificationEquiv.toLinearMap ∘ₗ (hodgeLaplacian o hkl).baseChange ℂ ∘ₗ
        complexificationEquiv.symm.toLinearMap :=
  (rfl)

/-- The complex Hodge Laplacian of `φ` is `Δ (Re φ) + i Δ (Im φ)`. -/
theorem complexHodgeLaplacian_apply (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (φ : SmoothForm I M ℂ k) :
    complexHodgeLaplacian o hkl φ =
      mapCoeff Complex.ofRealCLM (hodgeLaplacian o hkl (mapCoeff Complex.reCLM φ)) +
        Complex.I •
          mapCoeff Complex.ofRealCLM (hodgeLaplacian o hkl (mapCoeff Complex.imCLM φ)) :=
  complexificationEquiv_baseChange_complexificationEquiv_symm _ φ

/-- The real part of the complex Hodge Laplacian is the Hodge Laplacian of the real part. -/
@[simp]
theorem mapCoeff_reCLM_complexHodgeLaplacian (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (φ : SmoothForm I M ℂ k) :
    mapCoeff Complex.reCLM (complexHodgeLaplacian o hkl φ) =
      hodgeLaplacian o hkl (mapCoeff Complex.reCLM φ) :=
  mapCoeff_reCLM_complexificationEquiv_baseChange _ φ

/-- The imaginary part of the complex Hodge Laplacian is the Hodge Laplacian of the imaginary
part. -/
@[simp]
theorem mapCoeff_imCLM_complexHodgeLaplacian (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (φ : SmoothForm I M ℂ k) :
    mapCoeff Complex.imCLM (complexHodgeLaplacian o hkl φ) =
      hodgeLaplacian o hkl (mapCoeff Complex.imCLM φ) :=
  mapCoeff_imCLM_complexificationEquiv_baseChange _ φ

/-- On real forms, the complex Hodge Laplacian is the real Hodge Laplacian. -/
@[simp]
theorem complexHodgeLaplacian_mapCoeff_ofRealCLM (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (α : SmoothForm I M ℝ k) :
    complexHodgeLaplacian o hkl (mapCoeff Complex.ofRealCLM α) =
      mapCoeff Complex.ofRealCLM (hodgeLaplacian o hkl α) :=
  complexificationEquiv_baseChange_symm_mapCoeff_ofRealCLM _ α

/-! ### The complex Hodge star -/

/-- The Hodge star of complex-valued forms on an oriented Riemannian manifold of dimension
`m = k + l`: the complex-linear extension of the real Hodge star, the base change to `ℂ` of
`hodgeStar` read through `complexificationEquiv`. It is the real Hodge star on real and imaginary
parts, and involves no complex conjugation. -/
def complexHodgeStar (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :
    SmoothForm I M ℂ k →ₗ[ℂ] SmoothForm I M ℂ l :=
  complexificationEquiv.toLinearMap ∘ₗ (hodgeStar o hkl).baseChange ℂ ∘ₗ
    complexificationEquiv.symm.toLinearMap

/-- The complex Hodge star is the base change of the real one. -/
theorem complexHodgeStar_def (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :
    complexHodgeStar (I := I) o hkl =
      complexificationEquiv.toLinearMap ∘ₗ (hodgeStar o hkl).baseChange ℂ ∘ₗ
        complexificationEquiv.symm.toLinearMap :=
  (rfl)

/-- The complex Hodge star of `φ` is `⋆(Re φ) + i ⋆(Im φ)`. -/
theorem complexHodgeStar_apply (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (φ : SmoothForm I M ℂ k) :
    complexHodgeStar o hkl φ =
      mapCoeff Complex.ofRealCLM (hodgeStar o hkl (mapCoeff Complex.reCLM φ)) +
        Complex.I • mapCoeff Complex.ofRealCLM (hodgeStar o hkl (mapCoeff Complex.imCLM φ)) :=
  complexificationEquiv_baseChange_complexificationEquiv_symm _ φ

/-- The real part of the complex Hodge star is the Hodge star of the real part. -/
@[simp]
theorem mapCoeff_reCLM_complexHodgeStar (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (φ : SmoothForm I M ℂ k) :
    mapCoeff Complex.reCLM (complexHodgeStar o hkl φ) =
      hodgeStar o hkl (mapCoeff Complex.reCLM φ) :=
  mapCoeff_reCLM_complexificationEquiv_baseChange _ φ

/-- The imaginary part of the complex Hodge star is the Hodge star of the imaginary part. -/
@[simp]
theorem mapCoeff_imCLM_complexHodgeStar (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (φ : SmoothForm I M ℂ k) :
    mapCoeff Complex.imCLM (complexHodgeStar o hkl φ) =
      hodgeStar o hkl (mapCoeff Complex.imCLM φ) :=
  mapCoeff_imCLM_complexificationEquiv_baseChange _ φ

/-- On real forms, the complex Hodge star is the real Hodge star. -/
@[simp]
theorem complexHodgeStar_mapCoeff_ofRealCLM (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (α : SmoothForm I M ℝ k) :
    complexHodgeStar o hkl (mapCoeff Complex.ofRealCLM α) =
      mapCoeff Complex.ofRealCLM (hodgeStar o hkl α) :=
  complexificationEquiv_baseChange_symm_mapCoeff_ofRealCLM _ α

end SmoothForm

/-! ### Complex harmonic forms -/

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {m k l : ℕ}

/-- The complex harmonic `k`-forms on an oriented Riemannian manifold of dimension `m = k + l`:
the kernel of the complex Hodge Laplacian, that is, the complex forms whose real and imaginary
parts are harmonic (`mem_complexHarmonicForms_iff_realPart_imaginaryPart`). -/
def complexHarmonicForms (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :
    Submodule ℂ (SmoothForm I M ℂ k) :=
  LinearMap.ker (SmoothForm.complexHodgeLaplacian o hkl)

/-- A complex form is harmonic precisely when its complex Hodge Laplacian vanishes. -/
@[simp]
theorem mem_complexHarmonicForms_iff (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (φ : SmoothForm I M ℂ k) :
    φ ∈ complexHarmonicForms o hkl ↔ SmoothForm.complexHodgeLaplacian o hkl φ = 0 :=
  LinearMap.mem_ker

/-- A complex form is harmonic exactly when its real and imaginary parts are harmonic. -/
theorem mem_complexHarmonicForms_iff_realPart_imaginaryPart
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) (φ : SmoothForm I M ℂ k) :
    φ ∈ complexHarmonicForms o hkl ↔
      SmoothForm.mapCoeff Complex.reCLM φ ∈ harmonicForms o hkl ∧
        SmoothForm.mapCoeff Complex.imCLM φ ∈ harmonicForms o hkl := by
  rw [mem_complexHarmonicForms_iff, mem_harmonicForms, mem_harmonicForms,
    SmoothForm.complexHodgeLaplacian_apply]
  refine ⟨fun h ↦ ?_, fun ⟨hre, him⟩ ↦ by simp [hre, him]⟩
  have hre := congrArg (SmoothForm.mapCoeff Complex.reCLM) h
  have him := congrArg (SmoothForm.mapCoeff Complex.imCLM) h
  rw [SmoothForm.realPart_ofReal_add_I_smul_ofReal, map_zero] at hre
  rw [SmoothForm.imaginaryPart_ofReal_add_I_smul_ofReal, map_zero] at him
  exact ⟨hre, him⟩

/-- The complex form `α + i β` is harmonic when the real forms `α` and `β` are. -/
theorem ofReal_add_I_smul_ofReal_mem_complexHarmonicForms (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) {α β : SmoothForm I M ℝ k} (hα : α ∈ harmonicForms o hkl)
    (hβ : β ∈ harmonicForms o hkl) :
    SmoothForm.mapCoeff Complex.ofRealCLM α +
        Complex.I • SmoothForm.mapCoeff Complex.ofRealCLM β ∈ complexHarmonicForms o hkl := by
  rw [mem_complexHarmonicForms_iff_realPart_imaginaryPart,
    SmoothForm.realPart_ofReal_add_I_smul_ofReal, SmoothForm.imaginaryPart_ofReal_add_I_smul_ofReal]
  exact ⟨hα, hβ⟩

/-- A complex form is harmonic exactly when its complex Hodge star is harmonic. -/
theorem complexHodgeStar_mem_complexHarmonicForms_iff (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (hlk : l + k = m) (φ : SmoothForm I M ℂ k) :
    SmoothForm.complexHodgeStar o hkl φ ∈ complexHarmonicForms o hlk ↔
      φ ∈ complexHarmonicForms o hkl := by
  simp only [mem_complexHarmonicForms_iff_realPart_imaginaryPart,
    SmoothForm.mapCoeff_reCLM_complexHodgeStar, SmoothForm.mapCoeff_imCLM_complexHodgeStar,
    hodgeStar_mem_harmonicForms_iff]

section Compact

variable [BoundarylessManifold I M] [T2Space M] [CompactSpace M]

/-- On a compact oriented boundaryless Riemannian manifold, complex harmonic forms are closed. -/
theorem complexHarmonicForms_le_complexClosedForms (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) : complexHarmonicForms o hkl ≤ complexClosedForms I M k := fun φ hφ ↦ by
  rw [mem_complexHarmonicForms_iff_realPart_imaginaryPart] at hφ
  exact (mem_complexClosedForms_iff_realPart_imaginaryPart I φ).2
    ⟨harmonicForms_le_closedForms o hkl hφ.1, harmonicForms_le_closedForms o hkl hφ.2⟩

/-- The complex de Rham class of a complex harmonic form on a compact oriented boundaryless
Riemannian manifold. -/
def complexHarmonicForms.toComplexDeRhamCohomology (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) : complexHarmonicForms o hkl →ₗ[ℂ] complexDeRhamCohomology I M k :=
  complexDeRhamCohomology.mk I k ∘ₗ
    Submodule.inclusion (complexHarmonicForms_le_complexClosedForms o hkl)

/-- A complex harmonic form is sent to the class of the underlying closed form. -/
@[simp]
theorem complexHarmonicForms.toComplexDeRhamCohomology_apply
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) (φ : complexHarmonicForms o hkl) :
    complexHarmonicForms.toComplexDeRhamCohomology o hkl φ =
      complexDeRhamCohomology.mk I k
        ⟨φ.val, complexHarmonicForms_le_complexClosedForms o hkl φ.property⟩ :=
  (rfl)

/-- **The complex Hodge theorem**: on a closed oriented Riemannian manifold, every complex de Rham
class has exactly one harmonic representative. -/
theorem complexHarmonicForms.toComplexDeRhamCohomology_bijective
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :
    Function.Bijective (complexHarmonicForms.toComplexDeRhamCohomology o hkl) := by
  refine ⟨fun φ ψ h ↦ ?_, fun c ↦ ?_⟩
  · -- The real and imaginary parts of `φ - ψ` are harmonic and exact, hence zero.
    rw [toComplexDeRhamCohomology_apply, toComplexDeRhamCohomology_apply, ← sub_eq_zero,
      ← map_sub, complexDeRhamCohomology.mk_eq_zero_iff, Submodule.coe_sub,
      mem_complexExactForms_iff_realPart_imaginaryPart] at h
    have hharm := (mem_complexHarmonicForms_iff_realPart_imaginaryPart o hkl _).1
      (sub_mem φ.property ψ.property)
    have hre := Submodule.disjoint_def.1 (disjoint_harmonicForms_exactForms o hkl) _ hharm.1 h.1
    have him := Submodule.disjoint_def.1 (disjoint_harmonicForms_exactForms o hkl) _ hharm.2 h.2
    rw [Subtype.ext_iff, ← sub_eq_zero,
      ← SmoothForm.ofReal_realPart_add_I_smul_ofReal_imaginaryPart (φ.val - ψ.val), hre, him,
      map_zero, smul_zero, add_zero]
  · -- Take harmonic representatives of the real and imaginary parts.
    obtain ⟨ψ, rfl⟩ := complexDeRhamCohomology.mk_surjective I k c
    obtain ⟨hre, hhre, hre'⟩ := exists_mem_harmonicForms_sub_mem_exactForms o hkl
      ((mem_complexClosedForms_iff_realPart_imaginaryPart I ψ.val).1 ψ.property).1
    obtain ⟨him, hhim, him'⟩ := exists_mem_harmonicForms_sub_mem_exactForms o hkl
      ((mem_complexClosedForms_iff_realPart_imaginaryPart I ψ.val).1 ψ.property).2
    refine ⟨⟨_, ofReal_add_I_smul_ofReal_mem_complexHarmonicForms o hkl hhre hhim⟩, ?_⟩
    rw [toComplexDeRhamCohomology_apply, eq_comm, ← sub_eq_zero, ← map_sub,
      complexDeRhamCohomology.mk_eq_zero_iff, Submodule.coe_sub,
      mem_complexExactForms_iff_realPart_imaginaryPart, map_sub, map_sub,
      SmoothForm.realPart_ofReal_add_I_smul_ofReal,
      SmoothForm.imaginaryPart_ofReal_add_I_smul_ofReal]
    exact ⟨hre', him'⟩

/-- **The Hodge decomposition of a complex form**: on a closed oriented Riemannian manifold, every
complex `k`-form is `h + Δγ` with `h` complex harmonic and `γ` a complex form. -/
theorem exists_mem_complexHarmonicForms_add_complexHodgeLaplacian
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) (φ : SmoothForm I M ℂ k) :
    ∃ h ∈ complexHarmonicForms o hkl, ∃ γ : SmoothForm I M ℂ k,
      φ = h + SmoothForm.complexHodgeLaplacian o hkl γ := by
  obtain ⟨hre, hhre, γre, hγre⟩ :=
    exists_mem_harmonicForms_add_hodgeLaplacian o hkl (SmoothForm.mapCoeff Complex.reCLM φ)
  obtain ⟨him, hhim, γim, hγim⟩ :=
    exists_mem_harmonicForms_add_hodgeLaplacian o hkl (SmoothForm.mapCoeff Complex.imCLM φ)
  refine ⟨_, ofReal_add_I_smul_ofReal_mem_complexHarmonicForms o hkl hhre hhim,
    SmoothForm.mapCoeff Complex.ofRealCLM γre +
      Complex.I • SmoothForm.mapCoeff Complex.ofRealCLM γim, ?_⟩
  conv_lhs => rw [← SmoothForm.ofReal_realPart_add_I_smul_ofReal_imaginaryPart φ, hγre, hγim]
  rw [map_add (SmoothForm.complexHodgeLaplacian o hkl),
    map_smul (SmoothForm.complexHodgeLaplacian o hkl),
    SmoothForm.complexHodgeLaplacian_mapCoeff_ofRealCLM,
    SmoothForm.complexHodgeLaplacian_mapCoeff_ofRealCLM, map_add, map_add, smul_add]
  abel

end Compact

/-- The complex dimension of complex de Rham cohomology is the real dimension of real de Rham
cohomology, since the former is the complexification of the latter. -/
theorem finrank_complexDeRhamCohomology {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M] (k : ℕ) :
    finrank ℂ (complexDeRhamCohomology I M k) = finrank ℝ (deRhamCohomology I M k) := by
  rw [← (complexDeRhamCohomology.complexificationEquiv I k).finrank_eq,
    Module.finrank_baseChange]

end TauCeti

end
