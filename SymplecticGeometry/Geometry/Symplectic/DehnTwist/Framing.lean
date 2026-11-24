/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import Mathlib.Tactic.Group

/-!
# Framings of a sphere

A framing of an embedded sphere `L ⊆ M` is a parametrization `f : Sⁿ → M` of `L`, taken up to
reparametrization by the orthogonal group `O(n + 1)` and by diffeomorphisms of `Sⁿ` that are
smoothly isotopic to the identity. This file defines the relation `FramingRel` on smooth
embeddings `Sⁿ → M` that identifies two such parametrizations, shows that it is an equivalence
relation, and defines the type `FramedSphere` of its classes.

## Main definitions

* `SymplecticGeometry.FramingRel f₁ f₂`: `f₁ = f₂ ∘ Φ₁ ∘ A` for a smooth diffeotopy `Φ` of `Sⁿ`
  and an orthogonal matrix `A`, acting on `Sⁿ` by `TauCeti.orthogonalToDiffSphere`.
* `SymplecticGeometry.framingSetoid`: the setoid of `FramingRel`.
* `SymplecticGeometry.FramedSphere`: smooth embeddings `Sⁿ → M` up to `FramingRel`, with
  `FramedSphere.lift`, which makes a function of parametrizations that respects `FramingRel` a
  function of framed spheres.

## Main results

* `SymplecticGeometry.framingRel_iff`: `FramingRel` as an equality of reparametrized embeddings.
* `SymplecticGeometry.FramingRel.range_eq`: related embeddings have the same image.
* `SymplecticGeometry.framingRel_equivalence`: `FramingRel` is an equivalence relation.
* `SymplecticGeometry.framingRel_comp_orthogonal`, `SymplecticGeometry.framingRel_comp_final`:
  reparametrizing by an orthogonal transformation, or by the final diffeomorphism of a
  diffeotopy, does not change the framing.
* `SymplecticGeometry.FramedSphere.range`: the image of a framed sphere.

## Implementation notes

Transitivity rests on the fact that `O(n + 1)` normalizes the final diffeomorphisms of
diffeotopies: `B * Φ₁ * B⁻¹` is the final diffeomorphism of the diffeotopy `Φ` conjugated by
`B` (`TauCeti.Diffeotopy.final_transDiffeomorph_eq_mul_mul_inv`). Isotopies are smooth
diffeotopies (`TauCeti.Diffeotopy`), not continuous paths in the diffeomorphism group.

## References

* [P. Seidel, *A long exact sequence for symplectic Floer cohomology*][Seidel2003], for framed
  Lagrangian spheres.
* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, for smooth isotopies.
-/

public section

noncomputable section

namespace SymplecticGeometry

open Set TauCeti
open scoped Manifold ContDiff

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Two parametrizations `f₁ f₂ : Sⁿ → M` define the same framing: `f₁ = f₂ ∘ Φ₁ ∘ A` for a
smooth diffeotopy `Φ` of `Sⁿ`, with final diffeomorphism `Φ₁`, and an orthogonal matrix
`A ∈ O(n + 1)` acting on `Sⁿ`. -/
def FramingRel
    (f₁ f₂ : SmoothEmbedding (𝓡 n) I ∞ (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) M) :
    Prop :=
  ∃ (Φ : Diffeotopy (𝓡 n) ∞ (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (A : Matrix.orthogonalGroup (Fin (n + 1)) ℝ),
    ∀ q, f₁ q = f₂ (Φ.final (orthogonalToDiffSphere n ∞ A q))

variable {f f₁ f₂ f₃ :
  SmoothEmbedding (𝓡 n) I ∞ (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) M}

/-- The defining property of `FramingRel`. -/
theorem framingRel_def :
    FramingRel f₁ f₂ ↔
      ∃ (Φ : Diffeotopy (𝓡 n) ∞ (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
        (A : Matrix.orthogonalGroup (Fin (n + 1)) ℝ),
        ∀ q, f₁ q = f₂ (Φ.final (orthogonalToDiffSphere n ∞ A q)) :=
  Iff.rfl

/-- Two parametrizations define the same framing if and only if the first is the second
reparametrized by `Φ₁ * A`, the final diffeomorphism of a diffeotopy after an orthogonal
transformation. -/
theorem framingRel_iff :
    FramingRel f₁ f₂ ↔
      ∃ (Φ : Diffeotopy (𝓡 n) ∞ (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
        (A : Matrix.orthogonalGroup (Fin (n + 1)) ℝ),
        f₁ = f₂.compDiffeomorph (Φ.final * orthogonalToDiffSphere n ∞ A) := by
  simp only [framingRel_def, SmoothEmbedding.ext_iff, SmoothEmbedding.compDiffeomorph_apply,
    Diffeomorph.mul_apply]

/-- Parametrizations that define the same framing have the same image. -/
theorem FramingRel.range_eq (h : FramingRel f₁ f₂) : range f₁ = range f₂ := by
  obtain ⟨Φ, A, h⟩ := framingRel_iff.mp h
  rw [h, SmoothEmbedding.range_compDiffeomorph]

/-- Reparametrizing an embedding by an orthogonal transformation of `Sⁿ` does not change its
framing. -/
theorem framingRel_comp_orthogonal
    (f : SmoothEmbedding (𝓡 n) I ∞ (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) M)
    (A : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :
    FramingRel (f.compDiffeomorph (orthogonalToDiffSphere n ∞ A)) f :=
  framingRel_iff.mpr ⟨Diffeotopy.refl _ _ _, A, by
    rw [Diffeotopy.final_refl, ← Diffeomorph.one_def, one_mul]⟩

/-- Reparametrizing an embedding by the final diffeomorphism of a diffeotopy of `Sⁿ` does not
change its framing. -/
theorem framingRel_comp_final
    (f : SmoothEmbedding (𝓡 n) I ∞ (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) M)
    (Φ : Diffeotopy (𝓡 n) ∞ (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    FramingRel (f.compDiffeomorph Φ.final) f :=
  framingRel_iff.mpr ⟨Φ, 1, by rw [map_one, mul_one]⟩

/-- Every parametrization defines the same framing as itself. -/
@[refl]
theorem FramingRel.refl
    (f : SmoothEmbedding (𝓡 n) I ∞ (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) M) :
    FramingRel f f :=
  framingRel_iff.mpr ⟨Diffeotopy.refl _ _ _, 1, by
    rw [Diffeotopy.final_refl, map_one, mul_one, SmoothEmbedding.compDiffeomorph_refl]⟩

/-- Defining the same framing is a symmetric relation. -/
@[symm]
theorem FramingRel.symm (h : FramingRel f₁ f₂) : FramingRel f₂ f₁ := by
  obtain ⟨Φ, A, h⟩ := framingRel_iff.mp h
  -- `f₂ = f₁ ∘ A⁻¹ ∘ Φ₁⁻¹ = f₁ ∘ (A⁻¹ * Φ₁⁻¹ * A) ∘ A⁻¹`.
  refine framingRel_iff.mpr ⟨Φ.symm.transDiffeomorph (orthogonalToDiffSphere n ∞ A⁻¹), A⁻¹, ?_⟩
  rw [h, SmoothEmbedding.compDiffeomorph_compDiffeomorph, ← Diffeomorph.mul_def,
    Diffeotopy.final_transDiffeomorph_eq_mul_mul_inv, Diffeotopy.final_symm,
    ← Diffeomorph.inv_def, map_inv]
  conv_lhs => rw [← SmoothEmbedding.compDiffeomorph_refl f₂, ← Diffeomorph.one_def]
  congr 1
  group

/-- Defining the same framing is a transitive relation. -/
@[trans]
theorem FramingRel.trans (h₁₂ : FramingRel f₁ f₂) (h₂₃ : FramingRel f₂ f₃) :
    FramingRel f₁ f₃ := by
  obtain ⟨Φ, A, h₁₂⟩ := framingRel_iff.mp h₁₂
  obtain ⟨Ψ, B, h₂₃⟩ := framingRel_iff.mp h₂₃
  -- `f₁ = f₃ ∘ Ψ₁ ∘ B ∘ Φ₁ ∘ A = f₃ ∘ Ψ₁ ∘ (B * Φ₁ * B⁻¹) ∘ (B * A)`.
  refine framingRel_iff.mpr
    ⟨(Φ.transDiffeomorph (orthogonalToDiffSphere n ∞ B)).trans Ψ, B * A, ?_⟩
  rw [h₁₂, h₂₃, SmoothEmbedding.compDiffeomorph_compDiffeomorph, ← Diffeomorph.mul_def,
    Diffeotopy.final_trans, ← Diffeomorph.mul_def,
    Diffeotopy.final_transDiffeomorph_eq_mul_mul_inv, map_mul]
  congr 1
  group

/-- Defining the same framing is an equivalence relation on parametrizations of spheres. -/
theorem framingRel_equivalence : Equivalence (FramingRel (I := I) (M := M) (n := n)) :=
  ⟨FramingRel.refl, FramingRel.symm, FramingRel.trans⟩

variable (n I M) in
/-- The setoid on smooth embeddings `Sⁿ → M` given by `FramingRel`. -/
def framingSetoid :
    Setoid (SmoothEmbedding (𝓡 n) I ∞ (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) M) :=
  ⟨FramingRel, framingRel_equivalence⟩

/-- The relation of `framingSetoid` is `FramingRel`. -/
@[simp]
theorem framingSetoid_r : (framingSetoid n I M).r f₁ f₂ ↔ FramingRel f₁ f₂ :=
  Iff.rfl

variable (n I M) in
/-- A framed sphere in `M`: a smooth embedding `Sⁿ → M` up to `FramingRel`. -/
def FramedSphere : Type _ :=
  Quotient (framingSetoid n I M)

namespace FramedSphere

/-- The framed sphere of a parametrization. -/
def mk (f : SmoothEmbedding (𝓡 n) I ∞ (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) M) :
    FramedSphere n I M :=
  Quotient.mk _ f

/-- Two parametrizations give the same framed sphere exactly when they define the same framing. -/
@[simp]
theorem mk_eq_mk_iff : mk f₁ = mk f₂ ↔ FramingRel f₁ f₂ :=
  Quotient.eq

/-- Every framed sphere has a parametrization. -/
theorem mk_surjective : Function.Surjective (mk : _ → FramedSphere n I M) :=
  Quotient.mk_surjective

/-- To prove a property of all framed spheres, prove it for each parametrization. -/
@[elab_as_elim]
theorem ind {p : FramedSphere n I M → Prop} (h : ∀ f, p (mk f)) (L : FramedSphere n I M) : p L :=
  Quotient.ind h L

/-- A function on parametrizations that takes the same value on any two that define the same
framing, as a function on framed spheres. -/
def lift {α : Sort*}
    (g : SmoothEmbedding (𝓡 n) I ∞ (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) M → α)
    (hg : ∀ f₁ f₂, FramingRel f₁ f₂ → g f₁ = g f₂) : FramedSphere n I M → α :=
  Quotient.lift (s := framingSetoid n I M) g hg

/-- The function `lift g hg` takes the value `g f` at the framed sphere of `f`. -/
@[simp]
theorem lift_mk {α : Sort*}
    (g : SmoothEmbedding (𝓡 n) I ∞ (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) M → α)
    (hg : ∀ f₁ f₂, FramingRel f₁ f₂ → g f₁ = g f₂) : lift g hg (mk f) = g f :=
  (rfl)

/-- The image in `M` of a framed sphere, the image of any of its parametrizations. -/
def range : FramedSphere n I M → Set M :=
  lift (fun f ↦ Set.range f) fun _ _ h ↦ h.range_eq

/-- The image of the framed sphere of `f` is the image of `f`. -/
@[simp]
theorem range_mk : (mk f).range = Set.range f := by
  rw [range, lift_mk]

end FramedSphere

end SymplecticGeometry

end
