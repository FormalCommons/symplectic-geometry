/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.ModelTransport.Remodel
public import SymplecticGeometry.Geometry.Symplectic.Sum.ProductNeighborhood
public import SymplecticGeometry.Geometry.Symplectic.Sum.RationalEllipticSurface.FibreTorus
import SymplecticGeometry.Geometry.Symplectic.Sum.RationalEllipticSurface.AffineCoordinate
import SymplecticGeometry.Geometry.Symplectic.Sum.RationalEllipticSurface.FibreComplement

/-!
# The rational elliptic surface on a real model, with a framed standard torus

To form the fibre sum of a symplectic four-manifold `X`, modelled on a real normed space `E`, with
the rational elliptic surface `E(1)` along Tau Ceti's standard torus
`T = ∀ i : Unit ⊕ Unit, AddCircle (p i)` of area `p inl * p inr`, both pieces must be charted on
the same model. This file moves `E(1)` to the model `𝓘(ℝ, E)` along a real linear isomorphism
`e : (Fin 2 → ℂ) ≃L[ℝ] E`, and gives on it the data that the sum uses on the side of `E(1)`.

* `rationalEllipticSurface.OnModel e`: the rational elliptic surface with its charts followed by
  `e`, as `SymplecticGeometry.Remodel` gives it. It is a compact, connected, Hausdorff, second
  countable smooth manifold over `𝓘(ℝ, E)`, and lives in `Type`, the universe of the surface.
  Since the fibre sum takes both pieces in one universe, `X` must lie in `Type` too.
* `rationalEllipticSurface.OnModel.symplecticForm e p`: the form of the surface rescaled by
  `torusScale p`, moved along the change of model; it is symplectic
  (`OnModel.isSymplectic_symplecticForm`).
* `rationalEllipticSurface.OnModel.torusEmbedding e p`: the embedding of `T` given by
  `fibreEmbedding ∘ torusDiffeomorph p` followed by the change of model. It pulls the form back to
  `TauCeti.torusSymplecticForm p` (`OnModel.mpullback_torusEmbedding_symplecticForm`, from
  `mpullback_fibreEmbedding_comp_torusDiffeomorph`) and has symplectic tangent images
  (`OnModel.hasSymplecticTangentImages_torusEmbedding`).
* `rationalEllipticSurface.OnModel.torusFraming e p`: a symplectic framing of that embedding,
  obtained from `fibreFraming` by rescaling the form (`SymplecticFraming.smul`), reparametrising
  the fibre by `torusDiffeomorph p` (`SymplecticFraming.compDiffeomorphOfBoundaryless`) and
  changing the model (`SymplecticFraming.transDiffeomorph`).
* `rationalEllipticSurface.OnModel.simplyConnectedSpace_compl_range_torusEmbedding`: the
  complement of the image of the torus is simply connected, from
  `simplyConnectedSpace_compl_range_fibreEmbedding`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.2.
* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995].
-/

public section

noncomputable section

open Set Module TauCeti
open scoped Manifold ContDiff ComplexManifold

namespace SymplecticGeometry.rationalEllipticSurface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (e : (Fin 2 → ℂ) ≃L[ℝ] E)

/-- The rational elliptic surface charted on the real normed space `E`: its charts, read as real
charts in `Fin 2 → ℂ`, followed by the real linear isomorphism `e : (Fin 2 → ℂ) ≃L[ℝ] E`
(`SymplecticGeometry.Remodel`). It has the points and the topology of the surface, and lives in
`Type`. -/
abbrev OnModel : Type := Remodel e.toDiffeomorph rationalEllipticSurface

namespace OnModel

-- The instances that the fibre sum asks of its pieces.
example : IsManifold 𝓘(ℝ, E) ∞ (OnModel e) := inferInstance
example : CompactSpace (OnModel e) := inferInstance
example : ConnectedSpace (OnModel e) := inferInstance
example : T2Space (OnModel e) := inferInstance
example : SecondCountableTopology (OnModel e) := inferInstance

end OnModel

variable (p : Unit ⊕ Unit → ℝ) [∀ i, Fact (0 < p i)]

/-- The Fermat cubic, reparametrised by `torusDiffeomorph p` as the standard torus, has symplectic
tangent images in the rational elliptic surface for `torusScale p` times its form. -/
theorem hasSymplecticTangentImages_fibreEmbedding_compDiffeomorph_torusDiffeomorph :
    (isSymplectic_symplecticForm.isNondegenerate.smul _ (torusScale_pos p).ne')
      |>.HasSymplecticTangentImages (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ))
        (fibreEmbedding.compDiffeomorphOfBoundaryless (torusDiffeomorph p) (by simp)) :=
  (SmoothEmbedding.hasSymplecticTangentImages_compDiffeomorphOfBoundaryless_iff fibreEmbedding
    (torusDiffeomorph p) (by simp) (by simp)).2
    ((isSymplectic_symplecticForm.isNondegenerate.hasSymplecticTangentImages_smul_iff _
      (torusScale_pos p).ne').2 hasSymplecticTangentImages_fibreEmbedding)

namespace OnModel

/-- The symplectic form of the rational elliptic surface on the model `E`: `torusScale p` times the
form of the surface, moved to `OnModel e` along the identity of the surface, read from the model
`Fin 2 → ℂ` to the model `E` (`SymplecticGeometry.remodelDiffeomorph`). For this form the fibre
over `[1 : 0]` has the area `p inl * p inr` of the standard torus. -/
def symplecticForm : SmoothTwoForm 𝓘(ℝ, E) (OnModel e) :=
  SmoothForm.mpullback (remodelDiffeomorph e.toDiffeomorph rationalEllipticSurface).symm
    (remodelDiffeomorph e.toDiffeomorph rationalEllipticSurface).symm.contMDiff
    (torusScale p • rationalEllipticSurface.symplecticForm)

theorem symplecticForm_def :
    symplecticForm e p =
      SmoothForm.mpullback (remodelDiffeomorph e.toDiffeomorph rationalEllipticSurface).symm
        (remodelDiffeomorph e.toDiffeomorph rationalEllipticSurface).symm.contMDiff
        (torusScale p • rationalEllipticSurface.symplecticForm) :=
  (rfl)

/-- Pulled back along the change of model `remodelDiffeomorph`, the form of `OnModel e` is
`torusScale p` times the form of the rational elliptic surface. -/
theorem mpullback_remodelDiffeomorph_symplecticForm :
    SmoothForm.mpullback (remodelDiffeomorph e.toDiffeomorph rationalEllipticSurface)
        (remodelDiffeomorph e.toDiffeomorph rationalEllipticSurface).contMDiff
        (symplecticForm e p) =
      torusScale p • rationalEllipticSurface.symplecticForm := by
  rw [symplecticForm_def]
  exact SmoothForm.mpullback_mpullback_symm _ _

/-- The form of the rational elliptic surface on the model `E` is symplectic. -/
theorem isSymplectic_symplecticForm : (symplecticForm e p).IsSymplectic :=
  ((remodelDiffeomorph e.toDiffeomorph rationalEllipticSurface).symm.isLocalDiffeomorph
    |>.isSymplectic_mpullback_iff
      (remodelDiffeomorph e.toDiffeomorph rationalEllipticSurface).symm.surjective).2
    (rationalEllipticSurface.isSymplectic_symplecticForm.smul _ (torusScale_pos p).ne')

include e in
/-- The standard torus `∀ i : Unit ⊕ Unit, AddCircle (p i)` has codimension two in
`OnModel e`. -/
theorem finrank_complex_eq_finrank_sub :
    finrank ℝ ℂ = finrank ℝ E - finrank ℝ (Unit ⊕ Unit → ℝ) := by
  rw [← e.toLinearEquiv.finrank_eq]
  simp [Module.finrank_pi_fintype]

variable [FiniteDimensional ℝ E]

/-- The standard torus `∀ i : Unit ⊕ Unit, AddCircle (p i)` embedded in the rational elliptic
surface on the model `E`: the diffeomorphism `torusDiffeomorph p` onto the Fermat cubic, followed
by the inclusion `fibreEmbedding` of the cubic as the fibre over `[1 : 0]` and by the change of
model `remodelDiffeomorph`. -/
def torusEmbedding :
    SmoothEmbedding (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) 𝓘(ℝ, E) ∞
      (∀ i, AddCircle (p i)) (OnModel e) :=
  (fibreEmbedding.compDiffeomorphOfBoundaryless (torusDiffeomorph p) (by simp)
    ).transDiffeomorphOfBoundaryless (remodelDiffeomorph e.toDiffeomorph _) (by simp)

theorem torusEmbedding_def :
    torusEmbedding e p =
      (fibreEmbedding.compDiffeomorphOfBoundaryless (torusDiffeomorph p) (by simp)
        ).transDiffeomorphOfBoundaryless (remodelDiffeomorph e.toDiffeomorph _) (by simp) :=
  (rfl)

/-- The embedded torus is `remodelDiffeomorph ∘ fibreEmbedding ∘ torusDiffeomorph p`. -/
@[simp]
theorem coe_torusEmbedding :
    ⇑(torusEmbedding e p) =
      remodelDiffeomorph e.toDiffeomorph _ ∘ fibreEmbedding ∘ torusDiffeomorph p := by
  rw [torusEmbedding_def, SmoothEmbedding.coe_transDiffeomorphOfBoundaryless,
    SmoothEmbedding.coe_compDiffeomorphOfBoundaryless]

/-- The image of the embedded torus is the fibre of the rational elliptic surface over `[1 : 0]`,
the image of `fibreEmbedding`, as a subset of `OnModel e`. -/
theorem range_torusEmbedding :
    range (torusEmbedding e p) =
      remodelHomeomorph e.toDiffeomorph _ '' range fibreEmbedding := by
  rw [torusEmbedding_def, SmoothEmbedding.coe_transDiffeomorphOfBoundaryless, range_comp,
    SmoothEmbedding.range_compDiffeomorphOfBoundaryless, coe_remodelDiffeomorph]

/-- The embedded torus pulls the form of `OnModel e` back to the standard symplectic form
`TauCeti.torusSymplecticForm p` of the torus. -/
theorem mpullback_torusEmbedding_symplecticForm :
    SmoothForm.mpullback (torusEmbedding e p) (torusEmbedding e p).contMDiff
      (symplecticForm e p) = torusSymplecticForm p := by
  rw [← mpullback_fibreEmbedding_comp_torusDiffeomorph p,
    ← mpullback_remodelDiffeomorph_symplecticForm e p, SmoothForm.mpullback_mpullback]
  exact SmoothForm.mpullback_congr _ _ (coe_torusEmbedding e p) _

/-- The embedded torus has symplectic tangent images for the form of `OnModel e`. -/
theorem hasSymplecticTangentImages_torusEmbedding :
    (isSymplectic_symplecticForm e p).isNondegenerate.HasSymplecticTangentImages
      (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) (torusEmbedding e p) := by
  rw [torusEmbedding_def, SmoothEmbedding.coe_transDiffeomorphOfBoundaryless]
  exact (SmoothTwoForm.IsNondegenerate.hasSymplecticTangentImages_diffeomorph_comp_iff
    (remodelDiffeomorph e.toDiffeomorph rationalEllipticSurface)
    (mpullback_remodelDiffeomorph_symplecticForm e p)).2
    (hasSymplecticTangentImages_fibreEmbedding_compDiffeomorph_torusDiffeomorph p)

/-- **The symplectic framing of the embedded torus.** The framing `fibreFraming` of the fibre over
`[1 : 0]`, made a framing for `torusScale p` times the form of the surface
(`SymplecticFraming.smul`), read along the diffeomorphism `torusDiffeomorph p` of the torus onto
the fibre (`SymplecticFraming.compDiffeomorphOfBoundaryless`), and moved along the change of model
(`SymplecticFraming.transDiffeomorph`). -/
def torusFraming :
    SymplecticFraming (hasSymplecticTangentImages_torusEmbedding e p)
      (finrank_complex_eq_finrank_sub e) :=
  ((fibreFraming.smul (torusScale_pos p)).compDiffeomorphOfBoundaryless (torusDiffeomorph p)
    (hasSymplecticTangentImages_fibreEmbedding_compDiffeomorph_torusDiffeomorph p)
    (by simp [Module.finrank_pi_fintype])).transDiffeomorph
    (remodelDiffeomorph e.toDiffeomorph _) (isSymplectic_symplecticForm e p).isNondegenerate
    (mpullback_remodelDiffeomorph_symplecticForm e p) (finrank_complex_eq_finrank_sub e)

/-- The complement of the embedded torus in `OnModel e` is simply connected. -/
instance simplyConnectedSpace_compl_range_torusEmbedding :
    SimplyConnectedSpace ↥(range (torusEmbedding e p))ᶜ := by
  rw [range_torusEmbedding, ← (remodelHomeomorph e.toDiffeomorph _).image_compl]
  exact (remodelHomeomorph e.toDiffeomorph _).isSimplyConnected_image.2
    simplyConnectedSpace_compl_range_fibreEmbedding

end OnModel

end SymplecticGeometry.rationalEllipticSurface

end
