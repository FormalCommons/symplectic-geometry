/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Contact.Basic
public import TauCeti.Geometry.Manifold.Boundary.Orientation
public import TauCeti.Geometry.Symplectic.Liouville.ContactType
public import TauCeti.Geometry.Symplectic.Manifold.Flat
import TauCeti.Geometry.Manifold.Boundary.Derivative
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import SymplecticGeometry.Geometry.Symplectic.Liouville.ContactType

/-!
# Strong fillings and their boundary contact form

A strong symplectic filling, in McDuff–Salamon's sense, is a compact symplectic manifold with
boundary `(W, σ)` with a Liouville vector field `Y`, `L_Y σ = σ`, defined near the boundary and
pointing out of `W` along it. Here `W` is modelled on Tau Ceti's half-space `𝓡∂ (n + 1)`, so that
its boundary `∂W` is a manifold over `EuclideanSpace ℝ (Fin n)` and outward vectors are
`TauCeti.IsOutwardPointing`. The field is taken global and smooth, and Liouville on an open set
`U` containing `∂W`; a field smooth only on `U` is cut off to a global one
(`SymplecticGeometry.IsStrongFilling.of_contMDiffOn`).

The boundary of a strong filling is of contact type, and it carries the contact form
`α = -ι^*(ι_Y σ)`, where `ι : ∂W → W` is the inclusion, with `dα = -ι^*σ`. These are the signs of
McDuff–Salamon: the Liouville primitive is `λ = -ι_Y σ`, with `dλ = -σ`, and `α = ι^*λ`.

## Main definitions

* `SymplecticGeometry.IsStrongFilling σ U Y`: `σ` is symplectic, `U` is an open neighbourhood of
  the boundary, `Y` is a smooth outward field, Liouville for `σ` on `U`.
* `SymplecticGeometry.fillingContactForm σ X`: the one-form `-ι^*(ι_X σ)` on the boundary, for a
  smooth vector field `X`.

## Main results

* `TauCeti.IsOutwardPointingField.isTransverseAlong_subtypeVal`: an outward field is transverse to
  the boundary.
* `SymplecticGeometry.IsStrongFilling.mono`: the open set may be shrunk to any smaller open
  neighbourhood of the boundary.
* `SymplecticGeometry.IsStrongFilling.of_contMDiffOn`: a field that is smooth only on `U` agrees,
  near the boundary, with the field of a strong filling.
* `SymplecticGeometry.IsStrongFilling.isContactType`: the boundary inclusion is of contact type,
  in Tau Ceti's sense, with primitive `ι_Y σ`.
* `SymplecticGeometry.IsStrongFilling.isContactForm_fillingContactForm` and
  `SymplecticGeometry.IsStrongFilling.mextDerivₗ_fillingContactForm`: `α` is a contact form with
  `dα = -ι^*σ`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Definition 3.5.38.
-/

public section

open Bundle Set TauCeti
open scoped Manifold ContDiff

namespace TauCeti

variable {n : ℕ} {W : Type*} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]

/-- An outward vector at a boundary point is not tangent to the boundary: it is not in the range
of the differential of the boundary inclusion. -/
theorem IsOutwardPointing.notMem_range_mfderiv_subtypeVal [IsManifold (𝓡∂ (n + 1)) 1 W]
    {x : (𝓡∂ (n + 1)).boundary W}
    {v : TangentSpace (𝓡∂ (n + 1)) (x : W)} (hv : IsOutwardPointing (x : W) v) :
    v ∉ (mfderiv (𝓡 n) (𝓡∂ (n + 1)) (Subtype.val : (𝓡∂ (n + 1)).boundary W → W) x).range := by
  rintro ⟨w, rfl⟩
  have h := hv.coordinate_deriv_neg
  rw [mfderiv_extChartAt_self, mfderiv_subtypeVal_boundary] at h
  -- The tangent space of the model is the model space, and `fromTangentSpace` is the identity.
  change euclideanHalfSpaceBoundaryParam n w 0 < 0 at h
  linarith [euclideanHalfSpaceBoundaryParam_apply_zero w]

/-- An outward field is transverse to the boundary. -/
theorem IsOutwardPointingField.isTransverseAlong_subtypeVal [IsManifold (𝓡∂ (n + 1)) ∞ W]
    {Y : (x : W) → TangentSpace (𝓡∂ (n + 1)) x} (hY : IsOutwardPointingField Y) :
    IsTransverseAlong (𝓡 n) Y (Subtype.val : (𝓡∂ (n + 1)).boundary W → W) :=
  isTransverseAlong_iff.2 fun x ↦ (hY.isOutwardPointing x.property).notMem_range_mfderiv_subtypeVal

end TauCeti

namespace SymplecticGeometry

variable {n : ℕ} {W : Type*} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  [IsManifold (𝓡∂ (n + 1)) ∞ W]

/-- The boundary of `W` is a smooth manifold over `EuclideanSpace ℝ (Fin n)`. -/
local instance : IsManifold (𝓡 n) ∞ ((𝓡∂ (n + 1)).boundary W) := isManifold_boundary W

/-- A **strong filling** structure on a manifold with boundary `W`: the two-form `σ` is
symplectic, `U` is an open set containing the boundary, and `Y` is a smooth vector field on `W`
pointing outward along the boundary and Liouville for `σ` on `U`, that is `L_Y σ = σ` there.
For compact `W` this is McDuff–Salamon's strong filling of its boundary; `U = univ` is a
Liouville domain. -/
structure IsStrongFilling (σ : SmoothTwoForm (𝓡∂ (n + 1)) W) (U : Set W)
    (Y : (x : W) → TangentSpace (𝓡∂ (n + 1)) x) : Prop where
  /-- The two-form is symplectic. -/
  isSymplectic : σ.IsSymplectic
  /-- The set on which the field is Liouville is open. -/
  isOpen : IsOpen U
  /-- The set on which the field is Liouville contains the boundary. -/
  boundary_subset : (𝓡∂ (n + 1)).boundary W ⊆ U
  /-- The field is smooth and points outward along the boundary. -/
  isOutwardPointingField : IsOutwardPointingField Y
  /-- The field is Liouville on `U`. -/
  mlieDerivForm_eq : ∀ x ∈ U, mlieDerivForm Y σ.val x = σ.val x

variable {σ : SmoothTwoForm (𝓡∂ (n + 1)) W} {U : Set W}
  {Y : (x : W) → TangentSpace (𝓡∂ (n + 1)) x}

/-- The defining characterization of a strong filling. -/
theorem isStrongFilling_iff :
    IsStrongFilling σ U Y ↔ σ.IsSymplectic ∧ IsOpen U ∧ (𝓡∂ (n + 1)).boundary W ⊆ U ∧
      IsOutwardPointingField Y ∧ ∀ x ∈ U, mlieDerivForm Y σ.val x = σ.val x :=
  ⟨fun h ↦ ⟨h.isSymplectic, h.isOpen, h.boundary_subset, h.isOutwardPointingField,
    h.mlieDerivForm_eq⟩, fun ⟨h₁, h₂, h₃, h₄, h₅⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅⟩⟩

namespace IsStrongFilling

/-- A strong filling restricts to any smaller open neighbourhood of the boundary. -/
theorem mono (h : IsStrongFilling σ U Y) {V : Set W} (hV : IsOpen V)
    (hbV : (𝓡∂ (n + 1)).boundary W ⊆ V) (hVU : V ⊆ U) : IsStrongFilling σ V Y :=
  ⟨h.isSymplectic, hV, hbV, h.isOutwardPointingField, fun x hx ↦ h.mlieDerivForm_eq x (hVU hx)⟩

/-- **Cutting off a Liouville field.** Let `σ` be symplectic and `Y` a vector field, smooth and
Liouville for `σ` on an open set `U` containing the boundary of `W`, and pointing outward along
the boundary. Then on some smaller open neighbourhood `V` of the boundary, `Y` agrees with the
field of a strong filling. -/
theorem of_contMDiffOn [T2Space W] [SigmaCompactSpace W] (hσ : σ.IsSymplectic) (hU : IsOpen U)
    (hbU : (𝓡∂ (n + 1)).boundary W ⊆ U)
    (hY : ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞ (T% Y) U)
    (hout : ∀ x ∈ (𝓡∂ (n + 1)).boundary W, IsOutwardPointing x (Y x))
    (hYσ : ∀ x ∈ U, mlieDerivForm Y σ.val x = σ.val x) :
    ∃ (V : Set W) (Y' : (x : W) → TangentSpace (𝓡∂ (n + 1)) x),
      V ⊆ U ∧ EqOn Y' Y V ∧ IsStrongFilling σ V Y' := by
  have hb : IsClosed ((𝓡∂ (n + 1)).boundary W) := (𝓡∂ (n + 1)).isClosed_boundary one_ne_zero
  -- A smooth function `f` with `f = 0` exactly off `U` and `f = 1` exactly on `∂W`.
  obtain ⟨f, hf, -, hf0, hf1⟩ := exists_contMDiff_zero_iff_one_iff_of_isClosed (𝓡∂ (n + 1))
    (n := (⊤ : ℕ∞)) hU.isClosed_compl hb (disjoint_compl_left_iff_subset.2 hbU)
  -- A smooth cutoff `g`, zero where `f ≤ 1/2` and one where `3/4 ≤ f`.
  obtain ⟨g, hg, -, hg0, hg1⟩ := exists_contMDiff_zero_iff_one_iff_of_isClosed (𝓡∂ (n + 1))
    (n := (⊤ : ℕ∞)) (isClosed_le hf.continuous continuous_const)
    (isClosed_le continuous_const hf.continuous)
    (disjoint_left.2 fun x (h₁ : f x ≤ 1 / 2) (h₂ : 3 / 4 ≤ f x) ↦ by linarith)
  have hfU {x : W} (hx : 1 / 2 ≤ f x) : x ∈ U := by
    by_contra h
    have := (hf0 x).1 h
    linarith
  have htsupp : tsupport g ⊆ U := by
    refine (closure_minimal (fun x hx ↦ ?_) (isClosed_le continuous_const hf.continuous)).trans
      fun x hx ↦ hfU hx
    by_contra h
    exact hx ((hg0 x).1 (not_le.1 h).le)
  set V : Set W := {x | 3 / 4 < f x}
  have hVo : IsOpen V := isOpen_lt continuous_const hf.continuous
  have hVU : V ⊆ U := fun x (hx : 3 / 4 < f x) ↦ hfU (by linarith)
  have hgV : ∀ x ∈ V, g x = 1 := fun x (hx : 3 / 4 < f x) ↦ (hg1 x).1 hx.le
  have hbV : (𝓡∂ (n + 1)).boundary W ⊆ V := fun x hx ↦ by
    change 3 / 4 < f x
    rw [(hf1 x).1 hx]
    norm_num
  have hYV : EqOn (g • Y) Y V := fun x hx ↦ by
    rw [Pi.smul_apply', hgV x hx, one_smul]
  have hY' : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞ (T% (g • Y)) :=
    hg.contMDiffOn.smul_section_of_tsupport hU htsupp hY
  refine ⟨V, g • Y, hVU, hYV, hσ, hVo, hbV,
    .intro hY' fun x hx ↦ by rw [hYV (hbV hx)]; exact hout x hx, fun x hx ↦ ?_⟩
  have hYx : MDifferentiableAt (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent (T% Y) x :=
      ((hY.contMDiffAt (hU.mem_nhds (hVU hx))).mdifferentiableAt (by simp))
  -- Cartan's formula `L_Z σ = d(ι_Z σ)` at `x`, for the closed form `σ`, turns the claim into
  -- the equality of `d(ι_(g • Y) σ)` and `d(ι_Y σ)` at `x`.
  have hσx := (σ.contMDiff x).mdifferentiableAt (n := ∞) (by simp)
  have hdσ := congrFun ((SmoothForm.isClosed_def σ).1 hσ.isClosed) x
  rw [mlieDerivForm_eq_mextDeriv_interior_apply hσx ((hY' x).mdifferentiableAt (by simp)) hdσ,
    ← hYσ x (hVU hx), mlieDerivForm_eq_mextDeriv_interior_apply hσx hYx hdσ]
  refine mextDeriv_congr_of_eventuallyEq ?_
  filter_upwards [hVo.mem_nhds hx] with y hy
  ext v
  simp [RoughForm.interior_apply, hYV hy]

/-- **The boundary of a strong filling is of contact type.** The inclusion of the boundary is of
contact type for `σ`, in the sense of Tau Ceti's `TauCeti.IsContactType`, with primitive the
interior product `ι_Y σ`. -/
theorem isContactType (h : IsStrongFilling σ U Y) :
    IsContactType (𝓡 n) σ.val (σ.interiorₗ ⟨Y, h.isOutwardPointingField.contMDiff⟩ :
      RoughForm (𝓡∂ (n + 1)) W ℝ 1) (Subtype.val : (𝓡∂ (n + 1)).boundary W → W) := by
  rw [SmoothTwoForm.coe_interiorₗ]
  exact isContactType_interior (σ.isSmoothForm.of_le (by simp))
    ((SmoothForm.isClosed_def σ).1 h.isSymplectic.isClosed) h.isOpen
    (by simpa using h.boundary_subset) h.isOutwardPointingField.contMDiff.contMDiffOn
    h.mlieDerivForm_eq h.isOutwardPointingField.isTransverseAlong_subtypeVal

end IsStrongFilling

/-- The **contact form of a filling** along its boundary: for a smooth vector field `X` on `W`,
the one-form `-ι^*(ι_X σ)` on the boundary, where `ι : ∂W → W` is the inclusion. For the field
of a strong filling it is a contact form
(`SymplecticGeometry.IsStrongFilling.isContactForm_fillingContactForm`). -/
noncomputable def fillingContactForm (σ : SmoothTwoForm (𝓡∂ (n + 1)) W)
    (X : Cₛ^∞⟮𝓡∂ (n + 1); EuclideanSpace ℝ (Fin (n + 1)), TangentSpace (𝓡∂ (n + 1)) (M := W)⟯) :
    SmoothForm (𝓡 n) ((𝓡∂ (n + 1)).boundary W) ℝ 1 :=
  -SmoothForm.mpullback Subtype.val (isSmoothEmbedding_subtypeVal_boundary W).contMDiff
    (σ.interiorₗ X)

theorem fillingContactForm_def (σ : SmoothTwoForm (𝓡∂ (n + 1)) W)
    (X : Cₛ^∞⟮𝓡∂ (n + 1); EuclideanSpace ℝ (Fin (n + 1)), TangentSpace (𝓡∂ (n + 1)) (M := W)⟯) :
    fillingContactForm σ X =
      -SmoothForm.mpullback Subtype.val (isSmoothEmbedding_subtypeVal_boundary W).contMDiff
        (σ.interiorₗ X) :=
  (rfl)

/-- The underlying rough form of `fillingContactForm σ X` is `-ι^*(ι_X σ)`. -/
@[simp]
theorem coe_fillingContactForm (σ : SmoothTwoForm (𝓡∂ (n + 1)) W)
    (X : Cₛ^∞⟮𝓡∂ (n + 1); EuclideanSpace ℝ (Fin (n + 1)), TangentSpace (𝓡∂ (n + 1)) (M := W)⟯) :
    (fillingContactForm σ X : RoughForm (𝓡 n) ((𝓡∂ (n + 1)).boundary W) ℝ 1) =
      -mpullback (𝓡 n) (𝓡∂ (n + 1)) Subtype.val (RoughForm.interior X σ.val) := by
  rw [fillingContactForm_def, NegMemClass.coe_neg, SmoothForm.coe_mpullback,
    SmoothTwoForm.coe_interiorₗ]

namespace IsStrongFilling

/-- **The contact form of a strong filling.** For a strong filling, `-ι^*(ι_Y σ)` is a contact
form on the boundary. -/
theorem isContactForm_fillingContactForm (h : IsStrongFilling σ U Y) :
    (fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩).IsContactForm := by
  rw [fillingContactForm_def, SmoothForm.isContactForm_neg_iff]
  exact h.isContactType.isContactForm_mpullback h.isSymplectic.isNondegenerate
    (isSmoothEmbedding_subtypeVal_boundary W).contMDiff
    ((isSmoothEmbedding_subtypeVal_boundary (k := ∞) W).isImmersion.mfderiv_injective (by simp))
    (by simp)

/-- For a strong filling, the contact form `α = -ι^*(ι_Y σ)` of the boundary has
`dα = -ι^*σ`. -/
theorem mextDerivₗ_fillingContactForm (h : IsStrongFilling σ U Y) :
    mextDerivₗ (𝓡 n) 1 (fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩) =
      -SmoothForm.mpullback Subtype.val (isSmoothEmbedding_subtypeVal_boundary W).contMDiff σ := by
  obtain ⟨V, -, hbV, hdα, -⟩ := isContactType_iff.1 h.isContactType
  rw [fillingContactForm_def, map_neg, SmoothForm.mextDerivₗ_mpullback]
  congr 1
  refine Subtype.ext (funext fun x ↦ ?_)
  ext v
  rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback, mpullback_apply, mpullback_apply,
    mextDerivₗ_apply, hdα _ (hbV (mem_range_self x))]

end IsStrongFilling

end SymplecticGeometry

end
