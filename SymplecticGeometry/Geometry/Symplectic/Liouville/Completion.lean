/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.End
import SymplecticGeometry.Geometry.Contact.Symplectization.Basic
public import SymplecticGeometry.Geometry.Symplectic.Liouville.Filling
public import TauCeti.Geometry.Manifold.VectorField.ModelChart
public import TauCeti.Geometry.Manifold.VectorField.Prod
import TauCeti.Geometry.Manifold.IsManifold.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod
import SymplecticGeometry.Geometry.Manifold.VectorField.Pullback
import SymplecticGeometry.Geometry.Manifold.VectorField.Prod
import TauCeti.Topology.FiberBundle.Separation

/-!
# The completion of a strong filling: its symplectic form, primitive and Liouville field

Let `(W, σ, U, Y)` be a strong filling (`SymplecticGeometry.IsStrongFilling`) with compact
boundary `∂W`, with Liouville primitive `λ = -ι_Y σ` near `∂W` and boundary contact form
`α = fillingContactForm σ Y`. Following McDuff–Salamon (the completion on p. 148), its completion
`Ŵ` is `W` with the half-cylinder `[0, ∞) × ∂W` attached along the boundary, carrying the
two-form `ω̂` equal to `σ` on `W` and to the symplectization form `-d(e^s α)` on the end, the
one-form `λ̂` equal to `λ` on `W` and to `e^s α` on the end, and the vector field `Ŷ` equal to `Y`
on `W` and to `∂_s` on the end.

The end is attached by the Liouville collar of `IsStrongFilling.exists_liouvilleCollar`, chosen
once: its width `ε`, its map `Φ : ℝ × ∂W → W`, whose lines `s ↦ Φ (s, x)` are the integral curves
of `Y` on `(-ε, 0]` ending at the boundary points, and its smooth collar `c`. The completion is the
manifold `c.WithEnd` of `Boundary/Collar/End.lean`, and the end is parametrized by the Liouville
time: `completionEnd (s, x)` is the point of the end at time `s / ε` of `c.WithEnd`, so that for
`s ∈ (-ε, 0]` it is the point `Φ (s, x)` of `W`.

The form `ω̂` is defined pointwise: on the image of `(-ε, ∞) × ∂W`, where the end map is an
injective local diffeomorphism, it is `-d(e^s α)` read through the inverse of its differential;
elsewhere, on the image of the interior of `W`, it is `σ` read through the inverse of the
differential of the inclusion. The two descriptions agree on the overlap, the image of
`(-ε, 0) × ∂W`, because `Φ` pulls `σ` back to `-d(e^s α)` there; so `ω̂` pulls back to `σ` at
interior points of `W` and to `-d(e^s α)` on `(-ε, ∞) × ∂W`. Its smoothness follows from these
pullbacks along local diffeomorphisms (`IsLocalDiffeomorphAt.contMDiffAt_mpullback_form_iff`),
and the pullback to all of `W` from the density of the interior
(`TauCeti.SmoothBundleForm.eq_of_forall_mem_dense`). The primitive `λ̂` is built in the same way,
and the field `Ŷ` likewise from `∂_s` and `Y`, which agree on the overlap because the lines of `Φ`
are integral curves of `Y`. Reading a form through the inverse of a differential is what Tau
Ceti's `TauCeti.RoughForm.descendedForm` does through a right inverse; the field is identified
along the boundary of `W` by the argument of `TauCeti.SmoothBundleForm.eq_of_forall_mem_dense`,
applied to continuous maps into the tangent bundle.

Each point of the completion is on the end `(-ε, ∞) × ∂W` or is an interior point of `W`, and
both maps are local diffeomorphisms there. Closedness, nondegeneracy, the Liouville equation
`L_Ŷ ω̂ = ω̂`, the identity `ι_Ŷ ω̂ = -λ̂` and, for a Liouville domain, `dλ̂ = -ω̂` are therefore
checked on the two pieces, through the pointwise transfer lemmas of
`SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph`
(`IsLocalDiffeomorphAt.mextDeriv_apply_eq_iff` and its neighbours). On the end they are Tau
Ceti's results on the symplectization
(`TauCeti.SmoothForm.IsContactForm.isSymplectic_mextDerivₗ_symplectization`,
`TauCeti.SmoothForm.isLiouvilleVectorField_symplectization`,
`TauCeti.SmoothForm.interior_mextDeriv_symplectization`); on `W` they are the hypotheses on
`(σ, Y)`.

## Main definitions

* `SymplecticGeometry.IsStrongFilling.collarWidth`, `collarFlow`, `collar`: the chosen Liouville
  collar.
* `SymplecticGeometry.IsStrongFilling.Completion`: the completion, a boundaryless manifold over
  `EuclideanSpace ℝ (Fin (n + 1))`, with `toCompletion : W → h.Completion` and the end map
  `completionEnd : ℝ × ∂W → h.Completion`.
* `SymplecticGeometry.IsStrongFilling.completionForm`, `completionPrimitive`, `completionField`:
  the form `ω̂`, the primitive `λ̂` and the field `Ŷ` of the completion.

## Main results

* `completionEnd_zero`, `completionEnd_eq_toCompletion`: the end is attached along `∂W` by `Φ`.
* `mpullback_toCompletion_completionForm`, `mpullback_completionEnd_completionForm`: `ω̂` is `σ`
  on `W` and `-d(e^s α)` on `(-ε, ∞) × ∂W`.
* `mpullback_toCompletion_completionPrimitive`, `mpullback_completionEnd_completionPrimitive`:
  `λ̂` is `-ι_Y σ` on `W` and `e^s α` on `(-ε, ∞) × ∂W`.
* `contMDiff_completionField`, `mfderiv_toCompletion_apply`, `mfderiv_completionEnd_apply`: `Ŷ`
  is smooth, and is the image of `Y` under the inclusion and of `∂_s` under the end map.
* `isSymplectic_completionForm`: `ω̂` is symplectic.
* `mlieDerivForm_completionField_of_mem`: `L_Ŷ ω̂ = ω̂` at each point of the image of `U` and
  of the end; `interior_completionField_completionForm`: `ι_Ŷ ω̂ = -λ̂`.
* `mextDerivₗ_completionPrimitive`, `isLiouvilleVectorField_completionField`: for a Liouville
  domain, `dλ̂ = -ω̂` and `Ŷ` is a Liouville field of `ω̂` everywhere.
* `isSymplectic_completionForm_and_extends`: the completion of a strong filling, collected in one
  statement.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  the completion on p. 148.
-/

public section

open Bundle Set Function TauCeti
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

variable {n : ℕ} {W : Type*} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  [IsManifold (𝓡∂ (n + 1)) ∞ W] [T2Space W] [CompactSpace ((𝓡∂ (n + 1)).boundary W)]

/-- The boundary of `W` is a smooth manifold over `EuclideanSpace ℝ (Fin n)`. -/
local instance : IsManifold (𝓡 n) ∞ ((𝓡∂ (n + 1)).boundary W) := isManifold_boundary W

variable {σ : SmoothTwoForm (𝓡∂ (n + 1)) W} {U : Set W}
  {Y : (x : W) → TangentSpace (𝓡∂ (n + 1)) x}

namespace IsStrongFilling

/-- The width `ε` of the Liouville collar of a strong filling chosen for its completion. -/
noncomputable def collarWidth (h : IsStrongFilling σ U Y) : ℝ :=
  h.exists_liouvilleCollar.choose

/-- The map `Φ : ℝ × ∂W → W` of the Liouville collar chosen for the completion: `s ↦ Φ (s, x)`
is the integral curve of `Y` on `(-ε, 0]` that ends at the boundary point `x`. -/
noncomputable def collarFlow (h : IsStrongFilling σ U Y) : ℝ × (𝓡∂ (n + 1)).boundary W → W :=
  h.exists_liouvilleCollar.choose_spec.choose

/-- The smooth collar chosen for the completion, whose normal lines are the lines of
`h.collarFlow` run at speed `h.collarWidth`. -/
noncomputable def collar (h : IsStrongFilling σ U Y) : SmoothCollar n ∞ W :=
  h.exists_liouvilleCollar.choose_spec.choose_spec.choose

private theorem collar_spec (h : IsStrongFilling σ U Y) :
    0 < h.collarWidth ∧ (∀ x, h.collarFlow (0, x) = x) ∧
      (∀ x, IsMIntegralCurveOn (fun s ↦ h.collarFlow (s, x)) Y (Ioc (-h.collarWidth) 0)) ∧
      (∀ q, h.collar q =
        h.collarFlow (-h.collarWidth * (q.2 : EuclideanHalfSpace 1).val 0, q.1)) ∧
      range h.collar ⊆ U ∧
      (∀ p ∈ Ioo (-h.collarWidth) 0 ×ˢ univ,
        mpullback (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) h.collarFlow
          (-σ.interiorₗ ⟨Y, h.isOutwardPointingField.contMDiff⟩).val p =
        (fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩).symplectization.val p) ∧
      ∀ p ∈ Ioo (-h.collarWidth) 0 ×ˢ univ,
        mpullback (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) h.collarFlow σ.val p =
          (mextDerivₗ (𝓘(ℝ).prod (𝓡 n)) 1
            (-fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩).symplectization).val
              p :=
  h.exists_liouvilleCollar.choose_spec.choose_spec.choose_spec

/-- The width of the chosen collar is positive. -/
theorem collarWidth_pos (h : IsStrongFilling σ U Y) : 0 < h.collarWidth := h.collar_spec.1

/-- The lines of the chosen collar end on the boundary: `Φ (0, x) = x`. -/
@[simp] theorem collarFlow_zero (h : IsStrongFilling σ U Y) (x : (𝓡∂ (n + 1)).boundary W) :
    h.collarFlow (0, x) = x :=
  h.collar_spec.2.1 x

/-- The lines `s ↦ Φ (s, x)` of the chosen collar are integral curves of `Y` on `(-ε, 0]`. -/
theorem isMIntegralCurveOn_collarFlow (h : IsStrongFilling σ U Y)
    (x : (𝓡∂ (n + 1)).boundary W) :
    IsMIntegralCurveOn (fun s ↦ h.collarFlow (s, x)) Y (Ioc (-h.collarWidth) 0) :=
  h.collar_spec.2.2.1 x

/-- The normal lines of the chosen collar are the lines of `Φ` run at speed `ε`:
`c (x, t) = Φ (-ε t, x)`. -/
theorem collar_apply (h : IsStrongFilling σ U Y)
    (q : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace.normalIioOpens 1) :
    h.collar q = h.collarFlow (-h.collarWidth * (q.2 : EuclideanHalfSpace 1).val 0, q.1) :=
  h.collar_spec.2.2.2.1 q

/-- The chosen collar lies in the set on which `Y` is Liouville. -/
theorem range_collar_subset (h : IsStrongFilling σ U Y) : range h.collar ⊆ U :=
  h.collar_spec.2.2.2.2.1

/-- On `(-ε, 0) × ∂W`, the chosen collar map pulls the Liouville primitive `λ = -ι_Y σ` back to
`e^s α`. -/
theorem mpullback_collarFlow_neg_interiorₗ (h : IsStrongFilling σ U Y) :
    ∀ p ∈ Ioo (-h.collarWidth) 0 ×ˢ univ,
      mpullback (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) h.collarFlow
          (-σ.interiorₗ ⟨Y, h.isOutwardPointingField.contMDiff⟩).val p =
        (fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩).symplectization.val p :=
  h.collar_spec.2.2.2.2.2.1

/-- On `(-ε, 0) × ∂W`, the chosen collar map pulls `σ` back to `-d(e^s α)`. -/
theorem mpullback_collarFlow (h : IsStrongFilling σ U Y) :
    ∀ p ∈ Ioo (-h.collarWidth) 0 ×ˢ univ,
      mpullback (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) h.collarFlow σ.val p =
        (mextDerivₗ (𝓘(ℝ).prod (𝓡 n)) 1
          (-fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩).symplectization).val
            p :=
  h.collar_spec.2.2.2.2.2.2

/-- The collar map is smooth on `(-ε, 0) × ∂W`. -/
theorem contMDiffOn_collarFlow (h : IsStrongFilling σ U Y) :
    ContMDiffOn (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) ∞ h.collarFlow
      (Ioo (-h.collarWidth) 0 ×ˢ univ) :=
  SmoothCollar.contMDiffOn_of_forall_apply_eq h.collarWidth_pos h.collar_apply

/-- At times in `(-ε, 0)` the lines of the collar map lie in the interior of `W`. -/
theorem collarFlow_mem_interior (h : IsStrongFilling σ U Y) {s : ℝ}
    (hs : s ∈ Ioo (-h.collarWidth) 0) (x : (𝓡∂ (n + 1)).boundary W) :
    h.collarFlow (s, x) ∈ (𝓡∂ (n + 1)).interior W :=
  (h.isMIntegralCurveOn_collarFlow x).mem_interior_of_isOutwardPointing
    (fun _ hy ↦ h.isOutwardPointingField.isOutwardPointing hy)
    (Filter.mem_of_superset (Ioo_mem_nhds hs.1 hs.2) Ioo_subset_Ioc_self)

/-! ### The completion as a manifold -/

/-- The **completion** `Ŵ` of a strong filling: `W` with the end `[0, ∞) × ∂W` attached along
its boundary by the chosen collar, a boundaryless manifold over `EuclideanSpace ℝ (Fin (n + 1))`.
-/
-- Exposed so that `toCompletion_def` and `completionEnd_def` can state the bodies of those maps,
-- which land in `h.collar.WithEnd`.
@[expose] noncomputable def Completion (h : IsStrongFilling σ U Y) : Type _ := h.collar.WithEnd

variable (h : IsStrongFilling σ U Y)

noncomputable instance : TopologicalSpace h.Completion :=
  inferInstanceAs (TopologicalSpace h.collar.WithEnd)

noncomputable instance : T2Space h.Completion := inferInstanceAs (T2Space h.collar.WithEnd)

noncomputable instance : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) h.Completion :=
  inferInstanceAs (ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) h.collar.WithEnd)

noncomputable instance : IsManifold (𝓡 (n + 1)) ∞ h.Completion :=
  inferInstanceAs (IsManifold (𝓡 (n + 1)) ∞ h.collar.WithEnd)

/-- The inclusion of `W` in its completion. -/
noncomputable def toCompletion : W → h.Completion := SmoothCollar.WithEnd.inclusion h.collar

theorem toCompletion_def : h.toCompletion = SmoothCollar.WithEnd.inclusion h.collar := (rfl)

/-- The end of the completion in the Liouville time `s`: the point `(s, x)` of the end, for
`s > -ε`; its values for `s ≤ -ε` are junk. -/
noncomputable def completionEnd (p : ℝ × (𝓡∂ (n + 1)).boundary W) : h.Completion :=
  SmoothCollar.WithEnd.endMap h.collar (p.1 / h.collarWidth, p.2)

theorem completionEnd_def (p : ℝ × (𝓡∂ (n + 1)).boundary W) :
    h.completionEnd p = SmoothCollar.WithEnd.endMap h.collar (p.1 / h.collarWidth, p.2) := (rfl)

/-- The inclusion of `W` in its completion is smooth. -/
theorem contMDiff_toCompletion : ContMDiff (𝓡∂ (n + 1)) (𝓡 (n + 1)) ∞ h.toCompletion := by
  rw [toCompletion_def]
  exact SmoothCollar.WithEnd.contMDiff_inclusion h.collar

/-- The inclusion of `W` in its completion is injective. -/
theorem injective_toCompletion : Injective h.toCompletion := by
  rw [toCompletion_def]
  exact Function.LeftInverse.injective (SmoothCollar.WithEnd.retraction_inclusion h.collar)

/-- At interior points of `W`, the inclusion in the completion is a local diffeomorphism. -/
theorem isLocalDiffeomorphAt_toCompletion {p : W} (hp : p ∈ (𝓡∂ (n + 1)).interior W) :
    IsLocalDiffeomorphAt (𝓡∂ (n + 1)) (𝓡 (n + 1)) ∞ h.toCompletion p := by
  rw [toCompletion_def]
  exact SmoothCollar.WithEnd.isLocalDiffeomorphAt_inclusion h.collar hp

/-- The end starts at the boundary: `(0, x)` is the boundary point `x` of `W`. -/
@[simp] theorem completionEnd_zero (x : (𝓡∂ (n + 1)).boundary W) :
    h.completionEnd (0, x) = h.toCompletion x := by
  rw [completionEnd_def, zero_div, toCompletion_def, SmoothCollar.WithEnd.endMap_zero]

/-- For `s ∈ (-ε, 0]`, the point `(s, x)` of the end is the point `Φ (s, x)` of `W`. -/
theorem completionEnd_eq_toCompletion {s : ℝ} (hs : s ∈ Ioc (-h.collarWidth) 0)
    (x : (𝓡∂ (n + 1)).boundary W) :
    h.completionEnd (s, x) = h.toCompletion (h.collarFlow (s, x)) := by
  have hε := h.collarWidth_pos
  have hr : -s / h.collarWidth < 1 := by rw [div_lt_one hε]; linarith [hs.1]
  have h1 := SmoothCollar.WithEnd.endMap_neg_eq_inclusion h.collar x
    (EuclideanHalfSpace.normalIioRay ⟨-s / h.collarWidth, hr⟩)
  have hval : ((EuclideanHalfSpace.normalIioRay ⟨-s / h.collarWidth, hr⟩ :
      EuclideanHalfSpace.normalIioOpens 1) : EuclideanHalfSpace 1).val 0 = -s / h.collarWidth := by
    rw [EuclideanHalfSpace.normalIioRay_coe_apply,
      max_eq_left (div_nonneg (neg_nonneg.2 hs.2) hε.le)]
  rw [hval, show -(-s / h.collarWidth) = s / h.collarWidth by ring,
    SmoothCollar.apply_normalIioRay_eq hε h.collar_apply hs] at h1
  rw [completionEnd_def, h1, toCompletion_def]

/-- The rescaling `(s, x) ↦ (s / ε, x)` from the Liouville time to the time of the end. -/
private theorem isLocalDiffeomorph_scale :
    IsLocalDiffeomorph (𝓘(ℝ).prod (𝓡 n)) (𝓘(ℝ).prod (𝓡 n)) ∞
      (fun p : ℝ × (𝓡∂ (n + 1)).boundary W ↦ (p.1 / h.collarWidth, p.2)) := by
  have hε := h.collarWidth_pos.ne'
  let e : ℝ ≃L[ℝ] ℝ :=
    (LinearEquiv.smulOfNeZero ℝ ℝ h.collarWidth⁻¹ (inv_ne_zero hε)).toContinuousLinearEquiv
  have he : ⇑e.toDiffeomorph = fun s ↦ s / h.collarWidth := by
    funext s
    simp [e, div_eq_inv_mul]
  have := e.toDiffeomorph.isLocalDiffeomorph.prodMap
    (isLocalDiffeomorph_id (I := 𝓡 n) (M := (𝓡∂ (n + 1)).boundary W))
  rwa [he, Prod.map_def] at this

/-- On `(-ε, ∞) × ∂W`, the end map is a local diffeomorphism. -/
theorem isLocalDiffeomorphOn_completionEnd :
    IsLocalDiffeomorphOn (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) ∞ h.completionEnd
      (Ioi (-h.collarWidth) ×ˢ univ) := by
  rintro ⟨⟨s, x⟩, hs, -⟩
  have hε := h.collarWidth_pos
  have hs' : s / h.collarWidth ∈ Ioi (-1 : ℝ) := by
    rw [mem_Ioi, lt_div_iff₀ hε]; simpa using hs
  have hend : h.completionEnd = SmoothCollar.WithEnd.endMap h.collar ∘
      fun p : ℝ × (𝓡∂ (n + 1)).boundary W ↦ (p.1 / h.collarWidth, p.2) :=
    funext h.completionEnd_def
  rw [hend]
  exact (h.isLocalDiffeomorph_scale (s, x)).comp
    (hg := SmoothCollar.WithEnd.isLocalDiffeomorphOn_endMap
    h.collar ⟨(s / h.collarWidth, x), hs', trivial⟩)

/-- On `(-ε, ∞) × ∂W`, the end map is smooth. -/
theorem contMDiffOn_completionEnd :
    ContMDiffOn (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) ∞ h.completionEnd
      (Ioi (-h.collarWidth) ×ˢ univ) :=
  h.isLocalDiffeomorphOn_completionEnd.contMDiffOn

/-- On `(-ε, ∞) × ∂W`, the end map is injective. -/
theorem injOn_completionEnd : InjOn h.completionEnd (Ioi (-h.collarWidth) ×ˢ univ) := by
  rintro ⟨s, x⟩ ⟨hs, -⟩ ⟨s', x'⟩ ⟨hs', -⟩ heq
  have hε := h.collarWidth_pos
  have hm : ∀ {r : ℝ}, r ∈ Ioi (-h.collarWidth) → r / h.collarWidth ∈ Ioi (-1 : ℝ) :=
    fun hr ↦ by rw [mem_Ioi, lt_div_iff₀ hε]; simpa using hr
  rw [completionEnd_def, completionEnd_def] at heq
  have := SmoothCollar.WithEnd.injOn_endMap h.collar ⟨hm hs, trivial⟩ ⟨hm hs', trivial⟩ heq
  simp only [Prod.mk.injEq] at this
  rw [div_left_inj₀ hε.ne'] at this
  rw [this.1, this.2]

/-- The completion is the union of `W` and of the open end `(0, ∞) × ∂W`. -/
theorem range_toCompletion_union :
    range h.toCompletion ∪ h.completionEnd '' (Ioi 0 ×ˢ univ) = univ := by
  have hε := h.collarWidth_pos
  refine eq_univ_of_forall fun z ↦ ?_
  rcases SmoothCollar.WithEnd.exists_eq_inclusion_or_endMap h.collar z with
    ⟨p, rfl⟩ | ⟨s, x, hs, rfl⟩
  · exact Or.inl ⟨p, by rw [toCompletion_def]⟩
  · refine Or.inr ⟨(s * h.collarWidth, x), ⟨mul_pos hs hε, trivial⟩, ?_⟩
    rw [completionEnd_def, mul_div_cancel_right₀ _ hε.ne']

/-- `W` and the open end `(0, ∞) × ∂W` are disjoint in the completion. -/
theorem disjoint_range_toCompletion_completionEnd_image :
    Disjoint (range h.toCompletion) (h.completionEnd '' (Ioi 0 ×ˢ univ)) := by
  rw [toCompletion_def]
  refine (SmoothCollar.WithEnd.disjoint_range_inclusion_endMap_image h.collar).mono_right ?_
  rintro _ ⟨⟨s, x⟩, ⟨hs, -⟩, rfl⟩
  exact ⟨(s / h.collarWidth, x), ⟨div_pos hs h.collarWidth_pos, trivial⟩,
    (h.completionEnd_def (s, x)).symm⟩

/-- A point of the end `(-ε, ∞) × ∂W` that is the image of an interior point `p` of `W` has
`s ∈ (-ε, 0)`, and `p = Φ (s, x)`. -/
private theorem mem_Ioo_and_eq_collarFlow {p : W} (hp : p ∈ (𝓡∂ (n + 1)).interior W)
    {q : ℝ × (𝓡∂ (n + 1)).boundary W} (hq : q ∈ Ioi (-h.collarWidth) ×ˢ univ)
    (hpq : h.completionEnd q = h.toCompletion p) :
    q ∈ Ioo (-h.collarWidth) 0 ×ˢ univ ∧ p = h.collarFlow q := by
  obtain ⟨s, x⟩ := q
  rcases lt_or_ge 0 s with hs | hs
  · exact absurd ⟨(s, x), ⟨hs, trivial⟩, hpq⟩
      (Set.disjoint_left.1 h.disjoint_range_toCompletion_completionEnd_image ⟨p, rfl⟩)
  have hpΦ := h.injective_toCompletion ((h.completionEnd_eq_toCompletion ⟨hq.1, hs⟩ x).symm.trans
    hpq)
  rcases hs.lt_or_eq with hs | rfl
  · exact ⟨⟨⟨hq.1, hs⟩, trivial⟩, hpΦ.symm⟩
  · rw [collarFlow_zero] at hpΦ
    exact absurd (hpΦ ▸ x.property) (Set.disjoint_left.1
      (𝓡∂ (n + 1)).disjoint_interior_boundary hp)

/-! ### The collar in the completion -/

/-- On `(-ε, 0) × ∂W`, the end map is the collar map followed by the inclusion of `W`. -/
private theorem completionEnd_eventuallyEq {q : ℝ × (𝓡∂ (n + 1)).boundary W}
    (hq : q ∈ Ioo (-h.collarWidth) 0 ×ˢ univ) :
    h.completionEnd =ᶠ[𝓝 q] h.toCompletion ∘ h.collarFlow :=
  Filter.eventually_of_mem ((isOpen_Ioo.prod isOpen_univ).mem_nhds hq) fun r hr ↦
    h.completionEnd_eq_toCompletion ⟨hr.1.1, hr.1.2.le⟩ r.2

private theorem mdifferentiableAt_collarFlow {q : ℝ × (𝓡∂ (n + 1)).boundary W}
    (hq : q ∈ Ioo (-h.collarWidth) 0 ×ˢ univ) :
    MDifferentiableAt (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) h.collarFlow q :=
  (h.contMDiffOn_collarFlow.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hq))
    |>.mdifferentiableAt (by simp)

private theorem mfderiv_completionEnd_eq_comp {q : ℝ × (𝓡∂ (n + 1)).boundary W}
    (hq : q ∈ Ioo (-h.collarWidth) 0 ×ˢ univ) :
    mfderiv (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) h.completionEnd q =
      (mfderiv (𝓡∂ (n + 1)) (𝓡 (n + 1)) h.toCompletion (h.collarFlow q)).comp
        (mfderiv (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) h.collarFlow q) := by
  rw [(h.completionEnd_eventuallyEq hq).mfderiv_eq]
  exact mfderiv_comp q ((h.contMDiff_toCompletion _).mdifferentiableAt (by simp))
    (h.mdifferentiableAt_collarFlow hq)

private theorem mem_Ioi_of_mem_Ioo {q : ℝ × (𝓡∂ (n + 1)).boundary W}
    (hq : q ∈ Ioo (-h.collarWidth) 0 ×ˢ univ) : q ∈ Ioi (-h.collarWidth) ×ˢ univ :=
  ⟨hq.1.1, trivial⟩

/-- On `(-ε, 0) × ∂W`, the differential of the collar map is surjective. -/
private theorem surjective_mfderiv_collarFlow {q : ℝ × (𝓡∂ (n + 1)).boundary W}
    (hq : q ∈ Ioo (-h.collarWidth) 0 ×ˢ univ) :
    Surjective (mfderiv (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) h.collarFlow q) := by
  intro v
  have hinc := (h.isLocalDiffeomorphAt_toCompletion
    (h.collarFlow_mem_interior hq.1 q.2)).isInvertible_mfderiv (by simp)
  have hend : (mfderiv (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) h.completionEnd q).IsInvertible :=
    (h.isLocalDiffeomorphOn_completionEnd ⟨q, h.mem_Ioi_of_mem_Ioo hq⟩).isInvertible_mfderiv
      (by simp)
  rw [h.mfderiv_completionEnd_eq_comp hq] at hend
  obtain ⟨w, hw⟩ := hend.surjective
    (mfderiv (𝓡∂ (n + 1)) (𝓡 (n + 1)) h.toCompletion (h.collarFlow q) v)
  exact ⟨w, hinc.injective hw⟩

/-! ### Gluing forms over the two pieces -/

section Glue

variable {k : ℕ}

open Classical in
/-- The form on the completion that is `αE`, read through the end map, on the end
`(-ε, ∞) × ∂W`, and `αW`, read through the inclusion, on the rest of `W`. -/
private noncomputable def glue (αW : RoughForm (𝓡∂ (n + 1)) W ℝ k)
    (αE : RoughForm (𝓘(ℝ).prod (𝓡 n)) (ℝ × (𝓡∂ (n + 1)).boundary W) ℝ k) :
    RoughForm (𝓡 (n + 1)) h.Completion ℝ k := fun z ↦
  if hz : ∃ q ∈ Ioi (-h.collarWidth) ×ˢ univ, h.completionEnd q = z then
    RoughForm.pushforwardAt (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) h.completionEnd αE hz.choose z
  else if hz' : ∃ p, h.toCompletion p = z then
    RoughForm.pushforwardAt (𝓡∂ (n + 1)) (𝓡 (n + 1)) h.toCompletion αW hz'.choose z
  else 0

variable (αW : RoughForm (𝓡∂ (n + 1)) W ℝ k)
  (αE : RoughForm (𝓘(ℝ).prod (𝓡 n)) (ℝ × (𝓡∂ (n + 1)).boundary W) ℝ k)

private theorem glue_completionEnd {q : ℝ × (𝓡∂ (n + 1)).boundary W}
    (hq : q ∈ Ioi (-h.collarWidth) ×ˢ univ) :
    h.glue αW αE (h.completionEnd q) =
      RoughForm.pushforwardAt (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) h.completionEnd αE q
        (h.completionEnd q) := by
  have hz : ∃ q' ∈ Ioi (-h.collarWidth) ×ˢ univ, h.completionEnd q' = h.completionEnd q :=
    ⟨q, hq, rfl⟩
  unfold glue
  simp only [dite_eq_left hz]
  rw [h.injOn_completionEnd hz.choose_spec.1 hq hz.choose_spec.2]

private theorem glue_toCompletion {p : W}
    (hp : ¬∃ q ∈ Ioi (-h.collarWidth) ×ˢ univ, h.completionEnd q = h.toCompletion p) :
    h.glue αW αE (h.toCompletion p) =
      RoughForm.pushforwardAt (𝓡∂ (n + 1)) (𝓡 (n + 1)) h.toCompletion αW p
        (h.toCompletion p) := by
  have hz : ∃ p', h.toCompletion p' = h.toCompletion p := ⟨p, rfl⟩
  unfold glue
  simp only [dite_eq_right hp, dite_eq_left hz]
  rw [
    h.injective_toCompletion hz.choose_spec]

private theorem mpullback_completionEnd_glue {q : ℝ × (𝓡∂ (n + 1)).boundary W}
    (hq : q ∈ Ioi (-h.collarWidth) ×ˢ univ) :
    mpullback (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) h.completionEnd (h.glue αW αE) q = αE q :=
  mpullback_apply_eq_of_apply_eq_pushforwardAt
    ((h.isLocalDiffeomorphOn_completionEnd ⟨q, hq⟩).isInvertible_mfderiv (by simp))
    (h.glue_completionEnd αW αE hq)

variable {αW αE}

private theorem mpullback_toCompletion_glue_of_mem_interior
    (hc : ∀ q ∈ Ioo (-h.collarWidth) 0 ×ˢ univ,
      mpullback (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) h.collarFlow αW q = αE q)
    {p : W} (hp : p ∈ (𝓡∂ (n + 1)).interior W) :
    mpullback (𝓡∂ (n + 1)) (𝓡 (n + 1)) h.toCompletion (h.glue αW αE) p = αW p := by
  by_cases hz : ∃ q ∈ Ioi (-h.collarWidth) ×ˢ univ, h.completionEnd q = h.toCompletion p
  · obtain ⟨q, hq, hpq⟩ := hz
    obtain ⟨hq', rfl⟩ := h.mem_Ioo_and_eq_collarFlow hp hq hpq
    refine (mpullback_apply_eq_mpullback_apply_iff (h.surjective_mfderiv_collarFlow hq')).1 ?_
    rw [← mpullback_comp_at (h.mdifferentiableAt_collarFlow hq')
      ((h.contMDiff_toCompletion _).mdifferentiableAt (by simp)),
      ← (h.completionEnd_eventuallyEq hq').mpullback_eq, h.mpullback_completionEnd_glue αW αE hq,
      hc q hq']
  · exact mpullback_apply_eq_of_apply_eq_pushforwardAt
      ((h.isLocalDiffeomorphAt_toCompletion hp).isInvertible_mfderiv (by simp))
      (h.glue_toCompletion αW αE hz)

/-- Every point of the completion is on the end `(-ε, ∞) × ∂W` or is an interior point of `W`. -/
theorem exists_completionEnd_or_toCompletion (z : h.Completion) :
    (∃ q ∈ Ioi (-h.collarWidth) ×ˢ univ, h.completionEnd q = z) ∨
      ∃ p ∈ (𝓡∂ (n + 1)).interior W, h.toCompletion p = z := by
  refine or_iff_not_imp_left.2 fun hz ↦ ?_
  have hε := h.collarWidth_pos
  rcases (h.range_toCompletion_union ▸ mem_univ z :
      z ∈ range h.toCompletion ∪ h.completionEnd '' (Ioi 0 ×ˢ univ)) with ⟨p, rfl⟩ | ⟨q, hq, rfl⟩
  · refine ⟨p, ?_, rfl⟩
    rw [← (𝓡∂ (n + 1)).compl_boundary]
    intro hb
    exact hz ⟨(0, ⟨p, hb⟩), ⟨neg_lt_zero.2 hε, trivial⟩, h.completionEnd_zero _⟩
  · exact absurd ⟨q, ⟨lt_trans (neg_lt_zero.2 hε) hq.1, trivial⟩, rfl⟩ hz

private theorem isSmoothForm_glue (hW : IsSmoothForm (𝓡∂ (n + 1)) ∞ αW)
    (hE : IsSmoothForm (𝓘(ℝ).prod (𝓡 n)) ∞ αE)
    (hc : ∀ q ∈ Ioo (-h.collarWidth) 0 ×ˢ univ,
      mpullback (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) h.collarFlow αW q = αE q) :
    IsSmoothForm (𝓡 (n + 1)) ∞ (h.glue αW αE) := by
  rw [isSmoothForm_def]
  intro z
  by_cases hz : ∃ q ∈ Ioi (-h.collarWidth) ×ˢ univ, h.completionEnd q = z
  · obtain ⟨q, hq, rfl⟩ := hz
    refine ((h.isLocalDiffeomorphOn_completionEnd ⟨q, hq⟩).contMDiffAt_mpullback_form_iff
      (by simp)).1 ((hE.contMDiff q).congr_of_eventuallyEq ?_)
    filter_upwards [(isOpen_Ioi.prod isOpen_univ).mem_nhds hq] with r hr
    rw [h.mpullback_completionEnd_glue αW αE hr]
  · obtain ⟨p, hp, rfl⟩ := (h.exists_completionEnd_or_toCompletion _).resolve_left hz
    refine ((h.isLocalDiffeomorphAt_toCompletion hp).contMDiffAt_mpullback_form_iff
      (by simp)).1 ((hW.contMDiff p).congr_of_eventuallyEq ?_)
    filter_upwards [((𝓡∂ (n + 1)).isOpen_interior one_ne_zero).mem_nhds hp] with r hr
    rw [h.mpullback_toCompletion_glue_of_mem_interior hc hr]

end Glue

/-! ### The form and the primitive of the completion -/

/-- The **form of the completion** `ω̂`: the two-form that is `σ` on `W` and the symplectization
form `-d(e^s α)` of the contact form `α = fillingContactForm σ Y` on the end. -/
noncomputable def completionForm : SmoothTwoForm (𝓡 (n + 1)) h.Completion :=
  ⟨h.glue σ.val (mextDerivₗ (𝓘(ℝ).prod (𝓡 n)) 1
      (-fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩).symplectization).val,
    (h.isSmoothForm_glue σ.isSmoothForm (SmoothForm.isSmoothForm _)
      h.mpullback_collarFlow).mem_smoothBundleForms⟩

/-- The **primitive of the completion** `λ̂`: the one-form that is the Liouville primitive
`λ = -ι_Y σ` on `W` and `e^s α` on the end. -/
noncomputable def completionPrimitive : SmoothForm (𝓡 (n + 1)) h.Completion ℝ 1 :=
  ⟨h.glue (-σ.interiorₗ ⟨Y, h.isOutwardPointingField.contMDiff⟩).val
      (fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩).symplectization.val,
    (h.isSmoothForm_glue (SmoothForm.isSmoothForm _) (SmoothForm.isSmoothForm _)
      h.mpullback_collarFlow_neg_interiorₗ).mem_smoothBundleForms⟩

private theorem coe_completionForm :
    (h.completionForm : RoughForm (𝓡 (n + 1)) h.Completion ℝ 2) =
      h.glue σ.val (mextDerivₗ (𝓘(ℝ).prod (𝓡 n)) 1
        (-fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩).symplectization).val :=
  (rfl)

private theorem coe_completionPrimitive :
    (h.completionPrimitive : RoughForm (𝓡 (n + 1)) h.Completion ℝ 1) =
      h.glue (-σ.interiorₗ ⟨Y, h.isOutwardPointingField.contMDiff⟩).val
        (fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩).symplectization.val :=
  (rfl)

/-- The form of the completion restricts to `σ` on `W`. -/
theorem mpullback_toCompletion_completionForm :
    SmoothForm.mpullback h.toCompletion h.contMDiff_toCompletion h.completionForm = σ :=
  SmoothBundleForm.eq_of_forall_mem_dense ((𝓡∂ (n + 1)).dense_interior (n := ∞) (by simp))
    fun p hp ↦ by
      rw [SmoothForm.coe_mpullback, coe_completionForm]
      exact h.mpullback_toCompletion_glue_of_mem_interior h.mpullback_collarFlow hp

/-- On the end `(-ε, ∞) × ∂W`, the form of the completion is the symplectization form
`-d(e^s α)`. -/
theorem mpullback_completionEnd_completionForm :
    ∀ p ∈ Ioi (-h.collarWidth) ×ˢ univ,
      mpullback (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) h.completionEnd h.completionForm.val p =
        (mextDerivₗ (𝓘(ℝ).prod (𝓡 n)) 1
          (-fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩).symplectization).val
            p := fun p hp ↦ by
  rw [coe_completionForm]
  exact h.mpullback_completionEnd_glue _ _ hp

/-- The primitive of the completion restricts to the Liouville primitive `-ι_Y σ` on `W`. -/
theorem mpullback_toCompletion_completionPrimitive :
    SmoothForm.mpullback h.toCompletion h.contMDiff_toCompletion h.completionPrimitive =
      -σ.interiorₗ ⟨Y, h.isOutwardPointingField.contMDiff⟩ :=
  SmoothBundleForm.eq_of_forall_mem_dense ((𝓡∂ (n + 1)).dense_interior (n := ∞) (by simp))
    fun p hp ↦ by
      rw [SmoothForm.coe_mpullback, coe_completionPrimitive]
      exact h.mpullback_toCompletion_glue_of_mem_interior h.mpullback_collarFlow_neg_interiorₗ hp

/-- On the end `(-ε, ∞) × ∂W`, the primitive of the completion is `e^s α`. -/
theorem mpullback_completionEnd_completionPrimitive :
    ∀ p ∈ Ioi (-h.collarWidth) ×ˢ univ,
      mpullback (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) h.completionEnd h.completionPrimitive.val p =
        (fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩).symplectization.val p :=
  fun p hp ↦ by
    rw [coe_completionPrimitive]
    exact h.mpullback_completionEnd_glue _ _ hp

/-! ### The Liouville field of the completion -/

open Classical in
/-- The **Liouville field of the completion** `Ŷ`: the vector field that is `Y` on `W` and the
unit field `∂_s` along the end. -/
noncomputable def completionField (z : h.Completion) : TangentSpace (𝓡 (n + 1)) z :=
  if hz : ∃ q ∈ Ioi (-h.collarWidth) ×ˢ univ, h.completionEnd q = z then
    tangentSpaceCast (𝓡 (n + 1)) (h.completionEnd hz.choose) z
      (mfderiv (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) h.completionEnd hz.choose
        (Manifold.prodVectorField (constVectorField (1 : ℝ))
          (0 : (x : (𝓡∂ (n + 1)).boundary W) → TangentSpace (𝓡 n) x) hz.choose))
  else if hz' : ∃ p, h.toCompletion p = z then
    tangentSpaceCast (𝓡 (n + 1)) (h.toCompletion hz'.choose) z
      (mfderiv (𝓡∂ (n + 1)) (𝓡 (n + 1)) h.toCompletion hz'.choose (Y hz'.choose))
  else 0

/-- On the end `(-ε, ∞) × ∂W`, the end map sends the unit field `∂_s` to the Liouville field of
the completion. -/
theorem mfderiv_completionEnd_apply {q : ℝ × (𝓡∂ (n + 1)).boundary W}
    (hq : q ∈ Ioi (-h.collarWidth) ×ˢ univ) :
    mfderiv (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) h.completionEnd q
        (Manifold.prodVectorField (constVectorField (1 : ℝ))
          (0 : (x : (𝓡∂ (n + 1)).boundary W) → TangentSpace (𝓡 n) x) q) =
      h.completionField (h.completionEnd q) := by
  have hz : ∃ q' ∈ Ioi (-h.collarWidth) ×ˢ univ, h.completionEnd q' = h.completionEnd q :=
    ⟨q, hq, rfl⟩
  unfold completionField
  simp only [dite_eq_left hz]
  rw [h.injOn_completionEnd hz.choose_spec.1 hq hz.choose_spec.2, tangentSpaceCast_self]

/-- On `(-ε, 0) × ∂W`, the differential of the collar map sends `∂_s` to `Y`, since its lines are
integral curves of `Y`. -/
private theorem mfderiv_collarFlow_apply {q : ℝ × (𝓡∂ (n + 1)).boundary W}
    (hq : q ∈ Ioo (-h.collarWidth) 0 ×ˢ univ) :
    mfderiv (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) h.collarFlow q
        (Manifold.prodVectorField (constVectorField (1 : ℝ))
          (0 : (x : (𝓡∂ (n + 1)).boundary W) → TangentSpace (𝓡 n) x) q) =
      Y (h.collarFlow q) := by
  obtain ⟨s, x⟩ := q
  have hs : s ∈ Ioo (-h.collarWidth) 0 := hq.1
  have := (h.mdifferentiableAt_collarFlow hq).mfderiv_curry_left_apply (1 : ℝ)
  rw [(((h.isMIntegralCurveOn_collarFlow x) s (Ioo_subset_Ioc_self hs)).hasMFDerivAt
    (Ioc_mem_nhds hs.1 hs.2)).mfderiv] at this
  rw [Manifold.prodVectorField_constVectorField_zero_apply]
  exact this.trans (one_smul ℝ _)

/-- At interior points of `W`, the inclusion sends `Y` to the Liouville field of the completion. -/
private theorem mfderiv_toCompletion_apply_of_mem_interior {p : W}
    (hp : p ∈ (𝓡∂ (n + 1)).interior W) :
    mfderiv (𝓡∂ (n + 1)) (𝓡 (n + 1)) h.toCompletion p (Y p) =
      h.completionField (h.toCompletion p) := by
  by_cases hz : ∃ q ∈ Ioi (-h.collarWidth) ×ˢ univ, h.completionEnd q = h.toCompletion p
  · obtain ⟨q, hq, hpq⟩ := hz
    obtain ⟨hq', rfl⟩ := h.mem_Ioo_and_eq_collarFlow hp hq hpq
    have key := h.mfderiv_completionEnd_apply hq
    rw [hpq, h.mfderiv_completionEnd_eq_comp hq', ContinuousLinearMap.comp_apply,
      h.mfderiv_collarFlow_apply hq'] at key
    exact key
  · have hz' : ∃ p', h.toCompletion p' = h.toCompletion p := ⟨p, rfl⟩
    unfold completionField
    simp only [dite_eq_right hz, dite_eq_left hz']
    rw [h.injective_toCompletion hz'.choose_spec, tangentSpaceCast_self]

/-- The Liouville field of the completion is smooth. -/
theorem contMDiff_completionField :
    ContMDiff (𝓡 (n + 1)) (𝓡 (n + 1)).tangent ∞ (T% h.completionField) := by
  intro z
  by_cases hz : ∃ q ∈ Ioi (-h.collarWidth) ×ˢ univ, h.completionEnd q = z
  · obtain ⟨q, hq, rfl⟩ := hz
    exact (h.isLocalDiffeomorphOn_completionEnd ⟨q, hq⟩).contMDiffAt_of_eventually_mfderiv_apply_eq
      (by simp) (Manifold.contMDiff_prodVectorField (contMDiff_constVectorField 1)
        (Bundle.contMDiff_zeroSection ℝ (TangentSpace (𝓡 n))) q)
      (Filter.eventually_of_mem ((isOpen_Ioi.prod isOpen_univ).mem_nhds hq) fun r hr ↦
        h.mfderiv_completionEnd_apply hr)
  · obtain ⟨p, hp, rfl⟩ := (h.exists_completionEnd_or_toCompletion _).resolve_left hz
    exact (h.isLocalDiffeomorphAt_toCompletion hp).contMDiffAt_of_eventually_mfderiv_apply_eq
      (by simp) (h.isOutwardPointingField.contMDiff p)
      (Filter.eventually_of_mem (((𝓡∂ (n + 1)).isOpen_interior one_ne_zero).mem_nhds hp)
        fun r hr ↦ h.mfderiv_toCompletion_apply_of_mem_interior hr)

/-- The inclusion of `W` sends `Y` to the Liouville field of the completion. -/
theorem mfderiv_toCompletion_apply (p : W) :
    mfderiv (𝓡∂ (n + 1)) (𝓡 (n + 1)) h.toCompletion p (Y p) =
      h.completionField (h.toCompletion p) := by
  have h1 : Continuous fun p ↦ (⟨h.toCompletion p,
      mfderiv (𝓡∂ (n + 1)) (𝓡 (n + 1)) h.toCompletion p (Y p)⟩ :
        TangentBundle (𝓡 (n + 1)) h.Completion) :=
    (h.contMDiff_toCompletion.continuous_tangentMap (by simp)).comp
      h.isOutwardPointingField.contMDiff.continuous
  have h2 : Continuous fun p ↦ (⟨h.toCompletion p, h.completionField (h.toCompletion p)⟩ :
      TangentBundle (𝓡 (n + 1)) h.Completion) :=
    h.contMDiff_completionField.continuous.comp h.contMDiff_toCompletion.continuous
  have heq := h1.ext_on ((𝓡∂ (n + 1)).dense_interior (n := ∞) (by simp)) h2 fun p hp ↦ by
    simp only [h.mfderiv_toCompletion_apply_of_mem_interior hp]
  exact Bundle.TotalSpace.mk_inj.1 (congrFun heq p)

/-! ### Symplecticity and the Liouville property -/

/-- Near each point of the end `(-ε, ∞) × ∂W`, the form of the completion is `-d(e^s α)`. -/
theorem eventually_mpullback_completionEnd_completionForm
    {q : ℝ × (𝓡∂ (n + 1)).boundary W} (hq : q ∈ Ioi (-h.collarWidth) ×ˢ univ) :
    ∀ᶠ r in 𝓝 q,
      mpullback (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) h.completionEnd h.completionForm.val r =
        (mextDerivₗ (𝓘(ℝ).prod (𝓡 n)) 1
          (-fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩).symplectization).val
            r :=
  Filter.eventually_of_mem ((isOpen_Ioi.prod isOpen_univ).mem_nhds hq)
    h.mpullback_completionEnd_completionForm

private theorem eventually_mfderiv_completionEnd_apply
    {q : ℝ × (𝓡∂ (n + 1)).boundary W} (hq : q ∈ Ioi (-h.collarWidth) ×ˢ univ) :
    ∀ᶠ r in 𝓝 q, mfderiv (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) h.completionEnd r
        (Manifold.prodVectorField (constVectorField (1 : ℝ))
          (0 : (x : (𝓡∂ (n + 1)).boundary W) → TangentSpace (𝓡 n) x) r) =
      h.completionField (h.completionEnd r) :=
  Filter.eventually_of_mem ((isOpen_Ioi.prod isOpen_univ).mem_nhds hq) fun _ hr ↦
    h.mfderiv_completionEnd_apply hr

/-- At each point of `W`, the form of the completion restricts to `σ`. -/
theorem mpullback_toCompletion_completionForm_apply (p : W) :
    mpullback (𝓡∂ (n + 1)) (𝓡 (n + 1)) h.toCompletion h.completionForm.val p = σ.val p := by
  rw [← SmoothForm.coe_mpullback _ h.contMDiff_toCompletion,
    h.mpullback_toCompletion_completionForm]

/-- Near each point of the end `(-ε, ∞) × ∂W`, the primitive of the completion is `e^s α`. -/
theorem eventually_mpullback_completionEnd_completionPrimitive
    {q : ℝ × (𝓡∂ (n + 1)).boundary W} (hq : q ∈ Ioi (-h.collarWidth) ×ˢ univ) :
    ∀ᶠ r in 𝓝 q,
      mpullback (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) h.completionEnd h.completionPrimitive.val r =
        (fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩).symplectization.val r :=
  Filter.eventually_of_mem ((isOpen_Ioi.prod isOpen_univ).mem_nhds hq)
    h.mpullback_completionEnd_completionPrimitive

/-- At each point of `W`, the primitive of the completion restricts to `-ι_Y σ`. -/
theorem mpullback_toCompletion_completionPrimitive_apply (p : W) :
    mpullback (𝓡∂ (n + 1)) (𝓡 (n + 1)) h.toCompletion h.completionPrimitive.val p =
      -RoughForm.interior Y σ.val p := by
  have := congrArg (fun φ : SmoothForm (𝓡∂ (n + 1)) W ℝ 1 ↦ φ.val p)
    h.mpullback_toCompletion_completionPrimitive
  simpa only [SmoothForm.coe_mpullback, NegMemClass.coe_neg, SmoothTwoForm.coe_interiorₗ,
    ContMDiffSection.coeFn_mk, Pi.neg_apply] using this

private theorem isClosed_completionForm : h.completionForm.IsClosed := by
  rw [SmoothForm.isClosed_def]
  funext z
  rcases h.exists_completionEnd_or_toCompletion z with ⟨q, hq, rfl⟩ | ⟨p, hp, rfl⟩
  · exact ((h.isLocalDiffeomorphOn_completionEnd ⟨q, hq⟩).mextDeriv_apply_eq_iff (by simp)
      ((h.completionForm.contMDiff _).of_le (by simp)) (ψ := 0)).2 (by
        rw [mextDeriv_congr_of_eventuallyEq
          (h.eventually_mpullback_completionEnd_completionForm hq), mpullback_zero]
        exact congrFun ((SmoothForm.isClosed_def _).1 (SmoothForm.isClosed_mextDerivₗ _)) q)
  · exact ((h.isLocalDiffeomorphAt_toCompletion hp).mextDeriv_apply_eq_iff (by simp)
      ((h.completionForm.contMDiff _).of_le (by simp)) (ψ := 0)).2 (by
        rw [mextDeriv_congr_of_eventuallyEq
          (Filter.Eventually.of_forall h.mpullback_toCompletion_completionForm_apply),
          mpullback_zero]
        exact congrFun ((SmoothForm.isClosed_def _).1 h.isSymplectic.isClosed) p)

private theorem isNondegenerate_completionForm : h.completionForm.IsNondegenerate := by
  refine SmoothTwoForm.isNondegenerate_iff_forall_ker_bilinFormAt_eq_bot.2 fun z ↦ ?_
  suffices hz : (h.completionForm.bilinFormAt z).Nondegenerate from
    LinearMap.separatingLeft_iff_ker_eq_bot.1 hz.1
  rcases h.exists_completionEnd_or_toCompletion z with ⟨q, hq, rfl⟩ | ⟨p, hp, rfl⟩
  · exact ((h.isLocalDiffeomorphOn_completionEnd ⟨q, hq⟩).nondegenerate_bilinFormAt_iff (by simp)
      (h.mpullback_completionEnd_completionForm q hq)).2
      ((SmoothForm.isContactForm_neg_iff.2 h.isContactForm_fillingContactForm
        ).isSymplectic_mextDerivₗ_symplectization.isNondegenerate.nondegenerate_bilinFormAt q)
  · exact ((h.isLocalDiffeomorphAt_toCompletion hp).nondegenerate_bilinFormAt_iff (by simp)
      (h.mpullback_toCompletion_completionForm_apply p)).2
      (h.isSymplectic.isNondegenerate.nondegenerate_bilinFormAt p)

/-- The form `ω̂` of the completion is symplectic. -/
theorem isSymplectic_completionForm : h.completionForm.IsSymplectic :=
  ⟨h.isClosed_completionForm, h.isNondegenerate_completionForm⟩

/-- On the end `(-ε, ∞) × ∂W`, the field `Ŷ` is a Liouville field of `ω̂`. -/
theorem mlieDerivForm_completionField_completionEnd {q : ℝ × (𝓡∂ (n + 1)).boundary W}
    (hq : q ∈ Ioi (-h.collarWidth) ×ˢ univ) :
    mlieDerivForm h.completionField h.completionForm.val (h.completionEnd q) =
      h.completionForm.val (h.completionEnd q) := by
  have hL := congrFun (isLiouvilleVectorField_iff.1
    (SmoothForm.isLiouvilleVectorField_symplectization
      (-fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩))) q
  rw [← mextDerivₗ_apply] at hL
  exact ((h.isLocalDiffeomorphOn_completionEnd ⟨q, hq⟩).mlieDerivForm_apply_eq_iff
    (h.eventually_mpullback_completionEnd_completionForm hq)
    (Manifold.contMDiff_prodVectorField (contMDiff_constVectorField 1)
      (Bundle.contMDiff_zeroSection ℝ (TangentSpace (𝓡 n))) q)
    ((h.contMDiff_completionField _).of_le (by simp)) (h.eventually_mfderiv_completionEnd_apply hq)
    (congrFun ((SmoothForm.isClosed_def _).1 h.isSymplectic_completionForm.isClosed) _)).2
    (by rw [h.mpullback_completionEnd_completionForm q hq]; exact hL)

/-- The field `Ŷ` of the completion satisfies `L_Ŷ ω̂ = ω̂` at each point of the image of the set
`U` on which `Y` is Liouville and of the end `(0, ∞) × ∂W`. -/
theorem mlieDerivForm_completionField_of_mem {z : h.Completion}
    (hz : z ∈ h.toCompletion '' U ∪ h.completionEnd '' (Ioi 0 ×ˢ univ)) :
    mlieDerivForm h.completionField h.completionForm.val z = h.completionForm.val z := by
  rcases h.exists_completionEnd_or_toCompletion z with ⟨q, hq, rfl⟩ | ⟨p, hp, rfl⟩
  · exact h.mlieDerivForm_completionField_completionEnd hq
  obtain ⟨p', hp', hpp'⟩ | hpE := hz
  · rw [h.injective_toCompletion hpp'] at hp'
    exact ((h.isLocalDiffeomorphAt_toCompletion hp).mlieDerivForm_apply_eq_iff
      (Filter.Eventually.of_forall h.mpullback_toCompletion_completionForm_apply)
      ((h.isOutwardPointingField.contMDiff p).of_le (by simp))
      ((h.contMDiff_completionField _).of_le (by simp))
      (Filter.Eventually.of_forall h.mfderiv_toCompletion_apply)
      (congrFun ((SmoothForm.isClosed_def _).1 h.isSymplectic_completionForm.isClosed) _)).2
      (by rw [h.mpullback_toCompletion_completionForm_apply]; exact h.mlieDerivForm_eq p hp')
  · exact absurd hpE (Set.disjoint_left.1 h.disjoint_range_toCompletion_completionEnd_image
      ⟨p, rfl⟩)

/-- The field `Ŷ` and the primitive `λ̂` of the completion satisfy `ι_Ŷ ω̂ = -λ̂`. -/
theorem interior_completionField_completionForm :
    RoughForm.interior h.completionField h.completionForm.val = (-h.completionPrimitive).val := by
  funext z
  rcases h.exists_completionEnd_or_toCompletion z with ⟨q, hq, rfl⟩ | ⟨p, hp, rfl⟩
  · rw [(h.isLocalDiffeomorphOn_completionEnd ⟨q, hq⟩).interior_apply_eq_iff (by simp)
      (h.mfderiv_completionEnd_apply hq)]
    have hι := congrFun (SmoothForm.interior_mextDeriv_symplectization
      (-fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩)) q
    ext v
    rw [RoughForm.interior_apply, h.mpullback_completionEnd_completionForm q hq,
      mextDerivₗ_apply, ← RoughForm.interior_apply, hι, NegMemClass.coe_neg, mpullback_neg,
      Pi.neg_apply, h.mpullback_completionEnd_completionPrimitive q hq,
      SmoothForm.symplectization_neg]
    simp
  · rw [(h.isLocalDiffeomorphAt_toCompletion hp).interior_apply_eq_iff (by simp)
      (h.mfderiv_toCompletion_apply p)]
    ext v
    rw [RoughForm.interior_apply, h.mpullback_toCompletion_completionForm_apply,
      NegMemClass.coe_neg, mpullback_neg, Pi.neg_apply,
      h.mpullback_toCompletion_completionPrimitive_apply]
    simp [RoughForm.interior_apply]

/-! ### The completion of a Liouville domain -/

/-- For a Liouville domain, the primitive `λ̂` of the completion satisfies `dλ̂ = -ω̂`. -/
theorem mextDerivₗ_completionPrimitive (h : IsStrongFilling σ univ Y) :
    mextDerivₗ (𝓡 (n + 1)) 1 h.completionPrimitive = -h.completionForm := by
  apply Subtype.ext
  funext z
  rw [mextDerivₗ_apply, NegMemClass.coe_neg]
  rcases h.exists_completionEnd_or_toCompletion z with ⟨q, hq, rfl⟩ | ⟨p, hp, rfl⟩
  · rw [(h.isLocalDiffeomorphOn_completionEnd ⟨q, hq⟩).mextDeriv_apply_eq_iff (by simp)
      ((h.completionPrimitive.contMDiff _).of_le (by simp)),
      mpullback_neg, Pi.neg_apply,
      mextDeriv_congr_of_eventuallyEq (h.eventually_mpullback_completionEnd_completionPrimitive hq),
      h.mpullback_completionEnd_completionForm q hq, mextDerivₗ_apply,
      SmoothForm.symplectization_neg, NegMemClass.coe_neg, mextDeriv_neg, Pi.neg_apply, neg_neg]
  · have hprim : mpullback (𝓡∂ (n + 1)) (𝓡 (n + 1)) h.toCompletion h.completionPrimitive.val =
        -RoughForm.interior Y σ.val :=
      funext h.mpullback_toCompletion_completionPrimitive_apply
    rw [(h.isLocalDiffeomorphAt_toCompletion hp).mextDeriv_apply_eq_iff (by simp)
      ((h.completionPrimitive.contMDiff _).of_le (by simp)),
      mpullback_neg, Pi.neg_apply, hprim, mextDeriv_neg,
      Pi.neg_apply, h.mpullback_toCompletion_completionForm_apply,
      ← mlieDerivForm_eq_mextDeriv_interior_apply (σ.mdifferentiableAt p)
        ((h.isOutwardPointingField.contMDiff p).mdifferentiableAt (by simp))
        (congrFun ((SmoothForm.isClosed_def _).1 h.isSymplectic.isClosed) p),
      h.mlieDerivForm_eq p trivial]

/-- For a Liouville domain, the field `Ŷ` of the completion is a Liouville field of `ω̂`. -/
theorem isLiouvilleVectorField_completionField (h : IsStrongFilling σ univ Y) :
    IsLiouvilleVectorField h.completionForm.val h.completionField :=
  isLiouvilleVectorField_iff.2 <| funext fun z ↦
    h.mlieDerivForm_completionField_of_mem (by
      rw [image_univ, h.range_toCompletion_union]
      exact mem_univ z)

/-! ### The milestone -/

/-- **Completion of a strong filling.** The completion `Ŵ` of a strong filling `(W, σ, U, Y)`,
with the boundary contact form `α`, has the following properties.

* Its form `ω̂` is symplectic, restricts to `σ` on `W`, and is `-d(e^s α)` on the end
  `[0, ∞) × ∂W`.
* `Ŵ` is the disjoint union of `W` and of the open end `(0, ∞) × ∂W`.
* The end is attached along the Liouville collar: for some `ε > 0`, the lines
  `s ↦ Φ (s, x)` are the integral curves of `Y` on `(-ε, 0]` ending at the boundary points,
  the point `(s, x)` of the end is `Φ (s, x)` for `s ∈ (-ε, 0]`, and `Φ` pulls `σ` back to
  `-d(e^s α)` on `(-ε, 0) × ∂W`.
* On the end `[0, ∞) × ∂W`, the field `Ŷ` is the image of `∂_s` and is a Liouville field of
  `ω̂`.
* The field `Ŷ` and the primitive `λ̂` satisfy `ι_Ŷ ω̂ = -λ̂` on all of `Ŵ`.
* If `U` is all of `W` (a Liouville domain), the primitive `λ̂` restricts to `λ = -ι_Y σ` on `W`
  and is `e^s α` on the end, and `dλ̂ = -ω̂`.

Milestone: *Completion of a strong filling*. -/
theorem isSymplectic_completionForm_and_extends :
    h.completionForm.IsSymplectic ∧
      SmoothForm.mpullback h.toCompletion h.contMDiff_toCompletion h.completionForm = σ ∧
      (∀ p ∈ Ici 0 ×ˢ univ,
        mpullback (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) h.completionEnd h.completionForm.val p =
          (mextDerivₗ (𝓘(ℝ).prod (𝓡 n)) 1
            (-fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩).symplectization).val
              p) ∧
      range h.toCompletion ∪ h.completionEnd '' (Ioi 0 ×ˢ univ) = univ ∧
      Disjoint (range h.toCompletion) (h.completionEnd '' (Ioi 0 ×ˢ univ)) ∧
      0 < h.collarWidth ∧
      (∀ x, IsMIntegralCurveOn (fun s ↦ h.collarFlow (s, x)) Y (Ioc (-h.collarWidth) 0)) ∧
      (∀ x, h.collarFlow (0, x) = x) ∧
      (∀ s ∈ Ioc (-h.collarWidth) 0, ∀ x,
        h.completionEnd (s, x) = h.toCompletion (h.collarFlow (s, x))) ∧
      (∀ p ∈ Ioo (-h.collarWidth) 0 ×ˢ univ,
        mpullback (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) h.collarFlow σ.val p =
          (mextDerivₗ (𝓘(ℝ).prod (𝓡 n)) 1
            (-fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩).symplectization).val
              p) ∧
      (∀ q ∈ Ici 0 ×ˢ univ,
        mfderiv (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) h.completionEnd q
            (Manifold.prodVectorField (constVectorField (1 : ℝ))
              (0 : (x : (𝓡∂ (n + 1)).boundary W) → TangentSpace (𝓡 n) x) q) =
          h.completionField (h.completionEnd q) ∧
        mlieDerivForm h.completionField h.completionForm.val (h.completionEnd q) =
          h.completionForm.val (h.completionEnd q)) ∧
      RoughForm.interior h.completionField h.completionForm.val = (-h.completionPrimitive).val ∧
      (U = univ →
        SmoothForm.mpullback h.toCompletion h.contMDiff_toCompletion h.completionPrimitive =
            -σ.interiorₗ ⟨Y, h.isOutwardPointingField.contMDiff⟩ ∧
          (∀ p ∈ Ici 0 ×ˢ univ,
            mpullback (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) h.completionEnd h.completionPrimitive.val p =
              (fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩).symplectization.val
                p) ∧
          mextDerivₗ (𝓡 (n + 1)) 1 h.completionPrimitive = -h.completionForm) := by
  have hend {p : ℝ × (𝓡∂ (n + 1)).boundary W} (hp : p ∈ Ici 0 ×ˢ univ) :
      p ∈ Ioi (-h.collarWidth) ×ˢ univ :=
    ⟨lt_of_lt_of_le (neg_lt_zero.2 h.collarWidth_pos) hp.1, trivial⟩
  refine ⟨h.isSymplectic_completionForm, h.mpullback_toCompletion_completionForm,
    fun p hp ↦ h.mpullback_completionEnd_completionForm p (hend hp), h.range_toCompletion_union,
    h.disjoint_range_toCompletion_completionEnd_image, h.collarWidth_pos,
    h.isMIntegralCurveOn_collarFlow, h.collarFlow_zero,
    fun s hs x ↦ h.completionEnd_eq_toCompletion hs x, h.mpullback_collarFlow,
    fun q hq ↦ ⟨h.mfderiv_completionEnd_apply (hend hq),
      h.mlieDerivForm_completionField_completionEnd (hend hq)⟩,
    h.interior_completionField_completionForm, fun hU ↦ ?_⟩
  subst hU
  exact ⟨h.mpullback_toCompletion_completionPrimitive,
    fun p hp ↦ h.mpullback_completionEnd_completionPrimitive p (hend hp),
    h.mextDerivₗ_completionPrimitive⟩

end IsStrongFilling

end SymplecticGeometry

end
