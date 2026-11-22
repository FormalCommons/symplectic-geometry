/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Contact.Basic
public import TauCeti.Geometry.Contact.Symplectization.Basic
public import TauCeti.Geometry.Symplectic.Liouville.ContactType
public import TauCeti.Geometry.Symplectic.Manifold.Flat
public import SymplecticGeometry.Geometry.Manifold.Boundary.Charts
public import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Flow.Basic
public import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic
import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Local
import SymplecticGeometry.Geometry.Manifold.PartitionOfUnity
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Continuity
import SymplecticGeometry.Geometry.Symplectic.Liouville.ContactType
import SymplecticGeometry.Geometry.Symplectic.Liouville.Scaling

/-!
# Strong fillings, their boundary contact form and their Liouville collar

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

Near its boundary a strong filling is a piece of the symplectization of its boundary
(`SymplecticGeometry.IsStrongFilling.exists_liouvilleCollar`). The backward integral curves of `Y`
from the boundary points form a smooth collar
(`TauCeti.SmoothCollar.exists_eq_of_isOutwardPointing_of_subset`), and the map `Φ`, sending
`(s, x)` to the point at time `s` of the curve that ends at `x`, pulls `λ` back to `e^s α` and
`σ` back to `-d(e^s α)` on `(-ε, 0) × ∂W`. At negative times the curves run in the interior, where
Liouville scaling
(`TauCeti.mpullback_interiorₗ_apply_eq_symplectization_of_isMIntegralCurveOn`) relates `Φ^*λ` at
time `s` to its restriction to a slice `Φ (t₀, ·)` pushed into the interior. Since the collar is
smooth up to the boundary, these restrictions depend continuously on `t₀` up to `t₀ = 0`
(`TauCeti.IsSmoothForm.continuous_mpullback_prodMk_apply`), where the slice is the boundary
itself; letting `t₀ → 0` identifies the restriction with `α`. The identity for `σ` follows from
`σ = d(ι_Y σ)` on `U` (Cartan's formula) and the naturality of `d`, at the points where `Φ` is
smooth (`TauCeti.SmoothCollar.contMDiffOn_of_forall_apply_eq`); this last step has the shape of
the proof of Tau Ceti's `TauCeti.mpullback_flowOf_comp_mextDeriv_apply`.

## Main definitions

* `SymplecticGeometry.IsStrongFilling σ U Y`: `σ` is symplectic, `U` is an open neighbourhood of
  the boundary, `Y` is a smooth outward field, Liouville for `σ` on `U`.
* `SymplecticGeometry.fillingContactForm σ X`: the one-form `-ι^*(ι_X σ)` on the boundary, for a
  smooth vector field `X`.

## Main results

* `SymplecticGeometry.IsStrongFilling.mono`: the open set may be shrunk to any smaller open
  neighbourhood of the boundary.
* `SymplecticGeometry.IsStrongFilling.of_contMDiffOn`: a field that is smooth only on `U` agrees,
  near the boundary, with the field of a strong filling.
* `SymplecticGeometry.IsStrongFilling.isContactType`: the boundary inclusion is of contact type,
  in Tau Ceti's sense, with primitive `ι_Y σ`.
* `SymplecticGeometry.IsStrongFilling.isContactForm_fillingContactForm` and
  `SymplecticGeometry.IsStrongFilling.mextDerivₗ_fillingContactForm`: `α` is a contact form with
  `dα = -ι^*σ`, from the general case of a hypersurface,
  `TauCeti.SmoothEmbedding.exists_isContactForm_eq_neg_mpullback_interior`.
* `SymplecticGeometry.IsStrongFilling.exists_liouvilleCollar`: the Liouville collar of a strong
  filling, `Φ^*λ = e^s α` and `Φ^*σ = -d(e^s α)` along the integral curves of `Y` that end on the
  boundary.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Definition 3.5.38 and the completion on p. 148.
-/

public section

open Bundle Set TauCeti
open scoped Manifold ContDiff

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
  -- A smooth cutoff `g` with support in `U`, equal to one on an open `V₀ ⊇ ∂W`.
  obtain ⟨g, htsupp, hg1, -⟩ :=
    hb.exists_contMDiffMap_tsupport_subset_eventually_eq_one (𝓡∂ (n + 1)) hU hbU
  obtain ⟨V₀, hV₀, hbV₀, hgV₀⟩ := mem_nhdsSet_iff_exists.1 hg1
  set V := V₀ ∩ U
  have hVo : IsOpen V := hV₀.inter hU
  have hVU : V ⊆ U := inter_subset_right
  have hbV : (𝓡∂ (n + 1)).boundary W ⊆ V := subset_inter hbV₀ hbU
  have hYV : EqOn (⇑g • Y) Y V := fun x hx ↦ by
    rw [Pi.smul_apply', hgV₀ hx.1, one_smul]
  have hY' : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞ (T% (⇑g • Y)) :=
    g.contMDiff.contMDiffOn.smul_section_of_tsupport hU htsupp hY
  refine ⟨V, ⇑g • Y, hVU, hYV, hσ, hVo, hbV,
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

/-- The contact form of `TauCeti.SmoothEmbedding.exists_isContactForm_eq_neg_mpullback_interior`,
for the boundary inclusion and the field of a strong filling, is `fillingContactForm σ ⟨Y, _⟩`. -/
private theorem exists_eq_fillingContactForm (h : IsStrongFilling σ U Y) :
    ∃ α : SmoothForm (𝓡 n) ((𝓡∂ (n + 1)).boundary W) ℝ 1,
      α = fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩ ∧ α.IsContactForm ∧
        mextDerivₗ (𝓡 n) 1 α =
          -SmoothForm.mpullback Subtype.val (isSmoothEmbedding_subtypeVal_boundary W).contMDiff
            σ := by
  have hι := SmoothEmbedding.coe_ofIsSmoothEmbedding (I := 𝓡 n) (J := 𝓡∂ (n + 1)) (n := ∞) _
    (isSmoothEmbedding_subtypeVal_boundary W)
  obtain ⟨α, hα, hc, hd⟩ := SmoothEmbedding.exists_isContactForm_eq_neg_mpullback_interior
    h.isSymplectic (.ofIsSmoothEmbedding _ (isSmoothEmbedding_subtypeVal_boundary W)) (by simp)
    h.isOpen (by simpa [hι] using h.boundary_subset) h.isOutwardPointingField.contMDiff.contMDiffOn
    h.mlieDerivForm_eq (by rw [hι]; exact h.isOutwardPointingField.isTransverseAlong_subtypeVal)
  refine ⟨α, Subtype.ext ?_, hc, hd.trans (congrArg _ (Subtype.ext ?_))⟩
  · rw [coe_fillingContactForm, hα, hι, ContMDiffSection.coeFn_mk]
  · rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback, hι]

/-- **The contact form of a strong filling.** For a strong filling, `-ι^*(ι_Y σ)` is a contact
form on the boundary. -/
theorem isContactForm_fillingContactForm (h : IsStrongFilling σ U Y) :
    (fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩).IsContactForm := by
  obtain ⟨α, rfl, hc, -⟩ := h.exists_eq_fillingContactForm
  exact hc

/-- For a strong filling, the contact form `α = -ι^*(ι_Y σ)` of the boundary has
`dα = -ι^*σ`. -/
theorem mextDerivₗ_fillingContactForm (h : IsStrongFilling σ U Y) :
    mextDerivₗ (𝓡 n) 1 (fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩) =
      -SmoothForm.mpullback Subtype.val (isSmoothEmbedding_subtypeVal_boundary W).contMDiff σ := by
  obtain ⟨α, rfl, -, hd⟩ := h.exists_eq_fillingContactForm
  exact hd

end IsStrongFilling

section Collar

open _root_.TauCeti.EuclideanHalfSpace Filter Topology

variable [T2Space W]

omit [T2Space W] in
/-- At negative times the lines of `Φ` lie in `U` and in the interior of `W`. -/
private theorem IsStrongFilling.mem_inter_interior_of_eq_collar (h : IsStrongFilling σ U Y)
    {ε : ℝ} (hε : 0 < ε) {Φ : ℝ × (𝓡∂ (n + 1)).boundary W → W} {c : SmoothCollar n ∞ W}
    (hΦY : ∀ x, IsMIntegralCurveOn (fun s ↦ Φ (s, x)) Y (Ioc (-ε) 0))
    (hc : ∀ q, c q = Φ (-ε * (q.2 : EuclideanHalfSpace 1).val 0, q.1)) (hcU : range c ⊆ U)
    {t : ℝ} (ht : t ∈ Ioo (-ε) 0) (x : (𝓡∂ (n + 1)).boundary W) :
    Φ (t, x) ∈ U ∩ (𝓡∂ (n + 1)).interior W := by
  refine ⟨?_, (hΦY x).mem_interior_of_isOutwardPointing
    (fun y hy ↦ h.isOutwardPointingField.isOutwardPointing hy)
    (mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Ioc_self)⟩
  rw [← SmoothCollar.apply_normalIioRay_eq hε hc (Ioo_subset_Ioc_self ht)]
  exact hcU (mem_range_self _)

/-- The pullback of `ι_Y σ` along `Φ`, at `(t, x)` with `t ∈ (-ε, 0)`, is `e^t` times its pullback
to the boundary. By Liouville scaling, it is `e^(t - t₀)` times the pullback to the slice
`Φ (t₀, ·)` for every `t₀ ∈ (-ε, 0)`; that pullback depends continuously on `t₀` up to `t₀ = 0`,
where the slice is the boundary. -/
private theorem IsStrongFilling.mpullback_interiorₗ_apply_of_eq_collar
    (h : IsStrongFilling σ U Y) {ε : ℝ} (hε : 0 < ε) {Φ : ℝ × (𝓡∂ (n + 1)).boundary W → W}
    {c : SmoothCollar n ∞ W} (hΦY : ∀ x, IsMIntegralCurveOn (fun s ↦ Φ (s, x)) Y (Ioc (-ε) 0))
    (hc : ∀ q, c q = Φ (-ε * (q.2 : EuclideanHalfSpace 1).val 0, q.1)) (hcU : range c ⊆ U)
    {t : ℝ} (ht : t ∈ Ioo (-ε) 0) (x : (𝓡∂ (n + 1)).boundary W)
    (w : TangentSpace (𝓘(ℝ).prod (𝓡 n)) (t, x)) :
    mpullback (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) Φ
        (σ.interiorₗ ⟨Y, h.isOutwardPointingField.contMDiff⟩).val (t, x) ![w] =
      Real.exp t * mpullback (𝓡 n) (𝓡∂ (n + 1)) Subtype.val
        (σ.interiorₗ ⟨Y, h.isOutwardPointingField.contMDiff⟩).val x
          ![(Manifold.tangentSpaceProdEquiv (t, x) w).2] := by
  set hY := h.isOutwardPointingField.contMDiff
  set β := σ.interiorₗ ⟨Y, hY⟩
  set L := mpullback (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) Φ β.val (t, x) ![w] with hLdef
  set w₂ := (Manifold.tangentSpaceProdEquiv (t, x) w).2
  -- The pullback to the collar slice at depth `r`, evaluated on `w₂`, is continuous in `r`.
  let G : normalIioOpens 1 → ℝ := fun r ↦
    mpullback (𝓡 n) (𝓡∂ (n + 1)) (fun y ↦ c (y, r)) β.val x ![w₂]
  have hG : Continuous G :=
    (β.isSmoothForm.of_le (by simp)).continuous_mpullback_prodMk_apply
      (c.contMDiff.of_le (by simp)) x ![w₂]
  -- The depth of the slice at time `t₀`, for `t₀` near `0`.
  let ρ : ℝ → normalIioOpens 1 := fun t₀ ↦
    normalIioRay ⟨min (-t₀ / ε) (1 / 2), (min_le_right _ _).trans_lt (by norm_num)⟩
  have hρc : Continuous ρ :=
    continuous_normalIioRay.comp (((continuous_neg.div_const ε).min continuous_const).subtype_mk _)
  have hG0 : G (ρ 0) = mpullback (𝓡 n) (𝓡∂ (n + 1)) Subtype.val β.val x ![w₂] := by
    have hρ0 : ρ 0 = normalIioOpensZero one_pos := by
      simp only [ρ, neg_zero, zero_div, min_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 2),
        normalIioRay_zero]
    simp only [G, hρ0, c.apply_zero]
  -- By Liouville scaling, the slice at `t₀` determines `L`.
  have hscale : ∀ t₀ ∈ Ioo (-(ε / 2)) 0, G (ρ t₀) = Real.exp (t₀ - t) * L := by
    intro t₀ ht₀
    have hta : -t₀ / ε < 1 / 2 := by
      rw [div_lt_iff₀ hε]; linarith [ht₀.1]
    have hΦt₀ : (fun y ↦ Φ (t₀, y)) = fun y ↦ c (y, ρ t₀) := by
      funext y
      rw [← SmoothCollar.apply_normalIioRay_eq hε hc ⟨by linarith [ht₀.1], ht₀.2.le⟩]
      simp only [ρ, min_eq_left hta.le]
    have hΦ₀ : ContMDiff (𝓡 n) (𝓡∂ (n + 1)) ∞ fun y ↦ Φ (t₀, y) :=
      hΦt₀ ▸ c.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)
    have hsc := mpullback_interiorₗ_apply_eq_symplectization_of_isMIntegralCurveOn
      h.isSymplectic.isClosed hY
      ((𝓡∂ (n + 1)).isOpen_interior one_ne_zero |> h.isOpen.inter) inter_subset_right
      (fun y hy ↦ h.mlieDerivForm_eq y hy.1)
      (fun t ht x ↦ h.mem_inter_interior_of_eq_collar hε hΦY hc hcU ht x)
      (fun x ↦ (hΦY x).mono Ioo_subset_Ioc_self) (a := -ε) (b := 0)
      ⟨by linarith [ht₀.1], ht₀.2⟩ hΦ₀ ht x
    have hL : L = Real.exp (t - t₀) * G (ρ t₀) := by
      rw [hLdef, hsc]
      refine (SmoothForm.symplectization_apply _ (t - t₀, x) w).trans ?_
      rw [SmoothForm.coe_mpullback]
      simp only [G, ← hΦt₀, w₂]
      rw [Manifold.tangentSpaceProdEquiv_apply (t - t₀, x) w,
        Manifold.tangentSpaceProdEquiv_apply]
    rw [hL, ← mul_assoc, ← Real.exp_add, sub_add_sub_cancel, sub_self, Real.exp_zero, one_mul]
  -- Letting `t₀ → 0` identifies the slice with the boundary.
  have hlim₁ : Tendsto (fun t₀ ↦ G (ρ t₀)) (𝓝[<] 0) (𝓝 (G (ρ 0))) :=
    ((hG.comp hρc).tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim₂ : Tendsto (fun t₀ ↦ Real.exp (t₀ - t) * L) (𝓝[<] 0) (𝓝 (Real.exp (0 - t) * L)) :=
    (((Real.continuous_exp.comp (continuous_sub_right t)).mul continuous_const).tendsto
      0).mono_left nhdsWithin_le_nhds
  have heq := tendsto_nhds_unique hlim₁ (hlim₂.congr' (eventually_of_mem
    (Ioo_mem_nhdsLT (neg_lt_zero.2 (half_pos hε))) fun t₀ ht₀ ↦ (hscale t₀ ht₀).symm))
  rw [hG0, zero_sub] at heq
  rw [heq, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

/-- The pullback of `ι_Y σ` along `Φ` is the symplectization form `e^s (-α)` on
`(-ε, 0) × ∂W`. -/
private theorem IsStrongFilling.mpullback_interiorₗ_eq_of_eq_collar
    (h : IsStrongFilling σ U Y) {ε : ℝ} (hε : 0 < ε) {Φ : ℝ × (𝓡∂ (n + 1)).boundary W → W}
    {c : SmoothCollar n ∞ W} (hΦY : ∀ x, IsMIntegralCurveOn (fun s ↦ Φ (s, x)) Y (Ioc (-ε) 0))
    (hc : ∀ q, c q = Φ (-ε * (q.2 : EuclideanHalfSpace 1).val 0, q.1)) (hcU : range c ⊆ U) :
    ∀ p ∈ Ioo (-ε) 0 ×ˢ (univ : Set ((𝓡∂ (n + 1)).boundary W)),
      mpullback (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) Φ
          (σ.interiorₗ ⟨Y, h.isOutwardPointingField.contMDiff⟩).val p =
        (-fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩).symplectization.val p := by
  rintro ⟨t, x⟩ ⟨ht, -⟩
  ext w
  rw [h.mpullback_interiorₗ_apply_of_eq_collar hε hΦY hc hcU ht x w,
    SmoothForm.symplectization_apply, NegMemClass.coe_neg, coe_fillingContactForm,
    SmoothTwoForm.coe_interiorₗ]
  simp

/-- **The Liouville collar of a strong filling.** Let `(W, σ, U, Y)` be a strong filling with
compact boundary, `λ = -ι_Y σ` its Liouville primitive near `∂W` and
`α = fillingContactForm σ Y`, `-ι^*(ι_Y σ)`, the contact form of its boundary. There are `ε > 0`,
a map `Φ : ℝ × ∂W → W` whose lines `s ↦ Φ (s, x)` are the integral curves of `Y` on `(-ε, 0]`
ending at the boundary points, and a smooth collar `c` with image in `U` whose normal lines are
these curves, `c (x, t) = Φ (-ε t, x)`, such that on `(-ε, 0) × ∂W` the map `Φ` pulls `λ` back to
`e^s α` and `σ` back to `-d(e^s α)`.

The two identities are stated on the open set `(-ε, 0) × ∂W`, where `Φ` is smooth; at `s = 0`
the map `Φ` need not be differentiable as a map on `ℝ × ∂W`, and the collar `c` covers the
boundary itself. -/
theorem IsStrongFilling.exists_liouvilleCollar [CompactSpace ((𝓡∂ (n + 1)).boundary W)]
    (h : IsStrongFilling σ U Y) :
    ∃ (ε : ℝ) (Φ : ℝ × (𝓡∂ (n + 1)).boundary W → W) (c : SmoothCollar n ∞ W), 0 < ε ∧
      (∀ x, Φ (0, x) = x) ∧ (∀ x, IsMIntegralCurveOn (fun s ↦ Φ (s, x)) Y (Ioc (-ε) 0)) ∧
      (∀ q, c q = Φ (-ε * (q.2 : EuclideanHalfSpace 1).val 0, q.1)) ∧ range c ⊆ U ∧
      (∀ p ∈ Ioo (-ε) 0 ×ˢ univ, mpullback (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) Φ
          (-σ.interiorₗ ⟨Y, h.isOutwardPointingField.contMDiff⟩).val p =
        (fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩).symplectization.val p) ∧
      ∀ p ∈ Ioo (-ε) 0 ×ˢ univ, mpullback (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) Φ σ.val p =
        (mextDerivₗ (𝓘(ℝ).prod (𝓡 n)) 1
          (-fillingContactForm σ ⟨Y, h.isOutwardPointingField.contMDiff⟩).symplectization).val
            p := by
  obtain ⟨ε, Φ, c, hε, hΦ0, hΦY, hc, hcU⟩ :=
    SmoothCollar.exists_eq_of_isOutwardPointing_of_subset h.isOutwardPointingField h.isOpen
      h.boundary_subset
  set hY := h.isOutwardPointingField.contMDiff
  set β := σ.interiorₗ ⟨Y, hY⟩
  have hβα := h.mpullback_interiorₗ_eq_of_eq_collar hε hΦY hc hcU
  refine ⟨ε, Φ, c, hε, hΦ0, hΦY, hc, hcU, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · ext w
    have hw := congrArg (fun φ ↦ φ ![w]) (hβα p hp)
    simp only [SmoothForm.symplectization_apply, NegMemClass.coe_neg] at hw ⊢
    simp only [mpullback_apply, Pi.neg_apply, ContinuousAlternatingMap.neg_apply] at hw ⊢
    rw [hw]
    simp
  · obtain ⟨t, x⟩ := p
    have ht : t ∈ Ioo (-ε) 0 := hp.1
    have hΦU : Φ (t, x) ∈ U := (h.mem_inter_interior_of_eq_collar hε hΦY hc hcU ht x).1
    -- Cartan's formula: `σ = L_Y σ = d(ι_Y σ)` on `U`.
    have hcart : σ.val (Φ (t, x)) = mextDeriv β.val (Φ (t, x)) := by
      rw [← h.mlieDerivForm_eq _ hΦU, mlieDerivForm_eq_mextDeriv_interior_apply
        ((σ.contMDiff _).mdifferentiableAt (n := ∞) (by simp))
        ((hY _).mdifferentiableAt (by simp))
        (congrFun ((SmoothForm.isClosed_def σ).1 h.isSymplectic.isClosed) _),
        SmoothTwoForm.coe_interiorₗ, ContMDiffSection.coeFn_mk]
    calc mpullback (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) Φ σ.val (t, x)
        = mpullback (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) Φ (mextDeriv β.val) (t, x) := by
          ext v
          rw [mpullback_apply, mpullback_apply, hcart]
      _ = mextDeriv (mpullback (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) Φ β.val) (t, x) :=
          mpullback_mextDeriv_at (((SmoothCollar.contMDiffOn_of_forall_apply_eq hε hc).contMDiffAt
            ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).of_le (by simp))
            ((β.isSmoothForm.contMDiff (Φ (t, x))).of_le (by simp))
      _ = mextDeriv (-fillingContactForm σ ⟨Y, hY⟩).symplectization.val (t, x) :=
          mextDeriv_congr_of_eventuallyEq
            (eventually_of_mem ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp) hβα)
      _ = _ := by rw [mextDerivₗ_apply]

end Collar

end SymplecticGeometry

end
