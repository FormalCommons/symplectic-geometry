/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DeRham.Map
import SymplecticGeometry.Geometry.Manifold.DeRham.Basic
import SymplecticGeometry.Geometry.Manifold.DeRham.Map
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Map

/-!
# Splittings of closed forms that depend smoothly on families

A *smooth cohomology splitting* of a manifold `M`
(`SymplecticGeometry.SmoothCohomologySplitting I M`) consists, in every degree `k`, of

* a finite-dimensional space `S^k` of closed `k`-forms containing no nonzero exact form,
* a linear map `p : Z^k → S^k` on the closed `k`-forms, the identity in degree zero, and
* a linear map `h : Z^{k+1} → Ω^k` with `z = p z + d (h z)` for every closed `(k+1)`-form `z`,

such that `p` and `h` take smooth families of forms over a smooth parameter manifold to smooth
families; the structure takes the universe levels of the parameter manifolds as parameters.
In the proof of their Theorem 3.2.4 [McDuffSalamon2017], McDuff and Salamon need such primitives
only for exact `2`-forms; they sketch a Mayer–Vietoris induction over a good cover for them,
after Bott and Tu [BottTu1982], and leave its details to the reader. The structure here is the
stronger statement, in all degrees at once, that such an induction establishes; it is the form
in which smooth families of primitives are constructed.

From a splitting `σ` this file derives that `S^k` maps isomorphically onto the de Rham cohomology
in degree `k` (`SmoothCohomologySplitting.spaceEquiv`), so that cohomology is finite-dimensional;
that `p z = 0` exactly when `z` is exact; a primitive of exact forms that preserves smooth
families (`SmoothCohomologySplitting.exactPrimitive`); and that if `t ↦ z t` is smooth and each
`z t` is closed, then the cohomology classes `[z t]` have coordinates, in any basis, that are
smooth in `t` (`SmoothCohomologySplitting.contMDiff_repr_mk`).

## Main definitions

* `SymplecticGeometry.SmoothCohomologySplitting I M`: the spaces `S^k` and the maps `p` and `h`
  of every degree, preserving smooth families.
* `SymplecticGeometry.SmoothCohomologySplitting.spaceEquiv`: the class map `S^k ≃ H^k`.
* `SymplecticGeometry.SmoothCohomologySplitting.exactPrimitive`: a primitive on exact forms.
* `SymplecticGeometry.SmoothCohomologySplitting.ofDiffeomorph`: a splitting carried back along a
  diffeomorphism.

## Main results

* `SmoothCohomologySplitting.mk_proj`: `p z` has the class of `z`.
* `SmoothCohomologySplitting.proj_eq_zero_iff`: `p z = 0` exactly when `z` is exact, and
  `SmoothCohomologySplitting.proj_eq_of_sub_mem_exactForms`: `p z` is the form of `S^k` that
  differs from `z` by an exact form.
* `SmoothCohomologySplitting.finiteDimensional_deRhamCohomology`.
* `SmoothCohomologySplitting.mextDerivₗ_exactPrimitive` and
  `SmoothCohomologySplitting.preservesSmoothFamilies_exactPrimitive`.
* `SmoothCohomologySplitting.exists_isSmoothFamily_mextDerivₗ_eq_of_mem_exactForms`: a smooth
  family of forms that are exact at the parameters of a set `K` has a smooth family of
  primitives over `K`.
* `SmoothCohomologySplitting.contMDiff_repr_mk`: the coordinates of the classes of a smooth
  family of closed forms are smooth.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], proof of
  Theorem 3.2.4.
* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982]
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace SymplecticGeometry

open TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

universe uE uH uN

variable (M) in
/-- **Smooth cohomology splittings.** In every degree `k`, a finite-dimensional space
`space k` of closed `k`-forms containing no nonzero exact form, a linear map `proj k` from the
closed `k`-forms into `space k`, the identity in degree zero, and a linear map `primitive k` on
the closed `(k + 1)`-forms with `z = proj (k + 1) z + d (primitive k z)`, such that `proj` and
`primitive` take smooth families of forms over every smooth parameter manifold, in the universes
`uE`, `uH` and `uN` of its model space, model and points, to smooth families. -/
structure SmoothCohomologySplitting where
  /-- The space of closed `k`-forms that represents the cohomology in degree `k`. -/
  space (k : ℕ) : Submodule ℝ (SmoothForm I M ℝ k)
  space_le_closedForms (k : ℕ) : space k ≤ closedForms I M k
  finiteDimensional_space (k : ℕ) : FiniteDimensional ℝ (space k)
  /-- The projection of the closed `k`-forms to `space k`. -/
  proj (k : ℕ) : closedForms I M k →ₗ[ℝ] SmoothForm I M ℝ k
  proj_mem (k : ℕ) (z : closedForms I M k) : proj k z ∈ space k
  proj_zero (z : closedForms I M 0) : proj 0 z = z
  /-- A primitive of the difference between a closed `(k + 1)`-form and its projection. -/
  primitive (k : ℕ) : closedForms I M (k + 1) →ₗ[ℝ] SmoothForm I M ℝ k
  mextDerivₗ_primitive (k : ℕ) (z : closedForms I M (k + 1)) :
    mextDerivₗ I k (primitive k z) = z - proj (k + 1) z
  eq_zero_of_mem_exactForms (k : ℕ) {s : SmoothForm I M ℝ k} :
    s ∈ space k → s ∈ exactForms I M k → s = 0
  preservesSmoothFamilies_proj (k : ℕ) : PreservesSmoothFamilies.{uE, uH, uN} (proj k)
  preservesSmoothFamilies_primitive (k : ℕ) : PreservesSmoothFamilies.{uE, uH, uN} (primitive k)

namespace SmoothCohomologySplitting

attribute [instance] finiteDimensional_space

attribute [simp] proj_mem proj_zero mextDerivₗ_primitive

/-- Two splittings with the same spaces, projections and primitives are equal. -/
@[ext]
theorem ext {σ τ : SmoothCohomologySplitting.{uE, uH, uN} I M} (hspace : σ.space = τ.space)
    (hproj : σ.proj = τ.proj) (hprimitive : σ.primitive = τ.primitive) : σ = τ := by
  cases σ
  cases τ
  cases hspace
  cases hproj
  cases hprimitive
  rfl

variable {I} (σ : SmoothCohomologySplitting.{uE, uH, uN} I M)

/-- The projection of a splitting, as a map into its space of closed forms. -/
def projSpace (k : ℕ) : closedForms I M k →ₗ[ℝ] σ.space k :=
  (σ.proj k).codRestrict (σ.space k) (σ.proj_mem k)

/-- `projSpace` is `proj`, with its values in the space of the splitting. -/
@[simp]
theorem coe_projSpace (k : ℕ) (z : closedForms I M k) :
    (σ.projSpace k z : SmoothForm I M ℝ k) = σ.proj k z :=
  (rfl)

/-- The projection of a closed form, as a closed form, has the same de Rham class as the form. -/
theorem mk_proj (k : ℕ) (z : closedForms I M k) :
    deRhamCohomology.mk I k (Submodule.inclusion (σ.space_le_closedForms k) (σ.projSpace k z)) =
      deRhamCohomology.mk I k z := by
  cases k with
  | zero => exact congrArg _ (Subtype.ext (σ.proj_zero z))
  | succ k =>
    rw [eq_comm, deRhamCohomology.mk_eq_mk_iff, exactForms_succ,
      Submodule.coe_inclusion, coe_projSpace, ← σ.mextDerivₗ_primitive]
    exact LinearMap.mem_range_self _ _

/-- A closed form of the space of a splitting whose class vanishes is zero. -/
theorem eq_zero_of_mk_eq_zero {k : ℕ} {s : σ.space k}
    (hs : deRhamCohomology.mk I k (Submodule.inclusion (σ.space_le_closedForms k) s) = 0) :
    s = 0 :=
  Subtype.ext <| σ.eq_zero_of_mem_exactForms k s.property <|
    (deRhamCohomology.mk_eq_zero_iff I k _).mp hs

/-- The class map of a splitting, from its space of closed `k`-forms to the de Rham cohomology
in degree `k`, is bijective. -/
theorem bijective_mk_comp_inclusion (k : ℕ) :
    Function.Bijective
      (deRhamCohomology.mk I k ∘ₗ Submodule.inclusion (σ.space_le_closedForms k)) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun _ hs ↦
    σ.eq_zero_of_mk_eq_zero (by rwa [LinearMap.comp_apply] at hs), fun c ↦ ?_⟩
  obtain ⟨z, rfl⟩ := deRhamCohomology.mk_surjective I k c
  exact ⟨σ.projSpace k z, σ.mk_proj k z⟩

/-- The class map of a splitting, from its space of closed `k`-forms to the de Rham cohomology
in degree `k`, as a linear isomorphism. -/
def spaceEquiv (k : ℕ) : σ.space k ≃ₗ[ℝ] deRhamCohomology I M k :=
  LinearEquiv.ofBijective _ (σ.bijective_mk_comp_inclusion k)

/-- `spaceEquiv` takes a form of the space of the splitting to its de Rham class. -/
theorem spaceEquiv_apply (k : ℕ) (s : σ.space k) :
    σ.spaceEquiv k s =
      deRhamCohomology.mk I k (Submodule.inclusion (σ.space_le_closedForms k) s) := by
  rw [spaceEquiv, LinearEquiv.ofBijective_apply, LinearMap.comp_apply]

/-- `spaceEquiv` takes the projection of a closed form to the class of the form. -/
@[simp]
theorem spaceEquiv_projSpace (k : ℕ) (z : closedForms I M k) :
    σ.spaceEquiv k (σ.projSpace k z) = deRhamCohomology.mk I k z := by
  rw [spaceEquiv_apply, σ.mk_proj k z]

/-- The inverse of `spaceEquiv` takes the class of a closed form to the projection of the
form. -/
@[simp]
theorem spaceEquiv_symm_mk (k : ℕ) (z : closedForms I M k) :
    (σ.spaceEquiv k).symm (deRhamCohomology.mk I k z) = σ.projSpace k z := by
  rw [LinearEquiv.symm_apply_eq, spaceEquiv_projSpace]

/-- The projection of a splitting is the identity on the closed forms of its space. -/
theorem proj_eq_self_of_mem {k : ℕ} {z : closedForms I M k}
    (hz : (z : SmoothForm I M ℝ k) ∈ σ.space k) : σ.proj k z = z := by
  have h : σ.projSpace k z = ⟨z, hz⟩ := (σ.spaceEquiv k).injective <| by
    rw [spaceEquiv_projSpace, spaceEquiv_apply]
    exact congrArg _ (Subtype.ext (Submodule.coe_inclusion (σ.space_le_closedForms k) ⟨z, hz⟩).symm)
  rw [← coe_projSpace, h]

/-- The projection of a closed `(k + 1)`-form is the form minus the exterior derivative of its
primitive. -/
theorem proj_eq_sub_mextDerivₗ_primitive {k : ℕ} (z : closedForms I M (k + 1)) :
    σ.proj (k + 1) z = z - mextDerivₗ I k (σ.primitive k z) := by
  rw [σ.mextDerivₗ_primitive, sub_sub_cancel]

/-- A closed form differs from its projection by an exact form. -/
theorem sub_proj_mem_exactForms {k : ℕ} (z : closedForms I M k) :
    (z : SmoothForm I M ℝ k) - σ.proj k z ∈ exactForms I M k := by
  cases k with
  | zero => simp
  | succ k =>
    rw [exactForms_succ, ← σ.mextDerivₗ_primitive]
    exact LinearMap.mem_range_self _ _

/-- The projection of a closed form `z` is the form `s` of the space of the splitting that
differs from `z` by an exact form. -/
theorem proj_eq_of_sub_mem_exactForms {k : ℕ} {z : closedForms I M k} {s : SmoothForm I M ℝ k}
    (hs : s ∈ σ.space k) (h : (z : SmoothForm I M ℝ k) - s ∈ exactForms I M k) :
    σ.proj k z = s := by
  rw [← sub_eq_zero]
  refine σ.eq_zero_of_mem_exactForms k (sub_mem (σ.proj_mem k z) hs) ?_
  simpa only [sub_sub_sub_cancel_left] using sub_mem h (σ.sub_proj_mem_exactForms z)

/-- The projection of a splitting vanishes on a closed form exactly when the form is exact. -/
theorem proj_eq_zero_iff {k : ℕ} (z : closedForms I M k) :
    σ.proj k z = 0 ↔ (z : SmoothForm I M ℝ k) ∈ exactForms I M k := by
  rw [← deRhamCohomology.mk_eq_zero_iff, ← spaceEquiv_projSpace, LinearEquiv.map_eq_zero_iff,
    ← coe_projSpace, ZeroMemClass.coe_eq_zero]

include σ in
/-- A manifold with a smooth cohomology splitting has finite-dimensional de Rham cohomology in
every degree. -/
theorem finiteDimensional_deRhamCohomology (k : ℕ) :
    FiniteDimensional ℝ (deRhamCohomology I M k) :=
  Module.Finite.equiv (σ.spaceEquiv k)

/-- The primitive of a splitting, restricted to the exact `(k + 1)`-forms: a linear map giving
each exact form a primitive. -/
def exactPrimitive (k : ℕ) : exactForms I M (k + 1) →ₗ[ℝ] SmoothForm I M ℝ k :=
  σ.primitive k ∘ₗ Submodule.inclusion (exactForms_le_closedForms I (k + 1))

/-- `exactPrimitive` is `primitive` on exact forms, seen as closed forms. -/
theorem exactPrimitive_apply (k : ℕ) (x : exactForms I M (k + 1)) :
    σ.exactPrimitive k x =
      σ.primitive k (Submodule.inclusion (exactForms_le_closedForms I (k + 1)) x) :=
  (rfl)

/-- The exterior derivative of `exactPrimitive k x` is the exact form `x`. -/
@[simp]
theorem mextDerivₗ_exactPrimitive (k : ℕ) (x : exactForms I M (k + 1)) :
    mextDerivₗ I k (σ.exactPrimitive k x) = x := by
  rw [exactPrimitive_apply, σ.mextDerivₗ_primitive,
    (σ.proj_eq_zero_iff _).mpr (by simpa using x.property), sub_zero, Submodule.coe_inclusion]

/-- The primitive on exact forms takes smooth families to smooth families. -/
theorem preservesSmoothFamilies_exactPrimitive (k : ℕ) :
    PreservesSmoothFamilies.{uE, uH, uN} (σ.exactPrimitive k) :=
  (σ.preservesSmoothFamilies_primitive k).comp preservesSmoothFamilies_subtype _

/-- The projection of a splitting, as a map into its space of closed forms followed by the
inclusion of that space, takes smooth families to smooth families. -/
theorem preservesSmoothFamilies_subtype_comp_projSpace (k : ℕ) :
    PreservesSmoothFamilies.{uE, uH, uN} ((σ.space k).subtype ∘ₗ σ.projSpace k) := by
  rw [projSpace, LinearMap.subtype_comp_codRestrict]
  exact σ.preservesSmoothFamilies_proj k

include σ in
/-- **The classes of a smooth family of closed forms depend smoothly on the parameter.** For a
basis `b` of the de Rham cohomology in degree `k` and a smooth family `z` of closed `k`-forms
over a smooth manifold `N`, each coordinate `t ↦ b.repr [z t] i` is a smooth function on `N`. -/
theorem contMDiff_repr_mk {k : ℕ} {ι : Type*} (b : Module.Basis ι ℝ (deRhamCohomology I M k))
    {EN : Type uE} [NormedAddCommGroup EN] [NormedSpace ℝ EN] {HN : Type uH} [TopologicalSpace HN]
    {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN}
    [IsManifold J ∞ N] {z : N → closedForms I M k}
    (hz : IsSmoothFamily J (fun t ↦ (z t : SmoothForm I M ℝ k))) (i : ι) :
    ContMDiff J 𝓘(ℝ) ∞ (fun t ↦ b.repr (deRhamCohomology.mk I k (z t)) i) := by
  simpa using (σ.preservesSmoothFamilies_subtype_comp_projSpace k).contMDiff_dual_apply hz
    (b.coord i ∘ₗ (σ.spaceEquiv k).toLinearMap)

include σ in
/-- **Smooth primitives of a family that is exact at some parameters.** Let `τ` be a smooth
family of `(k + 1)`-forms over a manifold `N` such that `τ t` is exact for every `t` in a set `K`.
Then there is a smooth family `β` of `k`-forms with `d (β t) = τ t` for every `t ∈ K`. Off `K`,
`τ t` is first corrected to the closed form `τ t - h (d (τ t))`, with `h` the primitive on exact
forms; on `K` the correction vanishes. -/
theorem exists_isSmoothFamily_mextDerivₗ_eq_of_mem_exactForms {k : ℕ}
    {EN : Type uE} [NormedAddCommGroup EN] [NormedSpace ℝ EN] {HN : Type uH} [TopologicalSpace HN]
    {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN}
    [IsManifold J ∞ N] {τ : N → SmoothForm I M ℝ (k + 1)} (hτ : IsSmoothFamily J τ) {K : Set N}
    (hK : ∀ t ∈ K, τ t ∈ exactForms I M (k + 1)) :
    ∃ β : N → SmoothForm I M ℝ k, IsSmoothFamily J β ∧ ∀ t ∈ K, mextDerivₗ I k (β t) = τ t := by
  -- The exterior derivatives of `τ`, as exact forms.
  let dτ : N → exactForms I M (k + 1 + 1) :=
    fun t ↦ ⟨mextDerivₗ I (k + 1) (τ t), by
      rw [exactForms_succ]; exact LinearMap.mem_range_self _ _⟩
  -- The corrected, closed family.
  let c : N → closedForms I M (k + 1) := fun t ↦
    ⟨τ t - σ.exactPrimitive (k + 1) (dτ t), by
      rw [mem_closedForms_iff_mextDerivₗ_eq_zero, map_sub, σ.mextDerivₗ_exactPrimitive, sub_self]⟩
  have hc : IsSmoothFamily J (fun t ↦ (c t : SmoothForm I M ℝ (k + 1))) :=
    hτ.sub (preservesSmoothFamilies_def.mp (σ.preservesSmoothFamilies_exactPrimitive (k + 1)) dτ
      hτ.mextDeriv)
  have hcK : ∀ t ∈ K, (c t : SmoothForm I M ℝ (k + 1)) = τ t := by
    intro t ht
    have hdτ : dτ t = 0 := Subtype.ext
      ((mem_closedForms_iff_mextDerivₗ_eq_zero _ _).mp (exactForms_le_closedForms _ _ (hK t ht)))
    -- The value of `c t` is its defining difference.
    change τ t - σ.exactPrimitive (k + 1) (dτ t) = τ t
    rw [hdτ, map_zero, sub_zero]
  refine ⟨fun t ↦ σ.primitive k (c t),
    preservesSmoothFamilies_def.mp (σ.preservesSmoothFamilies_primitive k) c hc, fun t ht ↦ ?_⟩
  rw [σ.mextDerivₗ_primitive, (σ.proj_eq_zero_iff (c t)).mpr (by rw [hcK t ht]; exact hK t ht),
    sub_zero, hcK t ht]

section Diffeomorph

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' ∞ M']

variable (Φ : M ≃ₘ⟮I, I'⟯ M') (τ : SmoothCohomologySplitting.{uE, uH, uN} I' M')

/-- **Transport along a diffeomorphism.** A splitting `τ` of `M'` and a diffeomorphism
`Φ : M ≃ M'` give a splitting of `M`: its spaces are the pullbacks `Φ^* (τ.space k)`, and its
projections and primitives are `z ↦ Φ^* (τ.proj k ((Φ⁻¹)^* z))` and
`z ↦ Φ^* (τ.primitive k ((Φ⁻¹)^* z))`. -/
def ofDiffeomorph : SmoothCohomologySplitting.{uE, uH, uN} I M where
  space k := (τ.space k).map (SmoothForm.mpullback Φ Φ.contMDiff)
  space_le_closedForms k := by
    rintro _ ⟨s, hs, rfl⟩
    exact SmoothForm.mpullback_mem_closedForms Φ Φ.contMDiff (τ.space_le_closedForms k hs)
  finiteDimensional_space _ := inferInstance
  proj k := SmoothForm.mpullback Φ Φ.contMDiff ∘ₗ τ.proj k ∘ₗ
    closedForms.mpullback Φ.symm Φ.symm.contMDiff k
  proj_mem k z := Submodule.mem_map_of_mem (τ.proj_mem k _)
  proj_zero z := by
    simp only [LinearMap.comp_apply, proj_zero, closedForms.coe_mpullback,
      SmoothForm.mpullback_mpullback_symm]
  primitive k := SmoothForm.mpullback Φ Φ.contMDiff ∘ₗ τ.primitive k ∘ₗ
    closedForms.mpullback Φ.symm Φ.symm.contMDiff (k + 1)
  mextDerivₗ_primitive k z := by
    simp only [LinearMap.comp_apply, SmoothForm.mextDerivₗ_mpullback, mextDerivₗ_primitive,
      map_sub, closedForms.coe_mpullback, SmoothForm.mpullback_mpullback_symm]
  eq_zero_of_mem_exactForms k := by
    rintro _ ⟨s, hs, rfl⟩ hex
    have h := closedForms.mpullback_mem_exactForms Φ.symm Φ.symm.contMDiff k
      ⟨_, SmoothForm.mpullback_mem_closedForms Φ Φ.contMDiff (τ.space_le_closedForms k hs)⟩
      (by simpa using hex)
    simp only [closedForms.coe_mpullback, SmoothForm.mpullback_symm_mpullback] at h
    rw [τ.eq_zero_of_mem_exactForms k hs h, map_zero]
  preservesSmoothFamilies_proj k := preservesSmoothFamilies_def.mpr fun α hα ↦
    preservesSmoothFamilies_def.mp ((τ.preservesSmoothFamilies_proj k).mpullback Φ Φ.contMDiff)
      (fun t ↦ closedForms.mpullback Φ.symm Φ.symm.contMDiff k (α t))
      (by simpa only [closedForms.coe_mpullback] using hα.mpullback _ Φ.symm.contMDiff)
  preservesSmoothFamilies_primitive k := preservesSmoothFamilies_def.mpr fun α hα ↦
    preservesSmoothFamilies_def.mp
      ((τ.preservesSmoothFamilies_primitive k).mpullback Φ Φ.contMDiff)
      (fun t ↦ closedForms.mpullback Φ.symm Φ.symm.contMDiff (k + 1) (α t))
      (by simpa only [closedForms.coe_mpullback] using hα.mpullback _ Φ.symm.contMDiff)

/-- The spaces of `ofDiffeomorph Φ τ` are the pullbacks along `Φ` of those of `τ`. -/
@[simp]
theorem space_ofDiffeomorph (k : ℕ) :
    (τ.ofDiffeomorph Φ).space k = (τ.space k).map (SmoothForm.mpullback Φ Φ.contMDiff) :=
  (rfl)

/-- The projection of `ofDiffeomorph Φ τ` is `z ↦ Φ^* (τ.proj k ((Φ⁻¹)^* z))`. -/
@[simp]
theorem proj_ofDiffeomorph_apply (k : ℕ) (z : closedForms I M k) :
    (τ.ofDiffeomorph Φ).proj k z = SmoothForm.mpullback Φ Φ.contMDiff
      (τ.proj k (closedForms.mpullback Φ.symm Φ.symm.contMDiff k z)) :=
  (rfl)

/-- The primitive of `ofDiffeomorph Φ τ` is `z ↦ Φ^* (τ.primitive k ((Φ⁻¹)^* z))`. -/
@[simp]
theorem primitive_ofDiffeomorph_apply (k : ℕ) (z : closedForms I M (k + 1)) :
    (τ.ofDiffeomorph Φ).primitive k z = SmoothForm.mpullback Φ Φ.contMDiff
      (τ.primitive k (closedForms.mpullback Φ.symm Φ.symm.contMDiff (k + 1) z)) :=
  (rfl)

end Diffeomorph

end SmoothCohomologySplitting

end SymplecticGeometry
