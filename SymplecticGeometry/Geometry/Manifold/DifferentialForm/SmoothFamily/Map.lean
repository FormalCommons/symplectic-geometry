/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Geometry.Manifold.Instances.Real
public import SymplecticGeometry.Geometry.Manifold.ContMDiff.Dual
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic

/-!
# Linear maps preserving smooth families of forms

A linear map `T`, defined on a submodule `D` of the smooth `k`-forms on `M` and with values in
the smooth `l`-forms on `M'`, *preserves smooth families*
(`SymplecticGeometry.PreservesSmoothFamilies`) when, for every smooth family `t ↦ α t` of forms
in `D` over the unit interval, the family `t ↦ T (α t)` is smooth again. This is how the
smoothness in a parameter of the constructions behind smooth families of primitives is phrased:
a linear construction applied slice by slice to a smooth family gives a smooth family.

The property is closed under the linear operations on maps, under composition, and under
post-composition with the exterior derivative, pullback along a smooth map, and multiplication by
a smooth function; inclusions of submodules have it, and it can be checked on the restrictions
to two open sets covering the target.

For maps into a finite-dimensional space `S` of forms with a basis `b`, the property says that
the coordinates `t ↦ b.repr (T (α t)) i` are smooth functions on the unit interval
(`SymplecticGeometry.preservesSmoothFamilies_iff_contMDiff_repr`). One direction holds because
each linear functional on `S` is a finite linear combination of functionals
`ω ↦ φ (ω x v)`, with `φ` a continuous linear functional on the coefficient space, and these
are smooth on smooth families; the other writes `T (α t)` as `∑ i, c i t • b i`.

## Main definitions

* `SymplecticGeometry.PreservesSmoothFamilies T`: the linear map `T` takes smooth families of
  forms over the unit interval to smooth families.

## Main results

* The closure lemmas `PreservesSmoothFamilies.add`, `.smul`, `.neg`, `.sub`, `.comp`,
  `.mextDerivₗ`, `.mpullback`, `.funSMul`, `.of_mpullback_inclusion_sup`, and
  `SymplecticGeometry.preservesSmoothFamilies_zero`,
  `SymplecticGeometry.preservesSmoothFamilies_subtype`.
* `SymplecticGeometry.preservesSmoothFamilies_iff_contMDiff_repr`: a map into a
  finite-dimensional space of forms preserves smooth families exactly when its coordinates in a
  basis are smooth along smooth families.
* `SymplecticGeometry.preservesSmoothFamilies_sum_smulRight`: a finite linear combination of
  fixed forms, with coefficients that are smooth along smooth families, preserves smooth
  families; `SymplecticGeometry.preservesSmoothFamilies_comp_of_contMDiff_repr`: a map whose
  coordinates in a finite basis are smooth along smooth families, followed by any linear map,
  preserves smooth families; and `PreservesSmoothFamilies.comp_of_finiteDimensional`: a map
  that preserves smooth families into a finite-dimensional space of forms may be followed by
  any linear map.
* `SymplecticGeometry.isSmoothFamily_comp_of_contMDiff_repr`: a family of vectors of a space
  with a finite basis, over any manifold, whose coordinates are smooth, is carried by any linear
  map to a smooth family of forms; `SymplecticGeometry.isSmoothFamily_of_contMDiff_dual`: the
  same for a finite-dimensional space, with the values of all linear functionals in place of
  the coordinates.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], proof of
  Theorem 3.2.4.
-/

public section

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff

namespace SymplecticGeometry

open TauCeti

variable {E H M E' H' M' E'' H'' M'' F G G' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'} [IsManifold I' 1 M']
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  [TopologicalSpace M''] [ChartedSpace H'' M''] {I'' : ModelWithCorners ℝ E'' H''}
  [IsManifold I'' 1 M'']
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup G'] [NormedSpace ℝ G'] {k l l' : ℕ}
  {D : Submodule ℝ (SmoothForm I M F k)}

/-- **Linear maps preserving smooth families.** Let `T` be linear, defined on a submodule `D` of
the smooth `k`-forms on `M`, with values in the smooth `l`-forms on `M'`. Then `T` preserves
smooth families when, for every family `α` of forms in `D` over the unit interval that is smooth
as a family of forms on `M`, the family `t ↦ T (α t)` is smooth. -/
def PreservesSmoothFamilies (T : D →ₗ[ℝ] SmoothForm I' M' G l) : Prop :=
  ∀ α : unitInterval → D, IsSmoothFamily (𝓡∂ 1) (fun t ↦ (α t : SmoothForm I M F k)) →
    IsSmoothFamily (𝓡∂ 1) (fun t ↦ T (α t))

/-- The defining property of `SymplecticGeometry.PreservesSmoothFamilies`. -/
theorem preservesSmoothFamilies_def {T : D →ₗ[ℝ] SmoothForm I' M' G l} :
    PreservesSmoothFamilies T ↔
      ∀ α : unitInterval → D, IsSmoothFamily (𝓡∂ 1) (fun t ↦ (α t : SmoothForm I M F k)) →
        IsSmoothFamily (𝓡∂ 1) (fun t ↦ T (α t)) :=
  Iff.rfl

/-- The zero map preserves smooth families. -/
theorem preservesSmoothFamilies_zero :
    PreservesSmoothFamilies (0 : D →ₗ[ℝ] SmoothForm I' M' G l) := fun _ _ ↦ by
  simpa only [LinearMap.zero_apply] using isSmoothFamily_const (J := 𝓡∂ 1) (N := unitInterval)
    (0 : SmoothForm I' M' G l)

/-- The inclusion of a submodule of forms preserves smooth families. -/
theorem preservesSmoothFamilies_subtype : PreservesSmoothFamilies D.subtype := fun _ hα ↦ hα

namespace PreservesSmoothFamilies

variable {T T₁ T₂ : D →ₗ[ℝ] SmoothForm I' M' G l}

/-- The sum of two maps preserving smooth families preserves smooth families. -/
protected theorem add (h₁ : PreservesSmoothFamilies T₁) (h₂ : PreservesSmoothFamilies T₂) :
    PreservesSmoothFamilies (T₁ + T₂) := fun α hα ↦ by
  simpa only [LinearMap.add_apply] using (h₁ α hα).add (h₂ α hα)

/-- A constant multiple of a map preserving smooth families preserves smooth families. -/
protected theorem smul (hT : PreservesSmoothFamilies T) (c : ℝ) :
    PreservesSmoothFamilies (c • T) := fun α hα ↦ by
  simpa only [LinearMap.smul_apply] using (hT α hα).smul c

/-- The negative of a map preserving smooth families preserves smooth families. -/
protected theorem neg (hT : PreservesSmoothFamilies T) : PreservesSmoothFamilies (-T) :=
  fun α hα ↦ by simpa only [LinearMap.neg_apply] using (hT α hα).neg

/-- The difference of two maps preserving smooth families preserves smooth families. -/
protected theorem sub (h₁ : PreservesSmoothFamilies T₁) (h₂ : PreservesSmoothFamilies T₂) :
    PreservesSmoothFamilies (T₁ - T₂) := fun α hα ↦ by
  simpa only [LinearMap.sub_apply] using (h₁ α hα).sub (h₂ α hα)

/-- **Composition.** If `T` preserves smooth families and takes its values in a submodule `D'`,
and `S`, defined on `D'`, preserves smooth families, then so does `S` after `T`. -/
protected theorem comp {D' : Submodule ℝ (SmoothForm I' M' G l)}
    {S : D' →ₗ[ℝ] SmoothForm I'' M'' G' l'} (hS : PreservesSmoothFamilies S)
    (hT : PreservesSmoothFamilies T) (h : ∀ x, T x ∈ D') :
    PreservesSmoothFamilies (S ∘ₗ T.codRestrict D' h) :=
  fun α hα ↦ hS (fun t ↦ T.codRestrict D' h (α t)) (hT α hα)

/-- Following a map that preserves smooth families by the exterior derivative gives a map that
preserves smooth families. -/
protected theorem mextDerivₗ [IsManifold I' 2 M'] (hT : PreservesSmoothFamilies T) :
    PreservesSmoothFamilies (mextDerivₗ I' l ∘ₗ T) :=
  fun α hα ↦ (hT α hα).mextDeriv

/-- Following a map that preserves smooth families by the pullback along a smooth map gives a map
that preserves smooth families. -/
protected theorem mpullback (hT : PreservesSmoothFamilies T) (f : M'' → M')
    (hf : ContMDiff I'' I' ∞ f) :
    PreservesSmoothFamilies (SmoothForm.mpullback f hf ∘ₗ T) :=
  fun α hα ↦ (hT α hα).mpullback f hf

/-- Following a map that preserves smooth families by the multiplication with a smooth function
gives a map that preserves smooth families. -/
protected theorem funSMul (hT : PreservesSmoothFamilies T) (g : C^∞⟮I', M'; ℝ⟯) :
    PreservesSmoothFamilies (SmoothForm.funSMulₗ g ∘ₗ T) :=
  fun α hα ↦ (hT α hα).funSMul g

/-- **Gluing.** A map into the forms on `U ⊔ V` preserves smooth families when its restrictions
to `U` and to `V` do. -/
protected theorem of_mpullback_inclusion_sup {U V : Opens M'}
    {T : D →ₗ[ℝ] SmoothForm I' (U ⊔ V : Opens M') G l}
    (hU : PreservesSmoothFamilies
      (SmoothForm.mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) ∘ₗ T))
    (hV : PreservesSmoothFamilies
      (SmoothForm.mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) ∘ₗ T)) :
    PreservesSmoothFamilies T :=
  fun α hα ↦ isSmoothFamily_iff_mpullback_inclusion_sup.mpr ⟨hU α hα, hV α hα⟩

end PreservesSmoothFamilies

section FiniteDimensional

/-- **Finite linear combinations of fixed forms.** If the real coefficients `c i` are linear on
`D` and smooth along smooth families, then `x ↦ ∑ i ∈ s, c i x • w i` preserves smooth
families. -/
theorem preservesSmoothFamilies_sum_smulRight {ι : Type*} (s : Finset ι)
    (c : ι → D →ₗ[ℝ] ℝ) (w : ι → SmoothForm I' M' G l)
    (hc : ∀ α : unitInterval → D, IsSmoothFamily (𝓡∂ 1) (fun t ↦ (α t : SmoothForm I M F k)) →
      ∀ i ∈ s, ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (fun t ↦ c i (α t))) :
    PreservesSmoothFamilies (∑ i ∈ s, (c i).smulRight (w i)) := fun α hα ↦ by
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply]
  exact IsSmoothFamily.sum fun i hi ↦
    (isSmoothFamily_const (w i)).fun_smul (hc α hα i hi)

section Families

variable {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J 1 N]
  {X : Type*} [AddCommMonoid X] [Module ℝ X]

/-- **Families with smooth coordinates.** Let `b` be a finite basis of a real vector space `X`
and `x` a family of vectors of `X`, indexed by a manifold `N`, whose coordinates
`t ↦ b.repr (x t) i` are smooth. Then its image under any linear map `L` from `X` to forms is a
smooth family. -/
theorem isSmoothFamily_comp_of_contMDiff_repr {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ X)
    (L : X →ₗ[ℝ] SmoothForm I' M' G l) {x : N → X}
    (hx : ∀ i, ContMDiff J 𝓘(ℝ) ∞ (fun t ↦ b.repr (x t) i)) :
    IsSmoothFamily J (fun t ↦ L (x t)) := by
  cases nonempty_fintype ι
  have hsum : (fun t ↦ L (x t)) = fun t ↦ ∑ i, b.repr (x t) i • L (b i) := by
    funext t
    conv_lhs => rw [← b.sum_repr (x t)]
    simp only [map_sum, map_smul]
  rw [hsum]
  exact IsSmoothFamily.sum fun i _ ↦ (isSmoothFamily_const (L (b i))).fun_smul (hx i)

/-- **Families in a finite-dimensional space.** Let `x` be a family of vectors of a
finite-dimensional real vector space `X`, indexed by a manifold `N`, such that `t ↦ f (x t)` is
smooth for every linear functional `f` on `X`. Then its image under any linear map `L` from `X`
to forms is a smooth family. -/
theorem isSmoothFamily_of_contMDiff_dual {X : Type*} [AddCommGroup X] [Module ℝ X]
    [FiniteDimensional ℝ X]
    (L : X →ₗ[ℝ] SmoothForm I' M' G l) {x : N → X}
    (hx : ∀ f : Module.Dual ℝ X, ContMDiff J 𝓘(ℝ) ∞ (fun t ↦ f (x t))) :
    IsSmoothFamily J (fun t ↦ L (x t)) :=
  isSmoothFamily_comp_of_contMDiff_repr (Module.finBasis ℝ X) L fun i ↦
    hx ((Module.finBasis ℝ X).coord i)

end Families

variable {S : Submodule ℝ (SmoothForm I' M' G l)}

/-- The evaluation `ω ↦ φ (ω x v)` of the forms of a submodule at a point `x`, on tangent vectors
`v`, followed by a continuous linear functional `φ`, as a linear functional on the submodule. -/
private def evalDual (x : M') (v : Fin l → TangentSpace I' x) (φ : StrongDual ℝ G) :
    Module.Dual ℝ S where
  toFun w := φ ((w : SmoothForm I' M' G l).val x v)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- Let `S` be a finite-dimensional submodule of forms and `T : D →ₗ[ℝ] S` a map such that
`S.subtype ∘ₗ T` preserves smooth families. Then every linear functional on `S` is smooth along
the image under `T` of a smooth family. -/
theorem PreservesSmoothFamilies.contMDiff_dual_apply [FiniteDimensional ℝ S] {T : D →ₗ[ℝ] S}
    (hT : PreservesSmoothFamilies (S.subtype ∘ₗ T)) {α : unitInterval → D}
    (hα : IsSmoothFamily (𝓡∂ 1) (fun t ↦ (α t : SmoothForm I M F k))) (f : Module.Dual ℝ S) :
    ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (fun t ↦ f (T (α t))) := by
  -- `X := S` makes Lean use the module instances of `S` itself, which it cannot match with
  -- those coming from an `AddCommGroup` through `smoothBundleForms`, whose definition is not
  -- exposed. `J` and `x` are given because the separating condition is elaborated before the
  -- goal fixes the parameter manifold.
  refine contMDiff_dual_apply_of_separating (J := 𝓡∂ 1) (X := S) (x := fun t ↦ T (α t))
    (s := Set.range fun p : (x : M') × (Fin l → TangentSpace I' x) × StrongDual ℝ G ↦
      evalDual (S := S) p.1 p.2.1 p.2.2) (fun z hz ↦ ?_) ?_ f
  · obtain ⟨x, v, hv⟩ : ∃ x v, (z : SmoothForm I' M' G l).val x v ≠ 0 := by
      by_contra! h
      exact hz (Subtype.ext (SmoothBundleForm.ext h))
    obtain ⟨φ, hφ⟩ := SeparatingDual.exists_ne_zero (R := ℝ) hv
    exact ⟨_, ⟨⟨x, v, φ⟩, rfl⟩, hφ⟩
  rintro _ ⟨⟨x, v, φ⟩, rfl⟩
  exact φ.contMDiff.comp ((hT α hα).contMDiff_apply x v)

/-- Let `b` be a finite basis of a space `S` of forms, and `T : D →ₗ[ℝ] S` a map whose
coordinates `t ↦ b.repr (T (α t)) i` are smooth along every smooth family `α`. Then `T`
followed by any linear map `U` on `S` preserves smooth families. -/
theorem preservesSmoothFamilies_comp_of_contMDiff_repr {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℝ S) {T : D →ₗ[ℝ] S}
    (h : ∀ α : unitInterval → D, IsSmoothFamily (𝓡∂ 1) (fun t ↦ (α t : SmoothForm I M F k)) →
      ∀ i, ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (fun t ↦ b.repr (T (α t)) i))
    (U : S →ₗ[ℝ] SmoothForm I'' M'' G' l') : PreservesSmoothFamilies (U ∘ₗ T) := fun α hα ↦ by
  simpa only [LinearMap.comp_apply] using
    isSmoothFamily_comp_of_contMDiff_repr b U (x := fun t ↦ T (α t)) (h α hα)

/-- **Maps into a finite-dimensional space of forms.** A linear map `T` into a
finite-dimensional space `S` of forms with a basis `b` preserves smooth families exactly when, for
every smooth family `α`, each coordinate `t ↦ b.repr (T (α t)) i` is smooth on the unit
interval. -/
theorem preservesSmoothFamilies_iff_contMDiff_repr {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℝ S) (T : D →ₗ[ℝ] S) :
    PreservesSmoothFamilies (S.subtype ∘ₗ T) ↔
      ∀ α : unitInterval → D, IsSmoothFamily (𝓡∂ 1) (fun t ↦ (α t : SmoothForm I M F k)) →
        ∀ i, ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (fun t ↦ b.repr (T (α t)) i) := by
  have := Module.Finite.of_basis b
  exact ⟨fun hT α hα i ↦ hT.contMDiff_dual_apply hα (b.coord i),
    fun h ↦ preservesSmoothFamilies_comp_of_contMDiff_repr b h S.subtype⟩

/-- A map that preserves smooth families into a finite-dimensional space `S` of forms, followed by
any linear map on `S`, preserves smooth families. -/
theorem PreservesSmoothFamilies.comp_of_finiteDimensional [FiniteDimensional ℝ S]
    {T : D →ₗ[ℝ] S} (hT : PreservesSmoothFamilies (S.subtype ∘ₗ T))
    (U : S →ₗ[ℝ] SmoothForm I'' M'' G' l') : PreservesSmoothFamilies (U ∘ₗ T) :=
  have := Module.Free.of_divisionRing ℝ S
  preservesSmoothFamilies_comp_of_contMDiff_repr (Module.finBasis ℝ S)
    (fun _ hα i ↦ hT.contMDiff_dual_apply hα ((Module.finBasis ℝ S).coord i)) U

end FiniteDimensional

end SymplecticGeometry
