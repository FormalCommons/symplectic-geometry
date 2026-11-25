/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import SymplecticGeometry.Geometry.Manifold.ContMDiff.Dual
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic

/-!
# Linear maps preserving smooth families of forms

A linear map `T`, defined on a submodule `D` of the smooth `k`-forms on `M` and with values in
the smooth `l`-forms on `M'`, *preserves smooth families*
(`SymplecticGeometry.PreservesSmoothFamilies`) when, for every smooth family `t ↦ α t` of forms
in `D` over a smooth parameter manifold `N`, the family `t ↦ T (α t)` is smooth again. The
parameter manifold may have boundary, as the unit interval does, and is arbitrary but for its
universe levels, which the definition takes as parameters. This is how the smoothness in a
parameter of the constructions behind smooth families of primitives is phrased: a linear
construction applied slice by slice to a smooth family gives a smooth family.

The property is closed under the linear operations on maps, under composition, and under
post-composition with the exterior derivative, pullback along a smooth map, and multiplication by
a smooth function; inclusions of submodules have it, and it can be checked on the restrictions
to two open sets covering the target.

A linear functional `f` on `D` is *smooth along smooth families*
(`SymplecticGeometry.SmoothAlongFamilies`) when `t ↦ f (α t)` is a smooth real function for every
such family `α`. For maps into a finite-dimensional space `S` of forms with a basis `b`,
preserving smooth families says that the coordinate functionals `b.coord i ∘ₗ T` are smooth
along smooth families (`SymplecticGeometry.preservesSmoothFamilies_iff_contMDiff_repr`).
One direction holds because each linear functional on `S` is a finite linear combination of
functionals `ω ↦ φ (ω x v)`, with `φ` a continuous linear functional on the coefficient
space, and these are smooth on smooth families; the other writes `T (α t)` as `∑ i, c i t • b i`.

## Main definitions

* `SymplecticGeometry.PreservesSmoothFamilies T`: the linear map `T` takes smooth families of
  forms over every smooth parameter manifold to smooth families.
* `SymplecticGeometry.SmoothAlongFamilies f`: the linear functional `f` is smooth along smooth
  families of forms over every smooth parameter manifold.

## Main results

* The closure lemmas `PreservesSmoothFamilies.add`, `.smul`, `.neg`, `.sub`, `.comp`,
  `.mextDerivₗ`, `.mpullback`, `.funSMul`, `.of_mpullback_inclusion_sup`, and
  `SymplecticGeometry.preservesSmoothFamilies_zero`,
  `SymplecticGeometry.preservesSmoothFamilies_subtype`; for functionals, `SmoothAlongFamilies.add`,
  `.smul`, `.neg`, `.sub`, `.comp`, `SymplecticGeometry.smoothAlongFamilies_zero` and
  `PreservesSmoothFamilies.smoothAlongFamilies_comp`.
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

universe uE uH uN

/-- **Linear maps preserving smooth families.** Let `T` be linear, defined on a submodule `D` of
the smooth `k`-forms on `M`, with values in the smooth `l`-forms on `M'`. Then `T` preserves
smooth families when, for every smooth parameter manifold `N`, possibly with boundary or
corners, whose model space, model and points lie in the universes `uE`, `uH` and `uN`, and every
family `α` of forms in `D` over `N` that is smooth as a family of forms on `M`, the family
`t ↦ T (α t)` is smooth. -/
def PreservesSmoothFamilies (T : D →ₗ[ℝ] SmoothForm I' M' G l) : Prop :=
  ∀ {EN : Type uE} [NormedAddCommGroup EN] [NormedSpace ℝ EN] {HN : Type uH}
    [TopologicalSpace HN] {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
    {J : ModelWithCorners ℝ EN HN} [IsManifold J ∞ N] (α : N → D),
    IsSmoothFamily J (fun t ↦ (α t : SmoothForm I M F k)) → IsSmoothFamily J (fun t ↦ T (α t))

/-- The defining property of `SymplecticGeometry.PreservesSmoothFamilies`. -/
theorem preservesSmoothFamilies_def {T : D →ₗ[ℝ] SmoothForm I' M' G l} :
    PreservesSmoothFamilies.{uE, uH, uN} T ↔
      ∀ {EN : Type uE} [NormedAddCommGroup EN] [NormedSpace ℝ EN] {HN : Type uH}
        [TopologicalSpace HN] {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
        {J : ModelWithCorners ℝ EN HN} [IsManifold J ∞ N] (α : N → D),
        IsSmoothFamily J (fun t ↦ (α t : SmoothForm I M F k)) →
          IsSmoothFamily J (fun t ↦ T (α t)) :=
  Iff.rfl

/-- The zero map preserves smooth families. -/
theorem preservesSmoothFamilies_zero :
    PreservesSmoothFamilies.{uE, uH, uN} (0 : D →ₗ[ℝ] SmoothForm I' M' G l) := fun _ _ ↦ by
  simp only [LinearMap.zero_apply]
  exact isSmoothFamily_const 0

/-- The inclusion of a submodule of forms preserves smooth families. -/
theorem preservesSmoothFamilies_subtype : PreservesSmoothFamilies.{uE, uH, uN} D.subtype :=
  fun _ hα ↦ hα

namespace PreservesSmoothFamilies

variable {T T₁ T₂ : D →ₗ[ℝ] SmoothForm I' M' G l}

/-- The sum of two maps preserving smooth families preserves smooth families. -/
protected theorem add (h₁ : PreservesSmoothFamilies.{uE, uH, uN} T₁)
    (h₂ : PreservesSmoothFamilies.{uE, uH, uN} T₂) :
    PreservesSmoothFamilies.{uE, uH, uN} (T₁ + T₂) := fun α hα ↦ by
  simpa only [LinearMap.add_apply, Pi.add_def] using (h₁ α hα).add (h₂ α hα)

/-- A constant multiple of a map preserving smooth families preserves smooth families. -/
protected theorem smul (hT : PreservesSmoothFamilies.{uE, uH, uN} T) (c : ℝ) :
    PreservesSmoothFamilies.{uE, uH, uN} (c • T) := fun α hα ↦ by
  simpa only [LinearMap.smul_apply] using (hT α hα).smul c

/-- The negative of a map preserving smooth families preserves smooth families. -/
protected theorem neg (hT : PreservesSmoothFamilies.{uE, uH, uN} T) :
    PreservesSmoothFamilies.{uE, uH, uN} (-T) :=
  fun α hα ↦ by simpa only [LinearMap.neg_apply] using (hT α hα).neg

/-- The difference of two maps preserving smooth families preserves smooth families. -/
protected theorem sub (h₁ : PreservesSmoothFamilies.{uE, uH, uN} T₁)
    (h₂ : PreservesSmoothFamilies.{uE, uH, uN} T₂) :
    PreservesSmoothFamilies.{uE, uH, uN} (T₁ - T₂) := fun α hα ↦ by
  simpa only [LinearMap.sub_apply, Pi.sub_def] using (h₁ α hα).sub (h₂ α hα)

/-- **Composition.** If `T` preserves smooth families and takes its values in a submodule `D'`,
and `S`, defined on `D'`, preserves smooth families, then so does `S` after `T`. -/
protected theorem comp {D' : Submodule ℝ (SmoothForm I' M' G l)}
    {S : D' →ₗ[ℝ] SmoothForm I'' M'' G' l'} (hS : PreservesSmoothFamilies.{uE, uH, uN} S)
    (hT : PreservesSmoothFamilies.{uE, uH, uN} T) (h : ∀ x, T x ∈ D') :
    PreservesSmoothFamilies.{uE, uH, uN} (S ∘ₗ T.codRestrict D' h) :=
  fun α hα ↦ hS (fun t ↦ T.codRestrict D' h (α t)) (hT α hα)

/-- Following a map that preserves smooth families by the exterior derivative gives a map that
preserves smooth families. -/
protected theorem mextDerivₗ [IsManifold I' 2 M'] (hT : PreservesSmoothFamilies.{uE, uH, uN} T) :
    PreservesSmoothFamilies.{uE, uH, uN} (mextDerivₗ I' l ∘ₗ T) :=
  fun α hα ↦ (hT α hα).mextDeriv

/-- Following a map that preserves smooth families by the pullback along a smooth map gives a map
that preserves smooth families. -/
protected theorem mpullback (hT : PreservesSmoothFamilies.{uE, uH, uN} T) (f : M'' → M')
    (hf : ContMDiff I'' I' ∞ f) :
    PreservesSmoothFamilies.{uE, uH, uN} (SmoothForm.mpullback f hf ∘ₗ T) :=
  fun α hα ↦ (hT α hα).mpullback f hf

/-- Following a map that preserves smooth families by the multiplication with a smooth function
gives a map that preserves smooth families. -/
protected theorem funSMul (hT : PreservesSmoothFamilies.{uE, uH, uN} T)
    (g : C^∞⟮I', M'; ℝ⟯) :
    PreservesSmoothFamilies.{uE, uH, uN} (SmoothForm.funSMulₗ g ∘ₗ T) :=
  fun α hα ↦ (hT α hα).funSMul g

/-- **Gluing.** A map into the forms on `U ⊔ V` preserves smooth families when its restrictions
to `U` and to `V` do. -/
protected theorem of_mpullback_inclusion_sup {U V : Opens M'}
    {T : D →ₗ[ℝ] SmoothForm I' (U ⊔ V : Opens M') G l}
    (hU : PreservesSmoothFamilies.{uE, uH, uN}
      (SmoothForm.mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) ∘ₗ T))
    (hV : PreservesSmoothFamilies.{uE, uH, uN}
      (SmoothForm.mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) ∘ₗ T)) :
    PreservesSmoothFamilies.{uE, uH, uN} T :=
  fun α hα ↦ isSmoothFamily_iff_mpullback_inclusion_sup.mpr ⟨hU α hα, hV α hα⟩

end PreservesSmoothFamilies

/-- **Linear functionals smooth along smooth families.** A linear functional `f` on a submodule
`D` of the smooth `k`-forms on `M` is smooth along smooth families when, for every smooth
parameter manifold `N`, possibly with boundary or corners, whose model space, model and points
lie in the universes `uE`, `uH` and `uN`, and every family `α` of forms in `D` over `N` that is
smooth as a family of forms on `M`, the real function `t ↦ f (α t)` is smooth on `N`. -/
def SmoothAlongFamilies (f : D →ₗ[ℝ] ℝ) : Prop :=
  ∀ {EN : Type uE} [NormedAddCommGroup EN] [NormedSpace ℝ EN] {HN : Type uH}
    [TopologicalSpace HN] {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
    {J : ModelWithCorners ℝ EN HN} [IsManifold J ∞ N] (α : N → D),
    IsSmoothFamily J (fun t ↦ (α t : SmoothForm I M F k)) → ContMDiff J 𝓘(ℝ) ∞ (fun t ↦ f (α t))

/-- The defining property of `SymplecticGeometry.SmoothAlongFamilies`. -/
theorem smoothAlongFamilies_def {f : D →ₗ[ℝ] ℝ} :
    SmoothAlongFamilies.{uE, uH, uN} f ↔
      ∀ {EN : Type uE} [NormedAddCommGroup EN] [NormedSpace ℝ EN] {HN : Type uH}
        [TopologicalSpace HN] {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
        {J : ModelWithCorners ℝ EN HN} [IsManifold J ∞ N] (α : N → D),
        IsSmoothFamily J (fun t ↦ (α t : SmoothForm I M F k)) →
          ContMDiff J 𝓘(ℝ) ∞ (fun t ↦ f (α t)) :=
  Iff.rfl

/-- The zero functional is smooth along smooth families. -/
theorem smoothAlongFamilies_zero : SmoothAlongFamilies.{uE, uH, uN} (0 : D →ₗ[ℝ] ℝ) :=
  fun _ _ ↦ by simpa only [LinearMap.zero_apply] using contMDiff_const

namespace SmoothAlongFamilies

variable {f f₁ f₂ : D →ₗ[ℝ] ℝ}

/-- The sum of two functionals smooth along smooth families is smooth along smooth families. -/
protected theorem add (h₁ : SmoothAlongFamilies.{uE, uH, uN} f₁)
    (h₂ : SmoothAlongFamilies.{uE, uH, uN} f₂) : SmoothAlongFamilies.{uE, uH, uN} (f₁ + f₂) :=
  fun α hα ↦ contDiff_add.contMDiff.comp ((h₁ α hα).prodMk_space (h₂ α hα))

/-- A constant multiple of a functional smooth along smooth families is smooth along smooth
families. -/
protected theorem smul (hf : SmoothAlongFamilies.{uE, uH, uN} f) (c : ℝ) :
    SmoothAlongFamilies.{uE, uH, uN} (c • f) :=
  fun α hα ↦ ((contDiff_const_smul c).contMDiff).comp (hf α hα)

/-- The negative of a functional smooth along smooth families is smooth along smooth families. -/
protected theorem neg (hf : SmoothAlongFamilies.{uE, uH, uN} f) :
    SmoothAlongFamilies.{uE, uH, uN} (-f) :=
  fun α hα ↦ by simpa only [LinearMap.neg_apply, Pi.neg_def] using (hf α hα).neg

/-- The difference of two functionals smooth along smooth families is smooth along smooth
families. -/
protected theorem sub (h₁ : SmoothAlongFamilies.{uE, uH, uN} f₁)
    (h₂ : SmoothAlongFamilies.{uE, uH, uN} f₂) : SmoothAlongFamilies.{uE, uH, uN} (f₁ - f₂) :=
  fun α hα ↦ by simpa only [LinearMap.sub_apply] using (h₁ α hα).sub (h₂ α hα)

/-- **Composition.** If `T` preserves smooth families and takes its values in a submodule `D'`,
and the functional `g` on `D'` is smooth along smooth families, then so is `g` after `T`. -/
protected theorem comp {D' : Submodule ℝ (SmoothForm I' M' G l)} {g : D' →ₗ[ℝ] ℝ}
    {T : D →ₗ[ℝ] SmoothForm I' M' G l} (hg : SmoothAlongFamilies.{uE, uH, uN} g)
    (hT : PreservesSmoothFamilies.{uE, uH, uN} T) (h : ∀ x, T x ∈ D') :
    SmoothAlongFamilies.{uE, uH, uN} (g ∘ₗ T.codRestrict D' h) :=
  fun α hα ↦ hg (fun t ↦ T.codRestrict D' h (α t)) (hT α hα)

end SmoothAlongFamilies

section FiniteDimensional

/-- **Finite linear combinations of fixed forms.** If the real coefficients `c i` are linear on
`D` and smooth along smooth families, then `x ↦ ∑ i ∈ s, c i x • w i` preserves smooth
families. -/
theorem preservesSmoothFamilies_sum_smulRight {ι : Type*} (s : Finset ι)
    (c : ι → D →ₗ[ℝ] ℝ) (w : ι → SmoothForm I' M' G l)
    (hc : ∀ i ∈ s, SmoothAlongFamilies.{uE, uH, uN} (c i)) :
    PreservesSmoothFamilies.{uE, uH, uN} (∑ i ∈ s, (c i).smulRight (w i)) := fun α hα ↦ by
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply]
  exact IsSmoothFamily.sum fun i hi ↦
    (isSmoothFamily_const (w i)).fun_smul (hc i hi α hα)

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
the image under `T` of a smooth family over a smooth manifold `N`. -/
theorem PreservesSmoothFamilies.contMDiff_dual_apply [FiniteDimensional ℝ S] {T : D →ₗ[ℝ] S}
    (hT : PreservesSmoothFamilies.{uE, uH, uN} (S.subtype ∘ₗ T)) {EN : Type uE}
    [NormedAddCommGroup EN] [NormedSpace ℝ EN] {HN : Type uH} [TopologicalSpace HN]
    {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN}
    [IsManifold J ∞ N] {α : N → D} (hα : IsSmoothFamily J (fun t ↦ (α t : SmoothForm I M F k)))
    (f : Module.Dual ℝ S) :
    ContMDiff J 𝓘(ℝ) ∞ (fun t ↦ f (T (α t))) := by
  -- `X := S` makes Lean use the module instances of `S` itself, which it cannot match with
  -- those coming from an `AddCommGroup` through `smoothBundleForms`, whose definition is not
  -- exposed. `x` is given because the separating condition is elaborated before the goal fixes
  -- the family.
  refine contMDiff_dual_apply_of_separating (J := J) (X := S) (x := fun t ↦ T (α t))
    (s := Set.range fun p : (x : M') × (Fin l → TangentSpace I' x) × StrongDual ℝ G ↦
      evalDual (S := S) p.1 p.2.1 p.2.2) (fun z hz ↦ ?_) ?_ f
  · obtain ⟨x, v, hv⟩ : ∃ x v, (z : SmoothForm I' M' G l).val x v ≠ 0 := by
      by_contra! h
      exact hz (Subtype.ext (SmoothBundleForm.ext h))
    obtain ⟨φ, hφ⟩ := SeparatingDual.exists_ne_zero (R := ℝ) hv
    exact ⟨_, ⟨⟨x, v, φ⟩, rfl⟩, hφ⟩
  rintro _ ⟨⟨x, v, φ⟩, rfl⟩
  exact φ.contMDiff.comp ((hT α hα).contMDiff_apply x v)

/-- Let `S` be a finite-dimensional submodule of forms and `T : D →ₗ[ℝ] S` a map such that
`S.subtype ∘ₗ T` preserves smooth families. Then every linear functional on `S`, after `T`, is
smooth along smooth families. -/
theorem PreservesSmoothFamilies.smoothAlongFamilies_comp [FiniteDimensional ℝ S]
    {T : D →ₗ[ℝ] S} (hT : PreservesSmoothFamilies.{uE, uH, uN} (S.subtype ∘ₗ T))
    (f : Module.Dual ℝ S) : SmoothAlongFamilies.{uE, uH, uN} (f ∘ₗ T) :=
  fun _ hα ↦ hT.contMDiff_dual_apply hα f

/-- Let `b` be a finite basis of a space `S` of forms, and `T : D →ₗ[ℝ] S` a map whose
coordinates `t ↦ b.repr (T (α t)) i` are smooth along every smooth family `α`. Then `T`
followed by any linear map `U` on `S` preserves smooth families. -/
theorem preservesSmoothFamilies_comp_of_contMDiff_repr {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℝ S) {T : D →ₗ[ℝ] S}
    (h : ∀ i, SmoothAlongFamilies.{uE, uH, uN} (b.coord i ∘ₗ T))
    (U : S →ₗ[ℝ] SmoothForm I'' M'' G' l') : PreservesSmoothFamilies.{uE, uH, uN} (U ∘ₗ T) :=
  fun α hα ↦ by
    simpa only [LinearMap.comp_apply] using
      isSmoothFamily_comp_of_contMDiff_repr b U (x := fun t ↦ T (α t)) fun i ↦ by
        simpa only [LinearMap.comp_apply, Module.Basis.coord_apply] using h i α hα

/-- **Maps into a finite-dimensional space of forms.** A linear map `T` into a
finite-dimensional space `S` of forms with a basis `b` preserves smooth families exactly when, for
every smooth family `α` over a smooth manifold `N`, each coordinate `t ↦ b.repr (T (α t)) i` is
smooth on `N`. -/
theorem preservesSmoothFamilies_iff_contMDiff_repr {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℝ S) (T : D →ₗ[ℝ] S) :
    PreservesSmoothFamilies.{uE, uH, uN} (S.subtype ∘ₗ T) ↔
      ∀ i, SmoothAlongFamilies.{uE, uH, uN} (b.coord i ∘ₗ T) := by
  have := Module.Finite.of_basis b
  exact ⟨fun hT i ↦ hT.smoothAlongFamilies_comp (b.coord i),
    fun h ↦ preservesSmoothFamilies_comp_of_contMDiff_repr b h S.subtype⟩

/-- A map that preserves smooth families into a finite-dimensional space `S` of forms, followed by
any linear map on `S`, preserves smooth families. -/
theorem PreservesSmoothFamilies.comp_of_finiteDimensional [FiniteDimensional ℝ S]
    {T : D →ₗ[ℝ] S} (hT : PreservesSmoothFamilies.{uE, uH, uN} (S.subtype ∘ₗ T))
    (U : S →ₗ[ℝ] SmoothForm I'' M'' G' l') : PreservesSmoothFamilies.{uE, uH, uN} (U ∘ₗ T) :=
  have := Module.Free.of_divisionRing ℝ S
  preservesSmoothFamilies_comp_of_contMDiff_repr (Module.finBasis ℝ S)
    (fun i ↦ hT.smoothAlongFamilies_comp ((Module.finBasis ℝ S).coord i)) U

end FiniteDimensional

end SymplecticGeometry
