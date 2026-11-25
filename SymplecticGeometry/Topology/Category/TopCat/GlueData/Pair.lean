/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Category.TopCat.GlueData

/-!
# Gluing two spaces along a homeomorphism of open subsets

For topological spaces `X` and `Y`, open subsets `U` of `X` and `V` of `Y`, and a homeomorphism
`e : U ≃ₜ V`, the gluing data `TopCat.GlueData.ofHomeomorph e` has the two pieces `X` and `Y`,
indexed by `ULift Bool` (`false` for `X`, `true` for `Y`), so that it lives in the universe of
`X` and `Y`. Its overlaps are `U` and `V`, and its transition maps are `e` and `e.symm`. In the
glued space a point `x` of `X` and a point `y` of `Y` have the same image exactly when `x ∈ U`
and `e x = y` (`TopCat.GlueData.ofHomeomorph_ι_false_eq_ι_true_iff`).

## Main declarations

* `TopCat.GlueData.ofHomeomorph`: the gluing of `X` and `Y` along `e`.
* `TopCat.GlueData.ofHomeomorph_ι_false_eq_ι_true_iff`,
  `TopCat.GlueData.ofHomeomorph_ι_true_eq_ι_false_iff`: when points of the two pieces are
  identified.
* `TopCat.GlueData.ofHomeomorph_ι_jointly_surjective`: every point of the glued space comes from
  one of the two pieces.
* `TopCat.GlueData.ofHomeomorph_t2Space_iff`: the two-piece form of Tau Ceti's Hausdorff
  criterion `TopCat.GlueData.t2Space_iff_forall_nhds`.

The construction follows Tau Ceti's `TauCeti.doubleGlueData`, which glues two copies of one
space along an open subset by the identity.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 1 (gluing spaces along open subsets).
-/

public section

open CategoryTheory TopologicalSpace Set Topology

universe u

namespace TopCat.GlueData

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {U : Opens X} {V : Opens Y}
  (e : U ≃ₜ V)

/-- The gluing of `X` and `Y` along a homeomorphism `e : U ≃ₜ V` of open subsets: the pieces
are `X` (index `false`) and `Y` (index `true`), the overlaps of the two pieces are `U` and `V`,
and the transition maps are `e` and `e.symm`. -/
@[expose] noncomputable def ofHomeomorph : TopCat.GlueData.{u} :=
  TopCat.GlueData.mk'
    { J := ULift.{u} Bool
      U := fun i ↦ match i with
        | ⟨false⟩ => TopCat.of X
        | ⟨true⟩ => TopCat.of Y
      V := fun i j ↦ match i, j with
        | ⟨false⟩, ⟨false⟩ => ⊤
        | ⟨false⟩, ⟨true⟩ => U
        | ⟨true⟩, ⟨false⟩ => V
        | ⟨true⟩, ⟨true⟩ => ⊤
      t := fun i j ↦ match i, j with
        | ⟨false⟩, ⟨false⟩ => 𝟙 _
        | ⟨false⟩, ⟨true⟩ => TopCat.ofHom (e : C(U, V))
        | ⟨true⟩, ⟨false⟩ => TopCat.ofHom (e.symm : C(V, U))
        | ⟨true⟩, ⟨true⟩ => 𝟙 _
      V_id := by rintro ⟨_ | _⟩ <;> rfl
      t_id := by rintro ⟨_ | _⟩ <;> rfl
      t_inter := by
        rintro ⟨_ | _⟩ ⟨_ | _⟩ ⟨_ | _⟩ x hx <;>
          first | exact hx | exact (e x).property | exact (e.symm x).property | trivial
      cocycle := by
        rintro ⟨_ | _⟩ ⟨_ | _⟩ ⟨_ | _⟩ x hx <;>
          first
          | rfl
          | exact congrArg Subtype.val (e.apply_symm_apply x)
          | exact congrArg Subtype.val (e.symm_apply_apply x) }

/-- The gluing along `e` is indexed by `ULift Bool`. -/
@[simp] theorem ofHomeomorph_J : (ofHomeomorph e).J = ULift.{u} Bool := (rfl)

/-- The piece of index `false` is `X`. -/
@[simp] theorem ofHomeomorph_U_false : (ofHomeomorph e).U ⟨false⟩ = TopCat.of X := (rfl)

/-- The piece of index `true` is `Y`. -/
@[simp] theorem ofHomeomorph_U_true : (ofHomeomorph e).U ⟨true⟩ = TopCat.of Y := (rfl)

/-- The overlap of the piece `X` with the piece `Y` is `U`. -/
@[simp] theorem ofHomeomorph_V_false_true :
    (ofHomeomorph e).V (⟨false⟩, ⟨true⟩) = TopCat.of U := (rfl)

/-- The overlap of the piece `Y` with the piece `X` is `V`. -/
@[simp] theorem ofHomeomorph_V_true_false :
    (ofHomeomorph e).V (⟨true⟩, ⟨false⟩) = TopCat.of V := (rfl)

/-- The overlap `U` includes into the piece `X` as a subspace. -/
@[simp] theorem ofHomeomorph_f_false_true :
    (ofHomeomorph e).f ⟨false⟩ ⟨true⟩ =
      TopCat.ofHom (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, X)) := (rfl)

/-- The overlap `V` includes into the piece `Y` as a subspace. -/
@[simp] theorem ofHomeomorph_f_true_false :
    (ofHomeomorph e).f ⟨true⟩ ⟨false⟩ =
      TopCat.ofHom (⟨Subtype.val, continuous_subtypeVal⟩ : C(V, Y)) := (rfl)

/-- The transition map from the overlap `U` to the overlap `V` is `e`. -/
@[simp] theorem ofHomeomorph_t_false_true :
    (ofHomeomorph e).t ⟨false⟩ ⟨true⟩ = TopCat.ofHom (e : C(U, V)) := (rfl)

/-- The transition map from the overlap `V` to the overlap `U` is `e.symm`. -/
@[simp] theorem ofHomeomorph_t_true_false :
    (ofHomeomorph e).t ⟨true⟩ ⟨false⟩ = TopCat.ofHom (e.symm : C(V, U)) := (rfl)

/-- A point `x` of `X` and a point `y` of `Y` have the same image in the glued space exactly
when `x ∈ U` and `e x = y`. -/
theorem ofHomeomorph_ι_false_eq_ι_true_iff {x : X} {y : Y} :
    (ofHomeomorph e).toGlueData.ι ⟨false⟩ x = (ofHomeomorph e).toGlueData.ι ⟨true⟩ y ↔
      ∃ h : x ∈ U, (e ⟨x, h⟩ : Y) = y := by
  -- `ι_eq_iff_rel` is stated for points of the pieces `(ofHomeomorph e).U i`, which are `X`
  -- and `Y` only after unfolding `ofHomeomorph`; apply it rather than rewriting with it.
  refine ((ofHomeomorph e).ι_eq_iff_rel ⟨false⟩ ⟨true⟩ x y).trans ⟨?_, ?_⟩
  · rintro ⟨⟨w, hw⟩, hx, h⟩
    have hx' : (w : X) = x := hx
    have hw' : (w : X) ∈ U := hw
    have h' : ((e ⟨w, hw'⟩ : V) : Y) = y := h
    refine ⟨hx' ▸ hw', ?_⟩
    rw [← h']
    congr
    exact hx'.symm
  · rintro ⟨h, rfl⟩
    exact ⟨⟨x, h⟩, rfl, rfl⟩

/-- A point `y` of `Y` and a point `x` of `X` have the same image in the glued space exactly
when `y ∈ V` and `e.symm y = x`. -/
theorem ofHomeomorph_ι_true_eq_ι_false_iff {y : Y} {x : X} :
    (ofHomeomorph e).toGlueData.ι ⟨true⟩ y = (ofHomeomorph e).toGlueData.ι ⟨false⟩ x ↔
      ∃ h : y ∈ V, (e.symm ⟨y, h⟩ : X) = x := by
  refine ((ofHomeomorph e).ι_eq_iff_rel ⟨true⟩ ⟨false⟩ y x).trans ⟨?_, ?_⟩
  · rintro ⟨⟨w, hw⟩, hx, h⟩
    have hx' : (w : Y) = y := hx
    have hw' : (w : Y) ∈ V := hw
    have h' : ((e.symm ⟨w, hw'⟩ : U) : X) = x := h
    refine ⟨hx' ▸ hw', ?_⟩
    rw [← h']
    congr
    exact hx'.symm
  · rintro ⟨h, rfl⟩
    exact ⟨⟨y, h⟩, rfl, rfl⟩

/-- A point of `U` and its image under `e` have the same image in the glued space. -/
theorem ofHomeomorph_ι_true_apply (x : U) :
    (ofHomeomorph e).toGlueData.ι ⟨true⟩ (e x : Y) =
      (ofHomeomorph e).toGlueData.ι ⟨false⟩ (x : X) :=
  ((ofHomeomorph_ι_false_eq_ι_true_iff e).2 ⟨x.property, rfl⟩).symm

/-- Every point of the glued space is the image of a point of `X` or of a point of `Y`. -/
theorem ofHomeomorph_ι_jointly_surjective (z : (ofHomeomorph e).toGlueData.glued) :
    (∃ x : X, (ofHomeomorph e).toGlueData.ι ⟨false⟩ x = z) ∨
      ∃ y : Y, (ofHomeomorph e).toGlueData.ι ⟨true⟩ y = z := by
  obtain ⟨⟨_ | _⟩, y, rfl⟩ := (ofHomeomorph e).ι_jointly_surjective z
  exacts [Or.inl ⟨y, rfl⟩, Or.inr ⟨y, rfl⟩]

/-- The space glued from `X` and `Y` along `e` is Hausdorff exactly when `X` and `Y` are, and
any point of `X` outside `U` and point of `Y` outside `V` have neighbourhoods `A` and `B` such
that `e` maps no point of `U ∩ A` into `B`. -/
theorem ofHomeomorph_t2Space_iff :
    T2Space (ofHomeomorph e).toGlueData.glued ↔ T2Space X ∧ T2Space Y ∧
      ∀ x ∉ U, ∀ y ∉ V, ∃ A ∈ 𝓝 x, ∃ B ∈ 𝓝 y, ∀ z : U, (z : X) ∈ A → (e z : Y) ∉ B := by
  refine (ofHomeomorph e).t2Space_iff_forall_nhds.trans ⟨?_, ?_⟩
  · rintro ⟨hT, h⟩
    refine ⟨hT ⟨false⟩, hT ⟨true⟩, fun x hx y hy ↦ h ⟨false⟩ ⟨true⟩ x ?_ y ?_⟩
    · rintro ⟨z, rfl⟩
      exact hx z.property
    · rintro ⟨z, rfl⟩
      exact hy z.property
  · rintro ⟨hX, hY, h⟩
    refine ⟨by rintro ⟨_ | _⟩ <;> assumption, ?_⟩
    rintro ⟨_ | _⟩ ⟨_ | _⟩ x hx y hy
    · exact (hx ⟨⟨x, True.intro⟩, rfl⟩).elim
    · exact h x (fun h' ↦ hx ⟨⟨x, h'⟩, rfl⟩) y (fun h' ↦ hy ⟨⟨y, h'⟩, rfl⟩)
    · obtain ⟨A, hA, B, hB, hAB⟩ :=
        h y (fun h' ↦ hy ⟨⟨y, h'⟩, rfl⟩) x (fun h' ↦ hx ⟨⟨x, h'⟩, rfl⟩)
      refine ⟨B, hB, A, hA, fun (z : V) hz hz' ↦ hAB (e.symm z) hz' ?_⟩
      rwa [e.apply_symm_apply]
    · exact (hx ⟨⟨x, True.intro⟩, rfl⟩).elim

end TopCat.GlueData

end
