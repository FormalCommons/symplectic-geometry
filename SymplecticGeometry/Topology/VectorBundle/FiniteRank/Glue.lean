/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback

/-!
# Gluing a finite-rank core over two open sets by an automorphism

Let `A` be a point-indexed finite-rank core over `B`, let `U` and `V` be open sets covering `B`,
and let `g` be an automorphism of the restriction of `A` to `U ∩ V`, that is, of the pullback of
`A` along the inclusion of `U ∩ V`. This file builds the core `A.glue hU hV hUV g` that is `A` over
`U` and over `V`, the vector `v` over `b ∈ U ∩ V` in the copy over `V` being identified with
`g_b v` in the copy over `U`. This is the clutching construction of a bundle from a clutching
function [Hatcher2017, §1.2], over any base, any field and any rank.

The chart of the glued core at `x` is the chart of `A` at `x` cut down to `U` if `x ∈ U`, and to
`V` otherwise. In fibre coordinates its transition from the chart at `x` to the chart at `y` is the
chart expression of `glueCocycle g s t b`, where `s = glueIndex U x` and `t = glueIndex U y` are
the sides of `x` and `y` (`true` for `U`): the identity for charts on the same side, the fibre
map of `g.hom` from `V` to `U`, and that of `g.inv` from `U` to `V`. Its continuity comes from
that of the chart expressions, in charts of `A` at arbitrary points, of a morphism between
pullbacks to a subset (`continuousOn_inChartCoordinates_fiberMap_pullback_subtypeVal`), and the
cocycle condition from `g.hom ≫ g.inv = 𝟙` and `g.inv ≫ g.hom = 𝟙` (`glueCocycle_comp`).

## Main definitions and results

* `TauCeti.FiniteRankBundleCore.glueSide U V s` and `TauCeti.FiniteRankBundleCore.glueIndex U x`:
  the set `U` or `V` of the side `s`, and the side of the chart at `x`.
* `TauCeti.FiniteRankBundleCore.glueCocycle g s t b`: the fibre map from the side `s` to the
  side `t` at `b` (`true` for `U`, `false` for `V`).
* `TauCeti.FiniteRankBundleCore.glue`: the glued core, of rank `A.rank` (`rank_glue`), with the
  transitions of `A` between charts on the same side (`coordChange_glue_of_glueIndex_eq`) and `g`
  between charts on different sides (`coordChange_glue_of_notMem_of_mem`,
  `coordChange_glue_of_mem_of_notMem`).
* `TauCeti.FiniteRankBundleCore.glueRestrictIso`: over `U` (`s = true`) and over `V`
  (`s = false`), the restriction of the glued core is isomorphic to that of `A`, by the
  gluing cocycle from the side of each point to `s`. Over `U` it is the identity in coordinates
  (`fiberMap_glueRestrictIso_true_hom`); over `V` it is `g.inv` on `U ∩ V`
  (`fiberMap_glueRestrictIso_false_hom`).
* `TauCeti.FiniteRankBundleCore.glueReflIso`: gluing by the identity gives back `A`.

The construction follows the pattern of Tau Ceti's `TauCeti.FiniteRankBundleCore.doubleAlong`, a
point-indexed core whose transitions are given piecewise, and of
`SymplecticGeometry.Bundle.twoChartCore`, two charts glued along a transition. The isomorphism
`glueReflIso` is built, as Tau Ceti's `TauCeti.FiniteRankBundleCore.doubleAlongInlIso` is, with
`TauCeti.FiniteRankBundleCore.constIso`.

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §1.2 (clutching functions).
-/

public section

noncomputable section

open Set CategoryTheory Topology Filter

/-- The chart expression of the identity, between two charts of a core at a point of both, is
their coordinate change. -/
theorem VectorBundleCore.inChartCoordinates_id {𝕜 B F ι : Type*} [NontriviallyNormedField 𝕜]
    [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace 𝕜 F] (Z : VectorBundleCore 𝕜 B F ι)
    {i j : ι} {x : B} (hi : x ∈ Z.baseSet i) (hj : x ∈ Z.baseSet j) :
    Z.inChartCoordinates Z i j x (ContinuousLinearMap.id 𝕜 F) = Z.coordChange i j x := by
  ext v : 1
  rw [VectorBundleCore.inChartCoordinates_apply, ContinuousLinearMap.id_apply,
    Z.coordChange_comp _ _ _ x ⟨⟨hi, Z.mem_baseSet_at x⟩, hj⟩]

namespace TauCeti.FiniteRankBundleCore

/-! ### The two sides of the gluing -/

section Side

variable {B : Type*} {U V : Set B}

/-- The set over which the side `s` of a gluing over `U` and `V` lies: `U` for `true`, `V` for
`false`. -/
abbrev glueSide (U V : Set B) (s : Bool) : Set B :=
  bif s then U else V

open Classical in
/-- The side of a gluing over `U` and a second set on which the chart at `x` lies: `true` (the
side `U`) exactly when `x ∈ U`. -/
def glueIndex (U : Set B) (x : B) : Bool :=
  decide (x ∈ U)

@[simp]
theorem glueIndex_eq_true_iff {x : B} : glueIndex U x = true ↔ x ∈ U := by
  classical
  simp [glueIndex]

@[simp]
theorem glueIndex_eq_false_iff {x : B} : glueIndex U x = false ↔ x ∉ U := by
  classical
  simp [glueIndex]

/-- Each point lies on its own side: in `U` if it is in `U`, and otherwise in `V`. -/
theorem mem_glueSide_glueIndex (hUV : U ∪ V = univ) (x : B) :
    x ∈ glueSide U V (glueIndex U x) := by
  by_cases hx : x ∈ U
  · simp [glueIndex_eq_true_iff.2 hx, hx]
  · simpa [glueIndex_eq_false_iff.2 hx] using
      (hUV.symm ▸ mem_univ x : x ∈ U ∪ V).resolve_left hx

end Side

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]

/-! ### Chart expressions of a morphism over a subset -/

section ChartExpression

variable {A D : FiniteRankBundleCore 𝕜 B} {W : Set B}

/-- The chart expression, in any two charts of `A` and `D`, of a morphism between the
restrictions of `A` and `D` to a subset `W` is continuous where both charts are defined. -/
theorem continuousOn_inChartCoordinates_fiberMap_pullback_subtypeVal
    (a : A.pullback (ContinuousMap.subtypeVal W) ⟶ D.pullback (ContinuousMap.subtypeVal W))
    (x y : B) :
    ContinuousOn (fun w : W ↦ A.core.inChartCoordinates D.core x y w (a.fiberMap w))
      (Subtype.val ⁻¹' (A.core.baseSet x ∩ D.core.baseSet y)) := by
  have hopen : ∀ s : Set B, IsOpen s → IsOpen (Subtype.val ⁻¹' s : Set W) :=
    fun s hs ↦ hs.preimage continuous_subtypeVal
  intro w₀ hw₀
  set b₀ : B := w₀.val
  -- Read the morphism in the charts at `b₀` of the two pullbacks, then change charts.
  set S : Set W := Subtype.val ⁻¹' (A.core.baseSet b₀ ∩ D.core.baseSet b₀)
  have hS : IsOpen S := hopen _ ((A.core.isOpen_baseSet _).inter (D.core.isOpen_baseSet _))
  have hw₀S : w₀ ∈ S := ⟨A.mem_baseSet_self b₀, D.mem_baseSet_self b₀⟩
  have h₁ : ContinuousAt (fun w : W ↦ A.core.inChartCoordinates D.core b₀ b₀ w (a.fiberMap w))
      w₀ := by
    have := VectorBundleCore.continuousOn_inChartCoordinates (i := w₀) (j := w₀)
      a.continuous_fiberMap.continuousOn
    simp only [inChartCoordinates_pullback] at this
    exact this.continuousAt (hS.mem_nhds hw₀S)
  have hcc : ∀ (C : FiniteRankBundleCore 𝕜 B) (i j : B), b₀ ∈ C.core.baseSet i →
      b₀ ∈ C.core.baseSet j → ContinuousAt (fun w : W ↦ C.core.coordChange i j w) w₀ :=
    fun C i j hi hj ↦ ((C.core.continuousOn_coordChange i j).continuousAt
      (((C.core.isOpen_baseSet i).inter (C.core.isOpen_baseSet j)).mem_nhds ⟨hi, hj⟩)).comp
      continuous_subtypeVal.continuousAt
  have h₂ := hcc D b₀ y (D.mem_baseSet_self b₀) hw₀.2
  have h₃ := hcc A x b₀ hw₀.1 (A.mem_baseSet_self b₀)
  refine ((h₂.clm_comp (h₁.clm_comp h₃)).congr ?_).continuousWithinAt
  have hT : IsOpen (S ∩ Subtype.val ⁻¹' (A.core.baseSet x ∩ D.core.baseSet y)) :=
    hS.inter (hopen _ ((A.core.isOpen_baseSet _).inter (D.core.isOpen_baseSet _)))
  filter_upwards [hT.mem_nhds ⟨hw₀S, hw₀⟩] with w hw
  ext v
  simp only [ContinuousLinearMap.comp_apply, inChartCoordinates_core_apply]
  rw [D.core.coordChange_comp _ _ _ _ ⟨⟨D.mem_baseSet_self _, hw.1.2⟩, hw.2.2⟩,
    A.core.coordChange_comp _ _ _ _ ⟨⟨hw.2.1, hw.1.1⟩, A.mem_baseSet_self _⟩]

end ChartExpression

/-! ### The cocycle of the gluing -/

section Cocycle

variable {A : FiniteRankBundleCore 𝕜 B} {U V : Set B}
  (g : A.pullback (ContinuousMap.subtypeVal (U ∩ V)) ≅
    A.pullback (ContinuousMap.subtypeVal (U ∩ V)))

open scoped Classical in
/-- The fibre map at `b` from the side `s` to the side `t` of the gluing of `A` over `U` and `V`
by `g`, sides being `true` for `U` and `false` for `V`: the identity from a side to itself, the
fibre map of `g.hom` from `V` to `U`, and that of `g.inv` from `U` to `V`. Off `U ∩ V` it is the
identity. -/
def glueCocycle : Bool → Bool → B → (Fin A.rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜)
  | false, true, b => if h : b ∈ U ∩ V then g.hom.fiberMap ⟨b, h⟩ else .id 𝕜 _
  | true, false, b => if h : b ∈ U ∩ V then g.inv.fiberMap ⟨b, h⟩ else .id 𝕜 _
  | _, _, _ => .id 𝕜 _

@[simp]
theorem glueCocycle_self (s : Bool) (b : B) : glueCocycle g s s b = .id 𝕜 _ := by
  cases s <;> rfl

theorem glueCocycle_false_true {b : B} (hb : b ∈ U ∩ V) :
    glueCocycle g false true b = g.hom.fiberMap ⟨b, hb⟩ :=
  dite_eq_left hb

theorem glueCocycle_true_false {b : B} (hb : b ∈ U ∩ V) :
    glueCocycle g true false b = g.inv.fiberMap ⟨b, hb⟩ :=
  dite_eq_left hb

/-- The cocycle condition of the gluing at a point of the three sides. -/
theorem glueCocycle_comp (s t r : Bool) {b : B}
    (hb : b ∈ glueSide U V s ∩ glueSide U V t ∩ glueSide U V r) :
    (glueCocycle g t r b).comp (glueCocycle g s t b) = glueCocycle g s r b := by
  have hhi : ∀ h : b ∈ U ∩ V, (g.inv.fiberMap ⟨b, h⟩).comp (g.hom.fiberMap ⟨b, h⟩) = .id 𝕜 _ :=
    fun h ↦ by rw [← fiberMap_comp, g.hom_inv_id, fiberMap_id]
  have hih : ∀ h : b ∈ U ∩ V, (g.hom.fiberMap ⟨b, h⟩).comp (g.inv.fiberMap ⟨b, h⟩) = .id 𝕜 _ :=
    fun h ↦ by rw [← fiberMap_comp, g.inv_hom_id, fiberMap_id]
  rcases hb with ⟨⟨hs, ht⟩, hr⟩
  cases s <;> cases t <;> cases r <;>
    simp only [glueSide, Bool.cond_true, Bool.cond_false] at hs ht hr
  all_goals try first
    | (simp only [glueCocycle_self, ContinuousLinearMap.id_comp]; done)
    | (simp only [glueCocycle_self, ContinuousLinearMap.comp_id]; done)
  · have h : b ∈ U ∩ V := ⟨ht, hs⟩
    rw [glueCocycle_false_true g h, glueCocycle_true_false g h, hhi, glueCocycle_self]
    -- Both sides agree once the ranks of the fibre models are unfolded.
    rfl
  · have h : b ∈ U ∩ V := ⟨hs, ht⟩
    rw [glueCocycle_true_false g h, glueCocycle_false_true g h, hih, glueCocycle_self]
    -- Both sides agree once the ranks of the fibre models are unfolded.
    rfl

/-- The chart expressions of the gluing cocycle compose as the cocycle does, through a chart
containing the point. -/
theorem inChartCoordinates_glueCocycle_comp {s t r : Bool} {x y z b : B}
    (hb : b ∈ glueSide U V s ∩ glueSide U V t ∩ glueSide U V r) (hy : b ∈ A.core.baseSet y) :
    (A.core.inChartCoordinates A.core y z b (glueCocycle g t r b)).comp
        (A.core.inChartCoordinates A.core x y b (glueCocycle g s t b)) =
      A.core.inChartCoordinates A.core x z b (glueCocycle g s r b) := by
  rw [← VectorBundleCore.inChartCoordinates_comp _ _ _ _ _ hy, glueCocycle_comp g s t r hb]

/-- The chart expressions of the gluing cocycle in two charts of `A` are continuous where both
charts and both sides are defined. -/
theorem continuousOn_inChartCoordinates_glueCocycle (hU : IsOpen U) (hV : IsOpen V)
    (s t : Bool) (x y : B) :
    ContinuousOn (fun b ↦ A.core.inChartCoordinates A.core x y b (glueCocycle g s t b))
      (A.core.baseSet x ∩ A.core.baseSet y ∩ glueSide U V s ∩ glueSide U V t) := by
  by_cases hst : s = t
  · subst hst
    refine ((A.core.continuousOn_coordChange x y).mono fun b
      (hb : b ∈ A.core.baseSet x ∩ A.core.baseSet y ∩ glueSide U V s ∩ glueSide U V s) ↦
        hb.1.1).congr fun b hb ↦ ?_
    rw [glueCocycle_self, A.core.inChartCoordinates_id hb.1.1.1 hb.1.1.2]
  -- On different sides the domain lies in `U ∩ V`; read it through the inclusion of `U ∩ V`.
  have hUV : IsOpen (U ∩ V) := hU.inter hV
  have hsub : glueSide U V s ∩ glueSide U V t ⊆ U ∩ V := by
    cases s <;> cases t <;> simp_all [inter_comm]
  let a : A.pullback (ContinuousMap.subtypeVal (U ∩ V)) ⟶
      A.pullback (ContinuousMap.subtypeVal (U ∩ V)) := bif t then g.hom else g.inv
  have ha : ∀ w : ↥(U ∩ V), glueCocycle g s t w = a.fiberMap w := by
    intro w
    cases s <;> cases t <;> simp_all [glueCocycle_false_true g w.property,
      glueCocycle_true_false g w.property, a]
  have hc := continuousOn_inChartCoordinates_fiberMap_pullback_subtypeVal a x y
  intro b hb
  have hbUV : b ∈ U ∩ V := hsub ⟨hb.1.2, hb.2⟩
  have hopen : IsOpen (A.core.baseSet x ∩ A.core.baseSet y) :=
    (A.core.isOpen_baseSet x).inter (A.core.isOpen_baseSet y)
  refine ContinuousAt.continuousWithinAt ?_
  rw [← hUV.isOpenEmbedding_subtypeVal.continuousAt_iff (x := ⟨b, hbUV⟩)]
  refine ((hc ⟨b, hbUV⟩ hb.1.1).continuousAt
    ((hopen.preimage continuous_subtypeVal).mem_nhds hb.1.1)).congr
    (Eventually.of_forall fun w ↦ ?_)
  simp only [Function.comp_apply, ha]

end Cocycle

/-! ### The glued core -/

section Glue

variable (A : FiniteRankBundleCore 𝕜 B) {U V : Set B} (hU : IsOpen U) (hV : IsOpen V)
  (hUV : U ∪ V = univ)
  (g : A.pullback (ContinuousMap.subtypeVal (U ∩ V)) ≅
    A.pullback (ContinuousMap.subtypeVal (U ∩ V)))

/-- **The gluing of `A` over `U` and `V` by `g`.** The core over `B` that is `A` over `U` and over
`V`, a vector `v` over `b ∈ U ∩ V` in the copy over `V` being the vector `g_b v` in the copy over
`U`. The chart at `x` is that of `A` cut down to `U` if `x ∈ U` and to `V` otherwise. -/
-- Expose the rank so that the fibre model of the glued core reduces to that of `A`.
@[expose, implicit_reducible]
def glue : FiniteRankBundleCore 𝕜 B where
  rank := A.rank
  core :=
    { baseSet := fun x ↦ A.core.baseSet x ∩ glueSide U V (glueIndex U x)
      isOpen_baseSet := fun x ↦ (A.core.isOpen_baseSet x).inter <| by
        cases glueIndex U x <;> assumption
      indexAt := id
      mem_baseSet_at := fun x ↦ ⟨A.mem_baseSet_self x, mem_glueSide_glueIndex hUV x⟩
      coordChange := fun x y b ↦
        A.core.inChartCoordinates A.core x y b (glueCocycle g (glueIndex U x) (glueIndex U y) b)
      coordChange_self := fun x b hb v ↦ by
        rw [glueCocycle_self, inChartCoordinates_core_apply, ContinuousLinearMap.id_apply,
          A.core.coordChange_comp _ _ _ _ ⟨⟨hb.1, A.mem_baseSet_self b⟩, hb.1⟩,
          A.core.coordChange_self _ _ hb.1]
      continuousOn_coordChange := fun x y ↦
        (continuousOn_inChartCoordinates_glueCocycle g hU hV _ _ x y).mono
          fun b hb ↦ ⟨⟨⟨hb.1.1, hb.2.1⟩, hb.1.2⟩, hb.2.2⟩
      coordChange_comp := fun x y z b hb v ↦ by
        rw [← ContinuousLinearMap.comp_apply,
          inChartCoordinates_glueCocycle_comp g ⟨⟨hb.1.1.2, hb.1.2.2⟩, hb.2.2⟩ hb.1.2.1] }
  indexAt_eq := fun _ ↦ rfl

@[simp]
theorem rank_glue : (A.glue hU hV hUV g).rank = A.rank :=
  (rfl)

theorem baseSet_glue (x : B) :
    (A.glue hU hV hUV g).core.baseSet x = A.core.baseSet x ∩ glueSide U V (glueIndex U x) :=
  (rfl)

@[simp]
theorem localTriv_baseSet_glue (x : B) :
    ((A.glue hU hV hUV g).core.localTriv x).baseSet =
      A.core.baseSet x ∩ glueSide U V (glueIndex U x) :=
  (rfl)

theorem coordChange_glue (x y b : B) :
    (A.glue hU hV hUV g).core.coordChange x y b =
      A.core.inChartCoordinates A.core x y b
        (glueCocycle g (glueIndex U x) (glueIndex U y) b) :=
  (rfl)

/-- Between two charts on the same side, the transition of the glued core is that of `A`. -/
theorem coordChange_glue_of_glueIndex_eq {x y b : B} (hxy : glueIndex U x = glueIndex U y)
    (hb : b ∈ A.core.baseSet x ∩ A.core.baseSet y) :
    (A.glue hU hV hUV g).core.coordChange x y b = A.core.coordChange x y b := by
  rw [coordChange_glue, hxy, glueCocycle_self, A.core.inChartCoordinates_id hb.1 hb.2]

/-- From a chart on the side `V` to a chart on the side `U`, at a point of `U ∩ V`, the
transition of the glued core is the fibre map of `g.hom` read in the two charts of `A`. -/
theorem coordChange_glue_of_notMem_of_mem {x y b : B} (hx : x ∉ U) (hy : y ∈ U)
    (hb : b ∈ U ∩ V) :
    (A.glue hU hV hUV g).core.coordChange x y b =
      (A.core.coordChange b y b).comp
        ((g.hom.fiberMap ⟨b, hb⟩).comp (A.core.coordChange x b b)) := by
  rw [coordChange_glue, glueIndex_eq_false_iff.2 hx, glueIndex_eq_true_iff.2 hy,
    glueCocycle_false_true g hb, inChartCoordinates_core]

/-- From a chart on the side `U` to a chart on the side `V`, at a point of `U ∩ V`, the
transition of the glued core is the fibre map of `g.inv` read in the two charts of `A`. -/
theorem coordChange_glue_of_mem_of_notMem {x y b : B} (hx : x ∈ U) (hy : y ∉ U)
    (hb : b ∈ U ∩ V) :
    (A.glue hU hV hUV g).core.coordChange x y b =
      (A.core.coordChange b y b).comp
        ((g.inv.fiberMap ⟨b, hb⟩).comp (A.core.coordChange x b b)) := by
  rw [coordChange_glue, glueIndex_eq_true_iff.2 hx, glueIndex_eq_false_iff.2 hy,
    glueCocycle_true_false g hb, inChartCoordinates_core]

/-! ### The glued core over each side -/

/-- The chart operators, from the restriction of the glued core to the side `s` to that of `A`:
in the charts at `i` and `j`, the chart expression of the cocycle from the side of `i` to `s`. -/
private def glueRestrictHom (s : Bool) :
    (A.glue hU hV hUV g).pullback (ContinuousMap.subtypeVal (glueSide U V s)) ⟶
      A.pullback (ContinuousMap.subtypeVal (glueSide U V s)) where
  operator i j :=
    ⟨fun c ↦ A.core.inChartCoordinates A.core i j c.val (glueCocycle g (glueIndex U i) s c.val),
      (continuousOn_inChartCoordinates_glueCocycle g hU hV (glueIndex U i) s i j).comp_continuous
        (continuous_subtypeVal.comp continuous_subtypeVal)
        fun c ↦ ⟨⟨⟨c.property.1.1, c.property.2⟩, c.property.1.2⟩, c.val.property⟩⟩
  compatible i i' j j' x hi hi' hj hj' v := by
    simp only [ContinuousMap.coe_mk, coordChange_pullback, ContinuousMap.subtypeVal_apply,
      coordChange_glue]
    rw [← A.core.inChartCoordinates_id (i := (j : B)) (j := (j' : B)) (x := (x : B)) hj hj',
      ← glueCocycle_self g s x,
      ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
      inChartCoordinates_glueCocycle_comp g (s := glueIndex U i) (t := s) (r := s) (x := (i : B))
        (y := (j : B)) (z := (j' : B)) (b := (x : B)) ⟨⟨hi.2, x.property⟩, x.property⟩ hj,
      inChartCoordinates_glueCocycle_comp g (s := glueIndex U i) (t := glueIndex U i') (r := s)
        (x := (i : B)) (y := (i' : B)) (z := (j' : B)) (b := (x : B))
        ⟨⟨hi.2, hi'.2⟩, x.property⟩ hi'.1]

/-- The chart operators, from the restriction of `A` to the side `s` to that of the glued core:
in the charts at `i` and `j`, the chart expression of the cocycle from `s` to the side of
`j`. -/
private def glueRestrictInv (s : Bool) :
    A.pullback (ContinuousMap.subtypeVal (glueSide U V s)) ⟶
      (A.glue hU hV hUV g).pullback (ContinuousMap.subtypeVal (glueSide U V s)) where
  operator i j :=
    ⟨fun c ↦ A.core.inChartCoordinates A.core i j c.val (glueCocycle g s (glueIndex U j) c.val),
      (continuousOn_inChartCoordinates_glueCocycle g hU hV s (glueIndex U j) i j).comp_continuous
        (continuous_subtypeVal.comp continuous_subtypeVal)
        fun c ↦ ⟨⟨⟨c.property.1, c.property.2.1⟩, c.val.property⟩, c.property.2.2⟩⟩
  compatible i i' j j' x hi hi' hj hj' v := by
    simp only [ContinuousMap.coe_mk, coordChange_pullback, ContinuousMap.subtypeVal_apply,
      coordChange_glue]
    rw [← A.core.inChartCoordinates_id (i := (i : B)) (j := (i' : B)) (x := (x : B)) hi hi',
      ← glueCocycle_self g s x,
      ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
      inChartCoordinates_glueCocycle_comp g (s := s) (t := glueIndex U j) (r := glueIndex U j')
        (x := (i : B)) (y := (j : B)) (z := (j' : B)) (b := (x : B))
        ⟨⟨x.property, hj.2⟩, hj'.2⟩ hj.1,
      inChartCoordinates_glueCocycle_comp g (s := s) (t := s) (r := glueIndex U j') (x := (i : B))
        (y := (i' : B)) (z := (j' : B)) (b := (x : B)) ⟨⟨x.property, x.property⟩, hj'.2⟩ hi']

private theorem fiberMap_glueRestrictHom (s : Bool) (x : glueSide U V s) :
    (glueRestrictHom A hU hV hUV g s).fiberMap x = glueCocycle g (glueIndex U x) s x := by
  rw [← operator_self]
  -- The chart operators of `glueRestrictHom` are given by its definition.
  have h : (glueRestrictHom A hU hV hUV g s).operator x x
      ⟨x, mem_baseSet_self _ x, mem_baseSet_self _ x⟩ =
        A.core.inChartCoordinates A.core x x x (glueCocycle g (glueIndex U x) s x) := (rfl)
  rw [h]
  ext v : 1
  rw [inChartCoordinates_core_apply]
  simp

private theorem fiberMap_glueRestrictInv (s : Bool) (x : glueSide U V s) :
    (glueRestrictInv A hU hV hUV g s).fiberMap x = glueCocycle g s (glueIndex U x) x := by
  rw [← operator_self]
  -- The chart operators of `glueRestrictInv` are given by its definition.
  have h : (glueRestrictInv A hU hV hUV g s).operator x x
      ⟨x, mem_baseSet_self _ x, mem_baseSet_self _ x⟩ =
        A.core.inChartCoordinates A.core x x x (glueCocycle g s (glueIndex U x) x) := (rfl)
  rw [h]
  ext v : 1
  rw [inChartCoordinates_core_apply]
  simp

/-- **The glued core over each side.** The restriction of `A.glue hU hV hUV g` to `U` (for
`s = true`) or to `V` (for `s = false`) is isomorphic to that of `A`; at `x` the isomorphism is
the gluing cocycle from the side of `x` to `s` (`fiberMap_glueRestrictIso_hom`). -/
def glueRestrictIso (s : Bool) :
    (A.glue hU hV hUV g).pullback (ContinuousMap.subtypeVal (glueSide U V s)) ≅
      A.pullback (ContinuousMap.subtypeVal (glueSide U V s)) where
  hom := glueRestrictHom A hU hV hUV g s
  inv := glueRestrictInv A hU hV hUV g s
  hom_inv_id := hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_glueRestrictHom, fiberMap_glueRestrictInv,
      glueCocycle_comp g _ _ _ ⟨⟨mem_glueSide_glueIndex hUV x.val, x.property⟩,
        mem_glueSide_glueIndex hUV x.val⟩, glueCocycle_self, fiberMap_id]
    -- Both sides agree once the ranks of the fibre models are unfolded.
    rfl
  inv_hom_id := hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_glueRestrictHom, fiberMap_glueRestrictInv,
      glueCocycle_comp g _ _ _ ⟨⟨x.property, mem_glueSide_glueIndex hUV x.val⟩, x.property⟩,
      glueCocycle_self, fiberMap_id]
    -- Both sides agree once the ranks of the fibre models are unfolded.
    rfl

theorem fiberMap_glueRestrictIso_hom (s : Bool) (x : glueSide U V s) :
    (A.glueRestrictIso hU hV hUV g s).hom.fiberMap x = glueCocycle g (glueIndex U x) s x :=
  fiberMap_glueRestrictHom A hU hV hUV g s x

theorem fiberMap_glueRestrictIso_inv (s : Bool) (x : glueSide U V s) :
    (A.glueRestrictIso hU hV hUV g s).inv.fiberMap x = glueCocycle g s (glueIndex U x) x :=
  fiberMap_glueRestrictInv A hU hV hUV g s x

/-- Over `U`, the glued core is `A` by the identity in coordinates. -/
@[simp]
theorem fiberMap_glueRestrictIso_true_hom (x : U) :
    (A.glueRestrictIso hU hV hUV g true).hom.fiberMap x = .id 𝕜 _ := by
  rw [fiberMap_glueRestrictIso_hom, glueIndex_eq_true_iff.2 x.property, glueCocycle_self]
  -- Both sides agree once the ranks of the fibre models are unfolded.
  rfl

@[simp]
theorem fiberMap_glueRestrictIso_true_inv (x : U) :
    (A.glueRestrictIso hU hV hUV g true).inv.fiberMap x = .id 𝕜 _ := by
  rw [fiberMap_glueRestrictIso_inv, glueIndex_eq_true_iff.2 x.property, glueCocycle_self]
  -- Both sides agree once the ranks of the fibre models are unfolded.
  rfl

/-- Over `V`, at a point of `U ∩ V`, the isomorphism of the glued core with `A` is the fibre map
of `g.inv`. -/
theorem fiberMap_glueRestrictIso_false_hom {x : V} (hx : (x : B) ∈ U) :
    (A.glueRestrictIso hU hV hUV g false).hom.fiberMap x =
      g.inv.fiberMap ⟨x, hx, x.property⟩ := by
  rw [fiberMap_glueRestrictIso_hom, glueIndex_eq_true_iff.2 hx,
    glueCocycle_true_false g (show (x : B) ∈ U ∩ V from ⟨hx, x.property⟩)]

/-- Over `V`, at a point outside `U`, the isomorphism of the glued core with `A` is the identity
in coordinates. -/
theorem fiberMap_glueRestrictIso_false_hom_of_notMem {x : V} (hx : (x : B) ∉ U) :
    (A.glueRestrictIso hU hV hUV g false).hom.fiberMap x = .id 𝕜 _ := by
  rw [fiberMap_glueRestrictIso_hom, glueIndex_eq_false_iff.2 hx, glueCocycle_self]
  -- Both sides agree once the ranks of the fibre models are unfolded.
  rfl

/-! ### Gluing by the identity -/

/-- The gluing cocycle of the identity is the identity. -/
@[simp]
theorem glueCocycle_refl (s t : Bool) (b : B) :
    glueCocycle (Iso.refl (A.pullback (ContinuousMap.subtypeVal (U ∩ V)))) s t b = .id 𝕜 _ := by
  cases s <;> cases t <;>
    simp only [glueCocycle, Iso.refl_hom, Iso.refl_inv, fiberMap_id, dite_eq_ite] <;>
    exact ite_self _

/-- Gluing `A` by the identity of its restriction to `U ∩ V` gives back `A`, by the identity in
coordinates. -/
def glueReflIso : A.glue hU hV hUV (Iso.refl _) ≅ A :=
  constIso (fun _ ↦ inter_subset_left) (ContinuousLinearEquiv.refl 𝕜 (Fin A.rank → 𝕜))
    fun i j x hi hj ↦ by
      -- State the identity on standard coordinates to fix the inherited fibre instances.
      have h : (ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)).comp
          ((A.glue hU hV hUV (Iso.refl _)).core.coordChange i j x) =
          (A.core.coordChange i j x).comp (ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) := by
        rw [coordChange_glue, glueCocycle_refl, A.core.inChartCoordinates_id hi.1 hj.1]
        -- Composition with the identity, once the ranks of the fibre models are unfolded.
        rfl
      exact h

@[simp]
theorem fiberMap_glueReflIso_hom (x : B) :
    (A.glueReflIso hU hV hUV).hom.fiberMap x = .id 𝕜 _ := by
  rw [glueReflIso]
  exact fiberMap_constIso_hom _ _ _ x

@[simp]
theorem fiberMap_glueReflIso_inv (x : B) :
    (A.glueReflIso hU hV hUV).inv.fiberMap x = .id 𝕜 _ := by
  rw [glueReflIso]
  exact fiberMap_constIso_inv _ _ _ x

end Glue

end TauCeti.FiniteRankBundleCore

end
