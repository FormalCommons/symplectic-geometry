/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Core.Basic
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Basic
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Biproduct
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.HomotopyInvariance
public import TauCeti.Topology.VectorBundle.FiniteRank.Monoidal

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
  (`fiberMap_glueRestrictIso_true_hom`); over `V` it is `g.inv` on `U ∩ V`, with inverse `g.hom`
  (`fiberMap_glueRestrictIso_false_hom`, `fiberMap_glueRestrictIso_false_inv`).
* `TauCeti.FiniteRankBundleCore.glueReflIso`: gluing by the identity gives back `A`.
* `TauCeti.FiniteRankBundleCore.isoGlue`: conversely, a core `F` whose restrictions to `U` and `V`
  are isomorphic to those of `A`, by `φ` and `ψ`, is isomorphic to the gluing of `A` by their
  transition `glueTransition φ ψ`, which is `φ_b ∘ ψ_b⁻¹` at `b` (`fiberMap_glueTransition_hom`).
  The isomorphism is `φ` over `U` and `ψ` off `U` (`fiberMap_isoGlue_hom_of_mem`,
  `fiberMap_isoGlue_hom_of_notMem`), and the gluing cocycle carries it to the given isomorphism
  on either side (`glueCocycle_comp_fiberMap_isoGlue_hom`); followed by `glueRestrictIso`, its
  restriction to either side is the given isomorphism there
  (`pullbackFunctor_mapIso_isoGlue_trans_glueRestrictIso`).
* `TauCeti.FiniteRankBundleCore.coordChange_glue_whitneyMapIso` and
  `TauCeti.FiniteRankBundleCore.coordChange_glue_tensorIso`: the gluing of `A ⊕ D` by the direct
  sum of two automorphisms has the transitions of the Whitney sum of the two gluings, and the
  gluing of `A ⊗ D` by their tensor product those of the tensor product of the two gluings, since
  the gluing cocycle of a direct sum or tensor product of automorphisms is the block-diagonal or
  Kronecker product of their cocycles (`glueCocycle_whitneyMapIso`, `glueCocycle_tensorIso`).
* `TauCeti.FiniteRankBundleCore.nonempty_iso_glue_of_homotopic`: over a paracompact R₁
  base, gluings by two automorphisms joined by an automorphism of the pullback of `A` to the
  part `(U ∩ V) × I` of `B × I` are isomorphic. The gluing over `B × I` by that automorphism
  pulls back along `x ↦ (x, t)` to the gluing by its slice at `t`, by the identity in
  coordinates (`pullbackGlueIso`), and the two ends are pullbacks along homotopic maps.

The construction follows the pattern of Tau Ceti's `TauCeti.FiniteRankBundleCore.doubleAlong`, a
point-indexed core whose transitions are given piecewise, and of
`SymplecticGeometry.Bundle.twoChartCore`, two charts glued along a transition. The isomorphism
`glueReflIso` is built, as Tau Ceti's `TauCeti.FiniteRankBundleCore.doubleAlongInlIso` is, with
`TauCeti.FiniteRankBundleCore.constIso`. The isomorphism `isoGlue` is built from its fibre maps
with Tau Ceti's `VectorBundleCore.CoordinateHom.ofContinuous`, as
`TauCeti.FiniteRankBundleCore.isoOfContinuousEquiv` is, and inverted with Tau Ceti's
`VectorBundleCore.CoordinateHom.invOfIsInvertible`. The proof of `nonempty_iso_glue_of_homotopic`
rests on homotopy invariance of pullbacks
(`TauCeti.FiniteRankBundleCore.nonempty_pullback_iso_of_homotopic`).

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §1.2 (clutching functions) and
  §2.1 (a bundle over a product with a sphere as a clutching).
-/

public section

noncomputable section

open Set CategoryTheory Topology Filter

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

open Classical in
theorem glueIndex_def (U : Set B) (x : B) : glueIndex U x = decide (x ∈ U) :=
  (rfl)

@[simp]
theorem glueIndex_eq_true_iff {x : B} : glueIndex U x = true ↔ x ∈ U := by
  classical
  simp [glueIndex]

@[simp]
theorem glueIndex_eq_false_iff {x : B} : glueIndex U x = false ↔ x ∉ U := by
  classical
  simp [glueIndex]

@[simp]
theorem glueIndex_of_mem {x : B} (hx : x ∈ U) : glueIndex U x = true :=
  glueIndex_eq_true_iff.2 hx

@[simp]
theorem glueIndex_of_notMem {x : B} (hx : x ∉ U) : glueIndex U x = false :=
  glueIndex_eq_false_iff.2 hx

/-- Each point lies on its own side: in `U` if it is in `U`, and otherwise in `V`. -/
theorem mem_glueSide_glueIndex (hUV : U ∪ V = univ) (x : B) :
    x ∈ glueSide U V (glueIndex U x) := by
  by_cases hx : x ∈ U
  · simp [hx]
  · simpa [hx] using
      (hUV.symm ▸ mem_univ x : x ∈ U ∪ V).resolve_left hx

/-- The two sides of a gluing over open sets are open. -/
theorem isOpen_glueSide [TopologicalSpace B] (hU : IsOpen U) (hV : IsOpen V) (s : Bool) :
    IsOpen (glueSide U V s) := by
  cases s <;> assumption

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

/-- The chart expression, in any two charts of `A` and `D`, of a family of fibre maps that agrees
over an open set `W` with a morphism between the restrictions of `A` and `D` to `W` is continuous
where both charts are defined and on `W`. -/
theorem continuousOn_inChartCoordinates_of_eq_fiberMap_pullback_subtypeVal (hW : IsOpen W)
    (a : A.pullback (ContinuousMap.subtypeVal W) ⟶ D.pullback (ContinuousMap.subtypeVal W))
    {f : B → (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)} (hf : ∀ w : W, f w = a.fiberMap w)
    (x y : B) :
    ContinuousOn (fun b ↦ A.core.inChartCoordinates D.core x y b (f b))
      (A.core.baseSet x ∩ D.core.baseSet y ∩ W) := by
  intro b hb
  have hopen : IsOpen (A.core.baseSet x ∩ D.core.baseSet y) :=
    (A.core.isOpen_baseSet x).inter (D.core.isOpen_baseSet y)
  refine ContinuousAt.continuousWithinAt ?_
  rw [← hW.isOpenEmbedding_subtypeVal.continuousAt_iff (x := ⟨b, hb.2⟩)]
  refine ((continuousOn_inChartCoordinates_fiberMap_pullback_subtypeVal a x y ⟨b, hb.2⟩
    hb.1).continuousAt ((hopen.preimage continuous_subtypeVal).mem_nhds hb.1)).congr
    (Eventually.of_forall fun w ↦ ?_)
  simp only [Function.comp_apply, hf]

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
  rcases hb with ⟨⟨hs, ht⟩, hr⟩
  cases s <;> cases t <;> cases r <;>
    simp only [glueSide, Bool.cond_true, Bool.cond_false] at hs ht hr
  all_goals try first
    | (simp only [glueCocycle_self, ContinuousLinearMap.id_comp]; done)
    | (simp only [glueCocycle_self, ContinuousLinearMap.comp_id]; done)
  · have h : b ∈ U ∩ V := ⟨ht, hs⟩
    rw [glueCocycle_false_true g h, glueCocycle_true_false g h, fiberMap_hom_inv_id,
      glueCocycle_self]
    -- Both sides agree once the ranks of the fibre models are unfolded.
    rfl
  · have h : b ∈ U ∩ V := ⟨hs, ht⟩
    rw [glueCocycle_true_false g h, glueCocycle_false_true g h, fiberMap_inv_hom_id,
      glueCocycle_self]
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
  exact (continuousOn_inChartCoordinates_of_eq_fiberMap_pullback_subtypeVal hUV a ha x y).mono
    fun b hb ↦ ⟨hb.1.1, hsub ⟨hb.1.2, hb.2⟩⟩

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
      isOpen_baseSet := fun x ↦ (A.core.isOpen_baseSet x).inter (isOpen_glueSide hU hV _)
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
  rw [coordChange_glue, glueIndex_of_notMem hx, glueIndex_of_mem hy,
    glueCocycle_false_true g hb, inChartCoordinates_core]

/-- From a chart on the side `U` to a chart on the side `V`, at a point of `U ∩ V`, the
transition of the glued core is the fibre map of `g.inv` read in the two charts of `A`. -/
theorem coordChange_glue_of_mem_of_notMem {x y b : B} (hx : x ∈ U) (hy : y ∉ U)
    (hb : b ∈ U ∩ V) :
    (A.glue hU hV hUV g).core.coordChange x y b =
      (A.core.coordChange b y b).comp
        ((g.inv.fiberMap ⟨b, hb⟩).comp (A.core.coordChange x b b)) := by
  rw [coordChange_glue, glueIndex_of_mem hx, glueIndex_of_notMem hy,
    glueCocycle_true_false g hb, inChartCoordinates_core]

/-- A fibre map into the glued core, read in a chart of the glued core, is the same map followed
by the gluing cocycle from the side of the point to that of the chart, read in the chart of `A`. -/
theorem inChartCoordinates_glue_right (D : FiniteRankBundleCore 𝕜 B) (i j b : B)
    (ϕ : (Fin D.rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜)) :
    D.core.inChartCoordinates (A.glue hU hV hUV g).core i j b ϕ =
      D.core.inChartCoordinates A.core i j b
        ((glueCocycle g (glueIndex U b) (glueIndex U j) b).comp ϕ) := by
  rw [inChartCoordinates_core, inChartCoordinates_core, coordChange_glue, inChartCoordinates_core,
    coordChange_self]
  -- Composition with the identity, once the ranks of the fibre models are unfolded.
  rfl

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
  rw [fiberMap_glueRestrictIso_hom, glueIndex_of_mem x.property, glueCocycle_self]
  -- Both sides agree once the ranks of the fibre models are unfolded.
  rfl

@[simp]
theorem fiberMap_glueRestrictIso_true_inv (x : U) :
    (A.glueRestrictIso hU hV hUV g true).inv.fiberMap x = .id 𝕜 _ := by
  rw [fiberMap_glueRestrictIso_inv, glueIndex_of_mem x.property, glueCocycle_self]
  -- Both sides agree once the ranks of the fibre models are unfolded.
  rfl

/-- Over `V`, at a point of `U ∩ V`, the isomorphism of the glued core with `A` is the fibre map
of `g.inv`. -/
theorem fiberMap_glueRestrictIso_false_hom {x : V} (hx : (x : B) ∈ U) :
    (A.glueRestrictIso hU hV hUV g false).hom.fiberMap x =
      g.inv.fiberMap ⟨x, hx, x.property⟩ := by
  rw [fiberMap_glueRestrictIso_hom, glueIndex_of_mem hx,
    glueCocycle_true_false g (show (x : B) ∈ U ∩ V from ⟨hx, x.property⟩)]

/-- Over `V`, at a point outside `U`, the isomorphism of the glued core with `A` is the identity
in coordinates. -/
theorem fiberMap_glueRestrictIso_false_hom_of_notMem {x : V} (hx : (x : B) ∉ U) :
    (A.glueRestrictIso hU hV hUV g false).hom.fiberMap x = .id 𝕜 _ := by
  rw [fiberMap_glueRestrictIso_hom, glueIndex_of_notMem hx, glueCocycle_self]
  -- Both sides agree once the ranks of the fibre models are unfolded.
  rfl

/-- Over `V`, at a point of `U ∩ V`, the inverse isomorphism, from `A` to the glued core, is the
fibre map of `g.hom`. -/
theorem fiberMap_glueRestrictIso_false_inv {x : V} (hx : (x : B) ∈ U) :
    (A.glueRestrictIso hU hV hUV g false).inv.fiberMap x =
      g.hom.fiberMap ⟨x, hx, x.property⟩ := by
  rw [fiberMap_glueRestrictIso_inv, glueIndex_of_mem hx,
    glueCocycle_false_true g (show (x : B) ∈ U ∩ V from ⟨hx, x.property⟩)]

/-- Over `V`, at a point outside `U`, the inverse isomorphism, from `A` to the glued core, is the
identity in coordinates. -/
theorem fiberMap_glueRestrictIso_false_inv_of_notMem {x : V} (hx : (x : B) ∉ U) :
    (A.glueRestrictIso hU hV hUV g false).inv.fiberMap x = .id 𝕜 _ := by
  rw [fiberMap_glueRestrictIso_inv, glueIndex_of_notMem hx, glueCocycle_self]
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

/-! ### A core with isomorphic restrictions to two open sets is a gluing -/

section OfIso

variable {F A : FiniteRankBundleCore 𝕜 B} {U V : Set B}
  (φ : F.pullback (ContinuousMap.subtypeVal U) ≅ A.pullback (ContinuousMap.subtypeVal U))
  (ψ : F.pullback (ContinuousMap.subtypeVal V) ≅ A.pullback (ContinuousMap.subtypeVal V))

/-- The transition of two isomorphisms `φ`, over `U`, and `ψ`, over `V`, from the restrictions of
`F` to those of `A`: the automorphism of the restriction of `A` to `U ∩ V` that is `φ_b ∘ ψ_b⁻¹`
at `b`, from the copy of `A` over `V` to that over `U` (`fiberMap_glueTransition_hom`). -/
def glueTransition :
    A.pullback (ContinuousMap.subtypeVal (U ∩ V)) ≅
      A.pullback (ContinuousMap.subtypeVal (U ∩ V)) :=
  ((pullbackFunctor (ContinuousMap.inclusion inter_subset_right)).mapIso ψ).symm ≪≫
    (pullbackFunctor (ContinuousMap.inclusion inter_subset_left)).mapIso φ

/- In the next two proofs, the restriction of the pullback to `U` (or `V`) along the inclusion of
`U ∩ V` is the pullback to `U ∩ V` by `pullback_comp`, which holds by `rfl`; the fibre maps of the
composite are read through `fiberMap_comp` and `fiberMap_pullbackMap` at that type. -/

@[simp]
theorem fiberMap_glueTransition_hom (x : ↥(U ∩ V)) :
    (glueTransition φ ψ).hom.fiberMap x =
      (φ.hom.fiberMap ⟨x, x.property.1⟩).comp (ψ.inv.fiberMap ⟨x, x.property.2⟩) :=
  (fiberMap_comp (pullbackMap ψ.inv (ContinuousMap.inclusion inter_subset_right))
    (pullbackMap φ.hom (ContinuousMap.inclusion inter_subset_left)) x).trans
      (congrArg₂ ContinuousLinearMap.comp
        (fiberMap_pullbackMap _ _ x) (fiberMap_pullbackMap _ _ x))

@[simp]
theorem fiberMap_glueTransition_inv (x : ↥(U ∩ V)) :
    (glueTransition φ ψ).inv.fiberMap x =
      (ψ.hom.fiberMap ⟨x, x.property.2⟩).comp (φ.inv.fiberMap ⟨x, x.property.1⟩) :=
  (fiberMap_comp (pullbackMap φ.inv (ContinuousMap.inclusion inter_subset_left))
    (pullbackMap ψ.hom (ContinuousMap.inclusion inter_subset_right)) x).trans
      (congrArg₂ ContinuousLinearMap.comp
        (fiberMap_pullbackMap _ _ x) (fiberMap_pullbackMap _ _ x))

/-- The given isomorphism on the side `s`: `φ` over `U` (`s = true`) and `ψ` over `V`
(`s = false`). -/
def glueSideIso : (s : Bool) →
    (F.pullback (ContinuousMap.subtypeVal (glueSide U V s)) ≅
      A.pullback (ContinuousMap.subtypeVal (glueSide U V s)))
  | true => φ
  | false => ψ

@[simp]
theorem glueSideIso_true : glueSideIso φ ψ true = φ :=
  (rfl)

@[simp]
theorem glueSideIso_false : glueSideIso φ ψ false = ψ :=
  (rfl)

/-- The gluing cocycle of `glueTransition φ ψ` carries the isomorphism on one side to that on the
other, at a point of both sides. -/
theorem glueCocycle_comp_fiberMap_glueSideIso_hom (s t : Bool) {b : B}
    (hs : b ∈ glueSide U V s) (ht : b ∈ glueSide U V t) :
    (glueCocycle (glueTransition φ ψ) s t b).comp ((glueSideIso φ ψ s).hom.fiberMap ⟨b, hs⟩) =
      (glueSideIso φ ψ t).hom.fiberMap ⟨b, ht⟩ := by
  cases s <;> cases t
  · rw [glueCocycle_self, ContinuousLinearMap.id_comp]
  · rw [glueCocycle_false_true _ ⟨ht, hs⟩, fiberMap_glueTransition_hom, glueSideIso_false,
      glueSideIso_true, ContinuousLinearMap.comp_assoc, fiberMap_hom_inv_id]
    -- Composition with the identity, once the ranks of the fibre models are unfolded.
    rfl
  · rw [glueCocycle_true_false _ ⟨hs, ht⟩, fiberMap_glueTransition_inv, glueSideIso_false,
      glueSideIso_true, ContinuousLinearMap.comp_assoc, fiberMap_hom_inv_id]
    -- Composition with the identity, once the ranks of the fibre models are unfolded.
    rfl
  · rw [glueCocycle_self, ContinuousLinearMap.id_comp]

/-- The inverse of the isomorphism on one side, after the gluing cocycle of `glueTransition φ ψ`
from the other side, is the inverse of the isomorphism on the other side, at a point of both
sides. -/
theorem fiberMap_glueSideIso_inv_comp_glueCocycle (s t : Bool) {b : B}
    (hs : b ∈ glueSide U V s) (ht : b ∈ glueSide U V t) :
    ((glueSideIso φ ψ t).inv.fiberMap ⟨b, ht⟩).comp
        (glueCocycle (glueTransition φ ψ) s t b : (Fin A.rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜)) =
      (glueSideIso φ ψ s).inv.fiberMap ⟨b, hs⟩ := by
  cases s <;> cases t
  · rw [glueCocycle_self, ContinuousLinearMap.comp_id]
  · rw [glueCocycle_false_true _ ⟨ht, hs⟩, fiberMap_glueTransition_hom, glueSideIso_false,
      glueSideIso_true, ← ContinuousLinearMap.comp_assoc, fiberMap_hom_inv_id]
    -- Composition with the identity, once the ranks of the fibre models are unfolded.
    rfl
  · rw [glueCocycle_true_false _ ⟨hs, ht⟩, fiberMap_glueTransition_inv, glueSideIso_false,
      glueSideIso_true, ← ContinuousLinearMap.comp_assoc, fiberMap_hom_inv_id]
    -- Composition with the identity, once the ranks of the fibre models are unfolded.
    rfl
  · rw [glueCocycle_self, ContinuousLinearMap.comp_id]

variable (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)

/-- The forward map of `isoGlue`: at `b`, the given isomorphism on the side of `b`. -/
private def isoGlueHom : F ⟶ A.glue hU hV hUV (glueTransition φ ψ) :=
  VectorBundleCore.CoordinateHom.ofContinuous
    (fun b ↦ (glueSideIso φ ψ (glueIndex U b)).hom.fiberMap ⟨b, mem_glueSide_glueIndex hUV b⟩) <|
    VectorBundleCore.continuous_hom_bundle_iff_forall_continuousOn.2 fun i j ↦ by
      -- In the chart at `j`, on its side `glueIndex U j`, this is the isomorphism on that side.
      refine ((continuousOn_inChartCoordinates_of_eq_fiberMap_pullback_subtypeVal
        (isOpen_glueSide hU hV (glueIndex U j)) (glueSideIso φ ψ (glueIndex U j)).hom
        (f := fun b ↦ (glueCocycle (glueTransition φ ψ) (glueIndex U b) (glueIndex U j) b).comp
          ((glueSideIso φ ψ (glueIndex U b)).hom.fiberMap ⟨b, mem_glueSide_glueIndex hUV b⟩))
        (fun w ↦ glueCocycle_comp_fiberMap_glueSideIso_hom φ ψ _ _ _ w.property) i j).mono
        ?_).congr fun b _ ↦ ?_
      · exact fun b hb ↦ ⟨⟨hb.1, hb.2.1⟩, hb.2.2⟩
      exact inChartCoordinates_glue_right A hU hV hUV _ F i j b _

private theorem fiberMap_isoGlueHom (b : B) :
    (isoGlueHom φ ψ hU hV hUV).fiberMap b =
      (glueSideIso φ ψ (glueIndex U b)).hom.fiberMap ⟨b, mem_glueSide_glueIndex hUV b⟩ := by
  rw [isoGlueHom, VectorBundleCore.CoordinateHom.fiberMap_ofContinuous]

private theorem isInvertible_fiberMap_isoGlueHom (b : B) :
    ((isoGlueHom φ ψ hU hV hUV).fiberMap b).IsInvertible := by
  rw [fiberMap_isoGlueHom]
  exact isInvertible_fiberMap_hom _ _

/-- **A core with isomorphic restrictions to two open sets is a gluing.** If `U` and `V` are open
and cover `B`, and the restrictions of `F` to `U` and to `V` are isomorphic to those of `A` by `φ`
and `ψ`, then `F` is isomorphic to the gluing of `A` by their transition `glueTransition φ ψ`. At
`b` the isomorphism is `φ_b` if `b ∈ U` and `ψ_b` otherwise (`fiberMap_isoGlue_hom`). -/
def isoGlue : F ≅ A.glue hU hV hUV (glueTransition φ ψ) where
  hom := isoGlueHom φ ψ hU hV hUV
  inv := (isoGlueHom φ ψ hU hV hUV).invOfIsInvertible
    (isInvertible_fiberMap_isoGlueHom φ ψ hU hV hUV)
  hom_inv_id := VectorBundleCore.CoordinateHom.invOfIsInvertible_comp _ _
  inv_hom_id := VectorBundleCore.CoordinateHom.comp_invOfIsInvertible _ _

theorem fiberMap_isoGlue_hom (b : B) :
    (isoGlue φ ψ hU hV hUV).hom.fiberMap b =
      (glueSideIso φ ψ (glueIndex U b)).hom.fiberMap ⟨b, mem_glueSide_glueIndex hUV b⟩ :=
  fiberMap_isoGlueHom φ ψ hU hV hUV b

theorem fiberMap_isoGlue_inv (b : B) :
    (isoGlue φ ψ hU hV hUV).inv.fiberMap b =
      (glueSideIso φ ψ (glueIndex U b)).inv.fiberMap ⟨b, mem_glueSide_glueIndex hUV b⟩ := by
  rw [← inverse_fiberMap_hom (isoGlue φ ψ hU hV hUV), fiberMap_isoGlue_hom, inverse_fiberMap_hom]

/-- On the side `s`, the isomorphism `isoGlue φ ψ hU hV hUV` followed by the gluing cocycle from
the side of the point to `s` is the given isomorphism on `s`: `φ` over `U` and `ψ` over `V`. -/
theorem glueCocycle_comp_fiberMap_isoGlue_hom (s : Bool) {b : B} (hb : b ∈ glueSide U V s) :
    (glueCocycle (glueTransition φ ψ) (glueIndex U b) s b).comp
        ((isoGlue φ ψ hU hV hUV).hom.fiberMap b) =
      (glueSideIso φ ψ s).hom.fiberMap ⟨b, hb⟩ := by
  rw [fiberMap_isoGlue_hom, glueCocycle_comp_fiberMap_glueSideIso_hom]

/-- On the side `s`, the gluing cocycle from `s` to the side of the point followed by the inverse
of `isoGlue φ ψ hU hV hUV` is the inverse of the given isomorphism on `s`. -/
theorem fiberMap_isoGlue_inv_comp_glueCocycle (s : Bool) {b : B} (hb : b ∈ glueSide U V s) :
    ((isoGlue φ ψ hU hV hUV).inv.fiberMap b).comp
        (glueCocycle (glueTransition φ ψ) s (glueIndex U b) b :
          (Fin A.rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜)) =
      (glueSideIso φ ψ s).inv.fiberMap ⟨b, hb⟩ := by
  rw [fiberMap_isoGlue_inv, fiberMap_glueSideIso_inv_comp_glueCocycle]

/-- On the side `s`, the restriction of `isoGlue φ ψ hU hV hUV` followed by the isomorphism of the
glued core with `A` there (`glueRestrictIso`) is the given isomorphism on `s`. -/
theorem pullbackFunctor_mapIso_isoGlue_trans_glueRestrictIso (s : Bool) :
    (pullbackFunctor (ContinuousMap.subtypeVal (glueSide U V s))).mapIso
        (isoGlue φ ψ hU hV hUV) ≪≫
      A.glueRestrictIso hU hV hUV (glueTransition φ ψ) s = glueSideIso φ ψ s := by
  refine Iso.ext (hom_ext fun x ↦ ?_)
  rw [Iso.trans_hom, Functor.mapIso_hom, pullbackFunctor_map, fiberMap_comp, fiberMap_pullbackMap,
    fiberMap_glueRestrictIso_hom]
  exact glueCocycle_comp_fiberMap_isoGlue_hom φ ψ hU hV hUV s x.property

/-- Over `U`, the restriction of `isoGlue φ ψ hU hV hUV` followed by `glueRestrictIso` is `φ`. -/
theorem pullbackFunctor_mapIso_isoGlue_trans_glueRestrictIso_true :
    (pullbackFunctor (ContinuousMap.subtypeVal U)).mapIso (isoGlue φ ψ hU hV hUV) ≪≫
      A.glueRestrictIso hU hV hUV (glueTransition φ ψ) true = φ :=
  pullbackFunctor_mapIso_isoGlue_trans_glueRestrictIso φ ψ hU hV hUV true

/-- Over `V`, the restriction of `isoGlue φ ψ hU hV hUV` followed by `glueRestrictIso` is `ψ`. -/
theorem pullbackFunctor_mapIso_isoGlue_trans_glueRestrictIso_false :
    (pullbackFunctor (ContinuousMap.subtypeVal V)).mapIso (isoGlue φ ψ hU hV hUV) ≪≫
      A.glueRestrictIso hU hV hUV (glueTransition φ ψ) false = ψ :=
  pullbackFunctor_mapIso_isoGlue_trans_glueRestrictIso φ ψ hU hV hUV false

/-- Over `U`, the isomorphism of `F` with the gluing is `φ`. -/
theorem fiberMap_isoGlue_hom_of_mem {b : B} (hb : b ∈ U) :
    (isoGlue φ ψ hU hV hUV).hom.fiberMap b = φ.hom.fiberMap ⟨b, hb⟩ := by
  have h := glueCocycle_comp_fiberMap_isoGlue_hom φ ψ hU hV hUV true hb
  rwa [glueIndex_of_mem hb, glueCocycle_self, ContinuousLinearMap.id_comp] at h

/-- Over `U`, the inverse isomorphism, from the gluing to `F`, is the inverse of `φ`. -/
theorem fiberMap_isoGlue_inv_of_mem {b : B} (hb : b ∈ U) :
    (isoGlue φ ψ hU hV hUV).inv.fiberMap b = φ.inv.fiberMap ⟨b, hb⟩ := by
  have h := fiberMap_isoGlue_inv_comp_glueCocycle φ ψ hU hV hUV true hb
  rwa [glueIndex_of_mem hb, glueCocycle_self, ContinuousLinearMap.comp_id] at h

/-- Over `V`, outside `U`, the isomorphism of `F` with the gluing is `ψ`. -/
theorem fiberMap_isoGlue_hom_of_notMem {b : B} (hb : b ∉ U) (hbV : b ∈ V) :
    (isoGlue φ ψ hU hV hUV).hom.fiberMap b = ψ.hom.fiberMap ⟨b, hbV⟩ := by
  have h := glueCocycle_comp_fiberMap_isoGlue_hom φ ψ hU hV hUV false hbV
  rwa [glueIndex_of_notMem hb, glueCocycle_self, ContinuousLinearMap.id_comp] at h

/-- Over `V`, outside `U`, the inverse isomorphism, from the gluing to `F`, is the inverse of
`ψ`. -/
theorem fiberMap_isoGlue_inv_of_notMem {b : B} (hb : b ∉ U) (hbV : b ∈ V) :
    (isoGlue φ ψ hU hV hUV).inv.fiberMap b = ψ.inv.fiberMap ⟨b, hbV⟩ := by
  have h := fiberMap_isoGlue_inv_comp_glueCocycle φ ψ hU hV hUV false hbV
  rwa [glueIndex_of_notMem hb, glueCocycle_self, ContinuousLinearMap.comp_id] at h

end OfIso

/-! ### Gluing Whitney sums and tensor products -/

section Operations

open MonoidalCategory

variable {A D : FiniteRankBundleCore 𝕜 B} {U V : Set B} (hU : IsOpen U) (hV : IsOpen V)
  (hUV : U ∪ V = univ)
  (g₁ : A.pullback (ContinuousMap.subtypeVal (U ∩ V)) ≅
    A.pullback (ContinuousMap.subtypeVal (U ∩ V)))
  (g₂ : D.pullback (ContinuousMap.subtypeVal (U ∩ V)) ≅
    D.pullback (ContinuousMap.subtypeVal (U ∩ V)))

/-- The gluing cocycle of the direct sum of two automorphisms is block diagonal, with the gluing
cocycles of the two automorphisms as blocks. -/
theorem glueCocycle_whitneyMapIso (s t : Bool) (b : B) :
    glueCocycle (A := whitneySum A D) (whitneyMapIso g₁ g₂) s t b =
      (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm.toContinuousLinearMap.comp
        (((glueCocycle g₁ s t b).prodMap (glueCocycle g₂ s t b)).comp
          (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap) := by
  have hid : (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm.toContinuousLinearMap.comp
      (((ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)).prodMap (.id 𝕜 (Fin D.rank → 𝕜))).comp
        (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap) = .id 𝕜 _ :=
    ContinuousLinearMap.ext (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm_apply_apply
  cases s <;> cases t <;> simp only [glueCocycle, whitneyMapIso_hom, whitneyMapIso_inv] <;>
    (try split_ifs) <;> first | exact hid.symm | exact fiberMap_whitneyMap _ _ _

/-- The gluing cocycle of the tensor product of two automorphisms is the Kronecker product of
their gluing cocycles. -/
theorem glueCocycle_tensorIso (s t : Bool) (b : B) :
    glueCocycle (A := tensor A D) (g₁ ⊗ᵢ g₂) s t b =
      (glueCocycle g₁ s t b).kronecker (glueCocycle g₂ s t b) := by
  cases s <;> cases t <;> simp only [glueCocycle, tensorIso_hom, tensorIso_inv] <;>
    (try split_ifs) <;>
    first | exact ContinuousLinearMap.id_kronecker_id.symm | exact fiberMap_tensorHom_monoidal _ _ _

/-- The transitions of the gluing of `A ⊕ D` by the direct sum of `g₁` and `g₂` are those of the
Whitney sum of the gluing of `A` by `g₁` and that of `D` by `g₂`. -/
theorem coordChange_glue_whitneyMapIso (i j b : B) :
    ((whitneySum A D).glue hU hV hUV (whitneyMapIso g₁ g₂)).core.coordChange i j b =
      (whitneySum (A.glue hU hV hUV g₁) (D.glue hU hV hUV g₂)).core.coordChange i j b := by
  refine (coordChange_glue _ _ _ _ _ i j b).trans ?_
  rw [glueCocycle_whitneyMapIso]
  exact inChartCoordinates_whitneySum_prodMap A A D D _ _ i j b

/-- The transitions of the gluing of `A ⊗ D` by the tensor product of `g₁` and `g₂` are those of
the tensor product of the gluing of `A` by `g₁` and that of `D` by `g₂`. -/
theorem coordChange_glue_tensorIso (i j b : B) :
    ((tensor A D).glue hU hV hUV (g₁ ⊗ᵢ g₂)).core.coordChange i j b =
      (tensor (A.glue hU hV hUV g₁) (D.glue hU hV hUV g₂)).core.coordChange i j b := by
  refine (coordChange_glue _ _ _ _ _ i j b).trans ?_
  rw [glueCocycle_tensorIso]
  exact inChartCoordinates_tensor_kronecker A A D D _ _ i j b

end Operations

/-! ### Gluing by homotopic automorphisms -/

section Homotopic

variable {T : Type*} [TopologicalSpace T] (A : FiniteRankBundleCore 𝕜 B) {U V : Set B}
  (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
  (g : A.pullback (ContinuousMap.subtypeVal (U ∩ V)) ≅
    A.pullback (ContinuousMap.subtypeVal (U ∩ V)))
  (H : (A.pullback (ContinuousMap.fst : C(B × T, B))).pullback
      (ContinuousMap.subtypeVal (Prod.fst ⁻¹' U ∩ Prod.fst ⁻¹' V)) ≅
    (A.pullback (ContinuousMap.fst : C(B × T, B))).pullback
      (ContinuousMap.subtypeVal (Prod.fst ⁻¹' U ∩ Prod.fst ⁻¹' V)))
  (t : T)

/-- The side of the chart at `(x, t)` of a gluing over `U × T` and `V × T` is that of the chart
at `x` of a gluing over `U` and `V`. -/
private theorem glueIndex_prodMk_const (x : B) :
    glueIndex (Prod.fst ⁻¹' U) (((ContinuousMap.id B).prodMk (.const B t)) x) = glueIndex U x := by
  simp [glueIndex_def]

/-- The chart at `i` of the pullback of a gluing over `B × T` along `x ↦ (x, t)` lies in the chart
at `i` of a gluing over `B`. -/
private theorem baseSet_pullback_glue_subset (i : B) :
    (((A.pullback ContinuousMap.fst).glue (hU.preimage continuous_fst)
        (hV.preimage continuous_fst) (by rw [← preimage_union, hUV, preimage_univ]) H).pullback
        ((ContinuousMap.id B).prodMk (.const B t))).core.baseSet i ⊆
      (A.glue hU hV hUV g).core.baseSet i := by
  intro b hb
  rw [VectorBundleCore.baseSet_at, localTriv_baseSet_pullback, ← VectorBundleCore.baseSet_at,
    Set.mem_preimage, baseSet_glue, glueIndex_prodMk_const] at hb
  rw [baseSet_glue]
  generalize glueIndex U i = s at hb ⊢
  cases s <;> exact ⟨hb.1, hb.2⟩

variable {A g H t}

/-- If the fibre maps of `H` at `(x, t)` are those of `g` at `x`, so are the fibre maps of their
inverses. -/
private theorem fiberMap_inv_prodMk
    (hg : ∀ x : ↥(U ∩ V), H.hom.fiberMap ⟨(x.val, t), x.property⟩ = g.hom.fiberMap x)
    (x : ↥(U ∩ V)) :
    H.inv.fiberMap ⟨(x.val, t), x.property⟩ = g.inv.fiberMap x := by
  rw [← inverse_fiberMap_hom, hg, inverse_fiberMap_hom]

/-- The transitions of the pullback of a gluing over `B × T` along `x ↦ (x, t)` are those of the
gluing by the slice of `H` at `t`. -/
private theorem coordChange_pullback_glue
    (hg : ∀ x : ↥(U ∩ V), H.hom.fiberMap ⟨(x.val, t), x.property⟩ = g.hom.fiberMap x)
    (i k b : B)
    (hi : b ∈ (((A.pullback ContinuousMap.fst).glue (hU.preimage continuous_fst)
        (hV.preimage continuous_fst) (by rw [← preimage_union, hUV, preimage_univ]) H).pullback
        ((ContinuousMap.id B).prodMk (.const B t))).core.baseSet i)
    (hk : b ∈ (((A.pullback ContinuousMap.fst).glue (hU.preimage continuous_fst)
        (hV.preimage continuous_fst) (by rw [← preimage_union, hUV, preimage_univ]) H).pullback
        ((ContinuousMap.id B).prodMk (.const B t))).core.baseSet k) :
    (((A.pullback ContinuousMap.fst).glue (hU.preimage continuous_fst)
        (hV.preimage continuous_fst) (by rw [← preimage_union, hUV, preimage_univ]) H).pullback
        ((ContinuousMap.id B).prodMk (.const B t))).core.coordChange i k b =
      (A.glue hU hV hUV g).core.coordChange i k b := by
  have hs := ((baseSet_glue A hU hV hUV g i).le
    (baseSet_pullback_glue_subset A hU hV hUV g H t i hi)).2
  have hr := ((baseSet_glue A hU hV hUV g k).le
    (baseSet_pullback_glue_subset A hU hV hUV g H t k hk)).2
  simp only [coordChange_pullback, coordChange_glue, glueIndex_prodMk_const,
    inChartCoordinates_pullback]
  congr 1
  generalize glueIndex U i = s at hs ⊢
  generalize glueIndex U k = r at hr ⊢
  cases s <;> cases r
  · -- Both sides are the identity of `Fin A.rank → 𝕜`: the rank of a pullback is that of the core.
    simp only [glueCocycle_self]
    rfl
  · have hb : b ∈ U ∩ V := ⟨hr, hs⟩
    rw [glueCocycle_false_true _ (show ((ContinuousMap.id B).prodMk (.const B t)) b ∈
        Prod.fst ⁻¹' U ∩ Prod.fst ⁻¹' V from hb),
      glueCocycle_false_true _ hb]
    exact hg ⟨b, hb⟩
  · have hb : b ∈ U ∩ V := ⟨hs, hr⟩
    rw [glueCocycle_true_false _ (show ((ContinuousMap.id B).prodMk (.const B t)) b ∈
        Prod.fst ⁻¹' U ∩ Prod.fst ⁻¹' V from hb),
      glueCocycle_true_false _ hb]
    exact fiberMap_inv_prodMk hg ⟨b, hb⟩
  · -- Both sides are the identity of `Fin A.rank → 𝕜`: the rank of a pullback is that of the core.
    simp only [glueCocycle_self]
    rfl

variable (A g H t)

/-- **Restricting the parameter of a gluing.** Let `H` be an automorphism of the pullback of `A`
along `Prod.fst` to the part `(U ∩ V) × T` of `B × T`, and `g` one of the pullback of `A` to
`U ∩ V` whose fibre map at `x` is that of `H` at `(x, t)`. Then the pullback of the gluing of the
pullback of `A` to `B × T` over `U × T` and `V × T` by `H`, along `x ↦ (x, t)`, is isomorphic
to the gluing of `A` by `g`, by the identity in coordinates. -/
def pullbackGlueIso
    (hg : ∀ x : ↥(U ∩ V), H.hom.fiberMap ⟨(x.val, t), x.property⟩ = g.hom.fiberMap x) :
    ((A.pullback ContinuousMap.fst).glue (hU.preimage continuous_fst)
        (hV.preimage continuous_fst) (by rw [← preimage_union, hUV, preimage_univ]) H).pullback
        ((ContinuousMap.id B).prodMk (.const B t)) ≅ A.glue hU hV hUV g :=
  constIso (baseSet_pullback_glue_subset A hU hV hUV g H t) (.refl 𝕜 _) fun i k b hi hk ↦ by
    rw [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    exact coordChange_pullback_glue hU hV hUV hg i k b hi hk

/-- The isomorphism `pullbackGlueIso` is the identity in coordinates. -/
@[simp]
theorem fiberMap_pullbackGlueIso_hom
    (hg : ∀ x : ↥(U ∩ V), H.hom.fiberMap ⟨(x.val, t), x.property⟩ = g.hom.fiberMap x) (x : B) :
    (A.pullbackGlueIso hU hV hUV g H t hg).hom.fiberMap x = .id 𝕜 _ := by
  rw [pullbackGlueIso, fiberMap_constIso_hom]
  -- The two sides differ only in the rank they name, both `A.rank` by definition.
  exact ContinuousLinearEquiv.coe_refl

/-- The inverse of `pullbackGlueIso` is the identity in coordinates. -/
@[simp]
theorem fiberMap_pullbackGlueIso_inv
    (hg : ∀ x : ↥(U ∩ V), H.hom.fiberMap ⟨(x.val, t), x.property⟩ = g.hom.fiberMap x) (x : B) :
    (A.pullbackGlueIso hU hV hUV g H t hg).inv.fiberMap x = .id 𝕜 _ := by
  rw [pullbackGlueIso, fiberMap_constIso_inv, ContinuousLinearEquiv.refl_symm]
  -- The two sides differ only in the rank they name, both `A.rank` by definition.
  exact ContinuousLinearEquiv.coe_refl

end Homotopic

open scoped unitInterval in
/-- **Gluings by homotopic automorphisms are isomorphic.** Let `B` be paracompact and R₁, let `U`
and `V` be open sets covering `B`, and let `g₀` and `g₁` be automorphisms of the pullback of `A`
to `U ∩ V`. If an automorphism `H` of the pullback of `A` along `Prod.fst` to the part
`(U ∩ V) × I` of `B × I` has the fibre maps of `g₀` at time `0` and those of `g₁` at time `1`,
then the gluings of `A` by `g₀` and by `g₁` are isomorphic. -/
theorem nonempty_iso_glue_of_homotopic [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜] [ParacompactSpace B]
    [R1Space B] (A : FiniteRankBundleCore 𝕜 B) {U V : Set B} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = univ)
    {g₀ g₁ : A.pullback (ContinuousMap.subtypeVal (U ∩ V)) ≅
      A.pullback (ContinuousMap.subtypeVal (U ∩ V))}
    (H : (A.pullback (ContinuousMap.fst : C(B × I, B))).pullback
        (ContinuousMap.subtypeVal (Prod.fst ⁻¹' U ∩ Prod.fst ⁻¹' V)) ≅
      (A.pullback (ContinuousMap.fst : C(B × I, B))).pullback
        (ContinuousMap.subtypeVal (Prod.fst ⁻¹' U ∩ Prod.fst ⁻¹' V)))
    (h₀ : ∀ x : ↥(U ∩ V), H.hom.fiberMap ⟨(x.val, 0), x.property⟩ = g₀.hom.fiberMap x)
    (h₁ : ∀ x : ↥(U ∩ V), H.hom.fiberMap ⟨(x.val, 1), x.property⟩ = g₁.hom.fiberMap x) :
    Nonempty (A.glue hU hV hUV g₀ ≅ A.glue hU hV hUV g₁) := by
  -- The two ends of the gluing over `B × I` are pullbacks along homotopic maps; the homotopy
  -- `(s, x) ↦ (x, s)` is at its ends the two maps, as they are evaluated.
  have hJ : ((ContinuousMap.id B).prodMk (.const B (0 : I))).Homotopic
      ((ContinuousMap.id B).prodMk (.const B (1 : I))) :=
    ⟨⟨⟨fun p ↦ (p.2, p.1), by fun_prop⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩⟩
  obtain ⟨e⟩ := ((A.pullback ContinuousMap.fst).glue (hU.preimage continuous_fst)
    (hV.preimage continuous_fst) (by rw [← preimage_union, hUV, preimage_univ]) H)
    |>.nonempty_pullback_iso_of_homotopic hJ
  exact ⟨(A.pullbackGlueIso hU hV hUV g₀ H 0 h₀).symm ≪≫ e ≪≫
    A.pullbackGlueIso hU hV hUV g₁ H 1 h₁⟩

end TauCeti.FiniteRankBundleCore

end
