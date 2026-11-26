/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import SymplecticGeometry.Geometry.Manifold.ContMDiff.TimeExtension
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Families of local diffeomorphisms over the unit interval

Let `f : unitInterval × M → N` be jointly smooth, with `M` and `N` boundaryless and the model
space of `M` complete. If every slice `f (t, ·)` is a local diffeomorphism, then so is the map
`(t, x) ↦ (t, f (t, x))` of the cylinders `unitInterval × M → unitInterval × N`, at the ends of
the interval as well. Since `unitInterval × M` has boundary, the inverse function theorem does not
apply to it directly.

## Main results

* `ContDiffOn.isLocalDiffeomorphAt_fst_prodMk`: if `g : G × E → F` is smooth near a point and
  its partial derivative in the second variable is invertible there, then
  `(s, u) ↦ (s, g (s, u))` is a local diffeomorphism at that point.
* `IsLocalDiffeomorphAt.restrict_unitInterval`: a local diffeomorphism `(s, u) ↦ (s, g (s, u))` of
  `ℝ × M → ℝ × N` restricts to a local diffeomorphism of `unitInterval × M → unitInterval × N`.
* `ContMDiff.isLocalDiffeomorphAt_prodMk_unitInterval`: the pointwise version of the next result.
* `ContMDiff.isLocalDiffeomorph_prodMk_unitInterval`: a jointly smooth family of local
  diffeomorphisms over `[0, 1]` gives a local diffeomorphism `(t, x) ↦ (t, f (t, x))`.

## Implementation notes

Near `(t₀, x₀)`, in the charts at `x₀` and at `f (t₀, x₀)`, the family is a map smooth on
`[a, b] × U`, for an interval `[a, b]` that is a neighbourhood of `t₀` in `[0, 1]`
(`Continuous.exists_Icc_prod_extChartAt`, `ContMDiff.contDiffOn_extChartAt_comp_projIcc`).
Seeley's extension (`SymplecticGeometry.exists_contDiffOn_eqOn_Icc_prod`) extends it to a map `g`
smooth on `ℝ × U`. The map `(s, u) ↦ (s, g (s, u))` has a block triangular derivative at
`(t₀, u₀)`, whose diagonal blocks are the identity and the derivative of `f (t₀, ·)` in charts, so
it is invertible (Tau Ceti's `ContinuousLinearMap.isInvertible_iff_of_fst_comp_eq`) and the inverse
function theorem (`TauCeti.isLocalDiffeomorphAt_of_fderiv_eq`) makes the map a local
diffeomorphism. It preserves the time, so it restricts to `unitInterval × U`; composing with the
charts gives the result. This adapts the proof of Tau Ceti's
`TauCeti.isLocalDiffeomorph_fst_prodMk`, which works on boundaryless parameter manifolds, to the
parameter space `[0, 1]`.
`Diffeomorph.contMDiff_symm_eval_unitInterval`, on the inverses of a family of diffeomorphisms, is
a consequence.

## References

* R. T. Seeley, *Extension of $C^\infty$ functions defined in a half space*,
  Proc. Amer. Math. Soc. 15 (1964), 625–626.
-/

public section

open Set Filter Function
open scoped Manifold ContDiff Topology

/-- If `g : G × E → F` is `C^n` on an open set containing `p`, with `1 ≤ n`, and its partial
derivative `fderiv ℝ g p ∘L inr` in the second variable is invertible, then
`(s, u) ↦ (s, g (s, u))` is a `C^n` local diffeomorphism of `G × E → G × F` at `p`. -/
theorem ContDiffOn.isLocalDiffeomorphAt_fst_prodMk {G E F : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞} {g : G × E → F} {t : Set (G × E)}
    {p : G × E} (hg : ContDiffOn ℝ n g t) (ht : IsOpen t) (hp : p ∈ t) (hn : 1 ≤ n)
    (hinv : (fderiv ℝ g p ∘L ContinuousLinearMap.inr ℝ G E).IsInvertible) :
    IsLocalDiffeomorphAt 𝓘(ℝ, G × E) 𝓘(ℝ, G × F) n (fun q ↦ (q.1, g q)) p := by
  have hgd := ((hg.contDiffAt (ht.mem_nhds hp)).differentiableAt
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hn))).hasFDerivAt
  -- The derivative of `(s, u) ↦ (s, g (s, u))` is block triangular, with invertible diagonal
  -- blocks.
  set T := (ContinuousLinearMap.fst ℝ G E).prod (fderiv ℝ g p)
  have hT : T.IsInvertible := by
    refine (ContinuousLinearMap.isInvertible_iff_of_fst_comp_eq
      (ContinuousLinearMap.ext fun _ ↦ by simp [T])).2 ?_
    convert hinv using 1
    exact ContinuousLinearMap.ext fun _ ↦ by simp [T]
  obtain ⟨L, hL⟩ := hT
  exact TauCeti.isLocalDiffeomorphAt_of_fderiv_eq (contDiffOn_fst.prodMk hg) ht hp hn
    (hL.trans (hasFDerivAt_fst.prodMk hgd).fderiv.symm)

variable {E H M E' H' N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]

/-- A local diffeomorphism of `ℝ × M → ℝ × N` of the form `(s, x) ↦ (s, g (s, x))`, at a point of
time in `[0, 1]`, restricts to a local diffeomorphism `(t, x) ↦ (t, g (t, x))` of
`unitInterval × M → unitInterval × N` there. -/
theorem IsLocalDiffeomorphAt.restrict_unitInterval {n : WithTop ℕ∞} {g : ℝ × M → N}
    {t : unitInterval} {x : M}
    (hg : IsLocalDiffeomorphAt (𝓘(ℝ).prod I) (𝓘(ℝ).prod J) n (fun q ↦ (q.1, g q)) ((t : ℝ), x)) :
    IsLocalDiffeomorphAt ((𝓡∂ 1).prod I) ((𝓡∂ 1).prod J) n
      (fun p : unitInterval × M ↦ (p.1, g ((p.1 : ℝ), p.2))) (t, x) := by
  obtain ⟨Φ, hΦ, -, hgΦ⟩ := hg.exists_partialDiffeomorph_eqOn isOpen_univ (mem_univ _)
  -- The inverse of `Φ` preserves the time.
  have hfst {q : ℝ × N} (hq : q ∈ Φ.target) : (Φ.symm q).1 = q.1 :=
    congrArg Prod.fst ((hgΦ (Φ.map_target hq)).trans (Φ.right_inv hq))
  have hsymm {q : ℝ × N} (hq : q ∈ Φ.target) : (q.1, (Φ.symm q).2) = Φ.symm q :=
    Prod.ext (hfst hq).symm rfl
  -- The inclusions of `unitInterval × M` and `unitInterval × N` into `ℝ × M` and `ℝ × N`.
  have hιM : ContMDiff ((𝓡∂ 1).prod I) (𝓘(ℝ).prod I) n (Prod.map Subtype.val id) :=
    (contMDiff_subtypeVal_Icc (x := 0) (y := 1)).prodMap (contMDiff_id (I := I) (M := M))
  have hιN : ContMDiff ((𝓡∂ 1).prod J) (𝓘(ℝ).prod J) n (Prod.map Subtype.val id) :=
    (contMDiff_subtypeVal_Icc (x := 0) (y := 1)).prodMap (contMDiff_id (I := J) (M := N))
  let Ψ : PartialDiffeomorph ((𝓡∂ 1).prod I) ((𝓡∂ 1).prod J) (unitInterval × M) (unitInterval × N)
      n :=
    { toFun := fun p ↦ (p.1, g ((p.1 : ℝ), p.2))
      invFun := fun p ↦ (p.1, (Φ.symm ((p.1 : ℝ), p.2)).2)
      source := Prod.map Subtype.val id ⁻¹' Φ.source
      target := Prod.map Subtype.val id ⁻¹' Φ.target
      map_source' := fun p hp ↦ by
        have h := Φ.map_source hp
        rw [← hgΦ hp] at h
        exact h
      map_target' := fun p hp ↦ (congrArg (· ∈ Φ.source) (hsymm hp)).mpr (Φ.map_target hp)
      left_inv' := fun p hp ↦ by
        have h : Φ.symm (((p.1 : ℝ), g ((p.1 : ℝ), p.2))) = ((p.1 : ℝ), p.2) := by
          have h₂ : ((p.1 : ℝ), g ((p.1 : ℝ), p.2)) = Φ ((p.1 : ℝ), p.2) := hgΦ hp
          rw [h₂]
          exact Φ.left_inv hp
        have h' := congrArg Prod.snd h
        exact Prod.ext rfl h'
      right_inv' := fun p hp ↦ by
        have h := (hgΦ (Φ.map_target hp)).trans (Φ.right_inv hp)
        have h' := (congrArg g (hsymm hp)).trans (congrArg Prod.snd h)
        exact Prod.ext rfl h'
      open_source := Φ.open_source.preimage hιM.continuous
      open_target := Φ.open_target.preimage hιN.continuous
      contMDiffOn_toFun := by
        refine contMDiff_fst.contMDiffOn.prodMk ?_
        refine ((contMDiff_snd.contMDiffOn (s := univ)).comp Φ.contMDiffOn_toFun
          (fun _ _ ↦ mem_univ _)).comp hιM.contMDiffOn (fun _ hp ↦ hp) |>.congr fun p hp ↦ ?_
        exact congrArg Prod.snd (hgΦ hp)
      contMDiffOn_invFun := contMDiff_fst.contMDiffOn.prodMk <|
        ((contMDiff_snd.contMDiffOn (s := univ)).comp Φ.contMDiffOn_invFun
          (fun _ _ ↦ mem_univ _)).comp hιN.contMDiffOn (fun _ hp ↦ hp) }
  exact Ψ.isLocalDiffeomorphAt _ _ _ hΦ

variable [CompleteSpace E] [IsManifold I ∞ M] [IsManifold J ∞ N] [BoundarylessManifold I M]
  [BoundarylessManifold J N]

/-- Let `f : unitInterval × M → N` be jointly smooth, with `M` and `N` boundaryless. If the slice
`f (t₀, ·)` is a local diffeomorphism at `x₀`, then `(t, x) ↦ (t, f (t, x))` is a local
diffeomorphism of `unitInterval × M → unitInterval × N` at `(t₀, x₀)`, also when `t₀` is `0`
or `1`. -/
theorem ContMDiff.isLocalDiffeomorphAt_prodMk_unitInterval {f : unitInterval × M → N}
    (hf : ContMDiff ((𝓡∂ 1).prod I) J ∞ f) {t₀ : unitInterval} {x₀ : M}
    (hd : IsLocalDiffeomorphAt I J ∞ (fun x ↦ f (t₀, x)) x₀) :
    IsLocalDiffeomorphAt ((𝓡∂ 1).prod I) ((𝓡∂ 1).prod J) ∞
      (fun p : unitInterval × M ↦ (p.1, f p)) (t₀, x₀) := by
  set e := extChartAt I x₀
  set e' := extChartAt J (f (t₀, x₀))
  obtain ⟨a, b, U, ha, hab, hb, hU, hu₀, hnhds, hmaps⟩ :=
    hf.continuous.exists_Icc_prod_extChartAt (I := I) (J := J) t₀ x₀
  obtain ⟨g, hg, hgf⟩ := SymplecticGeometry.exists_contDiffOn_eqOn_Icc_prod hab hU
    (hf.contDiffOn_extChartAt_comp_projIcc (Icc_subset_Icc ha hb) hmaps)
  set u₀ := e x₀
  have ht₀ : (t₀ : ℝ) ∈ Icc a b := mem_ofPred_eq ▸ mem_of_mem_nhds hnhds
  have hgf' {s : unitInterval} (hs : (s : ℝ) ∈ Icc a b) {u : E} (hu : u ∈ U) :
      g (s, u) = e' (f (s, e.symm u)) := by
    rw [hgf ⟨hs, hu⟩]
    simp only [projIcc_val, e, e']
  have hgt₀ : (fun u ↦ g (t₀, u)) =ᶠ[𝓝 u₀] writtenInExtChartAt I J x₀ (fun x ↦ f (t₀, x)) := by
    filter_upwards [hU.mem_nhds hu₀] with u hu
    rw [hgf' ht₀ hu]
    simp only [writtenInExtChartAt, comp_apply, e, e']
  have hg₀ : g ((t₀ : ℝ), u₀) = e' (f (t₀, x₀)) := by
    rw [hgf' ht₀ hu₀]
    simp only [u₀, e, extChartAt_to_inv]
  -- The partial derivative of `g` in the space variable is the derivative of `f (t₀, ·)` in
  -- charts, which is invertible.
  have hgd := ((hg.contDiffAt (x := ((t₀ : ℝ), u₀))
    (prod_mem_nhds univ_mem (hU.mem_nhds hu₀))).differentiableAt
    (by simp)).hasFDerivAt
  have hfd : HasFDerivAt (writtenInExtChartAt I J x₀ (fun x ↦ f (t₀, x)))
      (mfderiv I J (fun x ↦ f (t₀, x)) x₀) u₀ :=
    (((hd.mdifferentiableAt (by simp)).hasMFDerivAt).2).hasFDerivAt
      (range_mem_nhds_isInteriorPoint BoundarylessManifold.isInteriorPoint)
  have hpartial : fderiv ℝ g ((t₀ : ℝ), u₀) ∘L ContinuousLinearMap.inr ℝ ℝ E =
      mfderiv I J (fun x ↦ f (t₀, x)) x₀ :=
    (hgd.comp u₀ (hasFDerivAt_prodMk_right (t₀ : ℝ) u₀)).congr_of_eventuallyEq hgt₀.symm
      |>.unique hfd
  have hK : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E') ∞ (fun q ↦ (q.1, g q))
      ((t₀ : ℝ), u₀) :=
    hg.isLocalDiffeomorphAt_fst_prodMk (isOpen_univ.prod hU) ⟨mem_univ _, hu₀⟩ (by simp)
      (hpartial ▸ hd.isInvertible_mfderiv (by simp))
  -- Read `hK` with the product models of `ℝ × E` and `ℝ × E'`.
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod, modelWithCornersSelf_prod,
    ← chartedSpaceSelf_prod] at hK
  have hint : u₀ ∈ interior e.target :=
    (ModelWithCorners.isInteriorPoint_iff (I := I)).mp BoundarylessManifold.isInteriorPoint
  have hint' : g ((t₀ : ℝ), u₀) ∈ interior e'.target :=
    hg₀ ▸ (ModelWithCorners.isInteriorPoint_iff (I := J)).mp BoundarylessManifold.isInteriorPoint
  have hE : IsLocalDiffeomorphAt ((𝓡∂ 1).prod I) ((𝓡∂ 1).prod 𝓘(ℝ, E)) ∞ (Prod.map id e)
      (t₀, x₀) :=
    (SymplecticGeometry.isLocalDiffeomorph_id t₀).prodMap
      (TauCeti.isLocalDiffeomorphAt_extChartAt (mem_extChartAt_source x₀) hint)
  have hE' : IsLocalDiffeomorphAt ((𝓡∂ 1).prod 𝓘(ℝ, E')) ((𝓡∂ 1).prod J) ∞
      (Prod.map id e'.symm) (t₀, g ((t₀ : ℝ), u₀)) :=
    (SymplecticGeometry.isLocalDiffeomorph_id t₀).prodMap
      (TauCeti.isLocalDiffeomorphAt_extChartAt_symm hint')
  refine ((hE.comp (hg := hK.restrict_unitInterval)).comp (hg := hE')).congr_of_eventuallyEq ?_
  -- Near `(t₀, x₀)` the composite of the charts with `(s, u) ↦ (s, g (s, u))` is the map.
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hnhds,
    continuous_snd.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) x₀),
    continuous_snd.continuousAt.preimage_mem_nhds
      ((continuousAt_extChartAt x₀).preimage_mem_nhds (hU.mem_nhds hu₀))] with p hpab hpe hpU
  have hpU' : e p.2 ∈ U := hpU
  have hpe' : f (p.1, e.symm (e p.2)) ∈ e'.source := (hmaps p.1 hpab _ hpU').2
  rw [e.left_inv hpe] at hpe'
  simp only [comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
  rw [hgf' hpab hpU', e.left_inv hpe, Prod.map_apply, e'.left_inv hpe']
  rfl

/-- A jointly smooth family `f : unitInterval × M → N` of local diffeomorphisms of boundaryless
manifolds gives a local diffeomorphism `(t, x) ↦ (t, f (t, x))` of
`unitInterval × M → unitInterval × N`. -/
theorem ContMDiff.isLocalDiffeomorph_prodMk_unitInterval {f : unitInterval × M → N}
    (hf : ContMDiff ((𝓡∂ 1).prod I) J ∞ f)
    (hd : ∀ t, IsLocalDiffeomorph I J ∞ (fun x ↦ f (t, x))) :
    IsLocalDiffeomorph ((𝓡∂ 1).prod I) ((𝓡∂ 1).prod J) ∞
      (fun p : unitInterval × M ↦ (p.1, f p)) :=
  fun p ↦ hf.isLocalDiffeomorphAt_prodMk_unitInterval (hd p.1 p.2)
