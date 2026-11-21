/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover
public import SymplecticGeometry.Geometry.Manifold.ContMDiffMap.Chart.CodRestrict
public import SymplecticGeometry.Geometry.Manifold.ContMDiffMap.Chart.Restriction
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.ManifoldFamily
import TauCeti.Geometry.Manifold.VectorBundle.Submersion

/-!
# Sections as maps into the total space, and fibrewise maps of sections

A `C^n` section `s` of a vector bundle `V` is also the `C^n` map `x ↦ ⟨x, s x⟩` into the total
space (`ContMDiffSection.toContMDiffMap`). For a covering frame system, this map is continuous from
Tau Ceti's frame topology on sections to the weak Whitney topology on `C^n` maps into the total
space (`ContMDiffSection.continuous_toContMDiffMap`). Read in a chart of the total space, which
Mathlib builds from a trivialization, a section is the pair of a chart of the base, which does not
depend on the section, and the coordinates of the section in that trivialization; these are
continuous in the section by Tau Ceti's `continuous_frameCoordinates_of_cover`.

The main result concerns fibre maps `Φ p x : V x → W x` that depend on a parameter `p` in a
manifold `P` and are jointly `C^n` in the parameter, the point and the fibre value on an open
subset `O` of the total space of `V`. For each `p` they send a section `s` with values in
`O` to the section `x ↦ Φ p x (s x)` of `W` (`ContMDiffSection.fiberwiseMap`), and this is jointly
continuous in `p` and `s` for the frame topologies (`ContMDiffSection.continuous_fiberwiseMap`).
In a frame of `W`, the coordinates of `x ↦ Φ p x (s x)` are the composite of the section,
viewed as a map into the points of `O` over the frame domain (`ContMDiffMap.codRestrict`), with
the fibre maps read in the frame; Tau Ceti's continuity of composition and of jointly `C^n`
families in the weak Whitney topology conclude.

## Main definitions and results

* `ContMDiffSection.toContMDiffMap`, `ContMDiffSection.continuous_toContMDiffMap`
* `ContMDiffSection.fiberwiseMap`, `ContMDiffSection.continuous_fiberwiseMap`

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 2, §1 (the weak topology on spaces of `C^r` maps, as Tau Ceti builds it)
-/

public section

open Bundle Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] {n : ℕ∞ω}

/-- A `C^n` section, as the `C^n` map `x ↦ ⟨x, s x⟩` from the base into the total space. -/
def toContMDiffMap (s : Cₛ^n⟮I; F, V⟯) : C^n⟮I, M; I.prod 𝓘(𝕜, F), TotalSpace F V⟯ :=
  ⟨fun x ↦ TotalSpace.mk' F x (s x), s.contMDiff⟩

/-- The map of a section sends `x` to the point `s x` of the fibre over `x`. -/
@[simp]
theorem toContMDiffMap_apply (s : Cₛ^n⟮I; F, V⟯) (x : M) :
    toContMDiffMap s x = TotalSpace.mk' F x (s x) :=
  (rfl)

/-- A section is determined by its map into the total space. -/
theorem toContMDiffMap_injective :
    Function.Injective (toContMDiffMap : Cₛ^n⟮I; F, V⟯ → C^n⟮I, M; I.prod 𝓘(𝕜, F), _⟯) :=
  fun s t h ↦ ext fun x ↦ by
    simpa using (TotalSpace.mk_inj (b := x)).mp (congrArg (· x) h)

section Frames

variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle n F V I] [IsManifold I n M]

/-- Over the base set of `trivializationAt F V y.proj`, the coordinate derivatives of a section
read in the chart of the total space at `y` are those of the chart of `M` at `y.proj` paired with
those of the coordinates of the section in that trivialization. -/
private theorem iteratedFDerivWithin_extChartAt_toContMDiffMap (s : Cₛ^n⟮I; F, V⟯) (x : M)
    (y : TotalSpace F V) {w : E} (hw : w ∈ (extChartAt I x).target)
    (hS : (extChartAt I x).symm w ∈ (trivializationAt F V y.proj).baseSet ∧
      (extChartAt I x).symm w ∈ (chartAt H y.proj).source) (m : ℕ) (hm : m ≤ n) :
    iteratedFDerivWithin 𝕜 m (extChartAt (I.prod 𝓘(𝕜, F)) y ∘ toContMDiffMap s ∘
        (extChartAt I x).symm) (extChartAt I x).target w =
      (iteratedFDerivWithin 𝕜 m (extChartAt I y.proj ∘ (extChartAt I x).symm)
        (extChartAt I x).target w).prod
      (iteratedFDerivWithin 𝕜 m ((fun p ↦ (trivializationAt F V y.proj ⟨p, s p⟩).2) ∘
        (extChartAt I x).symm) (extChartAt I x).target w) := by
  set φ := extChartAt I x
  set t := trivializationAt F V y.proj
  have hev : extChartAt (I.prod 𝓘(𝕜, F)) y ∘ toContMDiffMap s ∘ φ.symm =ᶠ[𝓝[φ.target] w]
      fun v ↦ ((extChartAt I y.proj ∘ φ.symm) v, ((fun p ↦ (t ⟨p, s p⟩).2) ∘ φ.symm) v) := by
    filter_upwards [(continuousOn_extChartAt_symm (I := I) x w hw).eventually
      (t.open_baseSet.mem_nhds hS.1)] with v hv
    exact Bundle.extChartAt_apply_of_mem_baseSet y (x := toContMDiffMap s (φ.symm v)) hv
  have hsrc : toContMDiffMap s (φ.symm w) ∈ (extChartAt (I.prod 𝓘(𝕜, F)) y).source :=
    (Bundle.mem_extChartAt_source_iff y _).mpr (by rwa [extChartAt_source])
  have hpair := ((toContMDiffMap s).contDiffWithinAt_extChartAt hw hsrc).congr_of_eventuallyEq
    hev.symm (hev.eq_of_nhdsWithin hw).symm
  rw [hev.iteratedFDerivWithin_eq (hev.eq_of_nhdsWithin hw)]
  exact iteratedFDerivWithin_prodMk (contDiff_fst.comp_contDiffWithinAt hpair)
    (contDiff_snd.comp_contDiffWithinAt hpair) (uniqueDiffOn_extChartAt_target x) hw hm

variable [LocallyCompactSpace E]
  {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- The local form of `continuous_toContMDiffMap`: a chart derivative test passed by a section at
a chart point is passed near that point by every nearby section. -/
private theorem eventually_toContMDiffMap_mem (hcover : ∀ x, ∃ i, x ∈ U i)
    {s₀ : Cₛ^n⟮I; F, V⟯} {x : M} {y : TotalSpace F V} {w : E}
    (hw : w ∈ (extChartAt I x).target)
    (h₀ : toContMDiffMap s₀ ((extChartAt I x).symm w) ∈ (extChartAt (I.prod 𝓘(𝕜, F)) y).source)
    {m : ℕ} (hm : m ≤ n) {W : Set (E [×m]→L[𝕜] (E × F))}
    (hW : W ∈ 𝓝 (iteratedFDerivWithin 𝕜 m (extChartAt (I.prod 𝓘(𝕜, F)) y ∘ toContMDiffMap s₀ ∘
      (extChartAt I x).symm) (extChartAt I x).target w)) :
    letI := frameTopology (I := I) (n := n) e U hU
    ∀ᶠ q : Cₛ^n⟮I; F, V⟯ × E in 𝓝 s₀ ×ˢ 𝓝[(extChartAt I x).target] w,
      toContMDiffMap q.1 ((extChartAt I x).symm q.2) ∈ (extChartAt (I.prod 𝓘(𝕜, F)) y).source ∧
      iteratedFDerivWithin 𝕜 m (extChartAt (I.prod 𝓘(𝕜, F)) y ∘ toContMDiffMap q.1 ∘
        (extChartAt I x).symm) (extChartAt I x).target q.2 ∈ W := by
  let _ := frameTopology (I := I) (n := n) e U hU
  set φ := extChartAt I x
  set t := trivializationAt F V y.proj
  rw [Bundle.mem_extChartAt_source_iff, extChartAt_source] at h₀
  have hφ := continuousOn_extChartAt_symm (I := I) x w hw
  have hS : ∀ᶠ q : Cₛ^n⟮I; F, V⟯ × E in 𝓝 s₀ ×ˢ 𝓝[φ.target] w,
      φ.symm q.2 ∈ t.baseSet ∧ φ.symm q.2 ∈ (chartAt H y.proj).source :=
    tendsto_snd.eventually ((hφ.eventually (t.open_baseSet.mem_nhds h₀.1)).and
      (hφ.eventually ((chartAt H y.proj).open_source.mem_nhds h₀.2)))
  have hT : ∀ᶠ q : Cₛ^n⟮I; F, V⟯ × E in 𝓝 s₀ ×ˢ 𝓝[φ.target] w, q.2 ∈ φ.target :=
    tendsto_snd.eventually self_mem_nhdsWithin
  -- The chart part does not depend on the section.
  have hA : Tendsto (fun q : Cₛ^n⟮I; F, V⟯ × E ↦
      iteratedFDerivWithin 𝕜 m (extChartAt I y.proj ∘ φ.symm) φ.target q.2)
      (𝓝 s₀ ×ˢ 𝓝[φ.target] w)
      (𝓝 (iteratedFDerivWithin 𝕜 m (extChartAt I y.proj ∘ φ.symm) φ.target w)) :=
    (((ContMDiffMap.id : C^n⟮I, M; I, M⟯).contDiffWithinAt_extChartAt hw
      (by rw [extChartAt_source]; exact h₀.2)).continuousWithinAt_iteratedFDerivWithin
        (uniqueDiffOn_extChartAt_target x) hm hw).tendsto.comp tendsto_snd
  -- The fibre part is controlled by the frame coordinates in `t`.
  let Ut : Opens M := ⟨t.baseSet, t.open_baseSet⟩
  have hB := ContMDiffMap.tendsto_iteratedFDerivWithin_of_eqOn_opens Ut
    ((continuous_frameCoordinates_of_cover e U hU hcover t Ut subset_rfl).tendsto s₀)
    (f := fun s p ↦ (t ⟨p, s p⟩).2) (f₀ := fun p ↦ (t ⟨p, s₀ p⟩).2)
    (fun s p ↦ (t.frameCoordinates_apply subset_rfl s p).symm)
    (fun p ↦ (t.frameCoordinates_apply subset_rfl s₀ p).symm) x hw h₀.1 m hm
  have hlim := ((ContinuousMultilinearMap.prodL 𝕜 (fun _ : Fin m ↦ E) E F).continuous.tendsto
    _).comp (hA.prodMk_nhds hB)
  rw [iteratedFDerivWithin_extChartAt_toContMDiffMap s₀ x y hw h₀ m hm] at hW
  filter_upwards [hS, hT, hlim.eventually_mem hW] with q hq hqT hqW
  refine ⟨(Bundle.mem_extChartAt_source_iff y _).mpr (by rwa [extChartAt_source]), ?_⟩
  rw [iteratedFDerivWithin_extChartAt_toContMDiffMap q.1 x y hqT hq m hm]
  exact hqW

/-- For a covering frame system, `s ↦ toContMDiffMap s` is continuous from the frame topology on
sections to the weak Whitney topology on `C^n` maps into the total space. -/
theorem continuous_toContMDiffMap (hcover : ∀ x, ∃ i, x ∈ U i) :
    letI := frameTopology (I := I) (n := n) e U hU
    Continuous (toContMDiffMap : Cₛ^n⟮I; F, V⟯ → C^n⟮I, M; I.prod 𝓘(𝕜, F), TotalSpace F V⟯) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  refine continuous_iff_continuousAt.mpr fun s₀ ↦ ?_
  refine ContMDiffMap.tendsto_manifoldWeakWhitney_iff.mpr fun x y m hm K hK W hW h₀ ↦ ?_
  simp only [ContMDiffMap.mem_chartJetSet]
  refine hK.eventually_forall_of_forall_eventually fun w hw ↦ ?_
  have h := eventually_toContMDiffMap_mem e U hU hcover w.property
    ((ContMDiffMap.mem_chartJetSet.mp h₀) w hw).1 hm
    (hW.mem_nhds ((ContMDiffMap.mem_chartJetSet.mp h₀) w hw).2)
  rw [nhds_prod_eq]
  exact (tendsto_id.prodMap (map_nhds_subtypeVal w).le).eventually h

end Frames

section FiberwiseMap

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {W : M → Type*} [∀ x, TopologicalSpace (W x)] [TopologicalSpace (TotalSpace F' W)]
  [FiberBundle F' W]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners 𝕜 EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  (Φ : P → ∀ x, V x → W x) {O : Set (TotalSpace F V)}
  (hΦ : ContMDiffOn (IP.prod (I.prod 𝓘(𝕜, F))) (I.prod 𝓘(𝕜, F')) n
    (fun q : P × TotalSpace F V ↦ TotalSpace.mk' F' q.2.proj (Φ q.1 q.2.proj q.2.snd))
    (univ ×ˢ O))

/-- The section `x ↦ Φ p x (s x)` of `W`, for a section `s` of `V` with values in `O`, where the
fibre maps `Φ p x : V x → W x` are jointly `C^n` on `P × O` in the parameter `p`, the point and the
fibre value. -/
def fiberwiseMap (p : P) (s : {s : Cₛ^n⟮I; F, V⟯ // ∀ x, ⟨x, s x⟩ ∈ O}) : Cₛ^n⟮I; F', W⟯ :=
  ⟨fun x ↦ Φ p x (s.val x),
    hΦ.comp_contMDiff (contMDiff_const.prodMk s.val.contMDiff) fun x ↦ ⟨mem_univ _, s.property x⟩⟩

/-- The value of `fiberwiseMap Φ hΦ p s` at `x` is `Φ p x (s x)`. -/
@[simp]
theorem fiberwiseMap_apply (p : P) (s : {s : Cₛ^n⟮I; F, V⟯ // ∀ x, ⟨x, s x⟩ ∈ O}) (x : M) :
    fiberwiseMap Φ hΦ p s x = Φ p x (s.val x) :=
  (rfl)

variable [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [VectorBundle 𝕜 F' W]
  [ContMDiffVectorBundle n F' W I]

include hΦ in
/-- Read in a trivialization `e'` of `W` in the atlas, the fibre maps give a jointly `C^n` map on
the product of the parameter space and the points of `O` over the base set of `e'`. -/
private theorem contMDiff_fiberwiseMap_coord (e' : Trivialization F' (π F' W))
    [MemTrivializationAtlas e'] (N : Opens (TotalSpace F V))
    (hN : ∀ v ∈ N, v ∈ O ∧ v.proj ∈ e'.baseSet) :
    ContMDiff (IP.prod (I.prod 𝓘(𝕜, F))) 𝓘(𝕜, F') n
      fun q : P × N ↦ (e' (TotalSpace.mk' F' (q.2 : TotalSpace F V).proj
        (Φ q.1 (q.2 : TotalSpace F V).proj (q.2 : TotalSpace F V).snd))).2 := by
  have h₁ := hΦ.comp_contMDiff (contMDiff_id.prodMap contMDiff_subtypeVal)
    fun q : P × N ↦ ⟨mem_univ _, (hN _ q.2.property).1⟩
  exact (contMDiff_snd.comp_contMDiffOn e'.contMDiffOn).comp_contMDiff h₁
    fun q ↦ e'.mem_source.mpr (hN _ q.2.property).2

variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle n F V I] [IsManifold I n M] [LocallyCompactSpace E]
  {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  {κ : Type*} (e' : κ → Trivialization F' (π F' W)) [∀ j, MemTrivializationAtlas (e' j)]
  (U' : κ → Opens M) (hU' : ∀ j, (U' j : Set M) ⊆ (e' j).baseSet)

/-- A map of section spaces given fibrewise by fibre maps `Φ p x : V x → W x` that are jointly
`C^n` in the parameter `p`, the point and the fibre value, on an open subset `O` of the total
space of `V`, is jointly continuous in the parameter and the section for the frame topologies,
for a covering frame system of `V` and any frame system of `W`.

Continuity of `Φ` in the parameter alone would not do for `n ≥ 1`: on the trivial line bundle
over `ℝ`, the fibre maps `Φ t x v = v + t * sin (x / t)` (and `Φ 0 x v = v`) are continuous in
`(t, x, v)`, but the derivative in `x` of `Φ t x (s x) - s x` is `cos (x / t)`, which does not tend
to `0` as `t → 0`.

The proof composes, in the weak Whitney topology, the section viewed as a map into the open set of
points of `O` over a frame domain of `W` with the fibre maps read in that frame. Tau Ceti proves
continuity of composition when the models of the source and of the middle manifold are locally
compact; the middle manifold here has model `E × F`, which is why `F` is assumed locally compact
(every finite-dimensional `F` is). The statement should hold without this assumption. -/
theorem continuous_fiberwiseMap [IsManifold IP n P] [LocallyCompactSpace F] (hO : IsOpen O)
    (hcover : ∀ x, ∃ i, x ∈ U i) :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) e' U' hU'
    Continuous fun q : P × {s : Cₛ^n⟮I; F, V⟯ // ∀ x, ⟨x, s x⟩ ∈ O} ↦
      fiberwiseMap Φ hΦ q.1 q.2 := by
  let _ := frameTopology (I := I) (n := n) e U hU
  let _ := frameTopology (I := I) (n := n) e' U' hU'
  refine (continuous_frameTopology_iff_frameCoordinates e' U' hU').mpr fun j ↦ ?_
  -- The points of `O` over the base set of the frame `e' j`.
  let N : Opens (TotalSpace F V) :=
    ⟨O ∩ π F V ⁻¹' (e' j).baseSet,
      hO.inter ((e' j).open_baseSet.preimage (FiberBundle.continuous_proj F V))⟩
  -- A section, restricted to `U' j` and corestricted to `N`.
  have hr := ((ContMDiffMap.continuous_restrict (U' j)).comp
    (continuous_toContMDiffMap (n := n) e U hU hcover)).comp
      (continuous_subtypeVal (p := fun s : Cₛ^n⟮I; F, V⟯ ↦ ∀ x, ⟨x, s x⟩ ∈ O))
  have hσ := hr.codRestrict_manifoldWeakWhitney N fun s (x : U' j) ↦
      by simp only [Function.comp_apply, ContMDiffMap.restrict_apply, toContMDiffMap_apply]
         exact ⟨s.property x, hU' j x.property⟩
  -- The fibre maps read in the frame `e' j`.
  have hG₀ := contMDiff_fiberwiseMap_coord Φ hΦ (e' j) N fun _ hv ↦ hv
  let G : P → C^n⟮I.prod 𝓘(𝕜, F), N; 𝓘(𝕜, F'), F'⟯ := fun p ↦
    ⟨fun v ↦ (e' j (TotalSpace.mk' F' (v : TotalSpace F V).proj
      (Φ p (v : TotalSpace F V).proj (v : TotalSpace F V).snd))).2,
      hG₀.comp (contMDiff_const.prodMk contMDiff_id)⟩
  have hG : Continuous G := ContMDiff.continuous_manifoldWeakWhitney hG₀
  convert ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp
    ((hG.comp continuous_fst).prodMk (hσ.comp continuous_snd)) using 1
  funext q
  ext x
  simp only [Function.comp_apply, ContMDiffMap.comp_apply,
    Bundle.Trivialization.frameCoordinates_apply, fiberwiseMap_apply]
  exact congrArg (fun v : TotalSpace F V ↦ (e' j ⟨v.proj, Φ q.1 v.proj v.snd⟩).2)
    (by simp : (⟨x, q.2.val x⟩ : TotalSpace F V) = _)

end FiberwiseMap

end ContMDiffSection

end
