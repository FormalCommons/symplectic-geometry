/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Topology.FiberBundle.Trivialization

/-!
# Maps of locally trivial maps glued from fibrewise maps in charts

Let `proj : M → B` and `proj' : M' → B` be maps with trivializations `e i` and `e' i`, indexed
by `ι`, and let `V i` be sets covering `B` with `V i` in the base sets of `e i` and `e' i`. A
family of bijections `k i b : F ≃ F'` between the model fibres, for `b ∈ V i`, that agree under the
coordinate changes of `e` and `e'` on the overlaps `V i ∩ V j`, glues to a map `M → M'` over `B`
which reads `(b, v) ↦ (b, k i b v)` through `e i` and `e' i` over `V i`
(`Bundle.Trivialization.glueFiberwise`). The family `(k i b)⁻¹` glues to its inverse.

When `M`, `M'`, `B`, `F` and `F'` are manifolds, the `V i` are open, the trivializations and
their inverses are `C^n`, and the maps `(b, v) ↦ k i b v` and `(b, v) ↦ (k i b)⁻¹ v` are `C^n` on
`V i × F` and `V i × F'`, the glued map is a `C^n` diffeomorphism over `B`
(`Bundle.Trivialization.glueFiberwiseDiffeomorph`). This is how two bundles with the same
clutching data, up to a change of charts, are shown to be isomorphic over the base when the
fibrewise maps do not lie in a Lie group, so that Tau Ceti's `TauCeti.diffeomorphOfCohomologous`
does not apply. The charts of a `C^n` atlas (`TauCeti.MapFiber.Atlas.IsContMDiff`) satisfy the
smoothness hypotheses.

## Main definitions

* `Bundle.Trivialization.glueFiberwise`: the map glued from the fibrewise maps `k i`.
* `Bundle.Trivialization.glueFiberwiseDiffeomorph`: the same map, as a `C^n` diffeomorphism.

## Main results

* `Bundle.Trivialization.symm_apply_mk_coordChange`: reading a coordinate change back through the
  second trivialization gives the inverse of the first.
* `Bundle.Trivialization.glueFiberwise_of_mem`: over `V i`, the glued map is read through `e i`
  and `e' i` by `k i`, whichever index the definition chose.
* `Bundle.Trivialization.proj_glueFiberwise`: the glued map lies over `B`.
* `Bundle.Trivialization.glueFiberwise_glueFiberwise_symm`: the family of inverses glues to the
  inverse map.
* `Bundle.Trivialization.contMDiff_glueFiberwise`: the glued map is `C^n`.

## Implementation notes

The smoothness proof follows Tau Ceti's `TauCeti.contMDiff_of_localTriv_snd`
(`TauCeti.Geometry.Manifold.FiberBundle.GroupCocycle`): near a point over `V i`, the glued map is
`e i`, then `(b, v) ↦ (b, k i b v)`, then the inverse of `e' i`.

## References

* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §2 (equivalence
  of coordinate bundles through maps of the coordinate functions).
-/

public section

open Set Filter
open scoped Manifold Topology ContDiff

namespace Bundle.Trivialization

section Topology

variable {B F M : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace M]
  {proj : M → B}

/-- Reading back through `e₂` the coordinate change from `e₁` to `e₂` gives the inverse of `e₁`:
over a point `b` of both base sets, `e₂⁻¹ (b, e₁.coordChange e₂ b v) = e₁⁻¹ (b, v)`. -/
theorem symm_apply_mk_coordChange (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) (v : F) :
    e₂.toOpenPartialHomeomorph.symm (b, e₁.coordChange e₂ b v) =
      e₁.toOpenPartialHomeomorph.symm (b, v) := by
  rw [e₁.mk_coordChange e₂ h₁ h₂]
  exact e₂.toOpenPartialHomeomorph.left_inv (e₂.mem_source.2 (by rwa [e₁.proj_symm_apply' h₁]))

variable {F' M' : Type*} [TopologicalSpace F'] [TopologicalSpace M'] {proj' : M' → B}
  {ι : Type*} {V : ι → Set B} (e : ι → Trivialization F proj) (e' : ι → Trivialization F' proj')
  (k : ι → B → F ≃ F') (hV : ∀ b, ∃ i, b ∈ V i)

/-- The map `M → M'` glued from fibrewise maps `k i b : F ≃ F'` in the trivializations `e i` and
`e' i`: a point `p` over `b` is sent to `(e' i)⁻¹ (b, k i b (e i p).2)` for an index `i` with
`b ∈ V i`, chosen by `hV`. When the `k i` agree under the coordinate changes of `e` and `e'`, it
does not depend on the choice (`Bundle.Trivialization.glueFiberwise_of_mem`). -/
noncomputable def glueFiberwise (p : M) : M' :=
  (e' (hV (proj p)).choose).toOpenPartialHomeomorph.symm
    (proj p, k (hV (proj p)).choose (proj p) (e (hV (proj p)).choose p).2)

variable {e e' k}
variable (hVe : ∀ i, V i ⊆ (e i).baseSet) (hVe' : ∀ i, V i ⊆ (e' i).baseSet)
  (hk : ∀ i j, ∀ b ∈ V i ∩ V j, ∀ v,
    (e' i).coordChange (e' j) b (k i b v) = k j b ((e i).coordChange (e j) b v))

include hVe hVe' hk in
/-- **The glued map in charts.** If the fibrewise maps `k i` agree under the coordinate changes,
then over every `V i` the glued map reads `(b, v) ↦ (b, k i b v)` through `e i` and `e' i`. -/
theorem glueFiberwise_of_mem {i : ι} {p : M} (hp : proj p ∈ V i) :
    glueFiberwise e e' k hV p = 
      (e' i).toOpenPartialHomeomorph.symm (proj p, k i (proj p) (e i p).2) := by
  set j := (hV (proj p)).choose
  have hj : proj p ∈ V j := (hV (proj p)).choose_spec
  rw [glueFiberwise, ← (e j).coordChange_apply_snd (e i) (hVe j hj),
    ← hk j i (proj p) ⟨hj, hp⟩, symm_apply_mk_coordChange _ _ (hVe' j hj) (hVe' i hp)]

include hVe' in
/-- The glued map lies over `B`. -/
theorem proj_glueFiberwise (p : M) : proj' (glueFiberwise e e' k hV p) = proj p :=
  (e' _).proj_symm_apply' (hVe' _ (hV (proj p)).choose_spec)

include hVe hVe' hk in
/-- Over `V i`, the chart `e' i` of the image of `p` under the glued map is
`(proj p, k i (proj p) v)`, where `v` is the fibre coordinate of `p` in `e i`. -/
theorem apply_glueFiberwise {i : ι} {p : M} (hp : proj p ∈ V i) :
    e' i (glueFiberwise e e' k hV p) = (proj p, k i (proj p) (e i p).2) := by
  rw [glueFiberwise_of_mem hV hVe hVe' hk hp, (e' i).apply_symm_apply' (hVe' i hp)]

include hVe hVe' hk in
/-- Over `b ∈ V i`, the glued map sends the point `(e i)⁻¹ (b, v)` to
`(e' i)⁻¹ (b, k i b v)`. -/
theorem glueFiberwise_symm_apply_mk {i : ι} {b : B} (hb : b ∈ V i) (v : F) :
    glueFiberwise e e' k hV ((e i).toOpenPartialHomeomorph.symm (b, v)) =
      (e' i).toOpenPartialHomeomorph.symm (b, k i b v) := by
  have hp : proj ((e i).toOpenPartialHomeomorph.symm (b, v)) = b :=
    (e i).proj_symm_apply' (hVe i hb)
  rw [glueFiberwise_of_mem hV hVe hVe' hk (hp ▸ hb), hp, (e i).apply_symm_apply' (hVe i hb)]

include hk in
/-- The inverses `(k i b)⁻¹` agree under the coordinate changes of `e'` and `e` when the `k i b`
agree under those of `e` and `e'`. -/
theorem coordChange_symm_apply_eq_symm_apply_coordChange (i j : ι) (b : B) (hb : b ∈ V i ∩ V j)
    (v : F') :
    (e i).coordChange (e j) b ((k i b).symm v) =
      (k j b).symm ((e' i).coordChange (e' j) b v) := by
  rw [Equiv.eq_symm_apply, ← hk i j b hb, Equiv.apply_symm_apply]

include hVe hVe' hk in
/-- **The inverse of the glued map.** The family of inverses `(k i b)⁻¹`, in the trivializations
`e' i` and `e i`, glues to a left inverse of the map glued from `k`. -/
theorem glueFiberwise_glueFiberwise_symm (p : M) :
    glueFiberwise e' e (fun i b ↦ (k i b).symm) hV (glueFiberwise e e' k hV p) = p := by
  obtain ⟨i, hi⟩ := hV (proj p)
  have hp := proj_glueFiberwise (e := e) (k := k) hV hVe' p
  rw [glueFiberwise_of_mem hV hVe' hVe (coordChange_symm_apply_eq_symm_apply_coordChange hk)
      (hp ▸ hi), apply_glueFiberwise hV hVe hVe' hk hi, hp, Equiv.symm_apply_apply,
    (e i).symm_apply_mk_proj ((e i).mem_source.2 (hVe i hi))]

end Topology

section Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {EF' : Type*} [NormedAddCommGroup EF'] [NormedSpace 𝕜 EF'] {HF' : Type*}
  [TopologicalSpace HF'] {IF' : ModelWithCorners 𝕜 EF' HF'} {F' : Type*} [TopologicalSpace F']
  [ChartedSpace HF' F']
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {EM' : Type*} [NormedAddCommGroup EM'] [NormedSpace 𝕜 EM'] {HM' : Type*}
  [TopologicalSpace HM'] {IM' : ModelWithCorners 𝕜 EM' HM'} {M' : Type*} [TopologicalSpace M']
  [ChartedSpace HM' M']
  {proj : M → B} {proj' : M' → B} {ι : Type*} {V : ι → Set B} {e : ι → Trivialization F proj}
  {e' : ι → Trivialization F' proj'} {k : ι → B → F ≃ F'} (hV : ∀ b, ∃ i, b ∈ V i)
  (hVo : ∀ i, IsOpen (V i)) (hVe : ∀ i, V i ⊆ (e i).baseSet)
  (hVe' : ∀ i, V i ⊆ (e' i).baseSet)
  (hk : ∀ i j, ∀ b ∈ V i ∩ V j, ∀ v,
    (e' i).coordChange (e' j) b (k i b v) = k j b ((e i).coordChange (e j) b v))

include hVo hVe hVe' hk in
/-- **The glued map is smooth.** If the `V i` are open, the trivializations `e i` are `C^n` on
their sources, the inverses of the `e' i` are `C^n` on their targets, and each
`(b, v) ↦ k i b v` is `C^n` on `V i × F`, then the map glued from the `k i` is `C^n`. -/
theorem contMDiff_glueFiberwise (he : ∀ i, ContMDiffOn IM (IB.prod IF) n (e i) (e i).source)
    (he' : ∀ i, ContMDiffOn (IB.prod IF') IM' n (e' i).toOpenPartialHomeomorph.symm
      (e' i).target)
    (hks : ∀ i, ContMDiffOn (IB.prod IF) IF' n (fun q : B × F ↦ k i q.1 q.2) (V i ×ˢ univ)) :
    ContMDiff IM IM' n (glueFiberwise e e' k hV) := by
  intro p
  obtain ⟨i, hi⟩ := hV (proj p)
  -- Over `V i`, the glued map is `e i`, then `(b, v) ↦ (b, k i b v)`, then `(e' i)⁻¹`.
  have hW : IsOpen ((e i).source ∩ proj ⁻¹' V i) :=
    (e i).continuousOn_proj.isOpen_inter_preimage (e i).open_source (hVo i)
  have hpW : p ∈ (e i).source ∩ proj ⁻¹' V i := ⟨(e i).mem_source.2 (hVe i hi), hi⟩
  have hmaps : MapsTo (e i) ((e i).source ∩ proj ⁻¹' V i) (V i ×ˢ univ) := fun x hx ↦
    ⟨by rw [(e i).coe_fst hx.1]; exact hx.2, mem_univ _⟩
  have hg : ContMDiffOn IM IM' n
      (fun x ↦ (e' i).toOpenPartialHomeomorph.symm ((e i x).1, k i (e i x).1 (e i x).2))
      ((e i).source ∩ proj ⁻¹' V i) :=
    (he' i).comp ((contMDiffOn_fst.prodMk (hks i)).comp ((he i).mono inter_subset_left) hmaps)
      fun x hx ↦ (e' i).mem_target.2 (hVe' i (hmaps hx).1)
  refine (hg.contMDiffAt (hW.mem_nhds hpW)).congr_of_eventuallyEq
    (eventually_of_mem (hW.mem_nhds hpW) fun x hx ↦ ?_)
  dsimp only
  rw [glueFiberwise_of_mem hV hVe hVe' hk hx.2, (e i).coe_fst hx.1]

include hVo hVe hVe' hk in
/-- **Fibrewise diffeomorphisms in charts glue to a diffeomorphism over the base.** Let the open
sets `V i` cover `B`, with `V i` in the base sets of trivializations `e i` of `proj : M → B` and
`e' i` of `proj' : M' → B` that are `C^n` with `C^n` inverses. Let `k i b : F ≃ F'` agree under the
coordinate changes of `e` and `e'` on the overlaps, with `(b, v) ↦ k i b v` and
`(b, v) ↦ (k i b)⁻¹ v` of class `C^n` on `V i × F` and `V i × F'`. Then the map that reads
`(b, v) ↦ (b, k i b v)` through `e i` and `e' i` over each `V i` is a `C^n` diffeomorphism
`M ≃ M'` over `B` (`Bundle.Trivialization.proj_glueFiberwise`,
`Bundle.Trivialization.glueFiberwise_of_mem`). -/
noncomputable def glueFiberwiseDiffeomorph
    (he : ∀ i, ContMDiffOn IM (IB.prod IF) n (e i) (e i).source)
    (he_symm : ∀ i, ContMDiffOn (IB.prod IF) IM n (e i).toOpenPartialHomeomorph.symm
      (e i).target)
    (he' : ∀ i, ContMDiffOn IM' (IB.prod IF') n (e' i) (e' i).source)
    (he'_symm : ∀ i, ContMDiffOn (IB.prod IF') IM' n (e' i).toOpenPartialHomeomorph.symm
      (e' i).target)
    (hks : ∀ i, ContMDiffOn (IB.prod IF) IF' n (fun q : B × F ↦ k i q.1 q.2) (V i ×ˢ univ))
    (hks_symm : ∀ i,
      ContMDiffOn (IB.prod IF') IF n (fun q : B × F' ↦ (k i q.1).symm q.2) (V i ×ˢ univ)) :
    M ≃ₘ^n⟮IM, IM'⟯ M' where
  toFun := glueFiberwise e e' k hV
  invFun := glueFiberwise e' e (fun i b ↦ (k i b).symm) hV
  left_inv := glueFiberwise_glueFiberwise_symm hV hVe hVe' hk
  right_inv := glueFiberwise_glueFiberwise_symm (k := fun i b ↦ (k i b).symm) hV hVe' hVe
    (coordChange_symm_apply_eq_symm_apply_coordChange hk)
  contMDiff_toFun := contMDiff_glueFiberwise hV hVo hVe hVe' hk he he'_symm hks
  contMDiff_invFun := contMDiff_glueFiberwise hV hVo hVe' hVe
    (coordChange_symm_apply_eq_symm_apply_coordChange hk) he' he_symm hks_symm

variable {hV hVo hVe hVe' hk}
variable {he : ∀ i, ContMDiffOn IM (IB.prod IF) n (e i) (e i).source}
  {he_symm : ∀ i, ContMDiffOn (IB.prod IF) IM n (e i).toOpenPartialHomeomorph.symm (e i).target}
  {he' : ∀ i, ContMDiffOn IM' (IB.prod IF') n (e' i) (e' i).source}
  {he'_symm : ∀ i, ContMDiffOn (IB.prod IF') IM' n (e' i).toOpenPartialHomeomorph.symm
    (e' i).target}
  {hks : ∀ i, ContMDiffOn (IB.prod IF) IF' n (fun q : B × F ↦ k i q.1 q.2) (V i ×ˢ univ)}
  {hks_symm : ∀ i,
    ContMDiffOn (IB.prod IF') IF n (fun q : B × F' ↦ (k i q.1).symm q.2) (V i ×ˢ univ)}

/-- The glued diffeomorphism is the glued map. -/
@[simp]
theorem coe_glueFiberwiseDiffeomorph :
    ⇑(glueFiberwiseDiffeomorph hV hVo hVe hVe' hk he he_symm he' he'_symm hks hks_symm) =
      glueFiberwise e e' k hV :=
  (rfl)

/-- The inverse of the glued diffeomorphism is the map glued from the inverses `(k i b)⁻¹`. -/
@[simp]
theorem coe_glueFiberwiseDiffeomorph_symm :
    ⇑(glueFiberwiseDiffeomorph hV hVo hVe hVe' hk he he_symm he' he'_symm hks hks_symm).symm =
      glueFiberwise e' e (fun i b ↦ (k i b).symm) hV :=
  (rfl)

end Manifold

end Bundle.Trivialization

end
