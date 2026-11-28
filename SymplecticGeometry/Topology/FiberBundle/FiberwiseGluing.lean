/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.FiberBundle.Trivialization
import SymplecticGeometry.Topology.FiberBundle.Trivialization

/-!
# Maps of locally trivial maps glued from fibrewise maps in charts

Let `proj : M → B` and `proj' : M' → B` be maps with trivializations `e i` and `e' i`, indexed
by `ι`, and let `V i` be sets covering `B` with `V i` in the base sets of `e i` and `e' i`. A
family of bijections `k i b : F ≃ F'` between the model fibres, for `b ∈ V i`, that agree under the
coordinate changes of `e` and `e'` on the overlaps `V i ∩ V j`, glues to a map `M → M'` over `B`
which reads `(b, v) ↦ (b, k i b v)` through `e i` and `e' i` over `V i`
(`Bundle.Trivialization.glueFiberwise`). The family `(k i b)⁻¹` glues to its inverse.
`SymplecticGeometry.Geometry.Manifold.FiberBundle.FiberwiseGluing` shows that the glued map is a
diffeomorphism when the data are smooth.

## Main definitions

* `Bundle.Trivialization.glueFiberwise`: the map glued from the fibrewise maps `k i`.

## Main results

* `Bundle.Trivialization.glueFiberwise_of_mem`: over `V i`, the glued map is read through `e i`
  and `e' i` by `k i`, whichever index the definition chose.
* `Bundle.Trivialization.proj_glueFiberwise`: the glued map lies over `B`.
* `Bundle.Trivialization.glueFiberwise_glueFiberwise_symm`: the family of inverses glues to the
  inverse map.

## References

* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §2 (equivalence
  of coordinate bundles through maps of the coordinate functions).
-/

public section

namespace Bundle.Trivialization

variable {B F M : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace M]
  {proj : M → B}

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

/-- The glued map, by its definition, with the index chosen by `hV`. -/
theorem glueFiberwise_def (p : M) :
    glueFiberwise e e' k hV p = (e' (hV (proj p)).choose).toOpenPartialHomeomorph.symm
      (proj p, k (hV (proj p)).choose (proj p) (e (hV (proj p)).choose p).2) :=
  (rfl)

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
  rw [glueFiberwise_def, ← (e j).coordChange_apply_snd (e i) (hVe j hj),
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


end Bundle.Trivialization

end
