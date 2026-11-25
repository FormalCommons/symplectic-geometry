/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Submersion.ParallelTransport.Smooth
public import TauCeti.Topology.FiberBundle.MapFiber
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Opens

/-!
# Local trivializations by parallel transport

Let `D` be a `C^n` Ehresmann connection, `1 ≤ n`, on a proper `C^(n+1)` map `f : P → B` of
finite-dimensional boundaryless Hausdorff manifolds. This file builds trivializations of `f` by
parallel transport along a family of curves that join a fixed point `b₀` to the points of an
open set `U`.

First, transport along the curves `u ↦ Γ (a, u)` of a family `Γ : N × ℝ → B` that is `C^(n+1)`
on `U ×ˢ univ`, for an open set `U` of a manifold `N`, is `C^n` as a function of the pair
`(a, x)`, on the set of pairs with `a ∈ U` and `x` over the starting point `Γ (a, s)`
(`TauCeti.IsEhresmannConnection.contMDiffOn_parallelTransport_param`). This follows from the
local statement `TauCeti.IsEhresmannConnection.exists_contMDiff_parallelTransport_param`, applied
with the open set `U` as the manifold of parameters: near each point, the function agrees on that
set with a `C^n` map, so no glueing is needed.

Then, for `Γ : B × ℝ → B` that is `C^(n+1)` on `U ×ˢ univ`, with `Γ (b, 0) = b₀` and
`Γ (b, 1) = b` for `b ∈ U`, transport along `u ↦ Γ (b, u)` from `0` to `1` carries the fibre over
`b₀` onto the fibre over `b`, with inverse the transport from `1` to `0`
(`TauCeti.IsEhresmannConnection.invOn_parallelTransport`). Together these maps form a
trivialization of `f` over `U` whose fibre is the fibre `TauCeti.MapFiber f b₀` of `f` over `b₀`,
with the subspace topology (`TauCeti.IsEhresmannConnection.parallelTransportTrivialization`). The
fibre has no manifold structure in general, so the smoothness of the trivialization and of its
inverse is stated through the inclusion of the fibre into `P`: the trivialization, followed by
that inclusion, is `C^n` on its source
(`TauCeti.IsEhresmannConnection.contMDiffOn_parallelTransportTrivialization`), and its inverse is
the restriction of a map `B × P → P` that is `C^n` on `U ×ˢ (f ⁻¹' {b₀})`
(`TauCeti.IsEhresmannConnection.contMDiffOn_parallelTransportTrivialization_symm`). For a
manifold structure on the fibre that makes the inclusion a `C^n` embedding, such as the
regular-fibre atlas of a submersion, these two statements give the fields of Tau Ceti's
`TauCeti.MapFiber.Atlas.IsContMDiff` for the trivialization.

A trivialization needs a value at every point of `P`, also over points outside `U`, so its fibre
is assumed nonempty. This is no loss: if the fibre over `b₀` is empty and `P` is not, `f` has no
trivialization with that fibre at all.

## Main results

* `TauCeti.IsEhresmannConnection.contMDiffOn_parallelTransport_param`: transport along a family of
  curves is `C^n` in the parameter and the point.
* `TauCeti.IsEhresmannConnection.parallelTransportTrivialization`: the trivialization of `f` over
  `U` by transport along a family of curves from `b₀`, with inverse
  `TauCeti.IsEhresmannConnection.parallelTransportTrivialization_symm_apply`.
* `TauCeti.IsEhresmannConnection.contMDiffOn_parallelTransportTrivialization`,
  `TauCeti.IsEhresmannConnection.contMDiffOn_parallelTransportTrivialization_symm`: it is `C^n`,
  with a `C^n` inverse.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.1
  (Exercise 6.1.1).
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §9.
-/

public section

noncomputable section

open Function Bundle Set Filter TopologicalSpace
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace IsEhresmannConnection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P] [I.Boundaryless]
  [T2Space P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {B : Type*} [TopologicalSpace B] [ChartedSpace G B] [IsManifold J ∞ B] [J.Boundaryless]
  [T2Space B]
  {n : ℕ∞} {f : P → B} {D : Π x : P, Submodule ℝ (TangentSpace I x)}
  (hD : IsEhresmannConnection I J n f D)

section Param

variable {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N] [IN.Boundaryless]
  [T2Space N]

include hD in
/-- Near a parameter `a₀ ∈ U`, transport along the curves of `Γ` is the restriction of a map
`N × P → P` that is `C^n` on `U ×ˢ univ`. -/
private theorem exists_contMDiffOn_parallelTransport_param (hn : 1 ≤ n)
    (hf : ContMDiff I J (n + 1) f) (hfp : IsProperMap f) {U : Set N} (hU : IsOpen U)
    {Γ : N × ℝ → B} (hΓ : ContMDiffOn (IN.prod 𝓘(ℝ, ℝ)) J (n + 1) Γ (U ×ˢ univ)) (s t : ℝ)
    {a₀ : N} (ha₀ : a₀ ∈ U) :
    ∃ Φ : N × P → P, ContMDiffOn (IN.prod I) I n Φ (U ×ˢ univ) ∧ ∀ᶠ a in 𝓝 a₀, ∀ x,
      f x = Γ (a, s) → Φ (a, x) = hD.parallelTransport (fun u ↦ Γ (a, u)) s t x := by
  classical
  let W : Opens N := ⟨U, hU⟩
  -- The family read on the open set `W`, as a manifold.
  have hΓW : ContMDiff (IN.prod 𝓘(ℝ, ℝ)) J (n + 1) (fun p : W × ℝ ↦ Γ (p.1, p.2)) :=
    hΓ.comp_contMDiff ((contMDiff_subtypeVal.comp contMDiff_fst).prodMk contMDiff_snd)
      fun p ↦ ⟨p.1.property, mem_univ _⟩
  obtain ⟨V, hV, Ψ, hΨ, hΨeq⟩ :=
    hD.exists_contMDiff_parallelTransport_param hn hf hfp hΓW s t ⟨a₀, ha₀⟩
  refine ⟨fun p ↦ if h : p.1 ∈ U then Ψ (⟨p.1, h⟩, p.2) else p.2,
    hΨ.contMDiffOn_opens_prod_of_eq (U := W) fun a ha x ↦ dite_eq_left ha, ?_⟩
  filter_upwards [hU.isOpenEmbedding_subtypeVal.image_mem_nhds.2 hV] with a ⟨c, hc, hca⟩ x hx
  subst hca
  simp only [dite_eq_left c.property]
  exact hΨeq c hc hx

include hD in
/-- **Parallel transport is smooth in a family of curves.** Let `D` be a `C^n` Ehresmann
connection, `1 ≤ n`, on a proper `C^(n+1)` map `f : P → B` of finite-dimensional boundaryless
Hausdorff manifolds, `U` an open set of a manifold `N` of the same kind, and `Γ : N × ℝ → B` a
family of curves that is `C^(n+1)` on `U ×ˢ univ`. The map `(a, x) ↦` transport of `x` along
`u ↦ Γ (a, u)` from `s` to `t` is `C^n` on the set of pairs with `a ∈ U` and `f x = Γ (a, s)`. -/
theorem contMDiffOn_parallelTransport_param (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f)
    (hfp : IsProperMap f) {U : Set N} (hU : IsOpen U) {Γ : N × ℝ → B}
    (hΓ : ContMDiffOn (IN.prod 𝓘(ℝ, ℝ)) J (n + 1) Γ (U ×ˢ univ)) (s t : ℝ) :
    ContMDiffOn (IN.prod I) I n (fun p : N × P ↦ hD.parallelTransport (fun u ↦ Γ (p.1, u)) s t p.2)
      {p | p.1 ∈ U ∧ f p.2 = Γ (p.1, s)} := by
  rintro ⟨a₀, x₀⟩ ⟨ha₀, hx₀⟩
  obtain ⟨Φ, hΦ, hΦeq⟩ := hD.exists_contMDiffOn_parallelTransport_param hn hf hfp hU hΓ s t ha₀
  have hev : ∀ᶠ p : N × P in 𝓝 (a₀, x₀), ∀ x, f x = Γ (p.1, s) →
      Φ (p.1, x) = hD.parallelTransport (fun u ↦ Γ (p.1, u)) s t x :=
    (continuous_fst.tendsto (a₀, x₀)).eventually hΦeq
  refine ((hΦ.contMDiffAt (prod_mem_nhds (hU.mem_nhds ha₀) univ_mem)).contMDiffWithinAt
    ).congr_of_eventuallyEq ?_ (hev.self_of_nhds x₀ hx₀).symm
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with p hp hpS
  exact (hp p.2 hpS.2).symm

end Param

section Trivialization

variable {b₀ : B} {U : Set B} {Γ : B × ℝ → B}

include hD in
/-- Transport along `u ↦ Γ (f x, u)` from `1` to `0` takes a point `x` over `U` into the fibre
over `b₀`. -/
private theorem apply_parallelTransport_one_zero (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f)
    (hfp : IsProperMap f) (hΓ : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) J (n + 1) Γ (U ×ˢ univ))
    (hΓ₀ : ∀ b ∈ U, Γ (b, 0) = b₀) (hΓ₁ : ∀ b ∈ U, Γ (b, 1) = b) {x : P} (hx : f x ∈ U) :
    f (hD.parallelTransport (fun u ↦ Γ (f x, u)) 1 0 x) = b₀ := by
  have h := hD.parallelTransport_mem_preimage hn hf hfp
    (γ := fun u ↦ Γ (f x, u))
    (hΓ.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) fun _ ↦ ⟨hx, mem_univ _⟩)
    (hΓ₁ _ hx).symm 0
  rwa [hΓ₀ _ hx] at h

include hD in
/-- Transport along `u ↦ Γ (b, u)` from `0` to `1` takes a point `v` of the fibre over `b₀` into
the fibre over `b ∈ U`. -/
private theorem apply_parallelTransport_zero_one (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f)
    (hfp : IsProperMap f) (hΓ : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) J (n + 1) Γ (U ×ˢ univ))
    (hΓ₀ : ∀ b ∈ U, Γ (b, 0) = b₀) (hΓ₁ : ∀ b ∈ U, Γ (b, 1) = b) {b : B} (hb : b ∈ U) {v : P}
    (hv : f v = b₀) : f (hD.parallelTransport (fun u ↦ Γ (b, u)) 0 1 v) = b := by
  have h := hD.parallelTransport_mem_preimage hn hf hfp
    (γ := fun u ↦ Γ (b, u))
    (hΓ.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) fun _ ↦ ⟨hb, mem_univ _⟩)
    (hv.trans (hΓ₀ _ hb).symm) 1
  rwa [hΓ₁ _ hb] at h

variable [Nonempty (MapFiber f b₀)]

open Classical in
/-- **The trivialization by parallel transport along a family of curves.** Let `D` be a `C^n`
Ehresmann connection, `1 ≤ n`, on a proper `C^(n+1)` map `f : P → B` of finite-dimensional
boundaryless Hausdorff manifolds, `U` an open set of `B`, and `Γ : B × ℝ → B` a family of curves,
`C^(n+1)` on `U ×ˢ univ`, from `Γ (b, 0) = b₀` to `Γ (b, 1) = b` for each `b ∈ U`. The
trivialization of `f` over `U` with fibre `TauCeti.MapFiber f b₀` sends a point `x` over `U` to
`f x` and the transport of `x` along `u ↦ Γ (f x, u)` from `1` to `0`; its inverse sends `(b, v)`
to the transport of `v` along `u ↦ Γ (b, u)` from `0` to `1`.

Points of `P` outside `f ⁻¹' U` are sent to an arbitrary point of the fibre, which is assumed
nonempty. -/
def parallelTransportTrivialization (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f)
    (hfp : IsProperMap f) (hU : IsOpen U)
    (hΓ : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) J (n + 1) Γ (U ×ˢ univ))
    (hΓ₀ : ∀ b ∈ U, Γ (b, 0) = b₀) (hΓ₁ : ∀ b ∈ U, Γ (b, 1) = b) :
    Trivialization (MapFiber f b₀) f where
  toFun x := (f x, if hx : f x ∈ U then
    ⟨hD.parallelTransport (fun u ↦ Γ (f x, u)) 1 0 x,
      hD.apply_parallelTransport_one_zero hn hf hfp hΓ hΓ₀ hΓ₁ hx⟩
    else Classical.arbitrary _)
  invFun p := hD.parallelTransport (fun u ↦ Γ (p.1, u)) 0 1 p.2
  source := f ⁻¹' U
  target := U ×ˢ univ
  map_source' _ hx := ⟨hx, mem_univ _⟩
  map_target' p hp := by
    rw [mem_preimage, hD.apply_parallelTransport_zero_one hn hf hfp hΓ hΓ₀ hΓ₁ hp.1
      p.2.property]
    exact hp.1
  left_inv' x hx := by
    have hγ : ContMDiff 𝓘(ℝ, ℝ) J (n + 1) (fun u ↦ Γ (f x, u)) :=
      hΓ.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) fun _ ↦ ⟨hx, mem_univ _⟩
    simp only [dite_eq_left (show f x ∈ U from hx)]
    exact (hD.invOn_parallelTransport hn hf hfp hγ 1 0).1 (hΓ₁ _ hx).symm
  right_inv' := by
    rintro ⟨b, v⟩ ⟨hb, -⟩
    have hγ : ContMDiff 𝓘(ℝ, ℝ) J (n + 1) (fun u ↦ Γ (b, u)) :=
      hΓ.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) fun _ ↦ ⟨hb, mem_univ _⟩
    have hfy : f (hD.parallelTransport (fun u ↦ Γ (b, u)) 0 1 v) = b :=
      hD.apply_parallelTransport_zero_one hn hf hfp hΓ hΓ₀ hΓ₁ hb v.property
    refine Prod.ext hfy (Subtype.ext ?_)
    simp only [hfy, show b ∈ U from hb, ↓reduceDIte]
    exact (hD.invOn_parallelTransport hn hf hfp hγ 0 1).1 (v.property.trans (hΓ₀ _ hb).symm)
  open_source := hU.preimage hf.continuous
  open_target := hU.prod isOpen_univ
  continuousOn_toFun := by
    refine hf.continuous.continuousOn.prodMk ?_
    refine (Topology.IsInducing.continuousOn_iff (g := (Subtype.val : MapFiber f b₀ → P))
      Topology.IsEmbedding.subtypeVal.isInducing).2 ?_
    refine ((hD.contMDiffOn_parallelTransport_param hn hf hfp hU hΓ 1 0).continuousOn.comp
      (hf.continuous.prodMk continuous_id).continuousOn fun x hx ↦ ⟨hx, (hΓ₁ _ hx).symm⟩).congr
      fun x hx ↦ ?_
    simp only [comp_apply, id_eq, dite_eq_left (show f x ∈ U from hx)]
  continuousOn_invFun :=
    (hD.contMDiffOn_parallelTransport_param hn hf hfp hU hΓ 0 1).continuousOn.comp
      (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd)).continuousOn
      fun p hp ↦ ⟨hp.1, p.2.property.trans (hΓ₀ _ hp.1).symm⟩
  baseSet := U
  open_baseSet := hU
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

variable (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f) (hfp : IsProperMap f) (hU : IsOpen U)
  (hΓ : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) J (n + 1) Γ (U ×ˢ univ))
  (hΓ₀ : ∀ b ∈ U, Γ (b, 0) = b₀) (hΓ₁ : ∀ b ∈ U, Γ (b, 1) = b)

@[simp]
theorem parallelTransportTrivialization_baseSet :
    (hD.parallelTransportTrivialization hn hf hfp hU hΓ hΓ₀ hΓ₁).baseSet = U :=
  (rfl)

@[simp]
theorem parallelTransportTrivialization_apply_fst (x : P) :
    (hD.parallelTransportTrivialization hn hf hfp hU hΓ hΓ₀ hΓ₁ x).1 = f x :=
  (rfl)

/-- The trivialization by transport sends a point `x` over `U` to the transport of `x` along
`u ↦ Γ (f x, u)` from `1` to `0`, in the fibre over `b₀`. -/
theorem coe_parallelTransportTrivialization_apply_snd {x : P} (hx : f x ∈ U) :
    ((hD.parallelTransportTrivialization hn hf hfp hU hΓ hΓ₀ hΓ₁ x).2 : P) =
      hD.parallelTransport (fun u ↦ Γ (f x, u)) 1 0 x :=
  congrArg Subtype.val (dite_eq_left hx)

/-- The inverse of the trivialization by transport sends `(b, v)` to the transport of `v` along
`u ↦ Γ (b, u)` from `0` to `1`. -/
@[simp]
theorem parallelTransportTrivialization_symm_apply (p : B × MapFiber f b₀) :
    (hD.parallelTransportTrivialization hn hf hfp hU hΓ hΓ₀ hΓ₁).toOpenPartialHomeomorph.symm p =
      hD.parallelTransport (fun u ↦ Γ (p.1, u)) 0 1 p.2 :=
  (rfl)

/-- **The trivialization by transport is `C^n`.** Followed by the inclusion of the fibre
`TauCeti.MapFiber f b₀` into `P`, the trivialization by transport is `C^n` on its source. -/
theorem contMDiffOn_parallelTransportTrivialization :
    ContMDiffOn I (J.prod I) n
      (fun x ↦ ((hD.parallelTransportTrivialization hn hf hfp hU hΓ hΓ₀ hΓ₁ x).1,
        ((hD.parallelTransportTrivialization hn hf hfp hU hΓ hΓ₀ hΓ₁ x).2 : P)))
      (hD.parallelTransportTrivialization hn hf hfp hU hΓ hΓ₀ hΓ₁).source := by
  have hfn : ContMDiff I J n f := hf.of_le le_self_add
  have h := (hD.contMDiffOn_parallelTransport_param hn hf hfp hU hΓ 1 0).comp
    (hfn.prodMk contMDiff_id).contMDiffOn (s := f ⁻¹' U) fun x hx ↦ ⟨hx, (hΓ₁ _ hx).symm⟩
  refine (hfn.contMDiffOn.prodMk h).congr fun x hx ↦ Prod.ext rfl ?_
  exact hD.coe_parallelTransportTrivialization_apply_snd hn hf hfp hU hΓ hΓ₀ hΓ₁ hx

/-- **The inverse of the trivialization by transport is `C^n`.** The map
`(b, x) ↦` transport of `x` along `u ↦ Γ (b, u)` from `0` to `1` is `C^n` on
`U ×ˢ (f ⁻¹' {b₀})`; by `TauCeti.IsEhresmannConnection.parallelTransportTrivialization_symm_apply`,
the inverse of the trivialization by transport is its composition with the inclusion of the
fibre `TauCeti.MapFiber f b₀` into `P`. -/
theorem contMDiffOn_parallelTransportTrivialization_symm :
    ContMDiffOn (J.prod I) I n (fun p : B × P ↦ hD.parallelTransport (fun u ↦ Γ (p.1, u)) 0 1 p.2)
      ((hD.parallelTransportTrivialization hn hf hfp hU hΓ hΓ₀ hΓ₁).baseSet ×ˢ (f ⁻¹' {b₀})) :=
  (hD.contMDiffOn_parallelTransport_param hn hf hfp hU hΓ 0 1).mono fun p hp ↦
    ⟨hp.1, (hp.2 : f p.2 = b₀).trans (hΓ₀ _ hp.1).symm⟩

end Trivialization

end IsEhresmannConnection

end TauCeti

end
