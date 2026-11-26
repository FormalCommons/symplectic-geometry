/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Submersion.ParallelTransport.Basic
public import SymplecticGeometry.Topology.FiberBundle.Basic
import Mathlib.Topology.Connected.Clopen
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Opens
import SymplecticGeometry.Geometry.Manifold.FiberBundle.MapFiber

/-!
# Parallel transport as a flow, as a diffeomorphism, in families of curves and in trivializations

Let `D` be a `C^n` Ehresmann connection, `1 ≤ n`, on a proper `C^(n+1)` map `f : P → B` of
finite-dimensional boundaryless Hausdorff manifolds, and `γ` a `C^(n+1)` curve in `B`.

If a jointly `C^n` time-dependent vector field `V` on `B`, vanishing outside a compact set, has
the velocity of `γ` as its value along `γ` at the times between `s` and `t`, then parallel
transport along `γ` from `s` to `t` is, on the fibre over `γ s`, the time-dependent flow of the
horizontal lift of `V` from `s` to `t`
(`TauCeti.IsEhresmannConnection.parallelTransport_eq_timeDependentFlowOf`): the trajectories of
that flow are horizontal lifts of `γ`
(`TauCeti.IsEhresmannConnection.isHorizontalMap_timeDependentFlowOf_horizontalLiftField`), and
transport follows every such lift (`TauCeti.IsEhresmannConnection.parallelTransport_eq`).

Such a field exists for times in a closed interval that `γ` maps into the base set of one
trivialization of the tangent bundle of `B`
(`Bundle.Trivialization.exists_timeDependentField_eq_curveVelocity`), and its flow is then a
`C^n` diffeomorphism of `P` (Tau Ceti's `TauCeti.timeDependentFlowDiffeomorph`). Transport from
`s` to `t` is the composition of the transports over the pieces of a subdivision of the interval
between them (`TauCeti.IsEhresmannConnection.parallelTransport_parallelTransport`), so it is the
restriction to the fibre over `γ s` of a composition of such diffeomorphisms
(`TauCeti.IsEhresmannConnection.exists_diffeomorph_eqOn_parallelTransport`). Rather than choosing
the subdivision, the proof applies Mathlib's `PreconnectedSpace.induction₂'` to the relation
between two times that some diffeomorphism of `P` agrees with transport between them on the
fibre: it is transitive, and holds between nearby times.

For a `C^(n+1)` family `Γ : N × ℝ → B` of curves, with parameters in a finite-dimensional
boundaryless Hausdorff manifold `N`, transport along the curves `u ↦ Γ (a, u)` is, for `a` near a
given `a₀`, the restriction to the fibres of one `C^n` map `N × P → P`
(`TauCeti.IsEhresmannConnection.exists_contMDiff_parallelTransport_param`). The proof is the one
above with parameters. Near `a₀` and between two times of an interval that the curve at `a₀` maps
into the base set of one trivialization, transport is the flow of the lift of a family of fields
that depends smoothly on the parameter
(`Bundle.Trivialization.exists_timeDependentField_param_eq_curveVelocity`), and such flows are
jointly `C^n` in the parameter and the point (`TauCeti.contMDiff_timeDependentFlowOf_param`). The
relation to which `PreconnectedSpace.induction₂'` is applied now also carries a neighbourhood of
`a₀`, and its transitivity composes the maps on the intersection of the neighbourhoods. The
statement is local in the parameter, so no smooth maps need to be glued. For a family that is
`C^(n+1)` only on `U ×ˢ univ`, for an open set `U` of `N`, the same holds with a map that is
`C^n` on `U ×ˢ univ`
(`TauCeti.IsEhresmannConnection.exists_contMDiffOn_parallelTransport_param`): apply the result
above with the open set `U` as the manifold of parameters, and read the map on `N × P` with
`ContMDiff.contMDiffOn_opens_prod_of_eq`. Hence transport is `C^n` as a function of the pair
`(a, x)` on the set of pairs with `a ∈ U` and `f x = Γ (a, s)`
(`TauCeti.IsEhresmannConnection.contMDiffOn_parallelTransport_param`).

For trivializations `e e' : Bundle.Trivialization Z f` with fibre `Z`, transport is read in the
model fibre as `TauCeti.IsEhresmannConnection.parallelTransportIn`: a point `v` goes to the
second coordinate in `e'` of the transport of the point with coordinates `(γ s, v)` in `e`. When
`e` and `e'` are `C^n` with `C^n` inverses, in the form of the fields of Tau Ceti's
`TauCeti.MapFiber.Atlas.IsContMDiff`, this reading is a `C^n` diffeomorphism of `Z`, since
transport is the restriction of a diffeomorphism of `P`; for a loop and `e = e'` it is the
holonomy of the loop read in `e`.

## Main results

* `TauCeti.IsEhresmannConnection.parallelTransport_eq_timeDependentFlowOf`: transport along `γ`
  is the time-dependent flow of the horizontal lift of a field through the velocities of `γ`.
* `TauCeti.IsEhresmannConnection.exists_diffeomorph_eqOn_parallelTransport`: transport from the
  fibre over `γ s` onto the fibre over `γ t` is the restriction of a `C^n` diffeomorphism of `P`.
* `TauCeti.IsEhresmannConnection.exists_contMDiff_parallelTransport_param`: transport along the
  curves of a `C^(n+1)` family is, near each parameter, the restriction of a `C^n` map of the
  parameters and the points of `P`.
* `TauCeti.IsEhresmannConnection.contMDiffOn_parallelTransport_param`: for a family that is
  `C^(n+1)` on an open set of parameters, transport is `C^n` in the parameter and the point.
* `TauCeti.IsEhresmannConnection.parallelTransportInDiffeomorph`: transport read in two
  trivializations, as a `C^n` diffeomorphism of the model fibre, with inverse the transport back
  (`TauCeti.IsEhresmannConnection.symm_parallelTransportInDiffeomorph`).
* `TauCeti.IsEhresmannConnection.parallelTransportIn_coordChange`: a change of trivializations
  conjugates the reading by the coordinate changes.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.3.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §9.
-/

public section

noncomputable section

open Function Bundle Set Filter TauCeti.Manifold
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

/-- **Parallel transport is the flow of a lifted field.** Let `D` be a `C^n` Ehresmann
connection, `1 ≤ n`, on a proper `C^(n+1)` map `f : P → B`, `γ` a `C²` curve in `B`, and `V` a
jointly `C^n` time-dependent vector field on `B` that vanishes outside a compact set and whose
value at `γ u` at time `u` is the velocity of `γ` at `u`, for every `u ∈ Set.uIcc s t`. On the
fibre over `γ s`, parallel transport along `γ` from `s` to `t` is the time-dependent flow from `s`
to `t` of the horizontal lift of `V`. -/
theorem parallelTransport_eq_timeDependentFlowOf (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f)
    (hfp : IsProperMap f) {γ : ℝ → B} (hγ : ContMDiff 𝓘(ℝ, ℝ) J 2 γ)
    {V : ℝ → Π y : B, TangentSpace J y}
    (hV : ContMDiff (𝓘(ℝ, ℝ).prod J) J.tangent n
      (fun p : ℝ × B ↦ (⟨p.2, V p.1 p.2⟩ : TangentBundle J B)))
    {K : Set B} (hK : IsCompact K) (hV0 : ∀ u, ∀ y ∉ K, V u y = 0) {s t : ℝ}
    (hVγ : ∀ u ∈ uIcc s t, V u (γ u) = curveVelocity J γ u) :
    EqOn (hD.parallelTransport γ s t)
      (timeDependentFlowOf (fun u ↦ hD.horizontalLiftField (V u)) s t) (f ⁻¹' {γ s}) := by
  intro x hx
  rw [mem_preimage, mem_singleton_iff] at hx
  have hn' : (1 : ℕ∞ω) ≤ n := mod_cast hn
  have h2 : (2 : ℕ∞ω) ≤ n + 1 := SymplecticGeometry.two_le_add_one_of_one_le hn'
  obtain ⟨hc, hh, hγc⟩ := hD.isHorizontalMap_timeDependentFlowOf_horizontalLiftField hn hf hfp
    (hγ.mdifferentiable (by simp)) hV hK hV0 isPreconnected_uIcc hVγ left_mem_uIcc hx
  exact hD.parallelTransport_eq hn' (hf.of_le h2) hγ
    (hc.mdifferentiable (zero_lt_one.trans_le hn').ne') hh hγc (timeDependentFlowOf_self _ s x)

include hD in
/-- The local step of `TauCeti.IsEhresmannConnection.exists_diffeomorph_eqOn_parallelTransport`:
between two times of a closed interval that `γ` maps into the base set of one trivialization of
the tangent bundle of `B`, transport is the restriction of the flow of a cut-off lifted field. -/
private theorem exists_diffeomorph_eqOn_parallelTransport_of_mapsTo_baseSet (hn : 1 ≤ n)
    (hf : ContMDiff I J (n + 1) f) (hfp : IsProperMap f) {γ : ℝ → B}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) J (n + 1) γ) {a b : ℝ}
    (e : Trivialization F (π F (TangentSpace J))) [MemTrivializationAtlas e]
    (hγe : MapsTo γ (Icc a b) e.baseSet) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ∃ Ψ : P ≃ₘ^n⟮I, I⟯ P, EqOn Ψ (hD.parallelTransport γ s t) (f ⁻¹' {γ s}) := by
  have h2 : (2 : ℕ∞ω) ≤ n + 1 := SymplecticGeometry.two_le_add_one_of_one_le (mod_cast hn)
  obtain ⟨V, K, hK, hV, hV0, hVγ⟩ := e.exists_timeDependentField_eq_curveVelocity hγ hγe
  refine ⟨timeDependentFlowDiffeomorph
    (hD.isCompleteVectorField_timeDependentSuspensionField_horizontalLiftField hn hf hfp hV hK hV0)
    hn (hD.contMDiff_horizontalLiftField_family hf hV) s t, fun x hx ↦ ?_⟩
  rw [timeDependentFlowDiffeomorph_apply]
  exact (hD.parallelTransport_eq_timeDependentFlowOf hn hf hfp (hγ.of_le h2) hV hK hV0
    (fun u hu ↦ hVγ u (uIcc_subset_Icc hs ht hu)) hx).symm

include hD in
/-- **Parallel transport is the restriction of a diffeomorphism.** Let `D` be a `C^n` Ehresmann
connection, `1 ≤ n`, on a proper `C^(n+1)` map `f : P → B` of finite-dimensional boundaryless
Hausdorff manifolds, and `γ` a `C^(n+1)` curve in `B`. There is a `C^n` diffeomorphism `Ψ` of
`P` that agrees with parallel transport along `γ` from `s` to `t` on the fibre over `γ s` and maps
that fibre onto the fibre over `γ t`. For `n = ∞`, `Ψ` is smooth. -/
theorem exists_diffeomorph_eqOn_parallelTransport (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f)
    (hfp : IsProperMap f) {γ : ℝ → B} (hγ : ContMDiff 𝓘(ℝ, ℝ) J (n + 1) γ) (s t : ℝ) :
    ∃ Ψ : P ≃ₘ^n⟮I, I⟯ P, EqOn Ψ (hD.parallelTransport γ s t) (f ⁻¹' {γ s}) ∧
      Ψ '' (f ⁻¹' {γ s}) = f ⁻¹' {γ t} := by
  -- Times between which some diffeomorphism agrees with transport on the fibre.
  let R : ℝ → ℝ → Prop := fun a b ↦
    ∃ Ψ : P ≃ₘ^n⟮I, I⟯ P, EqOn Ψ (hD.parallelTransport γ a b) (f ⁻¹' {γ a})
  -- The relation is transitive: compose the diffeomorphisms, and transport.
  have htrans : IsTrans ℝ R := ⟨fun a b c ⟨Ψ₁, h₁⟩ ⟨Ψ₂, h₂⟩ ↦ ⟨Ψ₁.trans Ψ₂, fun x hx ↦ by
    rw [Diffeomorph.coe_trans, comp_apply, h₁ hx,
      h₂ (hD.parallelTransport_mem_preimage hn hf hfp hγ hx b),
      hD.parallelTransport_parallelTransport hn hf hfp hγ hx]⟩⟩
  -- It holds between nearby times: near `u`, `γ` stays in the base set of one trivialization.
  have hloc (u : ℝ) : ∀ᶠ v in 𝓝 u, R u v ∧ R v u := by
    let e := trivializationAt F (TangentSpace J) (γ u)
    obtain ⟨a, b, hu, hab, hmaps⟩ := exists_Icc_mem_subset_of_mem_nhds
      (hγ.continuous.continuousAt.eventually_mem_baseSet_trivializationAt F (TangentSpace J))
    filter_upwards [hab] with v hv
    exact ⟨hD.exists_diffeomorph_eqOn_parallelTransport_of_mapsTo_baseSet hn hf hfp hγ e hmaps
      hu hv, hD.exists_diffeomorph_eqOn_parallelTransport_of_mapsTo_baseSet hn hf hfp hγ e hmaps
      hv hu⟩
  obtain ⟨Ψ, hΨ⟩ := PreconnectedSpace.induction₂' R hloc htrans s t
  exact ⟨Ψ, hΨ, hΨ.image_eq.trans (hD.bijOn_parallelTransport hn hf hfp hγ s t).image_eq⟩

section Param

variable {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N] [IN.Boundaryless]
  [T2Space N]

include hD in
/-- The local step of `TauCeti.IsEhresmannConnection.exists_contMDiff_parallelTransport_param`:
if the curve at `a₀` of the family `Γ` maps a closed interval into the base set of one
trivialization of the tangent bundle of `B`, then near `a₀`, between two times of that interval,
transport along the curves of the family is the restriction of a `C^n` map of `N × P`. -/
private theorem exists_contMDiff_parallelTransport_param_of_mapsTo_baseSet (hn : 1 ≤ n)
    (hf : ContMDiff I J (n + 1) f) (hfp : IsProperMap f) {Γ : N × ℝ → B}
    (hΓ : ContMDiff (IN.prod 𝓘(ℝ, ℝ)) J (n + 1) Γ) {a₀ : N} {a b : ℝ}
    (e : Trivialization F (π F (TangentSpace J))) [MemTrivializationAtlas e]
    (hΓe : MapsTo (fun u ↦ Γ (a₀, u)) (Icc a b) e.baseSet) :
    ∃ U ∈ 𝓝 a₀, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∃ Ψ : N × P → P, ContMDiff (IN.prod I) I n Ψ ∧
      ∀ c ∈ U, EqOn (fun x ↦ Ψ (c, x)) (hD.parallelTransport (fun u ↦ Γ (c, u)) s t)
        (f ⁻¹' {Γ (c, s)}) := by
  have h2 : (2 : ℕ∞ω) ≤ n + 1 := SymplecticGeometry.two_le_add_one_of_one_le (mod_cast hn)
  obtain ⟨U, hU, V, K, hK, hV, hV0, hVγ⟩ :=
    e.exists_timeDependentField_param_eq_curveVelocity hΓ hΓe
  -- The fields of the family at a parameter `c`, and their horizontal lifts.
  have hVc (c : N) : ContMDiff (𝓘(ℝ, ℝ).prod J) J.tangent n
      (fun p : ℝ × B ↦ (⟨p.2, V c p.1 p.2⟩ : TangentBundle J B)) :=
    hV.comp ((contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd)
  have hX : ContMDiff ((IN.prod 𝓘(ℝ, ℝ)).prod I) I.tangent n
      (fun p : (N × ℝ) × P ↦
        (⟨p.2, hD.horizontalLiftField (V p.1.1 p.1.2) p.2⟩ : TangentBundle I P)) :=
    hD.contMDiff_horizontalLiftField_family (V := fun q : N × ℝ ↦ V q.1 q.2) hf hV
  have hflow := contMDiff_timeDependentFlowOf_param hn hX fun c ↦
    hD.isCompleteVectorField_timeDependentSuspensionField_horizontalLiftField hn hf hfp (hVc c) hK
      (hV0 c)
  refine ⟨U, hU, fun s hs t ht ↦ ⟨_, hflow.comp (f := fun p : N × P ↦ ((p.1, s, t), p.2))
    ((contMDiff_fst.prodMk contMDiff_const).prodMk contMDiff_snd), fun c hc x hx ↦ ?_⟩⟩
  have hΓc : ContMDiff 𝓘(ℝ, ℝ) J (n + 1) (fun u ↦ Γ (c, u)) :=
    hΓ.comp (contMDiff_const.prodMk contMDiff_id)
  exact (hD.parallelTransport_eq_timeDependentFlowOf hn hf hfp (hΓc.of_le h2) (hVc c) hK (hV0 c)
    (fun u hu ↦ hVγ c hc u (uIcc_subset_Icc hs ht hu)) hx).symm

include hD in
/-- **Parallel transport depends smoothly on a family of curves.** Let `D` be a `C^n` Ehresmann
connection, `1 ≤ n`, on a proper `C^(n+1)` map `f : P → B` of finite-dimensional boundaryless
Hausdorff manifolds, and `Γ : N × ℝ → B` a `C^(n+1)` family of curves in `B`, with parameters in a
finite-dimensional boundaryless Hausdorff manifold `N`. For times `s t` and `a₀ : N`, there are a
neighbourhood `U` of `a₀` and a `C^n` map `Ψ : N × P → P` such that, for every `a ∈ U`,
`x ↦ Ψ (a, x)` agrees on the fibre over `Γ (a, s)` with parallel transport along the curve
`u ↦ Γ (a, u)` from `s` to `t`. For `n = ∞`, `Ψ` is smooth. -/
theorem exists_contMDiff_parallelTransport_param (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f)
    (hfp : IsProperMap f) {Γ : N × ℝ → B} (hΓ : ContMDiff (IN.prod 𝓘(ℝ, ℝ)) J (n + 1) Γ)
    (s t : ℝ) (a₀ : N) :
    ∃ U ∈ 𝓝 a₀, ∃ Ψ : N × P → P, ContMDiff (IN.prod I) I n Ψ ∧
      ∀ a ∈ U, EqOn (fun x ↦ Ψ (a, x)) (hD.parallelTransport (fun u ↦ Γ (a, u)) s t)
        (f ⁻¹' {Γ (a, s)}) := by
  -- Times between which, near `a₀`, some `C^n` map agrees with transport on the fibres.
  let R : ℝ → ℝ → Prop := fun u v ↦ ∃ U ∈ 𝓝 a₀, ∃ Ψ : N × P → P, ContMDiff (IN.prod I) I n Ψ ∧
    ∀ a ∈ U, EqOn (fun x ↦ Ψ (a, x)) (hD.parallelTransport (fun r ↦ Γ (a, r)) u v)
      (f ⁻¹' {Γ (a, u)})
  have hΓc (a : N) : ContMDiff 𝓘(ℝ, ℝ) J (n + 1) (fun u ↦ Γ (a, u)) :=
    hΓ.comp (contMDiff_const.prodMk contMDiff_id)
  -- The relation is transitive: compose the maps on the intersection of the neighbourhoods.
  have htrans : IsTrans ℝ R := ⟨fun u v w ⟨U₁, hU₁, Ψ₁, hΨ₁, h₁⟩ ⟨U₂, hU₂, Ψ₂, hΨ₂, h₂⟩ ↦
    ⟨U₁ ∩ U₂, inter_mem hU₁ hU₂, fun p ↦ Ψ₂ (p.1, Ψ₁ p), hΨ₂.comp (contMDiff_fst.prodMk hΨ₁),
      fun a ha x hx ↦ by
        simp only [h₁ a ha.1 hx,
          h₂ a ha.2 (hD.parallelTransport_mem_preimage hn hf hfp (hΓc a) hx v),
          hD.parallelTransport_parallelTransport hn hf hfp (hΓc a) hx]⟩⟩
  -- It holds between nearby times: near `u`, the curve at `a₀` stays in the base set of one
  -- trivialization.
  have hloc (u : ℝ) : ∀ᶠ v in 𝓝 u, R u v ∧ R v u := by
    let e := trivializationAt F (TangentSpace J) (Γ (a₀, u))
    obtain ⟨a, b, hu, hab, hmaps⟩ := exists_Icc_mem_subset_of_mem_nhds
      ((hΓc a₀).continuous.continuousAt.eventually_mem_baseSet_trivializationAt F
        (TangentSpace J))
    obtain ⟨U, hU, hΨ⟩ :=
      hD.exists_contMDiff_parallelTransport_param_of_mapsTo_baseSet hn hf hfp hΓ e hmaps
    filter_upwards [hab] with v hv
    exact ⟨⟨U, hU, hΨ u hu v hv⟩, ⟨U, hU, hΨ v hv u hu⟩⟩
  exact PreconnectedSpace.induction₂' R hloc htrans s t

include hD in
/-- **Parallel transport depends smoothly on a family of curves, on an open set of parameters.**
Let `Γ : N × ℝ → B` be a family of curves that is `C^(n+1)` on `U ×ˢ univ`, for an open set `U`
of `N`. Near a parameter `a₀ ∈ U`, transport along the curves `u ↦ Γ (a, u)` from `s` to `t` is,
on the fibre over `Γ (a, s)`, the restriction of a map `N × P → P` that is `C^n` on `U ×ˢ univ`. -/
theorem exists_contMDiffOn_parallelTransport_param (hn : 1 ≤ n)
    (hf : ContMDiff I J (n + 1) f) (hfp : IsProperMap f) {U : Set N} (hU : IsOpen U)
    {Γ : N × ℝ → B} (hΓ : ContMDiffOn (IN.prod 𝓘(ℝ, ℝ)) J (n + 1) Γ (U ×ˢ univ)) (s t : ℝ)
    {a₀ : N} (ha₀ : a₀ ∈ U) :
    ∃ Φ : N × P → P, ContMDiffOn (IN.prod I) I n Φ (U ×ˢ univ) ∧ ∀ᶠ a in 𝓝 a₀, ∀ x,
      f x = Γ (a, s) → Φ (a, x) = hD.parallelTransport (fun u ↦ Γ (a, u)) s t x := by
  classical
  let W : TopologicalSpace.Opens N := ⟨U, hU⟩
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

variable {EZ : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ]
  {HZ : Type*} [TopologicalSpace HZ] {IZ : ModelWithCorners ℝ EZ HZ}
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace HZ Z]

/-- **Parallel transport read in trivializations.** For trivializations `e` and `e'` of `f` with
fibre `Z`, the map `Z → Z` that sends `v` to the second coordinate in `e'` of the transport along
`γ` from `s` to `t` of the point with coordinates `(γ s, v)` in `e`. When `γ s ∈ e.baseSet` and
`γ t ∈ e'.baseSet` this is parallel transport from the fibre over `γ s` to the fibre over `γ t`
read in the model fibre (`TauCeti.IsEhresmannConnection.parallelTransportInDiffeomorph`); for a
loop at `b` and `e = e'` it is the holonomy of the loop read in `e`. -/
def parallelTransportIn (e e' : Trivialization Z f) (γ : ℝ → B) (s t : ℝ) (v : Z) : Z :=
  (e' (hD.parallelTransport γ s t (e.toOpenPartialHomeomorph.symm (γ s, v)))).2

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space P] [FiniteDimensional ℝ F]
  [IsManifold J ∞ B] [J.Boundaryless] [T2Space B] in
theorem parallelTransportIn_def (e e' : Trivialization Z f) (γ : ℝ → B) (s t : ℝ) (v : Z) :
    hD.parallelTransportIn e e' γ s t v =
      (e' (hD.parallelTransport γ s t (e.toOpenPartialHomeomorph.symm (γ s, v)))).2 :=
  (rfl)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space P] [FiniteDimensional ℝ F]
  [IsManifold J ∞ B] [J.Boundaryless] [T2Space B] in
/-- Transport from a time to itself, read twice in the same trivialization, is the identity. -/
@[simp]
theorem parallelTransportIn_self {e : Trivialization Z f} {γ : ℝ → B} {s : ℝ}
    (hs : γ s ∈ e.baseSet) (v : Z) : hD.parallelTransportIn e e γ s s v = v := by
  rw [parallelTransportIn_def, parallelTransport_self, e.apply_symm_apply' hs]

/-- Let `D` be a `C^n` Ehresmann connection, `1 ≤ n`, on a proper `C^(n+1)` map `f : P → B`, and
`γ` a `C^(n+1)` curve in `B`. If `γ s ∈ e.baseSet` and `γ t ∈ e'.baseSet`, the point of the fibre
over `γ t` with coordinate `hD.parallelTransportIn e e' γ s t v` in `e'` is the transport from `s`
to `t` of the point of the fibre over `γ s` with coordinate `v` in `e`. -/
theorem fiberInclusionMap_parallelTransportIn (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f)
    (hfp : IsProperMap f) {γ : ℝ → B} (hγ : ContMDiff 𝓘(ℝ, ℝ) J (n + 1) γ)
    {e e' : Trivialization Z f} {s t : ℝ} (hs : γ s ∈ e.baseSet) (ht : γ t ∈ e'.baseSet)
    (v : Z) :
    e'.fiberInclusionMap ht (hD.parallelTransportIn e e' γ s t v) =
      hD.parallelTransport γ s t (e.fiberInclusionMap hs v) := by
  have hy := hD.parallelTransport_mem_preimage hn hf hfp hγ (e.proj_symm_apply' (x := v) hs) t
  rw [mem_preimage, mem_singleton_iff] at hy
  rw [parallelTransportIn_def, e.fiberInclusionMap_apply hs, e'.fiberInclusionMap_apply ht, ← hy,
    e'.symm_apply_mk_proj (e'.mem_source.2 (hy ▸ ht))]

/-- Let `D` be a `C^n` Ehresmann connection, `1 ≤ n`, on a proper `C^(n+1)` map `f : P → B`, and
`γ` a `C^(n+1)` curve in `B`. If `γ s ∈ e.baseSet` and `γ t ∈ e'.baseSet`, transport from `s` to
`t` read in `e` and `e'`, followed by transport from `t` to `u` read in `e'` and `e''`, is
transport from `s` to `u` read in `e` and `e''`. -/
theorem parallelTransportIn_parallelTransportIn (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f)
    (hfp : IsProperMap f) {γ : ℝ → B} (hγ : ContMDiff 𝓘(ℝ, ℝ) J (n + 1) γ)
    {e e' : Trivialization Z f} (e'' : Trivialization Z f) {s t : ℝ} (hs : γ s ∈ e.baseSet)
    (ht : γ t ∈ e'.baseSet) (u : ℝ) (v : Z) :
    hD.parallelTransportIn e' e'' γ t u (hD.parallelTransportIn e e' γ s t v) =
      hD.parallelTransportIn e e'' γ s u v := by
  rw [hD.parallelTransportIn_def e', ← e'.fiberInclusionMap_apply ht,
    hD.fiberInclusionMap_parallelTransportIn hn hf hfp hγ hs ht, e.fiberInclusionMap_apply hs,
    hD.parallelTransport_parallelTransport hn hf hfp hγ (e.proj_symm_apply' hs),
    parallelTransportIn_def]

/-- **Smoothness of transport in trivializations.** Let `D` be a `C^n` Ehresmann connection,
`1 ≤ n`, on a proper `C^(n+1)` map `f : P → B` of finite-dimensional boundaryless Hausdorff
manifolds, `γ` a `C^(n+1)` curve in `B`, and `e`, `e'` trivializations of `f` with fibre `Z`, the
inverse of `e` being `C^n` on its target and `e'` being `C^n` on its source. If
`γ s ∈ e.baseSet` and `γ t ∈ e'.baseSet`, transport from `s` to `t` read in `e` and `e'` is a
`C^n` map of `Z`. -/
theorem contMDiff_parallelTransportIn (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f)
    (hfp : IsProperMap f) {γ : ℝ → B} (hγ : ContMDiff 𝓘(ℝ, ℝ) J (n + 1) γ)
    {e e' : Trivialization Z f}
    (he : ContMDiffOn (J.prod IZ) I n e.toOpenPartialHomeomorph.symm e.target)
    (he' : ContMDiffOn I (J.prod IZ) n e' e'.source) {s t : ℝ} (hs : γ s ∈ e.baseSet)
    (ht : γ t ∈ e'.baseSet) : ContMDiff IZ IZ n (hD.parallelTransportIn e e' γ s t) := by
  obtain ⟨Ψ, hΨ, -⟩ := hD.exists_diffeomorph_eqOn_parallelTransport hn hf hfp hγ s t
  have hx (v : Z) : e.toOpenPartialHomeomorph.symm (γ s, v) ∈ f ⁻¹' {γ s} :=
    e.proj_symm_apply' hs
  have h₁ : ContMDiff IZ I n fun v : Z ↦ e.toOpenPartialHomeomorph.symm (γ s, v) :=
    funext (e.fiberInclusionMap_apply hs) ▸ e.contMDiff_fiberInclusionMap he hs
  have h₂ : ContMDiff IZ (J.prod IZ) n fun v ↦ e' (Ψ (e.toOpenPartialHomeomorph.symm (γ s, v))) :=
    he'.comp_contMDiff (Ψ.contMDiff.comp h₁) fun v ↦ e'.mem_source.2 <| by
      rw [hΨ (hx v), mem_singleton_iff.1 (hD.parallelTransport_mem_preimage hn hf hfp hγ (hx v) t)]
      exact ht
  exact (contMDiff_snd.comp h₂).congr fun v ↦ by
    simp only [comp_apply, parallelTransportIn_def, hΨ (hx v)]

/-- **Parallel transport in trivializations as a diffeomorphism.** Let `D` be a `C^n` Ehresmann
connection, `1 ≤ n`, on a proper `C^(n+1)` map `f : P → B` of finite-dimensional boundaryless
Hausdorff manifolds, `γ` a `C^(n+1)` curve in `B`, and `e`, `e'` trivializations of `f` with fibre
`Z`, each `C^n` on its source with a `C^n` inverse on its target. If `γ s ∈ e.baseSet` and
`γ t ∈ e'.baseSet`, transport from `s` to `t` read in `e` and `e'` is a `C^n` diffeomorphism of
`Z`, whose inverse is transport from `t` to `s` read in `e'` and `e`. For a loop at `b` and
`e = e'`, it is the holonomy of the loop read in `e`. -/
def parallelTransportInDiffeomorph (e e' : Trivialization Z f) (γ : ℝ → B) (s t : ℝ)
    (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f) (hfp : IsProperMap f)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) J (n + 1) γ) (he : ContMDiffOn I (J.prod IZ) n e e.source)
    (he_symm : ContMDiffOn (J.prod IZ) I n e.toOpenPartialHomeomorph.symm e.target)
    (he' : ContMDiffOn I (J.prod IZ) n e' e'.source)
    (he'_symm : ContMDiffOn (J.prod IZ) I n e'.toOpenPartialHomeomorph.symm e'.target)
    (hs : γ s ∈ e.baseSet) (ht : γ t ∈ e'.baseSet) : Z ≃ₘ^n⟮IZ, IZ⟯ Z where
  toFun := hD.parallelTransportIn e e' γ s t
  invFun := hD.parallelTransportIn e' e γ t s
  left_inv v := by
    rw [hD.parallelTransportIn_parallelTransportIn hn hf hfp hγ e hs ht,
      parallelTransportIn_self _ hs]
  right_inv v := by
    rw [hD.parallelTransportIn_parallelTransportIn hn hf hfp hγ e' ht hs,
      parallelTransportIn_self _ ht]
  contMDiff_toFun := hD.contMDiff_parallelTransportIn hn hf hfp hγ he_symm he' hs ht
  contMDiff_invFun := hD.contMDiff_parallelTransportIn hn hf hfp hγ he'_symm he ht hs

/-- The diffeomorphism `parallelTransportInDiffeomorph` is the map `parallelTransportIn`. -/
@[simp]
theorem coe_parallelTransportInDiffeomorph (e e' : Trivialization Z f) (γ : ℝ → B) (s t : ℝ)
    (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f) (hfp : IsProperMap f)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) J (n + 1) γ) (he : ContMDiffOn I (J.prod IZ) n e e.source)
    (he_symm : ContMDiffOn (J.prod IZ) I n e.toOpenPartialHomeomorph.symm e.target)
    (he' : ContMDiffOn I (J.prod IZ) n e' e'.source)
    (he'_symm : ContMDiffOn (J.prod IZ) I n e'.toOpenPartialHomeomorph.symm e'.target)
    (hs : γ s ∈ e.baseSet) (ht : γ t ∈ e'.baseSet) :
    ⇑(hD.parallelTransportInDiffeomorph e e' γ s t hn hf hfp hγ he he_symm he' he'_symm hs ht) =
      hD.parallelTransportIn e e' γ s t :=
  (rfl)

/-- The inverse of transport from `s` to `t` read in `e` and `e'` is transport from `t` to `s`
read in `e'` and `e`. -/
@[simp]
theorem symm_parallelTransportInDiffeomorph (e e' : Trivialization Z f) (γ : ℝ → B) (s t : ℝ)
    (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f) (hfp : IsProperMap f)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) J (n + 1) γ) (he : ContMDiffOn I (J.prod IZ) n e e.source)
    (he_symm : ContMDiffOn (J.prod IZ) I n e.toOpenPartialHomeomorph.symm e.target)
    (he' : ContMDiffOn I (J.prod IZ) n e' e'.source)
    (he'_symm : ContMDiffOn (J.prod IZ) I n e'.toOpenPartialHomeomorph.symm e'.target)
    (hs : γ s ∈ e.baseSet) (ht : γ t ∈ e'.baseSet) :
    (hD.parallelTransportInDiffeomorph e e' γ s t hn hf hfp hγ he he_symm he' he'_symm hs ht).symm =
      hD.parallelTransportInDiffeomorph e' e γ t s hn hf hfp hγ he' he'_symm he he_symm ht hs :=
  (rfl)

/-- **Change of trivializations.** Let `D` be a `C^n` Ehresmann connection, `1 ≤ n`, on a proper
`C^(n+1)` map `f : P → B`, and `γ` a `C^(n+1)` curve in `B`. If `γ s` lies in the base sets of `e`
and `e₂`, and `γ t` in that of `e'`, transport from `s` to `t` read in `e₂` and `e₂'` is
transport read in `e` and `e'`, conjugated by the coordinate changes from `e₂` to `e` at `γ s` and
from `e'` to `e₂'` at `γ t`. -/
theorem parallelTransportIn_coordChange (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f)
    (hfp : IsProperMap f) {γ : ℝ → B} (hγ : ContMDiff 𝓘(ℝ, ℝ) J (n + 1) γ)
    {e e' e₂ e₂' : Trivialization Z f} {s t : ℝ} (hs : γ s ∈ e.baseSet)
    (hs₂ : γ s ∈ e₂.baseSet) (ht : γ t ∈ e'.baseSet) (v : Z) :
    hD.parallelTransportIn e₂ e₂' γ s t v =
      e'.coordChange e₂' (γ t) (hD.parallelTransportIn e e' γ s t (e₂.coordChange e (γ s) v)) := by
  rw [hD.parallelTransportIn_def e, ← e.fiberInclusionMap_apply hs,
    e₂.fiberInclusionMap_coordChange e hs₂ hs, e₂.fiberInclusionMap_apply hs₂]
  have hy := hD.parallelTransport_mem_preimage hn hf hfp hγ (e₂.proj_symm_apply' (x := v) hs₂) t
  rw [mem_preimage, mem_singleton_iff] at hy
  rw [← hy, e'.coordChange_apply_snd e₂' (hy ▸ ht), parallelTransportIn_def]

end Trivialization

end IsEhresmannConnection

end TauCeti

end
