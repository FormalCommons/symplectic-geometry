/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField.OrbitMap
public import TauCeti.Geometry.Manifold.GroupAction.Orbit
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Local sections of the orbit projection of a free proper action

Let a Lie group `K` act smoothly, freely and properly on a manifold `M`, and give the orbit space
`M ⧸ K` any manifold structure for which the orbit projection is smooth. A section `s` of the
orbit projection over an open set `U` of orbits, smooth on `U`, gives the map
`(k, q) ↦ k • s q` from `K × U` to `M`, in the form of Tau Ceti's slice maps
(`TauCeti/Geometry/Manifold/GroupAction/TransverseSlice.lean`). This file shows that this map is
smooth on `univ ×ˢ U`, that its differential is injective there, and, when the dimensions of `K`
and of the orbit space add up to that of `M`, that it is a local diffeomorphism on `univ ×ˢ U`.
This is the half of the quotient manifold theorem that turns local sections into local
trivializations of the orbit projection.

The injectivity of the differential combines two facts: composed with the differential of the
orbit projection, the differential is the second projection, since `s` is a section; and along
`K` it is the differential of an orbit map, injective because the action is free
(`TauCeti.injective_mfderiv_smul_const_iff`). The local diffeomorphism then comes from Tau Ceti's
inverse function theorem `TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv`.

## Main results

* `SymplecticGeometry.contMDiffOn_smul_section`: `(k, q) ↦ k • s q` is smooth on `univ ×ˢ U`.
* `SymplecticGeometry.injective_mfderiv_smul_section`: its differential is injective there.
* `SymplecticGeometry.isLocalDiffeomorphOn_smul_section`: it is a local diffeomorphism there.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 21.10 and its proof (local sections of the orbit projection give local
  diffeomorphisms `K × U → M`).
-/

public section

open MulAction Set Topology TauCeti
open scoped ContDiff Manifold

namespace SymplecticGeometry

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
  ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {IK : ModelWithCorners ℝ E H}
  {K : Type*} [TopologicalSpace K] [ChartedSpace H K] [Group K] [LieGroup IK ∞ K]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {IM : ModelWithCorners ℝ E' H'} [IM.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold IM ∞ M]
  [MulAction K M] [ContMDiffSMul IK IM ∞ K M] [ProperSMul K M] [IsCancelSMul K M]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  [ChartedSpace HB (orbitRel.Quotient K M)]
  {U : Set (orbitRel.Quotient K M)} {s : orbitRel.Quotient K M → M}

omit [FiniteDimensional ℝ E] [LieGroup IK ∞ K] [FiniteDimensional ℝ E'] [IM.Boundaryless]
  [IsManifold IM ∞ M] [ProperSMul K M] [IsCancelSMul K M] in
/-- For a map `s` from the orbit space to `M` that is smooth on `U`, the map `(k, q) ↦ k • s q`
is smooth on `univ ×ˢ U`. -/
theorem contMDiffOn_smul_section (hs : ContMDiffOn IB IM ∞ s U) :
    ContMDiffOn (IK.prod IB) IM ∞ (fun p : K × orbitRel.Quotient K M ↦ p.1 • s p.2)
      (univ ×ˢ U) :=
  contMDiff_fst.contMDiffOn.smul (I := IK) (hs.comp contMDiff_snd.contMDiffOn fun _ hp ↦ hp.2)

/-- For a section `s` of the orbit projection of a free proper smooth action, smooth on an open
set `U` of orbits, where the orbit projection is smooth, the differential of
`(k, q) ↦ k • s q` is injective at each point of `univ ×ˢ U`. -/
theorem injective_mfderiv_smul_section (hU : IsOpen U) (hs : ContMDiffOn IB IM ∞ s U)
    (hsec : ∀ q ∈ U, Quotient.mk (orbitRel K M) (s q) = q)
    (hπ : ContMDiff IM IB ∞ (Quotient.mk (orbitRel K M))) (k : K)
    {q : orbitRel.Quotient K M} (hq : q ∈ U) :
    Function.Injective (mfderiv (IK.prod IB) IM
      (fun p : K × orbitRel.Quotient K M ↦ p.1 • s p.2) (k, q)) := by
  have := FiniteDimensional.completeSpace ℝ E
  have := FiniteDimensional.completeSpace ℝ E'
  set Ψ := fun p : K × orbitRel.Quotient K M ↦ p.1 • s p.2
  have hmem : (univ : Set K) ×ˢ U ∈ 𝓝 (k, q) := (isOpen_univ.prod hU).mem_nhds ⟨trivial, hq⟩
  have hΨ : MDifferentiableAt (IK.prod IB) IM Ψ (k, q) :=
    ((contMDiffOn_smul_section hs).contMDiffAt hmem).mdifferentiableAt (by simp)
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
  -- The orbit projection after `Ψ` is the second projection near `(k, q)`.
  have hsnd : Quotient.mk (orbitRel K M) ∘ Ψ =ᶠ[𝓝 (k, q)] Prod.snd :=
    Filter.eventually_of_mem hmem fun p hp ↦ by
      simp only [Function.comp_apply, Ψ, orbitRel.Quotient.quotient_smul_eq, hsec _ hp.2]
  have h2 : v.2 = 0 := by
    have := mfderiv_comp_apply _ ((hπ (Ψ (k, q))).mdifferentiableAt (by simp)) hΨ v
    rw [hsnd.mfderiv_eq, hv, map_zero, mfderiv_snd] at this
    exact this
  -- Along `K`, `Ψ` is the orbit map of `s q`, whose differential is injective.
  set w : TangentSpace IK k := v.1
  have hι : MDifferentiableAt IK (IK.prod IB) (fun h : K ↦ (h, q)) k :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hv' : mfderiv IK (IK.prod IB) (fun h : K ↦ (h, q)) k w = v := by
    rw [mfderiv_prod_left]
    exact Prod.ext rfl h2.symm
  have h1 := mfderiv_comp_apply k hΨ hι w
  have hcomp : Ψ ∘ (fun h : K ↦ (h, q)) = fun h : K ↦ h • s q := rfl
  rw [hv', hv, hcomp] at h1
  have hinj := (injective_mfderiv_smul_const_iff (I := IK) (I' := IM) (s q) k).2
    (isotropy_fundamental_eq_bot_of_properSMul_of_stabilizer_eq_bot
      (IsCancelSMul.stabilizer_eq_bot _))
  have h3 : w = 0 := hinj (by rw [h1, map_zero])
  exact Prod.ext h3 h2

/-- For a section `s` of the orbit projection of a free proper smooth action, smooth on an open
set `U` of orbits, where the orbit projection is smooth and the dimensions of `K` and of the orbit
space add up to that of `M`, the map `(k, q) ↦ k • s q` is a local diffeomorphism on
`univ ×ˢ U`. -/
theorem isLocalDiffeomorphOn_smul_section [FiniteDimensional ℝ EB] [IB.Boundaryless]
    [IsManifold IB ∞ (orbitRel.Quotient K M)] (hU : IsOpen U) (hs : ContMDiffOn IB IM ∞ s U)
    (hsec : ∀ q ∈ U, Quotient.mk (orbitRel K M) (s q) = q)
    (hπ : ContMDiff IM IB ∞ (Quotient.mk (orbitRel K M)))
    (hdim : Module.finrank ℝ E + Module.finrank ℝ EB = Module.finrank ℝ E') :
    IsLocalDiffeomorphOn (IK.prod IB) IM ∞
      (fun p : K × orbitRel.Quotient K M ↦ p.1 • s p.2) (univ ×ˢ U) := fun p ↦
  isLocalDiffeomorphAt_of_injective_mfderiv (contMDiffOn_smul_section hs) (isOpen_univ.prod hU)
    p.property BoundarylessManifold.isInteriorPoint (by simp)
    (injective_mfderiv_smul_section hU hs hsec hπ _ p.property.2)
    (by rw [Module.finrank_prod, hdim])

end SymplecticGeometry

end
