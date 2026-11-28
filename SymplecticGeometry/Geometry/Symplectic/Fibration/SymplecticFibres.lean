/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Fibration.HorizontalDistribution
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.StructureGroup
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Maps.Proper.Basic
import SymplecticGeometry.Geometry.Symplectic.Fibration.Connection
import SymplecticGeometry.Geometry.Manifold.Submersion.RadialTrivialization
import SymplecticGeometry.Geometry.Manifold.FiberBundle.ChangeModelFiber

/-!
# Fibrations with symplectic fibres

Let `proj : M → B` be a map with a smooth atlas `A` with model fibre `F`, where `M` is compact and
connected, and let `τ` be a two-form on `M` that is vertically closed and nondegenerate on the
vertical spaces. Then the fibres of `proj`, with the forms that `τ` induces on them, are all
symplectomorphic to one symplectic manifold `(F, σ)`, and `proj` has a smooth atlas whose charts
carry `τ` to `σ` on every fibre. Its coordinate changes then preserve `σ`: it is a symplectic
atlas. For a symplectic form `ω` on `M` for which every fibre is a symplectic submanifold, this
makes `proj` a symplectic fibration compatible with `ω`.

The proof is by parallel transport for the connection `τ.horizontalDistribution proj` of `τ`
(McDuff–Salamon, Lemma 6.1.3; Seidel, Lemma 7.2). Since `M` is compact, `proj` is proper and
transport exists. Around each point `b` of `B`, transport along the rays of a chart of `B` from
`b` gives a smooth trivialization
(`TauCeti.IsEhresmannConnection.exists_trivialization_parallelTransport`); since `τ` is
vertically closed, transport preserves the forms on the fibres
(`TauCeti.SmoothTwoForm.IsVerticallyClosed.mpullback_parallelTransportIn`), so every fibre
inclusion of this trivialization pulls `τ` back to the form on the fibre over `b`. So the
relation "the fibre forms over two points differ by a diffeomorphism of `F`" has open classes,
and the base, the image of the connected `M`, is connected: all fibre forms are carried by
diffeomorphisms of `F` to the one `σ` over a chosen point. Composing each radial
trivialization in the fibre with such a diffeomorphism gives the charts of the new atlas.

## Main results

* `TauCeti.SmoothTwoForm.exists_hasStructureGroup_restrictsTo_of_isVerticallyClosed`: for compact
  connected `M` and a vertically closed, vertically nondegenerate `τ`, there are a symplectic form
  `σ` on `F` and a smooth atlas with structure group the stabilizer of `σ` along which `τ`
  restricts to `σ`.
* `TauCeti.SmoothTwoForm.exists_hasStructureGroup_restrictsTo`: the case of a symplectic form
  that is nondegenerate on the fibres; the new atlas is a reduction of `A` to the stabilizer.
* `TauCeti.MapFiber.Atlas.IsOrientedCompatible.exists_hasStructureGroup_restrictsTo`: the same
  for a form compatible with an oriented atlas.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.1, Lemma 6.1.3.
* [P. Seidel, *Floer homology and the symplectic isotopy problem*][Seidel1997Thesis], Lemma 7.2.
* [V. Guillemin, E. Lerman, S. Sternberg, *Symplectic Fibrations and Multiplicity
  Diagrams*][GuilleminLermanSternberg1996], §1.2, Theorem 1.2.4.
-/

public section

noncomputable section

open Bundle Function Set
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothTwoForm

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M] [IM.Boundaryless]
  [T2Space M]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B] [IB.Boundaryless]
  [T2Space B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF]
  {HF : Type*} [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF}
  {F : Type*} [TopologicalSpace F] [ChartedSpace HF F] [IsManifold IF ∞ F]
  {proj : M → B} {A : MapFiber.Atlas F proj} {τ : SmoothTwoForm IM M}

/-- The local step: around each point `b`, transport along the rays of a chart of `B` from `b`
gives a smooth trivialization whose fibre inclusions all pull a vertically closed `τ` back to its
pull-back to the fibre over `b` through the chart `A.trivAt b`. -/
private theorem exists_trivialization_mpullback_fiberInclusionMap (hfp : IsProperMap proj)
    (hA : A.IsContMDiff ∞ IB IF IM) (h : IsVerticallyClosed IB proj τ)
    (hD : IsEhresmannConnection IM IB ∞ proj (horizontalDistribution IB proj τ)) (b : B) :
    ∃ e : Trivialization F proj, ContMDiffOn IM (IB.prod IF) ∞ e e.source ∧
      ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target ∧ b ∈ e.baseSet ∧
      ∀ b' (hb' : b' ∈ e.baseSet), mpullback IF IM (e.fiberInclusionMap hb') τ.val =
        mpullback IF IM ((A.trivAt b).fiberInclusionMap (A.mem_baseSet_trivAt b)) τ.val := by
  have hf : ContMDiff IM IB ((⊤ : ℕ∞) + 1) proj :=
    hA.contMDiff_proj.of_le ENat.coe_top_add_one.le
  obtain ⟨e, he, he', hb, hray⟩ := hD.exists_trivialization_parallelTransport le_top hf hfp
    (A.trivAt b) (hA.contMDiffOn_trivAt b) (hA.contMDiffOn_trivAt_symm b) (A.mem_baseSet_trivAt b)
  refine ⟨e, he, he', hb, fun b' hb' ↦ ?_⟩
  obtain ⟨γ, hγ, hγeq, hsymm⟩ := hray b' hb'
  rcases isEmpty_or_nonempty F with hF | ⟨⟨v₀⟩⟩
  · exact funext fun v ↦ isEmptyElim v
  have hγ' : ContMDiff 𝓘(ℝ, ℝ) IB ((⊤ : ℕ∞) + 1) γ := hγ.of_le ENat.coe_top_add_one.le
  have hγ0 : γ 0 = b := by
    rw [hγeq (left_mem_Icc.2 zero_le_one)]
    simp only [zero_smul, add_zero, extChartAt_to_inv]
  -- The curve ends at `b'`, as transport along it carries the fibre over `b` to that over `b'`.
  have hγ1 : γ 1 = b' := by
    have h1 := hD.apply_parallelTransport le_top hf hfp hγ'
      (x := (A.trivAt b).toOpenPartialHomeomorph.symm (b, v₀))
      (((A.trivAt b).proj_symm_apply' (A.mem_baseSet_trivAt b)).trans hγ0.symm) 1
    rw [← hsymm v₀, e.proj_symm_apply' hb'] at h1
    exact h1.symm
  have hs₁ : γ 0 ∈ (A.trivAt b).baseSet := hγ0 ▸ A.mem_baseSet_trivAt b
  have ht₂ : γ 1 ∈ (A.trivAt b').baseSet := hγ1 ▸ A.mem_baseSet_trivAt b'
  -- The fibre inclusion of `e` over `b'` is transport after the fibre inclusion over `b`.
  have hι : ⇑(e.fiberInclusionMap hb') =
      hD.parallelTransport γ 0 1 ∘ (A.trivAt b).fiberInclusionMap hs₁ := funext fun v ↦ by
    rw [comp_apply, e.fiberInclusionMap_apply hb', hsymm v,
      (A.trivAt b).fiberInclusionMap_apply hs₁, hγ0]
  have key : ∀ (c : B) (hc : c ∈ (A.trivAt b).baseSet), c = b →
      mpullback IF IM ((A.trivAt b).fiberInclusionMap hc) τ.val =
        mpullback IF IM ((A.trivAt b).fiberInclusionMap (A.mem_baseSet_trivAt b)) τ.val := by
    rintro c hc rfl
    rfl
  rw [hι, IsEhresmannConnection.mpullback_comp_fiberInclusionMap_of_eqOn_parallelTransport hfp hA
    hγ' hs₁ ht₂ (fun _ _ ↦ rfl), h.mpullback_parallelTransportIn hfp hA hD hγ hs₁ ht₂]
  exact key _ hs₁ hγ0

/-- Over a preconnected base, the pull-backs of a vertically closed `τ` to any two fibres, each
through the chart of `A` at its point, are related by a diffeomorphism of the model fibre. -/
private theorem exists_diffeomorph_mpullback_eq [PreconnectedSpace B] (hfp : IsProperMap proj)
    (hA : A.IsContMDiff ∞ IB IF IM) (h : IsVerticallyClosed IB proj τ)
    (hD : IsEhresmannConnection IM IB ∞ proj (horizontalDistribution IB proj τ)) (b c : B) :
    ∃ φ : F ≃ₘ⟮IF, IF⟯ F, mpullback IF IF φ
        (mpullback IF IM ((A.trivAt c).fiberInclusionMap (A.mem_baseSet_trivAt c)) τ.val) =
      mpullback IF IM ((A.trivAt b).fiberInclusionMap (A.mem_baseSet_trivAt b)) τ.val := by
  have hdiff (φ : F ≃ₘ⟮IF, IF⟯ F) : MDifferentiable IF IF φ := φ.mdifferentiable (by simp)
  let R : B → B → Prop := fun b c ↦ ∃ φ : F ≃ₘ⟮IF, IF⟯ F, mpullback IF IF φ
      (mpullback IF IM ((A.trivAt c).fiberInclusionMap (A.mem_baseSet_trivAt c)) τ.val) =
    mpullback IF IM ((A.trivAt b).fiberInclusionMap (A.mem_baseSet_trivAt b)) τ.val
  have hsymm : ∀ b c, R b c → R c b := by
    rintro b c ⟨φ, hφ⟩
    refine ⟨φ.symm, ?_⟩
    rw [← hφ, mpullback_symm_mpullback (by simp)]
  have htrans : IsTrans B R := ⟨fun a b c ⟨ψ, hψ⟩ ⟨φ, hφ⟩ ↦ ⟨ψ.trans φ, by
    rw [Diffeomorph.coe_trans, mpullback_comp (hdiff ψ) (hdiff φ), hφ, hψ]⟩⟩
  -- Near each point, the coordinate changes to the radial trivialization relate the fibre forms.
  have hloc : ∀ b, ∀ᶠ c in 𝓝 b, R b c ∧ R c b := by
    intro b
    obtain ⟨e, he, he', hb, hω⟩ := exists_trivialization_mpullback_fiberInclusionMap hfp hA h hD b
    filter_upwards [e.open_baseSet.mem_nhds hb] with c hc
    have hc' := A.mem_baseSet_trivAt c
    have hRc : R b c := ⟨e.coordChangeDiffeomorph (A.trivAt c) he he' (hA.contMDiffOn_trivAt c)
        (hA.contMDiffOn_trivAt_symm c) hc hc', by
      rw [Trivialization.coe_coordChangeDiffeomorph, ← hω c hc]
      exact (e.mpullback_fiberInclusionMap_eq_mpullback_coordChange
        (hA.mdifferentiable_trivAt (by simp) c) hc hc'
        (e.contMDiff_coordChange (A.trivAt c) he' (hA.contMDiffOn_trivAt c) hc hc'
          |>.mdifferentiable (by simp)) τ.val).symm⟩
    exact ⟨hRc, hsymm _ _ hRc⟩
  exact PreconnectedSpace.induction₂' R hloc htrans b c

/-- **Vertically closed forms that are nondegenerate on the fibres give symplectic atlases.** Let
`A` be a smooth atlas of `proj : M → B` with model fibre `F`, where `M` is compact and connected,
and let `τ` be a two-form on `M` that is vertically closed and vertically nondegenerate for
`proj`. Then there are a symplectic form `σ` on `F` and a smooth atlas `A'` of `proj` with
structure group the stabilizer of `σ`, along which `τ` restricts to `σ`: every chart of `A'` pulls
`τ` back to `σ` on every fibre. -/
theorem exists_hasStructureGroup_restrictsTo_of_isVerticallyClosed [CompactSpace M]
    [ConnectedSpace M] (hA : A.IsContMDiff ∞ IB IF IM) (h : IsVerticallyClosed IB proj τ)
    (hnd : IsVerticallyNondegenerate IB proj τ) :
    ∃ σ : SmoothTwoForm IF F, σ.IsSymplectic ∧ ∃ A' : MapFiber.Atlas F proj,
      A'.IsContMDiff ∞ IB IF IM ∧ A'.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ) ∧
        A'.RestrictsTo σ τ := by
  have hproj := hA.contMDiff_proj.continuous
  have hfp : IsProperMap proj := hproj.isProperMap
  have hD := hnd.isEhresmannConnection (hA.isSubmersion ENat.LEInfty.out)
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  -- `proj` is onto, so `B` is connected.
  have hsurj : Surjective proj := fun b ↦
    ⟨(A.trivAt b).toOpenPartialHomeomorph.symm (b, (A.trivAt (proj x₀) x₀).2),
      (A.trivAt b).proj_symm_apply' (A.mem_baseSet_trivAt b)⟩
  have : ConnectedSpace B := hsurj.connectedSpace hproj
  -- The model form is the fibre form over a chosen point `b₀`.
  set b₀ := proj x₀
  have hι₀ := (A.trivAt b₀).contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm b₀)
    (A.mem_baseSet_trivAt b₀)
  set σ : SmoothTwoForm IF F :=
    SmoothForm.mpullback ((A.trivAt b₀).fiberInclusionMap (A.mem_baseSet_trivAt b₀)) hι₀ τ
  have hσ : σ.IsSymplectic :=
    ⟨h.isClosed_mpullback_fiberInclusionMap (hA.contMDiffOn_trivAt b₀)
        (hA.contMDiffOn_trivAt_symm b₀) _,
      hnd.isNondegenerate_mpullback_fiberInclusionMap (hA.contMDiffOn_trivAt b₀)
        (hA.contMDiffOn_trivAt_symm b₀) _⟩
  choose e he he' hb hω using
    exists_trivialization_mpullback_fiberInclusionMap (A := A) hfp hA h hD
  choose φ hφ using exists_diffeomorph_mpullback_eq hfp hA h hD b₀
  -- The chart at `b` is the radial trivialization at `b`, read in `F` through `φ b`.
  let A' : MapFiber.Atlas F proj :=
    ⟨fun b ↦ (e b).transFiberHomeomorph (φ b).symm.toHomeomorph, hb⟩
  have hA' : A'.IsContMDiff ∞ IB IF IM :=
    ⟨fun b ↦ (e b).contMDiffOn_transFiberHomeomorph_toHomeomorph (he b) _,
      fun b ↦ (e b).contMDiffOn_transFiberHomeomorph_toHomeomorph_symm (he' b) _⟩
  have hτ : A'.RestrictsTo σ τ := MapFiber.Atlas.restrictsTo_iff.2 fun b b' hb' ↦ by
    have hι : MDifferentiable IF IM ((e b).fiberInclusionMap hb') :=
      ((e b).contMDiff_fiberInclusionMap (he' b) hb').mdifferentiable (by simp)
    -- `A'.trivAt b` is the radial chart changed in the fibre, by the definition of `A'`.
    change mpullback IF IM
      ((e b).transFiberHomeomorph (φ b).symm.toHomeomorph |>.fiberInclusionMap hb') τ.val = _
    rw [(e b).coe_fiberInclusionMap_transFiberHomeomorph (φ b).symm.toHomeomorph hb',
      Diffeomorph.coe_toHomeomorph_symm, Diffeomorph.symm_symm,
      mpullback_comp ((φ b).mdifferentiable (by simp)) hι, hω b b' hb',
      hφ b, SmoothForm.coe_mpullback]
  exact ⟨σ, hσ, A', hA', hτ.hasStructureGroup hA', hτ⟩

/-- **Fibrations with symplectic fibres are symplectic fibrations.** Let `A` be a smooth atlas of
`proj : M → B` with model fibre `F`, where `M` is compact and connected, and let `τ` be a
symplectic form on `M` that is nondegenerate on the vertical spaces of `proj`, so that every
fibre is a symplectic submanifold. Then there are a symplectic form `σ` on `F` and a smooth atlas
`A'` of `proj`, compatible with `A`, with structure group the stabilizer of `σ`, along which `τ`
restricts to `σ` on every fibre: a reduction of the structure group of `A` to the symplectomorphisms
of `(F, σ)` that is compatible with `τ`.

Milestone: *Fibrations with symplectic fibres are symplectic fibrations*. -/
theorem exists_hasStructureGroup_restrictsTo [CompactSpace M] [ConnectedSpace M]
    (hA : A.IsContMDiff ∞ IB IF IM) (hτ : τ.IsSymplectic)
    (hnd : IsVerticallyNondegenerate IB proj τ) :
    ∃ σ : SmoothTwoForm IF F, σ.IsSymplectic ∧ ∃ A' : MapFiber.Atlas F proj,
      A'.IsContMDiff ∞ IB IF IM ∧ A.CoordChangeMem A' (⊤ : Subgroup (F ≃ₘ⟮IF, IF⟯ F)) ∧
        A'.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ) ∧ A'.RestrictsTo σ τ := by
  obtain ⟨σ, hσ, A', hA', hH, hR⟩ :=
    exists_hasStructureGroup_restrictsTo_of_isVerticallyClosed hA
      hτ.isClosed.isVerticallyClosed hnd
  exact ⟨σ, hσ, A', hA', MapFiber.Atlas.coordChangeMem_top hA hA', hH, hR⟩

end SmoothTwoForm

namespace MapFiber.Atlas.IsOrientedCompatible

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M] [IM.Boundaryless]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B] [IB.Boundaryless]
  [T2Space B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [FiniteDimensional ℝ EF]
  {HF : Type*} [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF}
  {F : Type*} [TopologicalSpace F] [ChartedSpace HF F] [IsManifold IF ∞ F]
  {proj : M → B} {A : MapFiber.Atlas F proj} {hA : A.IsContMDiff ∞ IB IF IM} {m k : ℕ}
  {oB : TauCeti.Manifold.Orientation IB B (Fin m)} {oF : TauCeti.Manifold.Orientation IF F (Fin k)}
  {τ : SmoothTwoForm IM M}

/-- **Oriented compatible forms give symplectic atlases.** For a compact connected `M` and a form
`τ` compatible with an oriented smooth atlas `A` of `proj`, there are a symplectic form `σ` on the
model fibre and a smooth atlas compatible with `A`, with structure group the stabilizer of `σ`,
along which `τ` restricts to `σ`. -/
theorem exists_hasStructureGroup_restrictsTo (h : A.IsOrientedCompatible hA oB oF τ) :
    ∃ σ : SmoothTwoForm IF F, σ.IsSymplectic ∧ ∃ A' : MapFiber.Atlas F proj,
      A'.IsContMDiff ∞ IB IF IM ∧ A.CoordChangeMem A' (⊤ : Subgroup (F ≃ₘ⟮IF, IF⟯ F)) ∧
        A'.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ) ∧ A'.RestrictsTo σ τ :=
  SmoothTwoForm.exists_hasStructureGroup_restrictsTo hA h.isSymplectic h.isVerticallyNondegenerate

end MapFiber.Atlas.IsOrientedCompatible

end TauCeti

end
