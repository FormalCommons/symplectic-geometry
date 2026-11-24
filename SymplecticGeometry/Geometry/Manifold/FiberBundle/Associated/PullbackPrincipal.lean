/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Associated.Basic
public import TauCeti.Geometry.Manifold.FiberBundle.Pullback.Basic
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Basic

/-!
# The product `P × F` as the pull-back of `P` to `P ×_G F`

Let `P` be a principal `G`-bundle over `B`, let `G` act on the left on a manifold `F`, and let
`M = P ×_G F` be the associated bundle, with charted total space
`TauCeti.ManifoldTotalSpace F (AssociatedBundle G P F)` and projection `π_M : M → B`. The
pull-back `Q = π_M^* P` is a principal `G`-bundle over `M`, whose fibre over `[x, v]` is the fibre
of `P` through `x`. The map `Φ (x, v) = ([x, v], x)` identifies `P × F` with the total space of `Q`:
the class `[x, v]` and the point `y = x` of its fibre recover `v` as the unique `w` with
`[y, w] = [x, v]`. Under `Φ`, the projection of `Q` becomes the quotient map `q (x, v) = [x, v]`,
and the principal action of `G` on `Q` becomes the diagonal action `(x, v) · g = (x · g, g⁻¹ v)`.

## Main definitions and results

* `TauCeti.AssociatedBundle.pullbackProjDiffeomorph`: the `C^n` diffeomorphism `Φ` from
  `ManifoldTotalSpace G P × F` onto the charted total space of `Q`.
* `TauCeti.AssociatedBundle.pullbackProjDiffeomorph_apply` and
  `TauCeti.AssociatedBundle.pullbackProjDiffeomorph_symm_apply`: `Φ` and its inverse on points.
* `TauCeti.AssociatedBundle.proj_pullbackProjDiffeomorph`: `π_Q ∘ Φ = q`.
* `TauCeti.AssociatedBundle.pullbackProjDiffeomorph_smul`: `Φ` is equivariant for the diagonal
  action on the source and the principal action on the target.

## Implementation notes

The fibre of `Q` over `Φ (x, v)` is that of `P` over the projection of `[x, v]`, which is the base
point of `x` only up to an equation (`TauCeti.ManifoldTotalSpace.homeomorph` does not unfold), so
`Φ` transports `x` along it. The inverse is smooth since, in the trivialization `e` of `P` at the
base point, the `w` with `[y, w] = m` is `(e y)₂⁻¹ • (e_M m)₂` for the corresponding chart `e_M`
of `M` (`TauCeti.AssociatedBundle.trivializationAt_mk_snd`); the forward map is smooth by the
universal property of the pull-back (`TauCeti.ManifoldTotalSpace.contMDiff_pullback_iff`).

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter I, §5 (associated bundles).
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.3.
-/

public section

noncomputable section

open Bundle MulOpposite TauCeti
open scoped Manifold ContDiff

namespace TauCeti.AssociatedBundle

variable {n : ℕ∞ω} {𝕜 B G F : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners 𝕜 EG HG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} [TopologicalSpace F] [ChartedSpace HF F] [MulAction G F]
  [ContinuousSMul G F]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

/-- The projection `π_M` of the associated bundle, as a `C^n` map. -/
local notation "πM" => ManifoldTotalSpace.projContMDiffMap n F (AssociatedBundle G P F) IB IF

/-- The pull-back `Q = π_M^* P` of `P` to the associated bundle. -/
local notation "Q" => (πM : ManifoldTotalSpace F (AssociatedBundle G P F) → B) *ᵖ P

/-- The point `([x, v], x)` of the total space of `Q`, before transport to its charted copy. -/
def pullbackProjMk (x : ManifoldTotalSpace G P × F) : TotalSpace G Q :=
  ⟨ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)
    ⟨((ManifoldTotalSpace.homeomorph G P).symm x.1).proj,
      mk G ((ManifoldTotalSpace.homeomorph G P).symm x.1).snd x.2⟩,
    cast (congrArg P (by simp)) ((ManifoldTotalSpace.homeomorph G P).symm x.1).snd⟩

/-- The projection of `([x, v], x)` is the class `[x, v]`. -/
theorem pullbackProjMk_proj (x : ManifoldTotalSpace G P × F) :
    (pullbackProjMk (n := n) (IB := IB) (IF := IF) x).proj =
      ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)
        ⟨((ManifoldTotalSpace.homeomorph G P).symm x.1).proj,
          mk G ((ManifoldTotalSpace.homeomorph G P).symm x.1).snd x.2⟩ := (rfl)

/-- The image of `([x, v], x)` in the total space of `P` is `x`. -/
theorem lift_pullbackProjMk (x : ManifoldTotalSpace G P × F) :
    Pullback.lift πM (pullbackProjMk (n := n) (IB := IB) (IF := IF) x) =
      (ManifoldTotalSpace.homeomorph G P).symm x.1 := by
  refine (Pullback.lift_mk _ _ _).trans ?_
  exact (TotalSpace.mk_cast (by simp) _).trans (TotalSpace.eta _)

/-- For a point `(m, y)` of the total space of `Q`, the unique `w : F` with `[y, w] = m`. -/
def pullbackProjFiber (z : TotalSpace G Q) : F :=
  (Equiv.ofBijective _ (mk_bijective (F := F) (G := G) (Pullback.lift πM z).snd)).symm
    ((ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm z.proj).snd

/-- `pullbackProjFiber z` is the `w` with `[y, w] = m`, for `z = (m, y)`. -/
theorem pullbackProjFiber_eq_iff (z : TotalSpace G Q) (w : F) :
    pullbackProjFiber z = w ↔
      (ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm z.proj =
        ⟨(Pullback.lift πM z).proj, mk G (Pullback.lift πM z).snd w⟩ :=
  (Equiv.symm_apply_eq _).trans <| eq_comm.trans <| TotalSpace.mk_inj.symm.trans <|
    eq_comm.trans Iff.rfl

/-- In the trivialization `e` of `P` at a point `b₀`, over its base set, the `w` with
`[y, w] = m` is `(e y)₂⁻¹ • (e_M m)₂`, for the chart `e_M` of the associated bundle at `b₀`. -/
theorem pullbackProjFiber_eq_of_mem_baseSet (z : TotalSpace G Q) {b₀ : B}
    (hb : πM z.proj ∈ (trivializationAt G P b₀).baseSet) :
    pullbackProjFiber z = ((trivializationAt G P b₀ (Pullback.lift πM z)).2)⁻¹ •
      (trivializationAt F (AssociatedBundle G P F) b₀
        ((ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm z.proj)).2 := by
  have hb' : (Pullback.lift πM z).proj ∈ (trivializationAt G P b₀).baseSet := hb
  rw [(pullbackProjFiber_eq_iff z _).1 rfl, trivializationAt_mk_snd hb', TotalSpace.eta,
    inv_smul_smul]

variable [∀ b, Nonempty (P b)] [LieGroup IG n G] [ContMDiffSMul IG IF n G F]

variable (n IB IG IF) in
/-- **`P × F` is the pull-back of `P` to the associated bundle.** The `C^n` diffeomorphism
`(x, v) ↦ ([x, v], x)` from `P × F` onto the total space of the pull-back `Q = π_M^* P` of `P` to
`M = P ×_G F`. -/
def pullbackProjDiffeomorph :
    (ManifoldTotalSpace G P × F) ≃ₘ^n⟮(IB.prod IG).prod IF, (IB.prod IF).prod IG⟯
      ManifoldTotalSpace G Q where
  toFun x := ManifoldTotalSpace.homeomorph G Q (pullbackProjMk x)
  invFun z :=
    (ManifoldTotalSpace.homeomorph G P
        (Pullback.lift πM ((ManifoldTotalSpace.homeomorph G Q).symm z)),
      pullbackProjFiber ((ManifoldTotalSpace.homeomorph G Q).symm z))
  left_inv x := by
    refine Prod.ext ?_ ?_
    · simp [lift_pullbackProjMk]
    · refine (pullbackProjFiber_eq_iff _ _).2 ?_
      rw [Homeomorph.symm_apply_apply, lift_pullbackProjMk, pullbackProjMk_proj,
        Homeomorph.symm_apply_apply]
  right_inv z := by
    obtain ⟨y, rfl⟩ := (ManifoldTotalSpace.homeomorph G Q).surjective z
    simp only [Homeomorph.symm_apply_apply]
    congr 1
    refine Pullback.totalSpace_ext ?_ ?_
    · rw [pullbackProjMk_proj, Homeomorph.symm_apply_apply,
        ← (pullbackProjFiber_eq_iff y _).1 rfl, Homeomorph.apply_symm_apply]
    · rw [lift_pullbackProjMk, Homeomorph.symm_apply_apply]
  contMDiff_toFun := by
    refine (ManifoldTotalSpace.contMDiff_pullback_iff πM (πM).contMDiff).2 ⟨?_, ?_⟩
    · exact contMDiff_totalSpaceMk_mk n G F IB IG IF P
    · simp only [lift_pullbackProjMk, Homeomorph.apply_symm_apply]
      exact contMDiff_fst
  contMDiff_invFun := by
    refine (ManifoldTotalSpace.contMDiff_pullbackLift n IG πM (πM).contMDiff).prodMk fun z₀ ↦ ?_
    set y₀ := (ManifoldTotalSpace.homeomorph G Q).symm z₀
    set b₀ := πM y₀.proj
    have hproj : ContMDiff ((IB.prod IF).prod IG) IB n
        fun z ↦ πM ((ManifoldTotalSpace.homeomorph G Q).symm z).proj :=
      (πM).contMDiff.comp (ManifoldTotalSpace.contMDiff_proj n G Q (IB.prod IF) IG)
    -- The coordinate of the point of `P`, in the trivialization of `P` at `b₀`.
    have hP := (ManifoldTotalSpace.contMDiffAt_trivializationAt_snd n IB IG
      (ManifoldTotalSpace.homeomorph G P (Pullback.lift πM y₀))).comp z₀
      (ManifoldTotalSpace.contMDiff_pullbackLift n IG πM (πM).contMDiff z₀)
    -- The coordinate of the point of `M`, in the trivialization of `M` at `b₀`.
    have hM := (ManifoldTotalSpace.contMDiffAt_trivializationAt_snd n IB IF y₀.proj).comp z₀
      (ManifoldTotalSpace.contMDiff_proj n G Q (IB.prod IF) IG z₀)
    simp only [Function.comp_def, Homeomorph.symm_apply_apply, Pullback.lift_proj] at hP hM
    refine (hP.inv.smul hM).congr_of_eventuallyEq ?_
    filter_upwards [hproj.continuous.continuousAt.preimage_mem_nhds
      ((trivializationAt G P b₀).open_baseSet.mem_nhds (mem_baseSet_trivializationAt G P b₀))]
      with z hz
    exact pullbackProjFiber_eq_of_mem_baseSet _ hz

/-- `Φ (x, v)` is the point `([x, v], x)`. -/
theorem pullbackProjDiffeomorph_apply (x : ManifoldTotalSpace G P × F) :
    pullbackProjDiffeomorph n IB IG IF x =
      ManifoldTotalSpace.homeomorph G Q (pullbackProjMk x) := (rfl)

/-- The inverse of `Φ` sends `(m, y)` to `(y, w)` with `[y, w] = m`. -/
theorem pullbackProjDiffeomorph_symm_apply (z : ManifoldTotalSpace G Q) :
    (pullbackProjDiffeomorph n IB IG IF).symm z =
      (ManifoldTotalSpace.homeomorph G P
          (Pullback.lift πM ((ManifoldTotalSpace.homeomorph G Q).symm z)),
        pullbackProjFiber ((ManifoldTotalSpace.homeomorph G Q).symm z)) := (rfl)

/-- **The projection of `Q` composed with `Φ` is the quotient map** `(x, v) ↦ [x, v]`. -/
theorem proj_pullbackProjDiffeomorph :
    (fun z : ManifoldTotalSpace G Q ↦ ((ManifoldTotalSpace.homeomorph G Q).symm z).proj) ∘
        pullbackProjDiffeomorph n IB IG IF =
      fun x : ManifoldTotalSpace G P × F ↦
        ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)
          ⟨((ManifoldTotalSpace.homeomorph G P).symm x.1).proj,
            mk G ((ManifoldTotalSpace.homeomorph G P).symm x.1).snd x.2⟩ := by
  funext x
  rw [Function.comp_apply, pullbackProjDiffeomorph_apply, Homeomorph.symm_apply_apply,
    pullbackProjMk_proj]

/-- **`Φ` is equivariant**, for the diagonal action `(x, v) · g = (x · g, g⁻¹ • v)` on
`P × F` and the principal action on `Q`. -/
theorem pullbackProjDiffeomorph_smul (g : G) (x : ManifoldTotalSpace G P × F) :
    pullbackProjDiffeomorph n IB IG IF (op g • x.1, g⁻¹ • x.2) =
      op g • pullbackProjDiffeomorph n IB IG IF x := by
  rw [pullbackProjDiffeomorph_apply, pullbackProjDiffeomorph_apply,
    ManifoldTotalSpace.smul_homeomorph]
  congr 1
  refine Pullback.totalSpace_ext ?_ ?_
  · rw [pullbackProjMk_proj, pullbackProjMk_proj, ManifoldTotalSpace.homeomorph_symm_smul,
      mk_smul_inv_smul]
  · rw [lift_pullbackProjMk, ManifoldTotalSpace.homeomorph_symm_smul]
    -- `Pullback.lift` of a point `⟨m, s⟩` is `⟨πM m, s⟩` by definition; `Pullback.lift_mk` does not
    -- rewrite here, since the fibre of `Q` is not reducibly that of `P`.
    exact congrArg (fun y : TotalSpace G P ↦ (⟨y.proj, op g • y.snd⟩ : TotalSpace G P))
      (lift_pullbackProjMk x).symm

end TauCeti.AssociatedBundle
