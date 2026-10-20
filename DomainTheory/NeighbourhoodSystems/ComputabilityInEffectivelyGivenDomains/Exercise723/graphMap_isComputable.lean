/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.mem_bitsCodeList
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.graphIdx_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.compl_nbhd_subset_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.graphMap_rel_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)










































































/-- **`graph` is computable (Exercise 7.23, dually to `gMap`).** Relative to *any* valid
function-space presentation `funPresentation PNpres PNpres gN incl0 incl1 eq1 …`, `graphMap`'s
neighbourhood relation reduces (via `graphMap_rel_iff`) to a bounded `∀ j < m`, r.e. by
`graphIdx_isComputable`/`REPred.forall_mem_decodeList₂` (the bound enumerated by `bitsCode m m`,
`mem_bitsCodeList`). -/
theorem graphMap_isComputable (gN incl0 incl1 eq1 : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf PNpres PNpres (decodeList c))
      : Set (ApproximableMap PN PN)).Nonempty) (hgNp : Nat.Primrec gN)
    (hincl0 : ∀ s, incl0 s = 1 ↔ PNpres.X s.unpair.1 ⊆ PNpres.X s.unpair.2)
    (hincl0p : Nat.Primrec incl0)
    (hincl1 : ∀ s, incl1 s = 1 ↔ PNpres.X s.unpair.1 ⊆ PNpres.X s.unpair.2)
    (hincl1p : Nat.Primrec incl1)
    (heq1 : ∀ s, eq1 s = 1 ↔ PNpres.X s.unpair.1 = PNpres.X s.unpair.2) (heq1p : Nat.Primrec eq1) :
    IsComputableMap
      (funPresentation PNpres PNpres gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p hincl1 hincl1p
        heq1 heq1p)
      PNpres graphMap := by
  have hidx := graphIdx_isComputable gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p hincl1 hincl1p
    heq1 heq1p
  have hforall : REPred (fun t : ℕ => ∀ j ∈ decodeList t.unpair.2,
      j ∈ GraphIdx (Xenum PNpres PNpres gN t.unpair.1 : Set (ApproximableMap PN PN))) :=
    REPred.forall_mem_decodeList₂ hidx
  have hreidx : Nat.Primrec (fun s : ℕ => Nat.pair s.unpair.1 (bitsCode s.unpair.2 s.unpair.2)) :=
    Nat.Primrec.left.pair ((primrec_bitsCode.comp (Nat.Primrec.right.pair
      Nat.Primrec.right)).of_eq fun s => by simp only [unpair_pair_fst, unpair_pair_snd])
  refine REPred.of_iff (fun s => ?_) (hforall.comp hreidx)
  simp only [unpair_pair_fst, unpair_pair_snd]
  exact (graphMap_rel_iff gN hgN s.unpair.1 s.unpair.2).trans (by
    rw [compl_nbhd_subset_iff]
    exact ⟨fun h j hj => h j (lt_of_testBit_true (mem_bitsCodeList.mp hj))
        (mem_bitsCodeList.mp hj),
      fun h j hjlt hjbit => h j (mem_bitsCodeList.mpr hjbit)⟩)

end DomainTheory.NeighbourhoodSystems.Exercise723
