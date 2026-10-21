/-ai
Every set in the term-algebra enumeration is a neighbourhood of the subsystem.

Proceed by strong induction on the code, and split on its tag. If the tag is zero, evaluation applies the enumerator to the payload, and the range specification says that this value is a neighbourhood. If the tag is one, both children are strictly smaller, so the inductive hypothesis supplies membership of both. The dichotomy of the universal intersection either returns the master neighbourhood or returns the intersection; in the latter case the witnessing index lists are appended, the element is closed under intersection, and the partial meet of an appended list is the intersection of the two partial meets. If the tag is at least two, evaluation is the master index, whose universal neighbourhood is the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nbhdGen_inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.interFrom_append_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.toSubsystemSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.UX_Uinter_dichotomy
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.unpair_snd_lt_of_unpair_fst_pos
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal_of_tag0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal_of_tag1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal_of_tag_ge2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2X
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

/-- **`mem_X` for `Q2X r`.** Every `Q2X r c` is a `D'x`-neighbourhood — by strong induction on the
code `c`, splitting on its tag exactly as `TreeVal` itself does: tag `0` (leaf) is
`D'x.mem (UX (r j))`, always true by `hspec` (witness `j` itself); tag `1` (node) combines the two
(inductively already-`D'x.mem`) children via `Uinter`'s dichotomy (`UX_Uinter_dichotomy`), landing on
`D'x.master_mem` on fallback or on `x`'s own filter closure (`nbhdGen_inter`/`interFrom_append_eq`,
exactly as in `toSubsystemSys_mem_foldl_Uinter`) otherwise; tag `≥ 2` (master) is `D'x.master_mem`
directly via `masterIdx_spec`. -/
theorem Q2x_mem_X (hspec : ∀ i, (toSubsystemSys UComputablePresentation x).mem (UX i) ↔ ∃ n, r n = i) :
    ∀ c, (toSubsystemSys UComputablePresentation x).mem (Q2X r c) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    show (toSubsystemSys UComputablePresentation x).mem (UX (TreeVal r c))
    rcases Nat.lt_or_ge c.unpair.1 2 with htag | htag
    · have htag01 : c.unpair.1 = 0 ∨ c.unpair.1 = 1 := by omega
      rcases htag01 with htagv | htagv
      · rw [TreeVal_of_tag0 r htagv]
        exact (hspec (r c.unpair.2)).mpr ⟨c.unpair.2, rfl⟩
      · rw [TreeVal_of_tag1 r htagv]
        have hsndlt : c.unpair.2 < c := unpair_snd_lt_of_unpair_fst_pos (by omega)
        have ht1 : c.unpair.2.unpair.1 < c := lt_of_le_of_lt (unpair_left_le c.unpair.2) hsndlt
        have ht2 : c.unpair.2.unpair.2 < c := lt_of_le_of_lt (unpair_snd_le c.unpair.2) hsndlt
        have hm1 := ih c.unpair.2.unpair.1 ht1
        have hm2 := ih c.unpair.2.unpair.2 ht2
        unfold Q2X at hm1 hm2
        rcases UX_Uinter_dichotomy (TreeVal r c.unpair.2.unpair.1) (TreeVal r c.unpair.2.unpair.2)
          with hcase | hcase
        · rw [hcase]; exact (toSubsystemSys UComputablePresentation x).master_mem
        · rw [hcase]
          obtain ⟨jsA, hxA, subA, hsubA, hDA, hAeq⟩ := hm1
          obtain ⟨jsB, hxB, subB, hsubB, hDB, hBeq⟩ := hm2
          have hUmem : U.mem (UX (TreeVal r c.unpair.2.unpair.1) ∩ UX (TreeVal r c.unpair.2.unpair.2)) :=
            hcase ▸ U_mem_UX (Uinter (TreeVal r c.unpair.2.unpair.1) (TreeVal r c.unpair.2.unpair.2))
          refine ⟨jsA ++ jsB, nbhdGen_inter UComputablePresentation jsA jsB ▸ x.inter_mem hxA hxB,
            subA ++ subB, hsubA.append hsubB, hUmem, ?_⟩
          rw [hAeq, hBeq, interFrom_append_eq UComputablePresentation U.master subA subB]
    · rw [TreeVal_of_tag_ge2 r htag]
      show (toSubsystemSys UComputablePresentation x).mem (UX UmasterIdx)
      rw [UX_UmasterIdx]
      exact (toSubsystemSys UComputablePresentation x).master_mem

end TreeVal2

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems
