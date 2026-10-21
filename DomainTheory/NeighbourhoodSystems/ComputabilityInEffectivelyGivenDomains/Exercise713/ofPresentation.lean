/-ai
The inclusion structure of a computable presentation takes inclusion of enumerated neighbourhoods as its relation, the presentation's intersection function as its meet, and the presentation's master index as its greatest code. Inclusion is the presentation's decidable inclusion. Consistency is the presentation's decidable consistency, transported across the equivalence of joint inclusion with inclusion in the intersection. The meet condition is the presentation's decidable intersection-equality, transported across the equivalence of the meet condition with equality of an intersection. Reflexivity and transitivity are those of containment. Every enumerated neighbourhood is contained in the master, because the master index enumerates the master and every neighbourhood is contained in the master. On a consistent pair, containment in the intersection neighbourhood is joint containment, by the intersection specification.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.InclStructure
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.mem_toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toSystem_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.meet_iff_interEq

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {V : NeighborhoodSystem α}

/-- **Exercise 7.13 (⇒) — every effectively given domain is an `INCL` relation.** Given a computable
presentation `P` of `V`, set `INCL(n, m) := Xₙ ⊆ Xₘ`. Reflexivity/transitivity are those of `⊆`; the
master code is `P.masterIdx` (`Xₙ ⊆ master`); the meet function is `P.inter`. `INCL`/`CONS` decidability
are `P.incl_computable`/`P.cons_computable`; `MEET` decidability is `meet_iff_interEq` ∘
`P.interEq_computable`. -/
def ofPresentation (P : ComputablePresentation V) : InclStructure where
  INCL n m := P.X n ⊆ P.X m
  meetIdx := P.inter
  topIdx := P.masterIdx
  incl_dec := P.incl_computable
  cons_dec :=
    RecDecidable.of_iff
      (fun t => by
        refine exists_congr fun k => ?_
        exact (Set.subset_inter_iff).symm)
      P.cons_computable
  meet_dec :=
    RecDecidable.of_iff
      (fun t => meet_iff_interEq P t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2)
      P.interEq_computable
  meetIdx_primrec := P.inter_primrec
  incl_refl := fun _ => subset_rfl
  incl_trans := fun h1 h2 => h1.trans h2
  topIdx_spec := by
    intro n
    show P.X n ⊆ P.X P.masterIdx
    rw [P.masterIdx_spec]
    exact V.sub_master (P.mem_X n)
  meetIdx_spec := by
    intro n m hcons j
    obtain ⟨k, h1, h2⟩ := hcons
    have hcons' : ∃ k, P.X k ⊆ P.X n ∩ P.X m := ⟨k, Set.subset_inter h1 h2⟩
    show P.X j ⊆ P.X (P.inter n m) ↔ _
    rw [P.inter_spec hcons', Set.subset_inter_iff]

end DomainTheory.NeighbourhoodSystems.Exercise713
