/-ai
When the enumerator is primitive recursive, it is recursively decidable whether the intersection of two enumerated neighbourhoods equals a third.

Reindex the intersection-equality decision of the universal domain along the primitive recursive evaluation of the three unpaired components. After the pairing is unpacked, the two predicates agree.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.primrec_TreeVal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2X
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

/-- **`interEq_computable` for `Q2X r`.** A pure reindexing of `U`'s own `U_interEq_computable`
along the primitive-recursive `TreeVal r` — exactly `ComputablePresentation.reindexInvolutive`'s
`interEq_computable` proof pattern, minus the involution (only needed there for the `masterIdx`/
`inter` fields, not for `.comp`-reindexing a `RecDecidable`). -/
theorem Q2_interEq_computable (hr : Nat.Primrec r) :
    RecDecidable₃ (fun n m k => Q2X r n ∩ Q2X r m = Q2X r k) := by
  have hTV := primrec_TreeVal r hr
  have hreindex : Nat.Primrec (fun t : ℕ => Nat.pair (TreeVal r t.unpair.1)
      (Nat.pair (TreeVal r t.unpair.2.unpair.1) (TreeVal r t.unpair.2.unpair.2))) :=
    (hTV.comp Nat.Primrec.left).pair
      ((hTV.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
        (hTV.comp (Nat.Primrec.right.comp Nat.Primrec.right)))
  refine RecDecidable.of_iff (fun t => ?_) (U_interEq_computable.comp hreindex)
  simp only [unpair_pair_fst, unpair_pair_snd]
  rfl

end TreeVal2

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems
