/-ai
When the enumerator is primitive recursive, it is recursively decidable whether some term-algebra code has neighbourhood contained in the intersection of two enumerated neighbourhoods.

Reindex the consistency decision of the universal domain along the primitive recursive evaluation of the two unpaired components. A witnessing code evaluates to a witnessing index. Conversely, the node code of the two components is a witness: evaluation at a node is the universal intersection of the two evaluations, and the intersection specification of the universal domain applies to the evaluated witness.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nodeCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.primrec_TreeVal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal_node
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2X
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

/-- **`cons_computable` for `Q2X r`.** The crux resolved by the term algebra: the backward
direction's witness is `nodeCode n m`, no search needed to *name* it, and it works because
`Uinter_spec` applies exactly when consistency holds. -/
theorem Q2_cons_computable (hr : Nat.Primrec r) :
    RecDecidable₂ (fun n m => ∃ k, Q2X r k ⊆ Q2X r n ∩ Q2X r m) := by
  have hTV := primrec_TreeVal r hr
  have hreindex : Nat.Primrec (fun t : ℕ => Nat.pair (TreeVal r t.unpair.1) (TreeVal r t.unpair.2)) :=
    (hTV.comp Nat.Primrec.left).pair (hTV.comp Nat.Primrec.right)
  refine RecDecidable.of_iff (fun t => ?_) (U_cons_computable.comp hreindex)
  simp only [unpair_pair_fst, unpair_pair_snd]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨TreeVal r k, hk⟩
  · rintro ⟨k, hk⟩
    refine ⟨nodeCode t.unpair.1 t.unpair.2, ?_⟩
    show UX (TreeVal r (nodeCode t.unpair.1 t.unpair.2)) ⊆
      UX (TreeVal r t.unpair.1) ∩ UX (TreeVal r t.unpair.2)
    rw [TreeVal_node, Uinter_spec ⟨k, hk⟩]

end TreeVal2

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems
