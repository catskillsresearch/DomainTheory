module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.fromAA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.aaEquiv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.slot_list_inj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.slotPre_inj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_embTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.nil_not_mem_embTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_ne_univ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_inter_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.memA_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.tag_eq_of_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.memA_tuple_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.memA_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Apow
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.apowNe
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.AAsys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.apow_mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.apow_mem_prodN_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.aa_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.aa_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.aa_mem_inj₀_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.aa_mem_inj₁_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.aa_mem_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.fromAA_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.fromAA_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.fromAA_toAA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA_fromAA

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB


variable {β : Type*} {n : ℕ}


variable {n : ℕ}


/-- **Example 6.2 (Scott 1981, PRG-19) — the domain equation `A ≅ Aⁿ + Aⁿ`.** Scott's "simple, yet
interesting generalization of `B`": the domain `A` over `{0,1}*` (whose non-`⊥` elements are the two
copies — left `−` and right `+` — of an `n`-tuple of elements of `A`) is isomorphic to the separated
sum `Aⁿ + Aⁿ` of two copies of its own `n`-fold cartesian power. -/
theorem A_domain_equation (hn : 0 < n) : Asys n hn ≅ᴰ AAsys hn := ⟨aaEquiv hn⟩

end Example62A
end DomainTheory.NeighbourhoodSystems
