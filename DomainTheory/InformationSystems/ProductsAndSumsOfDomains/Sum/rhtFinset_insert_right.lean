/-ai
Inserting the right token of an element into a finite set of sum tokens adjoins that element to the right projection.

By extensionality, a right token in the inserted set is either the inserted right token, and the right constructor is injective, or a right token of the original set. Conversely, the inserted element is recovered as that right token, and an element of the original right projection is a right token of the original set.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instDecidableEqSumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeLftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeRhtInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.mem_rhtFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem rhtFinset_insert_right (u : Finset (SumToken α β)) (y : β) :
    rhtFinset (insert (.right y) u) = insert y (rhtFinset u) := by
  ext z
  constructor
  · intro hz
    have : SumToken.right z ∈ insert (.right y) u := (mem_rhtFinset).1 hz
    rcases Finset.mem_insert.mp this with h | h
    · injection h with hz'
      exact Finset.mem_insert.mpr (Or.inl hz')
    · exact Finset.mem_insert.mpr (Or.inr ((mem_rhtFinset).2 h))
  · intro hz
    rcases Finset.mem_insert.mp hz with hz' | hz'
    · exact (mem_rhtFinset).2 (Finset.mem_insert.mpr (Or.inl (congrArg SumToken.right hz')))
    · exact (mem_rhtFinset).2 (Finset.mem_insert.mpr (Or.inr ((mem_rhtFinset).1 hz')))

end InfoSys

end DomainTheory.InformationSystems
