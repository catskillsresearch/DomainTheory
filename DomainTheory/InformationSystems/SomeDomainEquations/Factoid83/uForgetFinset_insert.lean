module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst33
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.UToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst39
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.uForgetFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.mem_uForgetFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

theorem uForgetFinset_insert (u : Finset UToken) (p : UToken) :
    uForgetFinset (insert p u) = insert p.val (uForgetFinset u) := by
  ext t
  constructor
  · intro ht
    rcases (mem_uForgetFinset).1 ht with ⟨q, hq, rfl⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem ((mem_uForgetFinset).2 ⟨q, hq, rfl⟩)
  · intro ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact (mem_uForgetFinset).2 ⟨p, Finset.mem_insert_self p u, rfl⟩
    · rcases (mem_uForgetFinset).1 ht with ⟨q, hq, rfl⟩
      exact (mem_uForgetFinset).2 ⟨q, Finset.mem_insert_of_mem hq, rfl⟩

end InfoSys

end DomainTheory.InformationSystems
