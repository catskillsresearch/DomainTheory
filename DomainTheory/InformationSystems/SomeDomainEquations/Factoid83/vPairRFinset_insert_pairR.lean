module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.mem_vPairRFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

theorem vPairRFinset_insert_pairR (u : Finset VToken) (t : VToken) :
    vPairRFinset (insert (.pairR t) u) = insert t (vPairRFinset u) := by
  ext s; simp only [Finset.mem_insert, mem_vPairRFinset]
  constructor
  · rintro (h | h)
    · exact Or.inl (VToken.pairR.inj h)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

end InfoSys

end DomainTheory.InformationSystems
