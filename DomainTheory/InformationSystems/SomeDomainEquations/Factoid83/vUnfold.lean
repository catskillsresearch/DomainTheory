module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vSystem

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

def vUnfold (t : VToken) : ProdToken vSystem vSystem :=
  match t with
  | .bot => prodBot vSystem vSystem
  | .top => ⟨(.top, .bot), ⟨Or.inr rfl⟩⟩
  | .pairL x => ⟨(x, .bot), ⟨Or.inr rfl⟩⟩
  | .pairR y => ⟨(.bot, y), ⟨Or.inl rfl⟩⟩

theorem vUnfold.bot : vUnfold .bot = prodBot vSystem vSystem := rfl

theorem vUnfold.pairL (x : VToken) :
    vUnfold (.pairL x) = ⟨(x, .bot), ⟨Or.inr rfl⟩⟩ := rfl

theorem vUnfold.pairR (y : VToken) :
    vUnfold (.pairR y) = ⟨(.bot, y), ⟨Or.inl rfl⟩⟩ := rfl

end InfoSys

end DomainTheory.InformationSystems
