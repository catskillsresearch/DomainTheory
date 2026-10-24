module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst33
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.UToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst39
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.uForgetFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.UCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.uBot

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
/-- Entailment for `U` (Scott (10)). -/
def UEnt (u : Finset UToken) (p : UToken) : Prop :=
  UCon u ∧ VEnt (uForgetFinset u) p.val

theorem UEnt.bot {u : Finset UToken} (hu : UCon u) : UEnt u uBot :=
  ⟨hu, VEnt.bot⟩

theorem UEnt.of_mem {u : Finset UToken} {p : UToken}
    (hu : UCon u) (hp : p ∈ u) : UEnt u p :=
  ⟨hu, VEnt.of_mem ((mem_uForgetFinset).2 ⟨p, hp, rfl⟩)⟩

theorem UEnt.trans {u v : Finset UToken} {c : UToken}
    (hv : UCon v) (_hu : UCon u)
    (hEnts : ∀ y ∈ u, UEnt v y) (h : UEnt u c) : UEnt v c :=
  ⟨hv, VEnt.trans
    (fun y hy => by
      rcases (mem_uForgetFinset).1 hy with ⟨p, hp, rfl⟩
      exact (hEnts p hp).2)
    h.2⟩

end InfoSys


end DomainTheory.InformationSystems
