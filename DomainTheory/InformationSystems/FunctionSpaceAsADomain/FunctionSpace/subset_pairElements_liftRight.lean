module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.pairElements
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.liftRight
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.sndMap_pairElements

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

theorem subset_pairElements_liftRight {x : A.Element} {y : B.Element}
    {v : Finset β} (hv : ↑v ⊆ y.carrier) :
    ↑(liftRight A B v) ⊆ (pairElements A B x y).carrier := by
  intro p hp
  rcases (liftRight.mem A B).1 (Finset.mem_coe.1 hp) with ⟨b, hb, rfl⟩
  have hby : b ∈ y.carrier := hv (Finset.mem_coe.2 hb)
  have : b ∈ ((productSystem.sndMap A B).toElement (pairElements A B x y)).carrier := by
    simpa [sndMap_pairElements] using hby
  rcases this with ⟨s, hs, ⟨hCon, _, hEnt⟩⟩
  exact (pairElements A B x y).closed s (mkRight A B b) hs ⟨hCon,
    fun _ => A.ent_bot hCon.1,
    fun _ => hEnt b (Finset.mem_singleton_self _)⟩

end InfoSys
end DomainTheory.InformationSystems
