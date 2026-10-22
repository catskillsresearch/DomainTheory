module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)


open ApproximableMap


theorem fstMap_pairElements (x : A.Element) (y : B.Element) :
    (fstMap A B).toElement (pairElements A B x y) = x := by
  apply le_antisymm
  · intro a ⟨s, hs, ⟨hCon, _, hEnt⟩⟩
    have hsub : ↑(fstFinset A B s) ⊆ x.carrier := by
      intro b hb
      rcases (mem_fstFinset A B).1 hb with ⟨p, hp, hbot, rfl⟩
      exact (hs (Finset.mem_coe.2 hp)).1 hbot
    exact x.closed _ a hsub (hEnt a (Finset.mem_singleton_self _))
  · intro a ha
    refine ⟨liftLeft A B {a}, ?_, ?_⟩
    · intro p hp
      rcases (mem_liftLeft A B).1 (Finset.mem_coe.1 hp) with ⟨b, hb, rfl⟩
      have : b = a := Finset.mem_singleton.mp hb
      subst this
      exact ⟨fun _ => ha, fun _ => factoid_3_2 B y⟩
    · refine ⟨ProdCon_liftLeft A B (A.con_sing a), A.con_sing a, ?_⟩
      rw [fstFinset_liftLeft]
      exact proposition_2_3_iii A (A.con_sing a)

end InfoSys
end DomainTheory.InformationSystems
