module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst33
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.UToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.uForgetInsert
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst39
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.mem_foldr_uForget

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
def uForgetFinset (u : Finset UToken) : Finset VToken :=
  Multiset.foldr uForgetInsert ∅ u.1

theorem mem_uForgetFinset {u : Finset UToken} {t : VToken} :
    t ∈ uForgetFinset u ↔ ∃ p ∈ u, p.val = t := by
  simpa [uForgetFinset] using mem_foldr_uForget u.1 t

theorem uForgetFinset.empty : uForgetFinset (∅ : Finset UToken) = ∅ := rfl

theorem uForgetFinset.insert (u : Finset UToken) (p : UToken) :
    uForgetFinset (Insert.insert p u) = Insert.insert p.val (uForgetFinset u) := by
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

theorem uForgetFinset.mono {u v : Finset UToken} (h : v ⊆ u) :
    uForgetFinset v ⊆ uForgetFinset u := by
  intro t ht
  rcases (mem_uForgetFinset).1 ht with ⟨p, hp, rfl⟩
  exact (mem_uForgetFinset).2 ⟨p, h hp, rfl⟩

theorem uForgetFinset.singleton (p : UToken) :
    uForgetFinset {p} = {p.val} := by
  ext t
  constructor
  · intro ht
    rcases (mem_uForgetFinset).1 ht with ⟨q, hq, hq'⟩
    have : q = p := Finset.mem_singleton.mp hq
    subst this; exact Finset.mem_singleton.mpr hq'.symm
  · intro ht
    exact (mem_uForgetFinset).2
      ⟨p, Finset.mem_singleton_self p, (Finset.mem_singleton.mp ht).symm⟩

end InfoSys

end DomainTheory.InformationSystems
