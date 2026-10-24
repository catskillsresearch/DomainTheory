module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst70
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamDForgetInsert
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst74
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_foldr_lamDForget

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]
variable (A : InfoSys α)

def lamDForgetFinset (u : Finset (LamDToken A)) : Finset (RawLamToken α) :=
  Multiset.foldr (lamDForgetInsert (A := A)) ∅ u.1

theorem mem_lamDForgetFinset {u : Finset (LamDToken A)} {t : RawLamToken α} :
    t ∈ lamDForgetFinset A u ↔ ∃ p ∈ u, p.val = t := by
  simpa [lamDForgetFinset] using mem_foldr_lamDForget A u.1 t

theorem lamDForgetFinset.insert (u : Finset (LamDToken A)) (p : LamDToken A) :
    lamDForgetFinset A (Insert.insert p u) = Insert.insert p.val (lamDForgetFinset A u) := by
  ext t
  constructor
  · intro ht
    rcases (mem_lamDForgetFinset A).1 ht with ⟨q, hq, rfl⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem ((mem_lamDForgetFinset A).2 ⟨q, hq, rfl⟩)
  · intro ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact (mem_lamDForgetFinset A).2 ⟨p, Finset.mem_insert_self p u, rfl⟩
    · rcases (mem_lamDForgetFinset A).1 ht with ⟨q, hq, rfl⟩
      exact (mem_lamDForgetFinset A).2 ⟨q, Finset.mem_insert_of_mem hq, rfl⟩

theorem lamDForgetFinset.mono {u v : Finset (LamDToken A)} (h : v ⊆ u) :
    lamDForgetFinset A v ⊆ lamDForgetFinset A u := by
  intro t ht
  rcases (mem_lamDForgetFinset A).1 ht with ⟨p, hp, rfl⟩
  exact (mem_lamDForgetFinset A).2 ⟨p, h hp, rfl⟩

theorem lamDForgetFinset.singleton (p : LamDToken A) :
    lamDForgetFinset A {p} = {p.val} := by
  ext t
  constructor
  · intro ht
    rcases (mem_lamDForgetFinset A).1 ht with ⟨q, hq, hq'⟩
    have : q = p := Finset.mem_singleton.mp hq
    subst this; exact Finset.mem_singleton.mpr hq'.symm
  · intro ht
    exact (mem_lamDForgetFinset A).2
      ⟨p, Finset.mem_singleton_self p, (Finset.mem_singleton.mp ht).symm⟩

end InfoSys


end DomainTheory.InformationSystems
