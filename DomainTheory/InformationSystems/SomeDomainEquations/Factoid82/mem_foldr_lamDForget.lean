module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst70
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamDForgetInsert
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst74

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem mem_foldr_lamDForget (s : Multiset (LamDToken A)) (t : RawLamToken α) :
    t ∈ Multiset.foldr (lamDForgetInsert (A := A)) ∅ s ↔ ∃ p ∈ s, p.val = t := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro ht; exact False.elim (Finset.notMem_empty t ht)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro p rest ih
    simp only [Multiset.foldr_cons, lamDForgetInsert, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (rfl | ⟨q, hq, hq'⟩)
      · exact ⟨p, Or.inl rfl, rfl⟩
      · exact ⟨q, Or.inr hq, hq'⟩
    · rintro ⟨q, hq, hq'⟩
      rcases hq with rfl | hq
      · exact Or.inl hq'.symm
      · exact Or.inr ⟨q, hq, hq'⟩

end InfoSys

end DomainTheory.InformationSystems
