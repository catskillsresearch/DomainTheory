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

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem funion_assoc_lam (a b c : Finset (RawLamToken α)) :
    (a ∪' b) ∪' c = a ∪' (b ∪' c) := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h
    · rcases mem_funion.mp h with h | h
      · exact mem_funion.mpr (Or.inl h)
      · exact mem_funion.mpr (Or.inr (mem_funion.mpr (Or.inl h)))
    · exact mem_funion.mpr (Or.inr (mem_funion.mpr (Or.inr h)))
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inl (mem_funion.mpr (Or.inl h)))
    · rcases mem_funion.mp h with h | h
      · exact mem_funion.mpr (Or.inl (mem_funion.mpr (Or.inr h)))
      · exact mem_funion.mpr (Or.inr h)

end InfoSys

end DomainTheory.InformationSystems
