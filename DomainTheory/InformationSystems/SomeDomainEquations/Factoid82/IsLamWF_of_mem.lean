/-ai
Every member of a depth-consistent finset of raw lambda tokens is well formed.

Bottom and atoms are well formed outright. A function token in the finset is a member of its function-token projection. That projection cannot be empty, so the nonempty function clause of depth consistency supplies depth consistency of both components.
ai-/
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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_of_fun_nonempty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamWF
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst70
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst74

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem IsLamWF_of_mem {u : Finset (RawLamToken α)} (hu : LamConDepth A u)
    {t : RawLamToken α} (ht : t ∈ u) : LamWF A t := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  match t with
  | .bot | .atom _ => exact ⟨trivial⟩
  | .funTok xs ys =>
    have hmem : (xs, ys) ∈ lamFunFinset u := mem_lamFunFinset.2 ht
    by_cases hF : lamFunFinset u = ∅
    · exact False.elim (Finset.notMem_empty _ (hF ▸ hmem))
    · exact ⟨((LamConDepth_of_fun_nonempty A hF).1 hu).2.1 _ hmem⟩

end InfoSys

end DomainTheory.InformationSystems
