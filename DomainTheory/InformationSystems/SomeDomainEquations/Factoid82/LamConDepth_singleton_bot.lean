module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_lamAtomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_of_fun_empty

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem LamConDepth_singleton_bot :
    LamConDepth A ({.bot} : Finset (RawLamToken α)) := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  have hF : lamFunFinset ({.bot} : Finset (RawLamToken α)) = ∅ := by
    ext p; constructor
    · intro hp; exact False.elim (nomatch mem_lamFunFinset.1 hp)
    · intro hp; exact False.elim (Finset.notMem_empty p hp)
  exact (LamConDepth_of_fun_empty A hF).2 (by
    have h : lamAtomFinset ({.bot} : Finset (RawLamToken α)) = ∅ := by
      ext x; constructor
      · intro hx; exact False.elim (nomatch mem_lamAtomFinset.1 hx)
      · intro hx; exact False.elim (Finset.notMem_empty x hx)
    rw [h]; exact A.con_empty)

end InfoSys

end DomainTheory.InformationSystems
