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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst74
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamDForgetFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_singleton_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_singleton_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_singleton_funTok
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.IsLamWF_of_mem
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.listToLamDFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamDForget_listToLamDFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_mono

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

/-- Bundled consistency on `LamDToken` finsets. -/
def LamDCon (u : Finset (LamDToken A)) : Prop :=
  LamConDepth A (lamDForgetFinset A u)


theorem LamDCon.singleton (p : LamDToken A) : LamDCon A {p} := by
  rw [LamDCon, lamDForgetFinset.singleton]
  match p.val, p.property with
  | .bot, _ => exact LamConDepth_singleton_bot A
  | .atom x, _ => exact LamConDepth_singleton_atom A x
  | .funTok xs ys, ⟨⟨hxs, hys⟩⟩ => exact LamConDepth_singleton_funTok A xs ys hxs hys

theorem LamDCon.listToLamDFinset (xs : List (RawLamToken α))
    (hCon : LamConDepth A (listToFinset xs)) :
    LamDCon A (listToLamDFinset A xs fun _t ht =>
      IsLamWF_of_mem A hCon ((mem_listToFinset).2 ht)) := by
  rw [LamDCon, lamDForget_listToLamDFinset]
  exact hCon

theorem LamDCon.subset {u v : Finset (LamDToken A)}
    (hu : LamDCon A u) (hv : v ⊆ u) : LamDCon A v :=
  LamConDepth_mono A (lamDForgetFinset.mono A hv) hu

end InfoSys

end DomainTheory.InformationSystems
