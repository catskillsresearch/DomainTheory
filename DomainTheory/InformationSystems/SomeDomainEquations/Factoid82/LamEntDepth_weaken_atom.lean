/-ai
Atom entailment weakens along a subset when the larger finite set of raw lambda tokens stays in the atom world, with empty function set. If the smaller set depth-entails an atom and the larger set is depth-consistent, then the larger set depth-entails that atom.

The proof cases on the atom entailment. The atom set grows along the subset and remains nonempty. Entailment in the underlying information system transports by transitivity, using reflexivity on the atoms of the smaller set as they sit in the larger set, in the atom world of both sets.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamAtomFinset_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_of_fun_empty

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

/-- Weaken atom-entailment when the larger set stays in the atom world (`fun = ∅`). -/
theorem LamEntDepth_weaken_atom {u v : Finset (RawLamToken α)} {x : α}
    (huv : u ⊆ v) (hv : LamConDepth A v) (hFv : lamFunFinset v = ∅)
    (ht : LamEntDepth A u (.atom x)) : LamEntDepth A v (.atom x) := by
  cases ht with
  | atom hu hF hne hEnt =>
    have hsubA := lamAtomFinset_mono huv
    have hne' : lamAtomFinset v ≠ ∅ := by
      intro hAv
      obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty hne
      exact Finset.notMem_empty y (by have := hsubA hy; rwa [hAv] at this)
    exact LamEntDepth.atom hv hFv hne'
      (A.ent_trans ((LamConDepth_of_fun_empty A hFv).1 hv)
        ((LamConDepth_of_fun_empty A hF).1 hu)
        (fun y hy => A.ent_refl ((LamConDepth_of_fun_empty A hFv).1 hv) (hsubA hy))
        hEnt)

end InfoSys

end DomainTheory.InformationSystems
