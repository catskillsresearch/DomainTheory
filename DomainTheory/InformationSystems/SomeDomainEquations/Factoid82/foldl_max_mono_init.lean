/-ai
Raising the initial value of the left fold that accumulates the maximum of the accumulator and the raw depth of each token raises the value of the fold.

The proof inducts on the list, keeping both initial values general. The empty fold is the assumed inequality. A nonempty fold applies the inductive hypothesis to the two maxima, which preserve the inequality of the initial values.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst9
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst10
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst17
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst18
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.max_le_max_nat
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.rawDepth

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

omit [DecidableEq α] in

theorem foldl_max_mono_init {u : List (RawLamToken α)} {i j : ℕ} (hij : i ≤ j) :
    List.foldl (fun d t => Nat.max d (rawDepth t)) i u ≤
      List.foldl (fun d t => Nat.max d (rawDepth t)) j u := by
  induction u generalizing i j with
  | nil => exact hij
  | cons a as ih => exact ih (max_le_max_nat hij le_rfl)

end InfoSys

end DomainTheory.InformationSystems
