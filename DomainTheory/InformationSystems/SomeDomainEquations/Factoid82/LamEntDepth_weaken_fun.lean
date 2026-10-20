module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamAtomFinset_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamFunFinset_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

/-- Weaken entailment when the larger set stays in the function world (`atom = ∅`). -/
theorem LamEntDepth_weaken_fun {u v : Finset (RawLamToken α)} {t : RawLamToken α}
    (huv : u ⊆ v) (hv : LamConDepth A v) (hAv : lamAtomFinset v = ∅)
    (ht : LamEntDepth A u t) : LamEntDepth A v t := by
  cases ht with
  | bot _ => exact LamEntDepth.bot hv
  | atom _ _ hne _ =>
    obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hne
    exact False.elim (Finset.notMem_empty x (by
      have := lamAtomFinset_mono huv hx; rwa [hAv] at this))
  | funTok _ _ hConIn hConOut hs hWorld hInCompat hEntIn hEntOut =>
    exact LamEntDepth.funTok hv hAv hConIn hConOut
      (fun p hp => lamFunFinset_mono huv (hs hp))
      (fun hFv => hWorld (Finset.Subset.antisymm
          (fun p hp => by
            have := lamFunFinset_mono huv hp
            rw [hFv] at this; exact False.elim (Finset.notMem_empty p this))
          (Finset.empty_subset _)))
      hInCompat hEntIn hEntOut

end InfoSys

end DomainTheory.InformationSystems
