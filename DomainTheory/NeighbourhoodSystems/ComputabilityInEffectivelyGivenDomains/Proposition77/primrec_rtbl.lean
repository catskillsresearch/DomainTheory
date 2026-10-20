module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.rtbl
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.rtbl_eq_rec

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- `rtbl step` is primitive recursive when `step` is (a single `prec` whose step is a cons). -/
theorem primrec_rtbl {step : ℕ → ℕ} (hstep : Nat.Primrec step) : Nat.Primrec (rtbl step) := by
  have hg : Nat.Primrec (fun c => Nat.pair (step c.unpair.2) c.unpair.2.unpair.2 + 1) :=
    Nat.Primrec.succ.comp ((hstep.comp Nat.Primrec.right).pair
      (Nat.Primrec.right.comp Nat.Primrec.right))
  refine ((Nat.Primrec.prec Nat.Primrec.zero hg).comp
    (Nat.Primrec.zero.pair primrec_id)).of_eq fun w => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rw [rtbl_eq_rec]

end Proposition77

end DomainTheory.NeighbourhoodSystems
