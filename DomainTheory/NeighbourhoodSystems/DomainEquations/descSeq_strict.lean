module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.iterBot_eq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.component_bot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.pair_bot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descOp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descOp_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descSeq

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

theorem descSeq_strict (k : ApproximableMap (prod V E) E) (hk : IsStrict k) :
    ∀ n, IsStrict (descSeq k n)
  | 0 => isStrict_constBot
  | (n + 1) => by
      have ih := descSeq_strict k hk n
      rw [isStrict_iff_apply_bot] at ih ⊢
      rw [show descSeq k (n + 1) = descOp k (descSeq k n) from rfl, descOp_apply]
      have htl : ofSeq (fun m => component (iterSys V).bot (m + 1)) = (iterSys V).bot := by
        have hconst : (fun m => component (iterSys V).bot (m + 1)) = (fun _ => V.bot) := by
          funext m; rw [component_bot]
        rw [hconst, ← iterBot_eq]
      rw [component_bot, htl, ih, pair_bot]
      exact isStrict_iff_apply_bot.mp hk

end Target

end Exercise618

end DomainTheory.NeighbourhoodSystems
